use std::collections::{HashMap, HashSet};

use anyhow::Result;
use cranelift_isle::sema::VarId;
use cranelift_isle_veri::expand::{Chaining, Expander};
use cranelift_isle_veri::program::Program;
use cranelift_isle_veri::solver::{ExampleKind, Solver};
use cranelift_isle_veri::trie;
use cranelift_isle_veri::type_inference::{self, Status};
use cranelift_isle_veri::types::Const;
use cranelift_isle_veri::veri::{Conditions, ExprId, Symbolic};
use cranelift_isle_veri_caching::{Context, ContextBuilder};

const ADD: &str = r#"
    (model i8 (type (bv 8)))
    (state state (type Bool) (default (not state)))
    (decl root (i8 i8) i8)
    (spec (root c x) (provide (= result x)))
    (decl pure add (i8 i8) i8)
    (extern constructor add add)
    (spec (add c x) (provide (= result (bvadd c x))))
    (rule candidate (root c x) (add c x))
"#;

fn with_solver(
    context: Context,
    source: &str,
    test: impl FnOnce(&mut Solver<'_>, ExprId) -> Result<()>,
) -> Result<()> {
    use std::io::Write as _;

    let mut input = tempfile::NamedTempFile::with_suffix(".isle")?;
    input.write_all(source.as_bytes())?;
    let program = Program::from_files(&vec![input.path().to_path_buf()], false)?;
    let source = &program.termenv.rules[0];
    let c = VarId(
        source
            .vars
            .iter()
            .position(|var| program.tyenv.syms[var.name.index()] == "c")
            .unwrap(),
    );
    let rule_sets: HashMap<_, _> = trie::build_trie(&program.termenv, program.files.clone())?
        .into_iter()
        .collect();
    let chaining = Chaining::new(&program, &rule_sets)?;
    let mut expander = Expander::new(&program, &rule_sets, chaining);
    expander.retain_rule_variables(source.id, &[c]);
    expander.add_root_term_name("root")?;
    expander.expand();
    assert_eq!(expander.expansions().len(), 1);
    let expansion = &expander.expansions()[0];
    let conditions = Conditions::from_expansion(expansion, &program, &HashSet::new())?;
    let Symbolic::Scalar(c) = conditions.bindings[&expansion.rule_variables[0][&c]] else {
        panic!("constant must have a scalar model");
    };
    let system = type_inference::type_constraint_system(&conditions);
    let solution = type_inference::Solver::new()
        .solve(&system)
        .into_iter()
        .next()
        .unwrap();
    assert!(matches!(solution.status, Status::Solved));
    let mut solver = Solver::new(context, &program, &conditions, &solution.assignment)?;
    solver.encode()?;
    test(&mut solver, c)
}

#[test]
fn projected_models_are_distinct_and_positive_queries_quantify_runtime_inputs() -> Result<()> {
    let context = ContextBuilder::new()
        .solver("z3")
        .solver_args(["-in", "-smt2", "-t:10000"])
        .build()?;
    with_solver(context, ADD, |solver, c| {
        let negative = solver.example_models(&[c], ExampleKind::Negative, 3)?;
        assert_eq!(negative.len(), 3);
        assert_eq!(negative.iter().collect::<HashSet<_>>().len(), 3);
        assert!(
            negative
                .iter()
                .all(|values| values != &[Const::BitVector(8, 0u8.into())])
        );
        assert_eq!(
            solver.example_models(&[c], ExampleKind::Positive, 2)?,
            [vec![Const::BitVector(8, 0u8.into())]]
        );
        // With no projected constants there is exactly one empty assignment.
        assert_eq!(
            solver.example_models(&[], ExampleKind::Negative, 3)?,
            [Vec::<Const>::new()]
        );
        assert!(
            solver
                .example_models(&[], ExampleKind::Positive, 3)?
                .is_empty()
        );
        Ok(())
    })
}

#[test]
fn uninterpreted_functions_are_rejected() -> Result<()> {
    let context = ContextBuilder::new()
        .solver("z3")
        .solver_args(["-in", "-smt2", "-t:10000"])
        .build()?;
    // sqrt(1.0) = 1.0; the verifier encodes sqrt as an uninterpreted function.
    let source = r#"
        (model i32 (type (bv 32)))
        (state state (type Bool) (default (not state)))
        (decl root (i32 i32) i32)
        (spec (root c x) (provide (= result x)))
        (decl pure square_root (i32) i32)
        (extern constructor square_root square_root)
        (spec (square_root x) (provide (= result (fp.sqrt x))))
        (rule candidate (root c 1065353216)
            (if-let 0 c)
            (square_root 1065353216))
    "#;
    with_solver(context, source, |solver, c| {
        for kind in [ExampleKind::Negative, ExampleKind::Positive] {
            let error = solver.example_models(&[c], kind, 1).unwrap_err();
            assert!(error.to_string().contains("unsupported function"));
            assert!(error.to_string().contains("fp.sqrt_uf_32"));
        }
        Ok(())
    })
}

#[cfg(unix)]
#[test]
fn unknown_is_not_a_positive_model() -> Result<()> {
    let context = ContextBuilder::new()
        .solver("sh")
        .solver_args([
            "-c",
            r#"while IFS= read -r line; do
            case "$line" in
                "(check-sat"*) echo unknown ;;
                "(exit)") echo success; exit ;;
                *) echo success ;;
            esac
        done"#,
        ])
        .build()?;
    with_solver(context, ADD, |solver, c| {
        assert!(
            solver
                .example_models(&[c], ExampleKind::Positive, 0)?
                .is_empty()
        );
        let error = solver
            .example_models(&[c], ExampleKind::Positive, 1)
            .unwrap_err();
        assert!(error.to_string().contains("unknown"));
        Ok(())
    })
}
