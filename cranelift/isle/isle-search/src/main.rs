use std::{collections::HashSet, path::PathBuf, str::FromStr};

use clap::Parser;
use cranelift_isle::{
    ast::Def,
    compile,
    files::Files,
    sema::{BuiltinType, Term, TermEnv, TermId, Type, TypeEnv},
};

#[derive(Parser)]
struct Args {
    #[arg(long)]
    identifier: Option<String>,

    #[arg(long)]
    arg_type: Option<String>,

    #[arg(required = true)]
    inputs: Vec<PathBuf>,
}

fn search_definitions<'a>(ident: &'a str, defs: &'a [Def]) -> Vec<&'a Def> {
    defs.iter()
        .filter(|def| match def {
            Def::Type(typ) if typ.name.0.contains(ident) => true,
            Def::Rule(rule) => match rule.pattern.root_term() {
                Some(rt) if rt.0.contains(ident) => true,
                _ => false,
            },
            Def::Extractor(extractor) if extractor.term.0.contains(ident) => true,
            Def::Decl(decl) if decl.term.0.contains(ident) => true,
            _ => false,
        })
        .collect::<Vec<_>>()
}

fn explain_type(typ: &Type, types: &TypeEnv) -> String {
    match typ {
        Type::Primitive(_, sym, _) => {
            let symbol = types.syms[sym.0].clone();
            format!("{} (primitive type)", symbol)
        }
        Type::Builtin(builtin_type) => match builtin_type {
            BuiltinType::Bool => format!("{} (builtin type)", "bool"),
            BuiltinType::Int(intty) => format!("{} (builtin type)", intty.name()),
        },
        Type::Enum {
            name, ref variants, ..
        } => {
            let mut description = format!("{} (variant type)", types.syms[name.0]);
            println!("{} is a variant type", types.syms[name.0]);
            for variant in variants {
                let name = types.syms[variant.fullname.0].clone();
                description.push_str(&format!("\n   - variant: {}", name));
            }
            description
        }
    }
}

fn explain_term(term: &Term, types: &TypeEnv, _terms: &TermEnv) {
    println!("[Term Explantion ({})]", types.syms[term.name.0].clone());
    // println!("[Argument Types]");
    term.arg_tys.iter().enumerate().for_each(|(i, arg)| {
        let ty = &types.types[arg.0];
        println!(" * arg{}: {}", i, explain_type(ty, types));
        // explain_type(ty, types);
    });
    // println!("[Return Type]");
    println!(
        " * ret: {}",
        explain_type(&types.types[term.ret_ty.0], types)
    );
    // explain_type(&types.types[term.ret_ty.0], types);

    use cranelift_isle::sema::TermKind::*;
    match &term.kind {
        EnumVariant { .. } => todo!(),
        Decl {
            flags,
            constructor_kind,
            extractor_kind,
        } => {
            println!(" * {:?}", flags);

            match constructor_kind {
                Some(cranelift_isle::sema::ConstructorKind::InternalConstructor) => {
                    println!(" * internal constructor")
                }
                Some(cranelift_isle::sema::ConstructorKind::ExternalConstructor { name }) => {
                    println!(" * external constructor: {}", types.syms[name.0])
                }
                None => {
                    println!(" * not a constructor");
                }
            }

            match extractor_kind {
                Some(kind) => match kind {
                    cranelift_isle::sema::ExtractorKind::InternalExtractor { .. } => {
                        println!(" * internal extractor")
                        // println!(" * extractor template: {:?}", template)
                    }
                    cranelift_isle::sema::ExtractorKind::ExternalExtractor {
                        name,
                        infallible,
                        pos: _,
                    } => {
                        if *infallible {
                            println!(" * external extractor: {} (infallible)", types.syms[name.0])
                        } else {
                            println!(" * external extractor: {} (fallible)", types.syms[name.0])
                        }
                    }
                },
                None => {
                    println!(" * not an extractor");
                }
            }
        }
    }
}

fn match_first_sexp(chars: impl Iterator<Item = char>) -> String {
    let mut stack = 0;
    let mut exp = String::new();
    for c in chars {
        exp.push(c);
        if c == '(' {
            stack += 1;
            continue;
        }

        if c == ')' {
            stack -= 1;
            if stack == 0 {
                break;
            }
        }
    }
    exp.trim().to_string()
}

fn get_pos(def: &Def) -> Option<(usize, usize)> {
    match def {
        Def::Type(ty) => Some((ty.name.1.file, ty.name.1.offset)),
        Def::Rule(rule) => {
            let term = rule.pattern.root_term().unwrap();
            Some((term.1.file, term.1.offset))
        }
        Def::Extractor(extractor) => Some((extractor.term.1.file, extractor.term.1.offset)),
        Def::Decl(decl) => Some((decl.term.1.file, decl.term.1.offset)),
        _ => None,
    }
}

fn explain_definition(def: &Def, files: &Files) {
    let (file, offset) = get_pos(def).expect("failed to get position");
    let filename = files.file_name(file).expect("failed to get filename");
    let filepath = PathBuf::from_str(filename).unwrap();
    let basename = filepath.file_name().unwrap();
    let source_code = files.file_text(file).unwrap();
    let linemap = files.file_line_map(file).unwrap();
    let line = linemap.line(offset);
    let linepos = linemap.get(line - 1).unwrap();

    let def_kind = match def {
        Def::Type(_) => "type",
        Def::Rule(_) => "rule definition",
        Def::Extractor(_) => "extractor",
        Def::Decl(_) => "declaration",
        Def::Extern(_) => "extern",
        _ => "unknown",
    };

    let sexp = match_first_sexp(source_code.chars().skip(*linepos));
    println!("[Definition ({})]", identifier_of_def(def));
    println!("* source code: {}", sexp);
    println!("* kind: {}", def_kind);
    println!("* location: {}:{}", basename.to_str().unwrap(), line);

    // eprintln!("* {:?}", def);
}

fn identifier_of_def(def: &Def) -> String {
    match def {
        Def::Type(ty) => ty.name.0.clone(),
        Def::Rule(rule) => rule.pattern.root_term().unwrap().0.clone(),
        Def::Extractor(extractor) => extractor.term.0.clone(),
        Def::Decl(decl) => decl.term.0.clone(),
        _ => "".to_string(),
    }
}

// (decl iconst (Type Imm64) Value)
// (extractor
//     (iconst ty N)
//     (inst_data ty (InstructionData.UnaryImm (Opcode.Iconst) N))
// )
// (rule (iconst ty N)
//     (make_inst ty (InstructionData.UnaryImm (Opcode.Iconst) N))
// )
#[allow(dead_code)]
fn lookup_def(def: &Def, types: &TypeEnv, terms: &TermEnv, _files: &Files) {
    match def {
        Def::Type(typ) => {
            let tid = types
                .get_type_by_name(&typ.name)
                .expect("failed to find type");
            let ty = &types.types[tid.0];
            explain_type(&ty, types);
        }
        Def::Rule(rule) => {
            let term_id = terms
                .get_term_by_name(types, rule.pattern.root_term().unwrap())
                .expect("failed to find term");
            let term = terms.terms[term_id.0].clone();
            // println!("TermId: {:?}", term_id);
            eprintln!("* Term: {:?}", term);
            explain_term(&term, types, terms);
        }
        Def::Extractor(extractor) => {
            let term_id = terms
                .get_term_by_name(types, &extractor.term)
                .expect("failed to find term");
            let term = terms.terms[term_id.0].clone();
            // println!("{:?}", term_id);
            eprintln!("* Term: {:?}", term);
            explain_term(&term, types, terms);
        }
        Def::Decl(decl) => {
            let term_id = terms
                .get_term_by_name(types, &decl.term)
                .expect("failed to find term");
            let term = terms.terms[term_id.0].clone();
            // println!("{:?}", term_id);
            eprintln!("* Term: {:?}", term);
            explain_term(&term, types, terms);
        }
        _ => {}
    }
}

fn termid_of_def(def: &Def, types: &TypeEnv, terms: &TermEnv) -> Option<TermId> {
    match def {
        Def::Rule(rule) => terms.get_term_by_name(types, &rule.pattern.root_term().unwrap()),
        Def::Extractor(extractor) => terms.get_term_by_name(types, &extractor.term),
        Def::Decl(decl) => terms.get_term_by_name(types, &decl.term),
        _ => None,
    }
}

fn search_by_identifier(
    identifier: &str,
    defs: &[Def],
    types: &TypeEnv,
    terms: &TermEnv,
    files: &Files,
) -> Result<(), ()> {
    let founds = search_definitions(identifier, &defs);
    let term_ids = founds
        .iter()
        .filter_map(|def| termid_of_def(def, &types, &terms))
        .collect::<HashSet<_>>();

    if founds.is_empty() {
        eprintln!("No definitions found for {}", identifier);
        return Err(());
    }

    for d in founds {
        explain_definition(d, &files);
    }
    println!();

    for ti in &term_ids {
        let term = terms.terms[ti.0].clone();
        explain_term(&term, &types, &terms);
    }

    println!();
    // find examples
    let mut examples = Vec::new();
    for d in defs {
        match d {
            Def::Rule(_) => {
                let (file, offset) = get_pos(d).expect("failed to get position");
                let source_code = files.file_text(file).unwrap();
                let linemap = files.file_line_map(file).unwrap();
                let line = linemap.line(offset);
                let linepos = linemap.get(line - 1).unwrap();
                let sexp = match_first_sexp(source_code.chars().skip(*linepos));
                // for ti in &term_ids {
                //     let term = terms.terms[ti.0].clone();
                //     let term_name = types.syms[term.name.0].clone();
                //     if sexp.contains(&term_name) {
                //         println!("[Usage ({})]", term_name);
                //         println!("{}", sexp);
                //     }
                // }

                if sexp.contains(identifier) {
                    examples.push(sexp);
                }
            }
            _ => {}
        }
    }
    println!("[Usage ({})]", identifier);
    for example in examples {
        println!("{}", example);
    }

    Ok(())
}

fn main() -> Result<(), ()> {
    let args = Args::parse();
    let files = Files::from_paths(args.inputs).expect("failed to read files");
    let (types, terms, defs) = compile::create_envs(
        files
            .file_names
            .iter()
            .map(|filename| PathBuf::from_str(filename).expect("failed to create path"))
            .collect(),
    )
    .expect("failed to create envs");

    match args.identifier {
        Some(ref ident) => {
            search_by_identifier(ident, &defs, &types, &terms, &files)?;
        }
        None => {}
    }
    Ok(())
}
