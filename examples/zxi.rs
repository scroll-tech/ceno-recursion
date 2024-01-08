use circ::front::zsharp::{Inputs, ZSharpFE};

use circ::cfg::{
    clap::{self, Parser},
    CircOpt,
};
use circ::front::Mode;
use rand_chacha::rand_core::block;
use std::path::PathBuf;

use zokrates_pest_ast::*;

#[derive(Debug, Parser)]
#[command(name = "zxi", about = "The Z# interpreter")]
struct Options {
    /// Input file
    #[arg()]
    zsharp_path: PathBuf,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let mut options = Options::parse();
    options.circ.ir.field_to_bv = circ_opt::FieldToBv::Panic;
    circ::cfg::set(&options.circ);
    let inputs = Inputs {
        file: options.zsharp_path,
        mode: Mode::Proof
    };
    let entry_regs = vec![
        LiteralExpression::DecimalLiteral(
            DecimalLiteralExpression {
                value: DecimalNumber {
                    value: "0".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            }
        ), 
        LiteralExpression::DecimalLiteral(
            DecimalLiteralExpression {
                value: DecimalNumber {
                    value: "5".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            }
        ), 
        LiteralExpression::DecimalLiteral(
            DecimalLiteralExpression {
                value: DecimalNumber {
                    value: "5".to_string(),
                    span: Span::new("", 0, 0).unwrap()
                },
                suffix: Some(DecimalSuffix::Field(FieldSuffix {
                    span: Span::new("", 0, 0).unwrap()
                })),
                span: Span::new("", 0, 0).unwrap()
            }
        )
    ];
    let (cs, block_id_list, block_inputs_list) = ZSharpFE::interpret(inputs, &entry_regs);
    print!("\n\nReturn value: ");
    cs.pretty(&mut std::io::stdout().lock())
        .expect("error pretty-printing value");
    println!();
    for i in 0..block_id_list.len() {
        println!("BLOCK ID: {}", block_id_list[i]);
        for (name, val) in &block_inputs_list[i] {
            println!("{}: {:?}", name, val);
        }
    }
}
