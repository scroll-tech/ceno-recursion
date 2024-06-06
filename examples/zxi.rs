use circ::front::zsharp::{Inputs, ZSharpFE};
use circ::ir::term::text::parse_value_map;

use circ::cfg::{
    clap::{self, Parser},
    CircOpt,
};
use circ::front::Mode;
use rand_chacha::rand_core::block;
use std::path::PathBuf;

use zokrates_pest_ast::*;
use rug::Integer;

#[derive(Debug, Parser)]
#[command(name = "zxi", about = "The Z# interpreter")]
struct Options {
    /// Input file
    #[arg()]
    zsharp_path: PathBuf,

    /// Scalar input values
    #[arg()]
    inputs_path: Option<PathBuf>,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,
}

fn main() {
    let func_inputs: Vec<usize> = vec![];

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
    let entry_regs: Vec<Integer> = func_inputs.iter().map(|i| Integer::from(*i)).collect();
    let (cs, block_id_list, _, block_inputs_list, mem_list) = ZSharpFE::interpret(inputs, &entry_regs);
    print!("\n\nReturn value: ");
    cs.pretty(&mut std::io::stdout().lock())
        .expect("error pretty-printing value");
    println!();
    for i in 0..block_id_list.len() {
        println!("BLOCK ID: {}", block_id_list[i]);
        let mut str_list = Vec::new();
        for (name, val) in &block_inputs_list[i] {
            str_list.push(format!("{}: {:?}", name, val));
        }
        str_list.sort();
        for s in str_list {
            println!("{}", s);
        }
    }
    println!("MEM");
    for (addr, data) in mem_list {
        println!("ADDR: {:?}", addr);
        println!("DATA: {:?}", data);
    }
}
