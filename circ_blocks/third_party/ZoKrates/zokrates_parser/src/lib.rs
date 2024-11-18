#![allow(clippy::upper_case_acronyms)] // we allow uppercase acronyms because the pest derive generates WHITESPACE and COMMENT which have special meaning in pest

extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::error::Error;
use pest::iterators::Pairs;
use pest::Parser;

#[derive(Parser)]
#[grammar = "zokrates.pest"]
struct ZoKratesParser;

pub fn parse(input: &str) -> Result<Pairs<Rule>, Error<Rule>> {
    ZoKratesParser::parse(Rule::file, input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::*;

    mod examples {
        use super::*;

        #[test]
        fn examples_dir() {
            use glob::glob;
            use std::fs;
            use std::io::Read;
            // Traverse all .zok files in examples dir
            for entry in
                glob("../zokrates_cli/examples/**/*.zok").expect("Failed to read glob pattern")
            {
                match entry {
                    Ok(path) => {
                        if path.to_str().unwrap().contains("error") {
                            continue;
                        }

                        println!("Parsing {:?}", path.display());
                        let mut file = fs::File::open(path).unwrap();

                        let mut data = String::new();
                        file.read_to_string(&mut data).unwrap();

                        assert!(ZoKratesParser::parse(Rule::file, &data).is_ok());
                    }
                    Err(e) => panic!("{:?}", e),
                }
            }
        }
    }

    mod rules {
        use super::*;
        #[test]
        fn parse_invalid_identifier_because_keyword() {
            fails_with! {
                parser: ZoKratesParser,
                input: "endfor",
                rule: Rule::identifier,
                positives: vec![Rule::identifier],
                negatives: vec![],
                pos: 0
            };
        }

        #[test]
        fn parse_for_loop() {
            let input = "for field i in 0..3 do \n c = c + a[i] \n endfor";

            let parse = ZoKratesParser::parse(Rule::iteration_statement, input);
            assert!(parse.is_ok());
        }
    }
}
