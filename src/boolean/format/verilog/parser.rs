use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "./boolean/format/verilog/gate-level-verilog.pest"]
pub struct GateLevelVerilogParser;

pub use Rule as GateLevelVerilogRule;

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;
    use std::fs;

    #[test]
    fn parse_pest() {
        let input_file = "./test-data/sample1.v";
        let input = fs::read_to_string(&input_file).unwrap();
        let result = GateLevelVerilogParser::parse(GateLevelVerilogRule::file, &input);
        let result = match result {
            Err(e) => panic!("{}", e),
            Ok(mut r) => r.next().unwrap(),
        };
        println!("{:#?}", result);
    }
}
