use crate::boolean::format::verilog::parser::{VerilogParser, VerilogRule};

use pest::iterators::{Pair, Pairs};
use pest::Parser;
use std::str::FromStr;

fn match_rule<'a, R: pest::RuleType>(pairs: &'a mut Pairs<'_, R>, rule: R) -> Option<Pair<'a, R>> {
    if pairs.peek().filter(|pair| pair.as_rule() == rule).is_some() {
        Some(pairs.next().unwrap())
    } else {
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident(pub String);

impl<'a> From<Pair<'a, VerilogRule>> for Ident {
    fn from(value: Pair<'a, VerilogRule>) -> Self {
        Self(value.as_str().to_string())
    }
}

#[derive(Clone, Copy, Debug)]
pub enum WireType {
    Input,
    Output,
    Wire,
}

impl<'a> From<Pair<'a, VerilogRule>> for WireType {
    fn from(value: Pair<'a, VerilogRule>) -> Self {
        match value.as_str() {
            "input" => Self::Input,
            "output" => Self::Output,
            "wire" => Self::Wire,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Wire {
    pub ty: WireType,
    pub width: u32,
    pub ident: Ident,
}

impl<'a> From<Pair<'a, VerilogRule>> for Wire {
    fn from(value: Pair<'a, VerilogRule>) -> Self {
        let mut pairs = value.into_inner();
        Self {
            ty: WireType::from(pairs.next().unwrap()),
            width: match_rule(&mut pairs, VerilogRule::width)
                .map(|width| {
                    u32::from_str(width.into_inner().next().unwrap().as_str()).unwrap() + 1
                })
                .unwrap_or(1),
            ident: Ident::from(pairs.next().unwrap()),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum GateCellType {
    Not,
    And,
    AndYN,
    AndNY,
    Nand,
    Or,
    OrYN,
    OrNY,
    Nor,
    Xor,
    Xnor,
}

impl<'a> From<Pair<'a, VerilogRule>> for GateCellType {
    fn from(value: Pair<'a, VerilogRule>) -> Self {
        match value.as_str() {
            "NOT" => Self::Not,
            "AND" => Self::And,
            "ANDYN" => Self::AndYN,
            "ANDNY" => Self::AndNY,
            "NAND" => Self::Nand,
            "OR" => Self::Or,
            "ORYN" => Self::OrYN,
            "ORNY" => Self::OrNY,
            "NOR" => Self::Nor,
            "XOR" => Self::Xor,
            "XNOR" => Self::Xnor,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Arg {
    pub port: Ident,
    pub ident: Ident,
    pub index: u32,
}

#[derive(Clone, Debug)]
pub struct GateCell {
    pub ty: GateCellType,
    pub ident: Ident,
    pub args: Vec<Arg>,
}

impl<'a> From<Pair<'a, VerilogRule>> for GateCell {
    fn from(value: Pair<'a, VerilogRule>) -> Self {
        let mut pairs = value.into_inner();
        let ty = GateCellType::from(pairs.next().unwrap());
        let ident = Ident::from(pairs.next().unwrap());
        let args = pairs
            .next()
            .unwrap()
            .into_inner()
            .map(|cell_args| {
                let mut pairs = cell_args.into_inner();
                let port = Ident::from(pairs.next().unwrap());
                let ident = Ident::from(pairs.next().unwrap());
                let index = match_rule(&mut pairs, VerilogRule::index)
                    .map(|index| {
                        u32::from_str(index.into_inner().next().unwrap().as_str()).unwrap()
                    })
                    .unwrap_or_default();
                Arg { port, ident, index }
            })
            .collect();
        Self { ty, ident, args }
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    pub ident: Ident,
    pub ports: Vec<Ident>,
    pub wires: Vec<Wire>,
    pub gate_cells: Vec<GateCell>,
}

impl Module {
    pub fn parse(input: &str) -> Result<Self, pest::error::Error<VerilogRule>> {
        let file = VerilogParser::parse(VerilogRule::file, input)?
            .next()
            .unwrap();
        let module = file.into_inner().next().unwrap();
        let mut module_pairs = module.into_inner();
        let module_ident = Ident::from(module_pairs.next().unwrap());

        let ports: Vec<Ident> = match_rule(&mut module_pairs, VerilogRule::port)
            .map(|port| port.into_inner().map(Ident::from).collect())
            .unwrap_or_default();

        let mut wires = Vec::new();
        let mut gate_cells = Vec::new();

        module_pairs.for_each(|pair| match pair.as_rule() {
            VerilogRule::wire => wires.push(Wire::from(pair)),
            VerilogRule::gate_cell => gate_cells.push(GateCell::from(pair)),
            _ => unreachable!(),
        });

        Ok(Module {
            ident: module_ident,
            ports,
            wires,
            gate_cells,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn parse_ast() {
        let input_file = "./test-data/sample1.v";
        let input = fs::read_to_string(&input_file).unwrap();
        let result = Module::parse(&input);
        println!("{:#?}", result);
    }
}
