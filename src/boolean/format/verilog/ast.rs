use crate::boolean::format::verilog::parser::{GateLevelVerilogParser, GateLevelVerilogRule};
use std::str::FromStr;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ident(pub String);

impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Ident {
    fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
        Self(value.as_str().to_string())
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    ident: Ident,
    ports: Vec<Ident>,
    wires: Vec<Wire>,
    gate_cells: Vec<GateCell>,
}

#[derive(Clone, Copy, Debug)]
pub enum WireType {
    Input,
    Output,
    Wire,
}

impl<'a> From<Pair<'a, GateLevelVerilogRule>> for WireType {
    fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
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
    ty: WireType,
    width: u32,
    ident: Ident,
}

impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Wire {
    fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
        let mut pairs = value.into_inner();
        Self {
            ty: WireType::from(pairs.next().unwrap()),
            width: match_rule(&mut pairs, GateLevelVerilogRule::width)
                .map(|width| {
                    // dbg!(&width);
                    u32::from_str(width.into_inner().next().unwrap().as_str()).unwrap()
                })
                .unwrap_or(1),
            ident: Ident::from(pairs.next().unwrap()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Arg {
    port: Ident,
    ident: Ident,
    index: u32,
}

#[derive(Clone, Debug)]
pub struct GateCell {
    ty: GateCellType,
    ident: Ident,
    args: Vec<Arg>,
}

impl<'a> From<Pair<'a, GateLevelVerilogRule>> for GateCell {
    fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
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
                let index = match_rule(&mut pairs, GateLevelVerilogRule::index)
                    .map(|index| {
                        dbg!(&index);
                        u32::from_str(index.into_inner().next().unwrap().as_str()).unwrap()
                    })
                    .unwrap_or_default();
                Arg { port, ident, index }
            })
            .collect();
        Self { ty, ident, args }
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

impl<'a> From<Pair<'a, GateLevelVerilogRule>> for GateCellType {
    fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
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

use pest::{
    iterators::{Pair, Pairs},
    Parser,
};

fn match_rule<'a, R: pest::RuleType>(pairs: &'a mut Pairs<'_, R>, rule: R) -> Option<Pair<'a, R>> {
    if pairs.peek().filter(|pair| pair.as_rule() == rule).is_some() {
        Some(pairs.next().unwrap())
    } else {
        None
    }
}

fn parse_verilog(input: &str) -> Result<Module, pest::error::Error<GateLevelVerilogRule>> {
    use GateLevelVerilogParser as Parser;
    use GateLevelVerilogRule as Rule;

    let file = Parser::parse(Rule::file, input)?.next().unwrap();
    let module = file.into_inner().next().unwrap();
    // dbg!(&module);
    let mut module_pairs = module.into_inner();
    let module_ident = Ident::from(module_pairs.next().unwrap());

    let ports: Vec<Ident> = match_rule(&mut module_pairs, Rule::port)
        .map(|port| port.into_inner().map(Ident::from).collect())
        .unwrap_or_default();

    let mut wires = Vec::new();
    let mut gate_cells = Vec::new();

    module_pairs.for_each(|pair| match pair.as_rule() {
        GateLevelVerilogRule::wire => wires.push(Wire::from(pair)),
        GateLevelVerilogRule::gate_cell => gate_cells.push(GateCell::from(pair)),
        _ => unreachable!(),
    });

    // fn parse_value(pair: Pair<Rule>) -> Module {
    //     match pair.as_rule() {
    //         Rule::file => parse_value(pair.into_inner()),
    //         _ => unreachable!(),
    //     }
    // }

    Ok(Module {
        ident: module_ident,
        ports,
        wires,
        gate_cells,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::Parser;
    use std::fs;

    #[test]
    fn parse_ast() {
        let input_file = "./test-data/sample1.v";
        let input = fs::read_to_string(&input_file).unwrap();
        let result = parse_verilog(&input);
        println!("{:#?}", result);
    }
}

// use crate::circuit::boolean::{
//     self,
//     format::{
//         topological_sort,
//         verilog::parser::{GateLevelVerilogParser, GateLevelVerilogRule},
//     },
// };
// use anyhow::Result;
// use core::fmt::{
//     self, {Display, Formatter},
// };
// use itertools::{chain, izip, Itertools};
// use pest::{iterators::Pair, Parser};
// use std::collections::HashMap;
//
// #[derive(Clone, Debug)]
// pub struct File {
//     module: Module,
// }
//
// impl File {
//     pub fn new(module: Module) -> Self {
//         Self { module }
//     }
//
//     pub fn parse(input: &str) -> Result<Self> {
//         Ok(Self::from(
//             GateLevelVerilogParser::parse(GateLevelVerilogRule::file, input)?
//                 .next()
//                 .unwrap(),
//         ))
//     }
//
//     pub fn module(&self) -> &Module {
//         &self.module
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for File {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         Self::new(
//             value
//                 .into_inner()
//                 .filter(|p| p.as_rule() == GateLevelVerilogRule::module)
//                 .map(From::from)
//                 .next()
//                 .unwrap(),
//         )
//     }
// }
//
// impl Display for File {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", self.module())
//     }
// }
//
// #[derive(Clone, Debug)]
// pub struct Module {
//     ident: Ident,
//     ports: Vec<Ident>,
//     wires: Vec<Wire>,
//     primitive_cells: Vec<PrimitiveCell>,
//     yosys_cells: Vec<YosysCell>,
//     assigns: Vec<Assign>,
// }
//
// impl Module {
//     pub fn new(
//         ident: Ident,
//         ports: Vec<Ident>,
//         wires: Vec<Wire>,
//         primitive_cells: Vec<PrimitiveCell>,
//         yosys_cells: Vec<YosysCell>,
//         assigns: Vec<Assign>,
//     ) -> Self {
//         Self {
//             ident,
//             ports,
//             wires,
//             primitive_cells,
//             yosys_cells,
//             assigns,
//         }
//     }
//
//     pub fn parse(input: &str) -> Result<Self> {
//         File::parse(input).map(|file| file.module)
//     }
//
//     pub fn ident(&self) -> &Ident {
//         &self.ident
//     }
//
//     pub fn ports(&self) -> &[Ident] {
//         &self.ports
//     }
//
//     pub fn wires(&self) -> &[Wire] {
//         &self.wires
//     }
//
//     pub fn primitive_cells(&self) -> &[PrimitiveCell] {
//         &self.primitive_cells
//     }
//
//     pub fn yosys_cells(&self) -> &[YosysCell] {
//         &self.yosys_cells
//     }
//
//     pub fn assigns(&self) -> &[Assign] {
//         &self.assigns
//     }
// }
//
// impl From<&boolean::BooleanCircuit> for Module {
//     fn from(circuit: &boolean::BooleanCircuit) -> Self {
//         let wire_ident = |i| format!("w{i}").into();
//         let gate_ident = |i| format!("g{i}").into();
//         Module::new(
//             circuit.ident().into(),
//             chain![circuit.inputs(), circuit.outputs()]
//                 .copied()
//                 .map(wire_ident)
//                 .collect(),
//             (0..circuit.n)
//                 .map(|i| {
//                     let ty = if circuit.inputs().contains(&i) {
//                         WireType::Input
//                     } else if circuit.outputs().contains(&i) {
//                         WireType::Output
//                     } else {
//                         WireType::Wire
//                     };
//                     Wire::new(ty, wire_ident(i))
//                 })
//                 .collect(),
//             circuit
//                 .gates()
//                 .iter()
//                 .enumerate()
//                 .map(|(i, gate)| {
//                     PrimitiveCell::new(
//                         gate.ty().into(),
//                         gate_ident(i),
//                         wire_ident(gate.y()),
//                         wire_ident(gate.a()),
//                         gate.b().map(wire_ident),
//                     )
//                 })
//                 .collect(),
//             vec![],
//             vec![],
//         )
//     }
// }
//
// impl From<boolean::BooleanCircuit> for Module {
//     fn from(value: boolean::BooleanCircuit) -> Self {
//         Self::from(&value)
//     }
// }
//
// impl From<&Module> for boolean::BooleanCircuit {
//     fn from(module: &Module) -> Self {
//         let mut circuit = boolean::BooleanCircuit::new(module.ident());
//         let assigns = module
//             .assigns()
//             .iter()
//             .map(|assign| (assign.lhs(), assign.rhs()))
//             .collect::<HashMap<_, _>>();
//         let mut wire_idx = module
//             .wires()
//             .iter()
//             .filter(|wire| !assigns.contains_key(wire.ident()))
//             .map(|wire| (wire.ident(), circuit.allocate()))
//             .collect::<HashMap<_, _>>();
//         module.assigns().iter().for_each(|assign| {
//             wire_idx.insert(assign.lhs(), wire_idx[assign.rhs()]);
//         });
//         let ports = module
//             .wires()
//             .iter()
//             .filter_map(|wire| match wire.ty() {
//                 WireType::Input | WireType::Output => Some((wire.ident(), wire.ty())),
//                 _ => None,
//             })
//             .collect::<HashMap<_, _>>();
//         module
//             .ports()
//             .iter()
//             .for_each(|port| match ports.get(port) {
//                 Some(WireType::Input) => circuit.set_input(wire_idx[port]),
//                 Some(WireType::Output) => circuit.set_output(wire_idx[port]),
//                 _ => {}
//             });
//         circuit.extend_gates(topological_sort(
//             &chain![
//                 module
//                     .primitive_cells()
//                     .iter()
//                     .map(|cell| cell.to_gate(&wire_idx)),
//                 module
//                     .yosys_cells()
//                     .iter()
//                     .map(|cell| cell.to_gate(&wire_idx))
//             ]
//             .collect_vec(),
//         ));
//         circuit
//     }
// }
//
// impl From<Module> for boolean::BooleanCircuit {
//     fn from(value: Module) -> Self {
//         Self::from(&value)
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Module {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         let mut pairs = value.into_inner().peekable();
//         let ident = pairs.next().unwrap().into();
//         let ports = if pairs
//             .peek()
//             .filter(|pair| pair.as_rule() == GateLevelVerilogRule::port)
//             .is_some()
//         {
//             pairs
//                 .next()
//                 .unwrap()
//                 .into_inner()
//                 .map(Ident::from)
//                 .collect()
//         } else {
//             Vec::new()
//         };
//         let mut wires = Vec::new();
//         let mut primitive_cells = Vec::new();
//         let mut yosys_cells = Vec::new();
//         let mut assigns = Vec::new();
//         pairs.for_each(|pair| match pair.as_rule() {
//             GateLevelVerilogRule::wire => wires.push(pair.into()),
//             GateLevelVerilogRule::primitive_cell => primitive_cells.push(pair.into()),
//             GateLevelVerilogRule::yosys_cell => yosys_cells.push(pair.into()),
//             GateLevelVerilogRule::assign => assigns.push(pair.into()),
//             _ => unreachable!(),
//         });
//         Module::new(ident, ports, wires, primitive_cells, yosys_cells, assigns)
//     }
// }
//
// impl Display for Module {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "module {}(", self.ident())?;
//         izip!(0.., self.ports()).try_for_each(|(i, port)| {
//             if i == 0 {
//                 write!(f, "{port}")
//             } else {
//                 write!(f, ", {port}")
//             }
//         })?;
//         writeln!(f, ");")?;
//         self.wires()
//             .iter()
//             .try_for_each(|wire| writeln!(f, "  {wire};"))?;
//         self.primitive_cells()
//             .iter()
//             .try_for_each(|cell| writeln!(f, "  {cell};"))?;
//         self.yosys_cells()
//             .iter()
//             .try_for_each(|cell| writeln!(f, "  {cell};"))?;
//         self.assigns()
//             .iter()
//             .try_for_each(|assign| writeln!(f, "  {assign};"))?;
//         writeln!(f, "endmodule")
//     }
// }
//
// #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct Ident(pub String);
//
// impl From<String> for Ident {
//     fn from(value: String) -> Self {
//         Self(value)
//     }
// }
//
// impl From<&str> for Ident {
//     fn from(value: &str) -> Self {
//         Self(value.to_owned())
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Ident {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         Self::from(value.as_str())
//     }
// }
//
// impl Display for Ident {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", self.0)
//     }
// }
//
// #[derive(Clone, Copy, Debug)]
// pub struct Literal(pub bool);
//
// impl From<bool> for Literal {
//     fn from(value: bool) -> Self {
//         Self(value)
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Literal {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         match value.as_str() {
//             "0" => Self(false),
//             "1" => Self(true),
//             _ => unreachable!(),
//         }
//     }
// }
//
// impl Display for Literal {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", if self.0 { "true" } else { "false" })
//     }
// }
//
// #[derive(Clone, Debug)]
// pub struct Wire {
//     ty: WireType,
//     ident: Ident,
// }
//
// impl Wire {
//     pub fn new(ty: WireType, ident: Ident) -> Self {
//         Self { ty, ident }
//     }
//
//     pub fn ty(&self) -> WireType {
//         self.ty
//     }
//
//     pub fn ident(&self) -> &Ident {
//         &self.ident
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Wire {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         let mut pairs = value.into_inner();
//         Self::new(pairs.next().unwrap().into(), pairs.next().unwrap().into())
//     }
// }
//
// impl Display for Wire {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "{} {}", self.ty, self.ident)
//     }
// }
//
// #[derive(Clone, Copy, Debug)]
// pub enum WireType {
//     Input,
//     Output,
//     Wire,
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for WireType {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         match value.as_str() {
//             "input" => Self::Input,
//             "output" => Self::Output,
//             "wire" => Self::Wire,
//             _ => unreachable!(),
//         }
//     }
// }
//
// impl Display for WireType {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(
//             f,
//             "{}",
//             match self {
//                 Self::Input => "input",
//                 Self::Output => "output",
//                 Self::Wire => "wire",
//             }
//         )
//     }
// }
//
// #[derive(Clone, Debug)]
// pub struct PrimitiveCell {
//     ty: PrimitiveCellType,
//     ident: Ident,
//     y: Ident,
//     a: Ident,
//     b: Option<Ident>,
// }
//
// impl PrimitiveCell {
//     pub fn new(ty: PrimitiveCellType, ident: Ident, y: Ident, a: Ident, b: Option<Ident>) -> Self {
//         assert!(matches!(ty, PrimitiveCellType::Not) ^ b.is_some());
//         Self { ty, ident, y, a, b }
//     }
//
//     pub fn ty(&self) -> PrimitiveCellType {
//         self.ty
//     }
//
//     pub fn ident(&self) -> &Ident {
//         &self.ident
//     }
//
//     pub fn y(&self) -> &Ident {
//         &self.y
//     }
//
//     pub fn a(&self) -> &Ident {
//         &self.a
//     }
//
//     pub fn b(&self) -> Option<&Ident> {
//         self.b.as_ref()
//     }
//
//     pub fn to_gate(&self, wire_idx: &HashMap<&Ident, usize>) -> boolean::BooleanGate {
//         let (y, a, b) = (
//             wire_idx[self.y()],
//             wire_idx[self.a()],
//             self.b().map(|b| wire_idx[b]),
//         );
//         match self.ty() {
//             PrimitiveCellType::Not => boolean::BooleanGate::not(y, a),
//             PrimitiveCellType::And => boolean::BooleanGate::and(y, a, b.unwrap()),
//             PrimitiveCellType::Nand => boolean::BooleanGate::nand(y, a, b.unwrap()),
//             PrimitiveCellType::Or => boolean::BooleanGate::or(y, a, b.unwrap()),
//             PrimitiveCellType::Nor => boolean::BooleanGate::nor(y, a, b.unwrap()),
//             PrimitiveCellType::Xor => boolean::BooleanGate::xor(y, a, b.unwrap()),
//             PrimitiveCellType::Xnor => boolean::BooleanGate::xnor(y, a, b.unwrap()),
//         }
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for PrimitiveCell {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         let mut pairs = value.into_inner();
//         let ty = pairs.next().unwrap().into();
//         let ident = pairs.next().unwrap().into();
//         let y = pairs.next().unwrap().into();
//         let (a, b) = if pairs.len() == 1 {
//             (pairs.next().unwrap().into(), None)
//         } else {
//             (
//                 pairs.next().unwrap().into(),
//                 Some(pairs.next().unwrap().into()),
//             )
//         };
//         Self::new(ty, ident, y, a, b)
//     }
// }
//
// impl Display for PrimitiveCell {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         if let Some(b) = self.b() {
//             write!(
//                 f,
//                 "{} {} ({}, {}, {})",
//                 self.ty(),
//                 self.ident(),
//                 self.y(),
//                 self.a(),
//                 b,
//             )
//         } else {
//             write!(
//                 f,
//                 "{} {} ({}, {})",
//                 self.ty(),
//                 self.ident(),
//                 self.y(),
//                 self.a(),
//             )
//         }
//     }
// }
//
// #[derive(Clone, Copy, Debug)]
// pub enum PrimitiveCellType {
//     Not,
//     And,
//     Nand,
//     Or,
//     Nor,
//     Xor,
//     Xnor,
// }
//
// impl From<boolean::BooleanGateType> for PrimitiveCellType {
//     fn from(value: boolean::BooleanGateType) -> Self {
//         match value {
//             boolean::BooleanGateType::Not => Self::Not,
//             boolean::BooleanGateType::And => Self::And,
//             boolean::BooleanGateType::Nand => Self::Nand,
//             boolean::BooleanGateType::Or => Self::Or,
//             boolean::BooleanGateType::Nor => Self::Nor,
//             boolean::BooleanGateType::Xor => Self::Xor,
//             boolean::BooleanGateType::Xnor => Self::Xnor,
//         }
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for PrimitiveCellType {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         match value.as_str() {
//             "not" => Self::Not,
//             "and" => Self::And,
//             "nand" => Self::Nand,
//             "or" => Self::Or,
//             "nor" => Self::Nor,
//             "xor" => Self::Xor,
//             "xnor" => Self::Xnor,
//             _ => unreachable!(),
//         }
//     }
// }
//
// impl Display for PrimitiveCellType {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(
//             f,
//             "{}",
//             match self {
//                 Self::Not => "not",
//                 Self::And => "and",
//                 Self::Nand => "nand",
//                 Self::Or => "or",
//                 Self::Nor => "nor",
//                 Self::Xor => "xor",
//                 Self::Xnor => "xnor",
//             }
//         )
//     }
// }
//
// #[derive(Clone, Debug)]
// pub struct YosysCell {
//     ty: YosysCellType,
//     ident: Ident,
//     y: Ident,
//     a: Ident,
//     b: Option<Ident>,
// }
//
// impl YosysCell {
//     pub fn new(ty: YosysCellType, ident: Ident, y: Ident, a: Ident, b: Option<Ident>) -> Self {
//         assert!(matches!(ty, YosysCellType::Not) ^ b.is_some());
//         Self { ty, ident, y, a, b }
//     }
//
//     pub fn ty(&self) -> YosysCellType {
//         self.ty
//     }
//
//     pub fn ident(&self) -> &Ident {
//         &self.ident
//     }
//
//     pub fn y(&self) -> &Ident {
//         &self.y
//     }
//
//     pub fn a(&self) -> &Ident {
//         &self.a
//     }
//
//     pub fn b(&self) -> Option<&Ident> {
//         self.b.as_ref()
//     }
//
//     pub fn to_gate(&self, wire_idx: &HashMap<&Ident, usize>) -> boolean::BooleanGate {
//         let (y, a, b) = (
//             wire_idx[self.y()],
//             wire_idx[self.a()],
//             self.b().map(|b| wire_idx[b]),
//         );
//         match self.ty() {
//             YosysCellType::Not => boolean::BooleanGate::not(y, a),
//             YosysCellType::And => boolean::BooleanGate::and(y, a, b.unwrap()),
//             YosysCellType::Nand => boolean::BooleanGate::nand(y, a, b.unwrap()),
//             YosysCellType::Or => boolean::BooleanGate::or(y, a, b.unwrap()),
//             YosysCellType::Nor => boolean::BooleanGate::nor(y, a, b.unwrap()),
//             YosysCellType::Xor => boolean::BooleanGate::xor(y, a, b.unwrap()),
//             YosysCellType::Xnor => boolean::BooleanGate::xnor(y, a, b.unwrap()),
//         }
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for YosysCell {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         let mut pairs = value.into_inner();
//         let ty = pairs.next().unwrap().into();
//         let ident = pairs.next().unwrap().into();
//         let a = pairs.next().unwrap().into();
//         let (b, y) = if pairs.len() == 1 {
//             (None, pairs.next().unwrap().into())
//         } else {
//             (
//                 Some(pairs.next().unwrap().into()),
//                 pairs.next().unwrap().into(),
//             )
//         };
//         Self::new(ty, ident, y, a, b)
//     }
// }
//
// impl Display for YosysCell {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         if let Some(b) = self.b() {
//             write!(
//                 f,
//                 "{} {} (.A({}), .B({}), .Y({}))",
//                 self.ty(),
//                 self.ident(),
//                 self.a(),
//                 b,
//                 self.y(),
//             )
//         } else {
//             write!(
//                 f,
//                 "{} {} (.A({}), .Y({}))",
//                 self.ty(),
//                 self.ident(),
//                 self.a(),
//                 self.y(),
//             )
//         }
//     }
// }
//
// #[derive(Clone, Copy, Debug)]
// pub enum YosysCellType {
//     Not,
//     And,
//     Nand,
//     Or,
//     Nor,
//     Xor,
//     Xnor,
// }
//
// impl From<boolean::BooleanGateType> for YosysCellType {
//     fn from(value: boolean::BooleanGateType) -> Self {
//         match value {
//             boolean::BooleanGateType::Not => Self::Not,
//             boolean::BooleanGateType::And => Self::And,
//             boolean::BooleanGateType::Nand => Self::Nand,
//             boolean::BooleanGateType::Or => Self::Or,
//             boolean::BooleanGateType::Nor => Self::Nor,
//             boolean::BooleanGateType::Xor => Self::Xor,
//             boolean::BooleanGateType::Xnor => Self::Xnor,
//         }
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for YosysCellType {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         match value.as_str() {
//             "\\$_NOT_" => Self::Not,
//             "\\$_AND_" => Self::And,
//             "\\$_NAND_" => Self::Nand,
//             "\\$_OR_" => Self::Or,
//             "\\$_NOR_" => Self::Nor,
//             "\\$_XOR_" => Self::Xor,
//             "\\$_XNOR_" => Self::Xnor,
//             _ => unreachable!(),
//         }
//     }
// }
//
// impl Display for YosysCellType {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(
//             f,
//             "{}",
//             match self {
//                 Self::Not => "\\$_NOT_",
//                 Self::And => "\\$_AND_",
//                 Self::Nand => "\\$_NAND_",
//                 Self::Or => "\\$_OR_",
//                 Self::Nor => "\\$_NOR_",
//                 Self::Xor => "\\$_XOR_",
//                 Self::Xnor => "\\$_XNOR_",
//             }
//         )
//     }
// }
//
// #[derive(Clone, Debug)]
// pub struct Assign {
//     lhs: Ident,
//     rhs: Ident,
// }
//
// impl Assign {
//     pub fn new(lhs: Ident, rhs: Ident) -> Self {
//         Self { lhs, rhs }
//     }
//
//     pub fn lhs(&self) -> &Ident {
//         &self.lhs
//     }
//
//     pub fn rhs(&self) -> &Ident {
//         &self.rhs
//     }
// }
//
// impl<'a> From<Pair<'a, GateLevelVerilogRule>> for Assign {
//     fn from(value: Pair<'a, GateLevelVerilogRule>) -> Self {
//         let mut pairs = value.into_inner();
//         Assign::new(pairs.next().unwrap().into(), pairs.next().unwrap().into())
//     }
// }
//
// impl Display for Assign {
//     fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//         write!(f, "assign {} = {}", self.lhs, self.rhs)
//     }
// }
