pub mod format;

use crate::boolean::format::verilog;

use core::fmt::{
    self, {Display, Formatter},
};
use core::mem;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct IOWire {
    name: String,
    width: u32,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum WireRef {
    Input { id: usize, index: u32 },
    Output { id: usize, index: u32 },
    Internal { id: usize },
}

impl Default for WireRef {
    fn default() -> Self {
        Self::Internal { id: 0 }
    }
}

// impl WireRef {
//     fn format(&self, c: &Circuit, f: &mut Formatter<'_>) -> fmt::Result {
//         match self {
//             Self::Input { id, index } => write!(f, "{}[{}]", c.inputs[id], index),
//             Self::Output { id, index } => write!(f, "{}[{}]", c.outputs[id], index),
//             Self::Internal { id } => write!(f, "w{}", id),
//         }
//     }
// }

impl Display for WireRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input { id, index } => write!(f, "i{}[{}]", id, index),
            Self::Output { id, index } => write!(f, "o{}[{}]", id, index),
            Self::Internal { id } => write!(f, "w{}", id),
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub enum GateType {
    #[default]
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

impl GateType {
    fn num_inputs(&self) -> usize {
        match self {
            Self::Not => 1,
            _ => 2,
        }
    }
    fn num_outputs(&self) -> usize {
        match self {
            _ => 1,
        }
    }
    fn eval(&self, i: &[bool]) -> Vec<bool> {
        match self {
            Self::Not => vec![!i[0]],
            Self::And => vec![i[0] & i[1]],
            Self::AndYN => vec![i[0] & !(i[1])],
            Self::AndNY => vec![!(i[0]) & i[1]],
            Self::Nand => vec![!(i[0] & i[1])],
            Self::Or => vec![i[0] | i[1]],
            Self::OrYN => vec![i[0] | !(i[1])],
            Self::OrNY => vec![!(i[0]) | i[1]],
            Self::Nor => vec![!(i[0] | i[1])],
            Self::Xor => vec![(i[0] & !(i[1])) | (!(i[0]) & i[1])],
            Self::Xnor => vec![!((i[0] & !(i[1])) | (!(i[0]) & i[1]))],
        }
    }
}

impl From<verilog::ast::GateCellType> for GateType {
    fn from(value: verilog::ast::GateCellType) -> Self {
        use verilog::ast::GateCellType;
        match value {
            GateCellType::Not => Self::Not,
            GateCellType::And => Self::And,
            GateCellType::AndYN => Self::AndYN,
            GateCellType::AndNY => Self::AndNY,
            GateCellType::Nand => Self::Nand,
            GateCellType::Or => Self::Or,
            GateCellType::OrYN => Self::OrYN,
            GateCellType::OrNY => Self::OrNY,
            GateCellType::Nor => Self::Nor,
            GateCellType::Xor => Self::Xor,
            GateCellType::Xnor => Self::Xnor,
        }
    }
}

impl Display for GateType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Not => "not",
            Self::And => "and",
            Self::AndYN => "and_yn",
            Self::AndNY => "nand_ny",
            Self::Nand => "nand",
            Self::Or => "or",
            Self::OrYN => "or_yn",
            Self::OrNY => "or_ny",
            Self::Nor => "nor",
            Self::Xor => "xor",
            Self::Xnor => "xnor",
        };
        write!(f, "{}", name)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Gate {
    ty: GateType,
    inputs: Vec<WireRef>,
    outputs: Vec<WireRef>,
}

impl Display for Gate {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (i, output) in self.outputs.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", output)?;
        }
        write!(f, " = {}(", self.ty)?;
        for (i, input) in self.inputs.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", input)?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, Debug)]
pub struct Circuit {
    inputs: Vec<IOWire>,
    outputs: Vec<IOWire>,
    gates: Vec<Gate>,
    // Number of internal wires
    num_wires: usize,
}

impl Circuit {
    fn from_verilog(module: &verilog::Module) -> Self {
        use crate::boolean::format::verilog::ast;

        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        let mut num_wires: usize = 0;
        let mut wire_map = HashMap::new();
        for wire in &module.wires {
            match wire.ty {
                ast::WireType::Input => {
                    let id = inputs.len();
                    inputs.push(IOWire {
                        name: wire.ident.0.clone(),
                        width: wire.width,
                    });
                    wire_map.insert(wire.ident.0.clone(), (ast::WireType::Input, id));
                }
                ast::WireType::Output => {
                    let id = outputs.len();
                    outputs.push(IOWire {
                        name: wire.ident.0.clone(),
                        width: wire.width,
                    });
                    wire_map.insert(wire.ident.0.clone(), (ast::WireType::Output, id));
                }
                ast::WireType::Wire => {
                    if wire_map.contains_key(&wire.ident.0) {
                        // Wire already defined as input / output
                        continue;
                    }
                    let id = num_wires;
                    num_wires += 1;
                    wire_map.insert(wire.ident.0.clone(), (ast::WireType::Wire, id));
                }
            }
        }

        fn new_wire_ref(cell_type: ast::WireType, id: usize, index: u32) -> WireRef {
            match cell_type {
                ast::WireType::Input => WireRef::Input { id, index },
                ast::WireType::Output => WireRef::Output { id, index },
                ast::WireType::Wire => WireRef::Internal { id },
            }
        }

        let mut gates = Vec::new();
        for gate in &module.gate_cells {
            let ty = GateType::from(gate.ty);
            let (num_inputs, num_outputs) = (ty.num_inputs(), ty.num_outputs());
            let mut inputs = Vec::with_capacity(num_inputs);
            let mut outputs = Vec::with_capacity(num_outputs);
            for i in 0..num_inputs {
                let arg = &gate.args[i];
                let (cell_type, id) = wire_map.get(&arg.ident.0).unwrap();
                inputs.push(new_wire_ref(*cell_type, *id, arg.index));
            }
            for i in num_inputs..num_inputs + num_outputs {
                let arg = &gate.args[i];
                let (cell_type, id) = wire_map.get(&arg.ident.0).unwrap();
                outputs.push(new_wire_ref(*cell_type, *id, arg.index));
            }
            gates.push(Gate {
                ty,
                inputs,
                outputs,
            });
        }

        Self {
            inputs,
            outputs,
            gates,
            num_wires,
        }
    }

    fn eval(&self, inputs: Vec<Vec<bool>>) -> Vec<Vec<bool>> {
        let mut wires = vec![None; self.num_wires];
        let mut outputs: Vec<_> = self
            .outputs
            .iter()
            .map(|output| vec![None; output.width as usize])
            .collect();

        for gate in &self.gates {
            let input_values: Vec<_> = gate
                .inputs
                .iter()
                .map(|input| match input {
                    WireRef::Input { id, index } => inputs[*id][*index as usize],
                    WireRef::Output { id, index } => outputs[*id][*index as usize].unwrap(),
                    WireRef::Internal { id } => wires[*id].unwrap(),
                })
                .collect();
            let output_values = gate.ty.eval(&input_values);
            for (output, value) in gate.outputs.iter().zip(output_values) {
                match output {
                    WireRef::Input { .. } => unreachable!(),
                    WireRef::Output { id, index } => outputs[*id][*index as usize] = Some(value),
                    WireRef::Internal { id } => wires[*id] = Some(value),
                }
            }
        }
        outputs
            .iter()
            .map(|output| output.iter().map(|output| output.unwrap()).collect())
            .collect()
    }
}

impl Display for Circuit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "wires = {}, gates = {}",
            self.num_wires,
            self.gates.len(),
        )?;
        writeln!(f, "inputs:")?;
        for (i, input) in self.inputs.iter().enumerate() {
            writeln!(f, "  i{} [{}] : {}", i, input.width, input.name)?;
        }
        writeln!(f, "outputs:")?;
        for (i, output) in self.outputs.iter().enumerate() {
            writeln!(f, "  o{} [{}] : {}", i, output.width, output.name)?;
        }

        for gate in &self.gates {
            writeln!(f, "{}", gate)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct LayeredCircuit {
    inputs: Vec<IOWire>,
    outputs: Vec<IOWire>,
    layers: Vec<Vec<Gate>>,
    // Number of internal wires
    num_wires: usize,
}

impl From<Circuit> for LayeredCircuit {
    fn from(mut c: Circuit) -> Self {
        // Track number of unready inputs per gate
        let mut gates_in_unready_count: Vec<_> =
            c.gates.iter().map(|g| g.ty.num_inputs()).collect();
        // Map of inputs WireRef to gates
        let mut wire_map: HashMap<WireRef, Vec<usize>> = HashMap::new();
        for (gate_index, gate) in c.gates.iter().enumerate() {
            for input in &gate.inputs {
                wire_map
                    .entry(input.clone())
                    .and_modify(|gates| gates.push(gate_index))
                    .or_insert_with(|| vec![gate_index]);
            }
        }
        // All circuit inputs are ready
        let mut wires_ready: Vec<_> = c
            .inputs
            .iter()
            .enumerate()
            .map(|(id, input)| (0..input.width).map(move |index| WireRef::Input { id, index }))
            .flatten()
            .collect();

        let mut num_gates = 0;
        let mut layers = Vec::new();
        while wires_ready.len() > 0 {
            let mut layer = Vec::new();
            let mut new_wires_ready = Vec::new();
            for avail_wire in wires_ready {
                let gates = match wire_map.get(&avail_wire) {
                    Some(gates) => gates,
                    None => continue,
                };
                for gate_index in gates {
                    // For each ready wire we update the number of unready wires of gates that use
                    // them.
                    gates_in_unready_count[*gate_index] -= 1;
                    // If the gate now has 0 unready wires it can be added to this layer and the
                    // outputs become ready wires for the next iteration.
                    if gates_in_unready_count[*gate_index] == 0 {
                        let gate = mem::take(&mut c.gates[*gate_index]);
                        for outputs in &gate.outputs {
                            new_wires_ready.push(*outputs);
                        }
                        layer.push(gate);
                        num_gates += 1;
                    }
                }
            }
            layers.push(layer);
            wires_ready = new_wires_ready;
        }
        assert_eq!(num_gates, c.gates.len());
        Self {
            inputs: c.inputs,
            outputs: c.outputs,
            layers,
            num_wires: c.num_wires,
        }
    }
}

impl Display for LayeredCircuit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "wires = {}, gates = {}",
            self.num_wires,
            self.layers.iter().map(|layer| layer.len()).sum::<usize>()
        )?;
        writeln!(f, "inputs:")?;
        for (i, input) in self.inputs.iter().enumerate() {
            writeln!(f, "  i{} [{}] : {}", i, input.width, input.name)?;
        }
        writeln!(f, "outputs:")?;
        for (i, output) in self.outputs.iter().enumerate() {
            writeln!(f, "  o{} [{}] : {}", i, output.width, output.name)?;
        }

        for (i, layer) in self.layers.iter().enumerate() {
            writeln!(f, "layer {} (len={})", i, layer.len())?;
            for gate in layer {
                writeln!(f, "  {}", gate)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolean::format::verilog::Module;
    use std::fs;

    #[test]
    fn parse_circuit_ast() {
        // let input_file = "./test-data/aes-128-decryption.v";
        let input_file = "./test-data/sample1.v";
        let input = fs::read_to_string(&input_file).unwrap();
        let result = Module::parse(&input).unwrap();
        // println!("{:#?}", result);
        let circuit = Circuit::from_verilog(&result);
        println!("{}", circuit);
        println!();
        let layered_circuit = LayeredCircuit::from(circuit);
        println!("{}", layered_circuit);
    }

    #[test]
    fn parse_circuit_eval() {
        let input_file = "./test-data/sample1.v";
        let input = fs::read_to_string(&input_file).unwrap();
        let result = Module::parse(&input).unwrap();
        // println!("{:#?}", result);
        let circuit = Circuit::from_verilog(&result);
        println!("{}", circuit);
        let output = circuit.eval(vec![
            vec![false, true, true, false, false, false, true, false],
            vec![true, true, false, false, true, true, false, false],
        ]);
        println!("out : {:?}", output);
    }
}
