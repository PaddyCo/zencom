# ZenCOM

A simple fantasy computer, easily embeddable in any Rust project.


## Description

Created to serve a very specific purpose in one a prototype I'm working on, ZenCOM is a 16-bit(?) computer with a extremely basic assembly language.


It will mainly be used for text output, but there might be some basic graphics/audio stuff down the line!

## Example usage

At the moment I only have the start of the CPU setup, here is an example of creating a new CPU and then running a simple addition loop:

```rust
use zencom::cpu::{Cpu, PC_START};
use zencom::cpu::opcode::{Opcode, Reference, ReferenceOrValue};

let mut cpu = Cpu::new();

cpu.insert_opcodes(
    PC_START as usize,
    vec![
        Opcode::Add(
            ReferenceOrValue::Reference(Reference::Register(0)),
            ReferenceOrValue::Value(0x0001),
        ),
        Opcode::Add(
            ReferenceOrValue::Reference(Reference::Register(1)),
            ReferenceOrValue::Value(0x0002),
        ),
        Opcode::Jump(ReferenceOrValue::Value(PC_START)),
    ],
);

cpu.registers[0] = 0x0000;
cpu.registers[1] = 0x0000;

// Loop through program 10 times
for _ in 0..10 {
    cpu.process(); // Add to register 0
    cpu.process(); // Add to register 1
    cpu.process(); // Jump back to start
}

assert_eq!(cpu.registers[0], 0x000A);
assert_eq!(cpu.registers[1], 0x0014);
```
