use std::io::Cursor;

use byteorder::{ByteOrder, LittleEndian};

use crate::cpu::opcode::{Reference, ReferenceOrValue};

use self::opcode::Opcode;

pub mod opcode;

/// Representation of a ZenCOM CPU
///
/// # Examples
///
/// A simple example of creating a new CPU and running a simple add loop:
/// ```
/// use zencom::cpu::{Cpu, PC_START};
/// use zencom::cpu::opcode::{Opcode, Reference, ReferenceOrValue};
///
/// let mut cpu = Cpu::new();
///
/// cpu.insert_opcodes(
///     PC_START as usize,
///     vec![
///         Opcode::Add(
///             ReferenceOrValue::Reference(Reference::Register(0)),
///             ReferenceOrValue::Value(0x0001),
///         ),
///         Opcode::Add(
///             ReferenceOrValue::Reference(Reference::Register(1)),
///             ReferenceOrValue::Value(0x0002),
///         ),
///         Opcode::Jump(ReferenceOrValue::Value(PC_START)),
///     ],
/// );
///
/// cpu.registers[0] = 0x0000;
/// cpu.registers[1] = 0x0000;
///
/// // Loop through program 10 times
/// for _ in 0..10 {
///     cpu.process(); // Add to register 0
///     cpu.process(); // Add to register 1
///     cpu.process(); // Jump back to start
/// }
///
/// assert_eq!(cpu.registers[0], 0x000A);
/// assert_eq!(cpu.registers[1], 0x0014);
/// ```
pub struct Cpu {
    /// 8 16-bit registers
    pub registers: [u16; 8],
    /// 4KB of addressable memory
    pub memory: [u8; 4096],
    /// 16-level stack (CURRENTLY UNUSED)
    pub stack: [u16; 16],
    /// Program counter
    pub pc: u16,
    /// Stack pointer (CURRENTLY UNUSED)
    pub sp: u8,
    /// Set when an operation results in a carry
    pub carry: bool,
    /// Set when an operation results in zero
    pub zero: bool,
    /// Set when an operation results in overflow
    pub overflow: bool,
    /// Set when an operation results in a negative number
    pub negative: bool,
}

pub const PC_START: u16 = 0x200;

impl Cpu {
    /// Create a new CPU
    ///
    /// # Examples
    /// ```
    /// use zencom::cpu::Cpu;
    /// let cpu = Cpu::new();
    /// ```
    pub fn new() -> Cpu {
        Cpu {
            registers: [0; 8],
            memory: [0; 4096],
            stack: [0; 16],
            pc: PC_START,
            sp: 0,
            carry: false,
            zero: false,
            overflow: false,
            negative: false,
        }
    }

    /// Reference to value
    ///
    /// # Examples
    /// ```
    /// use zencom::cpu::Cpu;
    /// use zencom::cpu::opcode::Reference;
    /// let mut cpu = Cpu::new();
    /// cpu.registers[0] = 0x1234;
    /// assert_eq!(cpu.ref_to_value(&Reference::Register(0)), 0x1234);
    /// assert_eq!(cpu.ref_to_value(&Reference::Memory(0x400)), 0);
    /// ```
    pub fn ref_to_value(&self, reference: &Reference) -> u16 {
        match reference {
            Reference::Register(reg) => self.registers[*reg as usize],
            Reference::Memory(addr) => LittleEndian::read_u16(&self.memory[*addr as usize..]),
        }
    }

    /// Reference/Value to value
    ///
    /// TODO: Make return value generic, not u16
    ///
    /// # Examples
    /// ```
    /// use zencom::cpu::Cpu;
    /// use zencom::cpu::opcode::{Reference, ReferenceOrValue};
    /// let mut cpu = Cpu::new();
    /// cpu.registers[0] = 0x4321;
    /// assert_eq!(cpu.ref_or_value_to_value(&ReferenceOrValue::Reference(Reference::Register(0))), 0x4321);
    /// assert_eq!(cpu.ref_or_value_to_value(&ReferenceOrValue::Value(0x1234)), 0x1234);
    /// ```
    pub fn ref_or_value_to_value(&self, reference_or_value: &ReferenceOrValue<u16>) -> u16 {
        match reference_or_value {
            ReferenceOrValue::Reference(r) => self.ref_to_value(r),
            ReferenceOrValue::Value(val) => *val,
        }
    }

    /// Process the next instruction
    ///
    /// # Examples
    /// ```
    /// use zencom::cpu::Cpu;
    /// let mut cpu = Cpu::new();
    /// assert_eq!(cpu.pc, 0x200);
    /// cpu.process();
    /// assert_eq!(cpu.pc, 0x201);
    /// ```
    pub fn process(&mut self) {
        // Fetch & parse opcode
        let opcode = {
            let mut reader = Cursor::new(&self.memory[(self.pc as usize)..]);
            let opcode = Opcode::parse(&mut reader);

            // Increment PC
            self.pc += reader.position() as u16;

            opcode
        };

        // Execute opcode
        match opcode {
            Ok(opcode) => match opcode {
                Opcode::Noop => {}
                Opcode::Copy(dst, src) => {
                    let value = self.ref_or_value_to_value(&src);
                    match dst {
                        Reference::Register(reg) => self.registers[reg as usize] = value,
                        Reference::Memory(addr) => {
                            self.memory[addr as usize] = (value & 0xFF) as u8;
                            self.memory[addr as usize + 1] = (value >> 8) as u8;
                        }
                    };
                }
                Opcode::Add(dst, src) => {
                    let a = self.ref_or_value_to_value(&dst);
                    let b = self.ref_or_value_to_value(&src);

                    let (result, overflow) = a.overflowing_add(b);

                    self.carry = result < a;
                    self.zero = result == 0;
                    self.overflow = overflow;
                    self.negative = result & 0x8000 != 0;

                    match dst {
                        ReferenceOrValue::Reference(r) => match r {
                            Reference::Register(reg) => self.registers[reg as usize] = result,
                            Reference::Memory(addr) => {
                                self.memory[addr as usize] = (result & 0xFF) as u8;
                                self.memory[addr as usize + 1] = (result >> 8) as u8;
                            }
                        },
                        ReferenceOrValue::Value(_) => {} // Only reason we add to value is to set flags
                    };
                }
                Opcode::Jump(dst) => {
                    self.pc = match dst {
                        ReferenceOrValue::Reference(Reference::Register(reg)) => {
                            self.registers[reg as usize]
                        }
                        ReferenceOrValue::Reference(Reference::Memory(addr)) => {
                            LittleEndian::read_u16(&self.memory[addr as usize..])
                        }
                        ReferenceOrValue::Value(val) => val,
                    };
                }
                Opcode::Halt => todo!(),
            },
            Err(e) => {
                // Invalid opcode
                panic!("Failed to parse opcode: {:?}", e);
            }
        }
    }

    /// Insert an opcode into memory
    ///
    /// # Examples
    /// ```
    /// use zencom::cpu::Cpu;
    /// use zencom::cpu::opcode::Opcode;
    /// let mut cpu = Cpu::new();
    /// cpu.insert_opcode(0x200, Opcode::Noop);
    /// ```
    pub fn insert_opcode(&mut self, addr: usize, opcode: Opcode) {
        opcode
            .encode(&mut Cursor::new(&mut self.memory[(addr as usize)..]))
            .expect("Failed to encode opcode");
    }

    /// Insert multiple opcodes into memory
    ///
    /// # Examples
    /// ```
    /// use zencom::cpu::Cpu;
    /// use zencom::cpu::opcode::Opcode;
    /// let mut cpu = Cpu::new();
    /// cpu.insert_opcodes(0x200, vec![Opcode::Noop, Opcode::Noop]);
    /// ```
    pub fn insert_opcodes(&mut self, addr: usize, opcodes: Vec<Opcode>) {
        let mut cursor = Cursor::new(&mut self.memory[(addr as usize)..]);

        for opcode in opcodes {
            opcode.encode(&mut cursor).expect("Failed to encode opcode");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_creates_a_new_cpu() {
        let cpu = Cpu::new();

        assert_eq!(cpu.registers, [0; 8]);
        assert_eq!(cpu.memory, [0; 4096]);
        assert_eq!(cpu.stack, [0; 16]);
        assert_eq!(cpu.pc, PC_START);
        assert_eq!(cpu.sp, 0);
        assert_eq!(cpu.carry, false);
        assert_eq!(cpu.zero, false);
        assert_eq!(cpu.overflow, false);
        assert_eq!(cpu.negative, false);
    }

    #[test]
    fn it_processes_an_noop_opcode() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(PC_START as usize, Opcode::Noop);
        cpu.process();

        assert_eq!(cpu.pc, PC_START + 1);
    }

    #[test]
    fn it_processes_a_copy_opcode_with_register_dest() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(
            PC_START as usize,
            Opcode::Copy(Reference::Register(0), ReferenceOrValue::Value(0x1234)),
        );
        cpu.process();

        assert_eq!(cpu.registers[0], 0x1234);
        assert_eq!(cpu.pc, PC_START + 6);
    }

    #[test]
    fn it_processes_a_copy_opcode_with_memory_dest() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(
            PC_START as usize,
            Opcode::Copy(Reference::Memory(0x400), ReferenceOrValue::Value(0x1234)),
        );
        cpu.process();

        assert_eq!(cpu.memory[0x400], 0x34);
        assert_eq!(cpu.memory[0x401], 0x12);
        assert_eq!(cpu.pc, PC_START + 7);
    }

    #[test]
    fn it_processes_a_copy_opcode_with_register_src() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(
            PC_START as usize,
            Opcode::Copy(
                Reference::Register(0),
                ReferenceOrValue::Reference(Reference::Register(1)),
            ),
        );

        cpu.registers[1] = 0x1234;

        cpu.process();

        assert_eq!(cpu.registers[0], 0x1234);
        assert_eq!(cpu.pc, PC_START + 5);
    }

    #[test]
    fn it_processes_a_copy_opcode_with_memory_src() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(
            PC_START as usize,
            Opcode::Copy(
                Reference::Register(0),
                ReferenceOrValue::Reference(Reference::Memory(0x400)),
            ),
        );

        cpu.memory[0x400] = 0x34;
        cpu.memory[0x401] = 0x12;

        cpu.process();

        assert_eq!(cpu.registers[0], 0x1234);
        assert_eq!(cpu.pc, PC_START + 6);
    }

    #[test]
    fn it_processes_a_jump_opcode_with_register_dest() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(
            PC_START as usize,
            Opcode::Jump(ReferenceOrValue::Reference(Reference::Register(0))),
        );

        cpu.registers[0] = 0x400;

        cpu.process();

        assert_eq!(cpu.pc, 0x400);
    }

    #[test]
    fn it_processes_a_add_opcode() {
        let mut cpu = Cpu::new();

        cpu.insert_opcodes(
            PC_START as usize,
            vec![
                Opcode::Add(
                    ReferenceOrValue::Reference(Reference::Register(0)),
                    ReferenceOrValue::Value(0x1234),
                ),
                Opcode::Add(
                    ReferenceOrValue::Reference(Reference::Register(0)),
                    ReferenceOrValue::Value(0x4321),
                ),
            ],
        );

        cpu.registers[0] = 0x2000;

        cpu.process();
        assert_eq!(cpu.registers[0], 0x2000 + 0x1234);
        assert_eq!(cpu.pc, PC_START + 6);
        cpu.process();
        assert_eq!(cpu.registers[0], 0x2000 + 0x1234 + 0x4321);
        assert_eq!(cpu.pc, PC_START + 12);

        // TODO: Verify overflow
    }

    #[test]
    fn it_processes_a_overflowing_add_opcode() {
        let mut cpu = Cpu::new();

        cpu.insert_opcode(
            PC_START as usize,
            Opcode::Add(
                ReferenceOrValue::Reference(Reference::Register(0)),
                ReferenceOrValue::Value(0xFFFF),
            ),
        );

        cpu.registers[0] = 0x0001;

        cpu.process();

        assert_eq!(cpu.registers[0], 0x0000);
        assert_eq!(cpu.carry, true);
        assert_eq!(cpu.zero, true);
        assert_eq!(cpu.overflow, true);
        assert_eq!(cpu.negative, false);
    }

    #[test]
    fn it_processes_a_adding_loop() {
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
            cpu.process();
            cpu.process();
            cpu.process();
        }

        assert_eq!(cpu.registers[0], 0x000A);
        assert_eq!(cpu.registers[1], 0x0014);
    }
}
