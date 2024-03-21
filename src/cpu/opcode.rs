use std::io::{BufRead, BufReader, Cursor, Read, Write};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

/// The instruction set for the CPU, each instruction is represented by a single byte.
#[repr(u8)]
pub enum Instruction {
    Noop = 0x00,
    Copy = 0x01,
    Add = 0x02,
    Jump = 0x03,
    Halt = 0xde,
}

/// A reference to a register or memory location.
#[derive(Debug, PartialEq)]
pub enum Reference {
    Register(u8),
    Memory(u16),
}

impl Reference {
    pub fn read<R: Read>(reader: &mut R) -> Result<Reference, std::io::Error> {
        let kind = reader.read_u8()?;
        match kind {
            0 => Ok(Reference::Register(reader.read_u8()?)),
            1 => Ok(Reference::Memory(reader.read_u16::<LittleEndian>()?)),
            _ => panic!("Invalid reference kind: {}", kind),
        }
    }

    pub fn write<W: Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
        match self {
            Reference::Register(a) => {
                writer.write_u8(0)?;
                writer.write_u8(*a)
            }
            Reference::Memory(a) => {
                writer.write_u8(1)?;
                writer.write_u16::<LittleEndian>(*a)
            }
        }
    }

    pub fn parse<R: Read>(reader: &mut R) -> Result<Reference, std::io::Error> {
        let kind = reader.read_u8()?;
        match kind {
            0 => Ok(Reference::Register(reader.read_u8()?)),
            1 => Ok(Reference::Memory(reader.read_u16::<LittleEndian>()?)),
            _ => panic!("Invalid reference kind: {}", kind),
        }
    }
}

/// A reference to a register or memory location, or a value.
#[derive(Debug, PartialEq)]
pub enum ReferenceOrValue<T> {
    Reference(Reference),
    Value(T),
}

impl ReferenceOrValue<u16> {
    pub fn read<R: Read>(reader: &mut R) -> Result<ReferenceOrValue<u16>, std::io::Error> {
        let kind = reader.read_u8()?;
        match kind {
            0 => Ok(ReferenceOrValue::Reference(Reference::Register(
                reader.read_u8()?,
            ))),
            1 => Ok(ReferenceOrValue::Reference(Reference::Memory(
                reader.read_u16::<LittleEndian>()?,
            ))),
            2 => Ok(ReferenceOrValue::Value(reader.read_u16::<LittleEndian>()?)),
            _ => panic!("Invalid reference kind: {}", kind),
        }
    }

    pub fn write<W: Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
        match self {
            ReferenceOrValue::Reference(r) => match r {
                Reference::Register(a) => {
                    writer.write_u8(0)?;
                    writer.write_u8(*a)
                }
                Reference::Memory(a) => {
                    writer.write_u8(1)?;
                    writer.write_u16::<LittleEndian>(*a)
                }
            },
            ReferenceOrValue::Value(v) => {
                writer.write_u8(2)?;
                writer.write_u16::<LittleEndian>(*v)
            }
        }
    }

    pub fn parse<R: Read>(reader: &mut R) -> Result<ReferenceOrValue<u16>, std::io::Error> {
        let kind = reader.read_u8()?;
        match kind {
            0 => Ok(ReferenceOrValue::Reference(Reference::Register(
                reader.read_u8()?,
            ))),
            1 => Ok(ReferenceOrValue::Reference(Reference::Memory(
                reader.read_u16::<LittleEndian>()?,
            ))),
            2 => Ok(ReferenceOrValue::Value(reader.read_u16::<LittleEndian>()?)),
            _ => panic!("Invalid reference kind: {}", kind),
        }
    }
}

/// The opcodes for the CPU, each opcode is represented by an instruction and a set of arguments.
#[derive(Debug, PartialEq)]
pub enum Opcode {
    Noop,
    Copy(Reference, ReferenceOrValue<u16>),
    Add(ReferenceOrValue<u16>, ReferenceOrValue<u16>),
    Jump(ReferenceOrValue<u16>),
    Halt,
}

#[derive(Debug)]
pub enum ParseError {
    InvalidOpcode(u8),
    Io(std::io::Error),
}

impl Opcode {
    /// Encode the opcode to a byte stream.
    ///
    /// # Examples
    /// ```
    /// use std::io::Cursor;
    /// use zencom::cpu::opcode::{Instruction, Opcode, Reference, ReferenceOrValue};
    /// let opcode = Opcode::Add(ReferenceOrValue::Reference(Reference::Register(0)), ReferenceOrValue::Value(0x1234));
    /// let mut cursor = Cursor::new(Vec::new());
    /// opcode.encode(&mut cursor).unwrap();
    /// assert_eq!(cursor.into_inner(), vec![Instruction::Add as u8, 0x0, 0x0, 0x2, 0x34, 0x12]);
    /// ```
    pub fn encode(&self, writer: &mut impl Write) -> Result<(), std::io::Error> {
        match self {
            Opcode::Noop => writer.write_u8(Instruction::Noop as u8),
            Opcode::Copy(dst, src) => {
                writer.write_u8(Instruction::Copy as u8)?;

                dst.write(writer)?;
                src.write(writer)
            }
            Opcode::Jump(dst) => {
                writer.write_u8(Instruction::Jump as u8)?;
                dst.write(writer)
            }
            Opcode::Add(dst, src) => {
                writer.write_u8(Instruction::Add as u8)?;
                dst.write(writer)?;
                src.write(writer)
            }
            Opcode::Halt => writer.write_all(&[4]),
        }
    }

    /// Parse an opcode from a byte stream.
    /// Returns an error if the opcode is invalid or if the stream is too short.
    ///
    /// # Examples
    /// ```
    /// use std::io::Cursor;
    /// use zencom::cpu::opcode::{Instruction, Opcode, Reference, ReferenceOrValue};
    /// let data: &[u8] = &[Instruction::Add as u8, 0x0, 0x0, 0x2, 0x34, 0x12];
    /// let mut cursor = Cursor::new(data);
    /// let opcode = Opcode::parse(&mut cursor).unwrap();
    /// assert_eq!(opcode, Opcode::Add(ReferenceOrValue::Reference(Reference::Register(0)), ReferenceOrValue::Value(0x1234)));
    /// ```
    pub fn parse(cursor: &mut Cursor<&[u8]>) -> Result<Opcode, ParseError> {
        let opcode = cursor.read_u8().map_err(ParseError::Io)?;
        match opcode {
            0 => Ok(Opcode::Noop),
            1 => {
                let src = Reference::parse(cursor).map_err(ParseError::Io)?;
                let dst = ReferenceOrValue::parse(cursor).map_err(ParseError::Io)?;
                Ok(Opcode::Copy(src, dst))
            }
            2 => {
                let src = ReferenceOrValue::parse(cursor).map_err(ParseError::Io)?;
                let dst = ReferenceOrValue::parse(cursor).map_err(ParseError::Io)?;
                Ok(Opcode::Add(src, dst))
            }
            3 => {
                let dst = ReferenceOrValue::parse(cursor).map_err(ParseError::Io)?;
                Ok(Opcode::Jump(dst))
            }
            0xde => Ok(Opcode::Halt),
            _ => Err(ParseError::InvalidOpcode(opcode)),
        }
    }
}
