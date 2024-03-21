//! # ZenCOM
//! A simple fantasy computer, easily embeddable in any Rust project.

/// The CPU module contains all the logic for the CPU.
pub mod cpu;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use crate::cpu::Cpu;

    use super::*;

    #[test]
    fn it_works() {
        Cpu::new();
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
