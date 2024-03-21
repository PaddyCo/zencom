use criterion::{criterion_group, criterion_main, Criterion};
use zencom::cpu::{
    opcode::{Opcode, Reference, ReferenceOrValue},
    Cpu, PC_START,
};

fn loop_benchmark(c: &mut Criterion) {
    let mut cpu = Cpu::new();

    cpu.insert_opcodes(
        PC_START as usize,
        vec![Opcode::Jump(ReferenceOrValue::Value(PC_START))],
    );

    c.bench_function("loop", |b| b.iter(|| cpu.process()));
}

fn add_loop_benchmark(c: &mut Criterion) {
    let mut cpu = Cpu::new();

    cpu.insert_opcodes(
        PC_START as usize,
        vec![
            Opcode::Add(
                ReferenceOrValue::Reference(Reference::Register(0)),
                ReferenceOrValue::Value(0x0001),
            ),
            Opcode::Jump(ReferenceOrValue::Value(PC_START)),
        ],
    );

    c.bench_function("add_loop", |b| b.iter(|| cpu.process()));
}

criterion_group!(benches, loop_benchmark, add_loop_benchmark);
criterion_main!(benches);
