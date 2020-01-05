use crate::{bb::{FuncBB, BB, NextKind}, flow::{FlowElem, Flow, Or}};
use common::{HashSet, HashMap, IndexSet};
use tac::{Tac, Operand};
use bitset::traits::*;

pub fn work(f: &mut FuncBB) {
    let mut alive_var_flow = Flow::<Or>::new(f.bb.len() + 1, f.reg_num as usize);
    let each = alive_var_flow.each();
    let FlowElem { gen, kill, out, .. } = alive_var_flow.split();

    for (off, b) in f.bb.iter().enumerate().map(|b| ((b.0 + 1) * each, b.1)) {
        compute_gen_kill(b, &mut gen[off..off + each], &mut kill[off..off+each]);
    }

    // set initial value of out to gen
    out.bsor(gen);
    alive_var_flow.solve(f.bb.iter().enumerate().map(|b| b.1.next_with_entry(b.0 + 1)));
    let FlowElem { in_, .. } = alive_var_flow.split();
    for (off, b) in f.bb.iter_mut().enumerate().map(|b| ((b.0 + 1) * each, b.1)) {
        do_optimize(b, &mut in_[off..off + each]);
    }
}

fn compute_gen_kill(b: &BB, liveUse: &mut [u32], def: &mut [u32]) {
    match b.next_r() {
        Some(r) => { liveUse.bsset(r); println!("Use tag {}", r); }
        _ => {}
    }
    for t in b.iter().rev() {
        let tac = t.tac.get();
        let (ops, w) = tac.rw();
        match w {
            Some(reg) => {
                println!("Write reg {}", reg);
                def.bsset(reg);
                liveUse.bsdel(reg);
            }
            None => {}
        }
        for o in ops {
            if let Operand::Reg(r) = o {
                println!("Use reg {}", r);
                liveUse.bsset(*r);
            }
        }
    }
}

fn do_optimize(b: &mut BB, in_: &mut [u32]) {
    match b.next_r() {
        Some(r) => { in_.bsset(r); }
        _ => {}
    }
    for t in b.iter().rev() {
        let mut tac = t.tac.get();
        let skip = if let (_, Some(w)) = tac.rw() {
            if in_.bsget(w) { true }
            else { false }
        } else { false };
        if !skip {
            match tac {
                Tac::Bin {..} | Tac::Un {..} | Tac::Assign {..} | Tac::Load {..} | Tac::LoadStr {..} | Tac::LoadVTbl {..} | Tac::LoadFunc {..} => {
                    // del tac
                    b.del(t);
                }
                _ => {}
            }
        }
        // compute in_ for the next tac
        let (op, w) = tac.rw();
        match w {
            Some(reg) => in_.bsdel(reg),
            None => {}
        }
        for o in op {
            if let Operand::Reg(r) = o {
                in_.bsset(*r);
            }
        }
    }
}
