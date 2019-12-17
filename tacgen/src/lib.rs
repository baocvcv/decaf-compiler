mod info;

use syntax::{ast::*, ty::*, ScopeOwner};
use ::tac::{self, *, Tac::{self, *}, Operand::*, Intrinsic::*};
use common::{Ref, MAIN_METHOD, BinOp::*, UnOp::*, IndexSet, IndexMap, HashMap};
use typed_arena::Arena;
use std::ops::{Deref, DerefMut};
use crate::info::*;

#[derive(Default)]
struct TacGen<'a> {
  // `reg_num` and `label_num` are manually set at the beginning of every function
  reg_num: u32,
  label_num: u32,
  loop_stk: Vec<u32>,
  // Id & Index will behave differently when they are the lhs of an assignment
  // cur_assign contains the current assign rhs operand, or None if the current handling expr doesn't involve in assign
  cur_assign: Option<Operand>,
  str_pool: IndexSet<&'a str>,
  // `*_info` just works like extra fields to those structs, their specific meaning can be found at `struct *Info`
  var_info: HashMap<Ref<'a, VarDef<'a>>, VarInfo>,
  func_info: HashMap<Ref<'a, FuncDef<'a>>, FuncInfo>,
  class_info: HashMap<Ref<'a, ClassDef<'a>>, ClassInfo<'a>>,
  lambda_info: HashMap<Ref<'a, Lambda<'a>>, LambdaInfo>,

  lambda_stack: Vec<&'a Lambda<'a>>,
  reg_num_stack: Vec<u32>,
  label_num_stack: Vec<u32>,
  lambda_cnt: u32,
  lambda_funcs: Vec<TacFunc<'a>>,

  tp: TacProgram<'a>,
  num_functions: u32,
}

pub fn work<'a>(p: &'a Program<'a>, alloc: &'a Arena<TacNode<'a>>) -> TacProgram<'a> {
  TacGen::default().program(p, alloc)
}

impl<'a> TacGen<'a> {
  fn program(mut self, p: &Program<'a>, alloc: &'a Arena<TacNode<'a>>) -> TacProgram<'a> {
    self.lambda_cnt = 0;
    // identify all the classes
    for (idx, &c) in p.class.iter().enumerate() {
      self.define_str(c.name);
      self.resolve_field(c);
      self.class_info.get_mut(&Ref(c)).unwrap().idx = idx as u32;
      let f = self.build_new(c, alloc);
      self.tp.func.push(f);
    }
    // identify all the functions
    {
      let mut idx = self.tp.func.len() as u32; // their are already some `_Xxx._new` functions in tp.func, so can't start from 0
      for &c in &p.class {
        for &f in &c.field {
          // HACK: this is changed!!!
          if let FieldDef::FuncDef(f) = f {
            if !f.abstract_ {
              self.func_info.get_mut(&Ref(f)).unwrap().idx = idx;
              idx += 1;
            }
          }
        }
      }
      self.num_functions = idx;
    }
    // parse all the functions
    for &c in &p.class {
      for f in &c.field {
        if let FieldDef::FuncDef(fu) = f {
          if !fu.abstract_ {
            // TODO: handle 'this'
//            let this = if fu.static_ { 0 } else { 1 };
            let this = 1;
            for (idx, p) in fu.param.iter().enumerate() {
              self.var_info.insert(Ref(p), VarInfo { off: idx as u32 + this });
            }
            // these regs are occupied by parameters
            self.reg_num = fu.param.len() as u32 + this;
            self.label_num = 0;
            let name = if Ref(c) == Ref(p.main.get().unwrap()) && fu.name == MAIN_METHOD { MAIN_METHOD.into() } else { format!("_{}.{}", c.name, fu.name) };
            let mut f = TacFunc::empty(alloc, name, self.reg_num);
            // TODO: handle abstract method, probably done
            if let Some(b) = &fu.body { self.block(b, &mut f, alloc); }
//          self.block(&fu.body, &mut f);
            f.reg_num = self.reg_num;
            // add an return at the end of return-void function
            if fu.ret_ty() == Ty::void() { f.push(Tac::Ret { src: None }); }
            self.tp.func.push(f);
          }
        }
      }
    }
    // name the vtables
    for &c in &p.class {
      self.tp.vtbl.push(tac::VTbl {
        parent: c.parent_ref.get().map(|p| self.class_info[&Ref(p)].idx),
        class: c.name,
        func: self.class_info[&Ref(c)].vtbl.iter().map(|(_, &f)| self.func_info[&Ref(f)].idx).collect(),
      });
    }
    self.tp.str_pool = self.str_pool;
    self.tp.func.append(&mut self.lambda_funcs);
    self.tp
  }

  fn block(&mut self, b: &'a Block<'a>, f: &mut TacFunc<'a>, alloc: &'a Arena<TacNode<'a>>) {
    for s in &b.stmt { self.stmt(s, f, alloc); }
  }

  fn stmt(&mut self, s: &'a Stmt<'a>, f: &mut TacFunc<'a>, alloc: &'a Arena<TacNode<'a>>) {
    use StmtKind::*;
    match &s.kind {
      Assign(a) => {
        self.cur_assign = Some(self.expr(&a.src, f, alloc));
        self.expr(&a.dst, f, alloc);
      }
      LocalVarDef(v) => {
        let reg = self.reg();
        self.var_info.insert(Ref(v), VarInfo { off: reg });
        // TODO: change to store function and object pointers
        if v.ty.get().is_func() {
          f.push(Param { src: [Const(2 * INT_SIZE)] });
          let add = self.intrinsic(_Alloc, f).unwrap();
          f.push(Tac::Assign { dst: reg, src: [Reg(add)] });
          if let Some((_, e)) = &v.init {
            // with init, store function pointer and object pointer
            // TODO: parse init correctly
            let init = self.expr(e, f, alloc);
            let tmp = self.reg();
            f.push(Load { dst: tmp, base: [init], off: 0, hint: MemHint::Immutable });
            f.push( Store { src_base: [Reg(tmp), Reg(reg)], off: 0, hint: MemHint::Immutable });
            f.push(Load { dst: tmp, base: [init], off: INT_SIZE, hint: MemHint::Immutable });
            f.push( Store { src_base: [Reg(tmp), Reg(reg)], off: INT_SIZE, hint: MemHint::Immutable });
          } else {
            // no init
            f.push( Store { src_base: [Const(0), Reg(reg)], off: 0, hint: MemHint::Immutable });
            f.push( Store { src_base: [Const(0), Reg(reg)], off: INT_SIZE, hint: MemHint::Immutable });
          }
        } else {
//          println!("Localvardef of {}@{:?}:%{}", v.name, v.loc, reg);
          let init = v.init.as_ref().map(|(_, e)| self.expr(e, f, alloc)).unwrap_or(Const(0));
          f.push(Tac::Assign { dst: reg, src: [init] });
        }
//        for (def, info) in self.var_info.iter() {
//          print!("{}@{:?}:{:?}, ", def.name, def.loc, info.off);
//        }
//        println!();
      }
      ExprEval(e) => { self.expr(e, f, alloc); }
      Skip(_) => {}
      If(i) => {
        let before_else = self.label();
        let cond = self.expr(&i.cond, f, alloc);
        f.push(Jif { label: before_else, z: true, cond: [cond] });
        self.block(&i.on_true, f, alloc);
        if let Some(of) = &i.on_false {
          let after_else = self.label();
          f.push(Jmp { label: after_else });
          f.push(Label { label: before_else });
          self.block(of, f, alloc);
          f.push(Label { label: after_else });
        } else {
          f.push(Label { label: before_else });
        }
      }
      While(w) => {
        //   jump before_cond
        // before_body:
        //   body
        // before_cond:
        //   compute cond
        //   if cond jump before_body
        // after_body: (for break's use)
        let (before_cond, before_body, after_body) = (self.label(), self.label(), self.label());
        self.loop_stk.push(after_body);
        f.push(Jmp { label: before_cond });
        f.push(Label { label: before_body });
        self.block(&w.body, f, alloc);
        f.push(Label { label: before_cond });
        let cond = self.expr(&w.cond, f, alloc);
        f.push(Jif { label: before_body, z: false, cond: [cond] });
        f.push(Label { label: after_body });
        self.loop_stk.pop();
      }
      For(fo) => {
        // init
        //   jump before_cond
        // before_body:
        //   body
        //   update
        // before_cond:
        //   compute cond
        //   if cond jump before_body
        // after_body: (for break's use)
        let (before_cond, before_body, after_body) = (self.label(), self.label(), self.label());
        self.loop_stk.push(after_body);
        self.stmt(&fo.init, f, alloc);
        f.push(Jmp { label: before_cond });
        f.push(Label { label: before_body });
        self.block(&fo.body, f, alloc);
        self.stmt(&fo.update, f, alloc);
        f.push(Label { label: before_cond });
        let cond = self.expr(&fo.cond, f, alloc);
        f.push(Jif { label: before_body, z: false, cond: [cond] });
        f.push(Label { label: after_body });
        self.loop_stk.pop();
      }
      Return(r) => {
        let src = r.as_ref().map(|e| [self.expr(e, f, alloc)]);
        f.push(Ret { src });
      }
      Print(p) => for e in p {
        let reg = self.expr(e, f, alloc);
        f.push(Param { src: [reg] });
        match e.ty.get() {
          t if t == Ty::int() => { self.intrinsic(_PrintInt, f); }
          t if t == Ty::bool() => { self.intrinsic(_PrintBool, f); }
          t if t == Ty::string() => { self.intrinsic(_PrintString, f); }
          t => unreachable!("Shouldn't meet type {:?} in Print in these phase, type checking should have reported error.", t),
        }
      }
      Break(_) => { f.push(Jmp { label: *self.loop_stk.last().unwrap() }); }
      Block(b) => self.block(b, f, alloc),
    }
  }

  fn expr(&mut self, e: &'a Expr<'a>, f: &mut TacFunc<'a>, alloc: &'a Arena<TacNode<'a>>) -> Operand {
    use ExprKind::*;
    let assign = self.cur_assign.take();
    match &e.kind {
      VarSel(v) => {
        // if selecting a lambda or function, allocate 8 bytes
        // if selecting a var, just return the register
        if let Some(var) = v.var.get() {
//          println!("{:?} Selected var {} @{:?}", e.loc, var.name, var.loc);
          let off = self.var_info[&Ref(var)].off; // may be register id or offset in class
          match var.owner.get().unwrap() {
            ScopeOwner::Local(_) | ScopeOwner::Param(_) | ScopeOwner::Lambda(_) => {
              let mut reg= off;
              if let Some(l) = self.lambda_stack.last() {
                for (idx, var_tmp) in l.captured_vars.borrow().iter().enumerate() {
                  if var.loc == var_tmp.loc {
                    reg = idx as u32 + 1; // register of the captured var
//                    println!("{:?} Found captured var {} at %{}", e.loc, var.name, reg);
                    break
                  }
                }
              }
              if let Some(src) = assign { // `reg` is register
                f.push(Tac::Assign { dst: reg, src: [src] });
                // the return value won't be used, so just return a meaningless Reg(0), the below Reg(0)s are the same
                Reg(0)
              } else { Reg(reg) }
            }
            ScopeOwner::Class(c) => { // `off` is offset
              // `this` is at argument 0
              // TODO: handle 'this'
              let owner;
              let dst = self.reg();
//              println!("Varsel of {}@{:?}", var.name, var.loc);
              if let Some(c) = self.lambda_stack.last() {
                if let Some(e) = &v.owner {
                  owner = self.expr(e.deref(), f, alloc);
                } else { owner = Reg(0); } // this
//                for (i, vardef_tmp) in c.captured_vars.borrow().iter().enumerate() {
//                  if var.loc == vardef_tmp.loc {
//                    f.push(Load { dst, base: [Reg(2 + i as u32)], off: off as i32 * INT_SIZE, hint: MemHint::Obj });
//                    break
//                  }
//                }
              } else {
                owner = v.owner.as_ref().map(|o| self.expr(o, f, alloc)).unwrap_or(Reg(0));
              }
              if let Some(src) = assign {
                f.push(Store { src_base: [src, owner], off: off as i32 * INT_SIZE, hint: MemHint::Obj });
                Reg(0)
              } else {
                // create a tmp var to store owner.v
                f.push(Load { dst, base: [owner], off: off as i32 * INT_SIZE, hint: MemHint::Obj });
                Reg(dst)
              }
            }
            ScopeOwner::ExprLocal(_) => unreachable!("Impossible to declare a var in Expr Lambda"),
            ScopeOwner::Global(_) => unreachable!("Impossible to declare a variable in global scope."),
          }
        } else if let Some(func) = v.func.get() {
//          println!("{:?} Selected func {} @{:?}", e.loc, func.name, func.loc);
          f.push(Param { src: [Const(2 * INT_SIZE)] });
          let ret = self.intrinsic(_Alloc, f).unwrap();
          if func.static_ {
            let func_ptr = self.reg();
            f.push(LoadFunc { dst: func_ptr, f: self.func_info[&Ref(func)].idx });
            f.push(Store { src_base: [Reg(func_ptr), Reg(ret)], off: 0, hint: MemHint::Immutable });
            f.push(Store { src_base: [Const(0), Reg(ret)], off: INT_SIZE, hint: MemHint::Immutable });
          } else {
            // TODO: non-static funcs should be fetched from the v-table??
            let func_ptr = self.reg();
            f.push(LoadFunc { dst: func_ptr, f: self.func_info[&Ref(func)].idx });
            f.push(Store { src_base: [Reg(func_ptr), Reg(ret)], off: 0, hint: MemHint::Immutable });
            let owner = v.owner.as_ref().map(|o| self.expr(o, f, alloc)).unwrap_or(Reg(0));
            f.push(Store { src_base: [owner, Reg(ret)], off: INT_SIZE, hint: MemHint::Immutable });
          }
          Reg(ret)
        } else { unimplemented!() }
      }
      IndexSel(i) => {
        let (arr, idx) = (self.expr(&i.arr, f, alloc), self.expr(&i.idx, f, alloc));
        let (ok, len, cmp) = (self.reg(), self.length(arr, f), self.reg());
        let (err, after) = (self.label(), self.label());
        f.push(Bin { op: Ge, dst: ok, lr: [idx, Const(0)] })
          .push(Bin { op: Lt, dst: cmp, lr: [idx, len] })
          .push(Bin { op: And, dst: ok, lr: [Reg(ok), Reg(cmp)] })
          .push(Jif { label: err, z: true, cond: [Reg(ok)] });
        // range check passed if reach here
        let off = self.reg();
        f.push(Bin { op: Mul, dst: off, lr: [idx, Const(INT_SIZE)] })
          .push(Bin { op: Add, dst: off, lr: [Reg(off), arr] });
        let ret = if let Some(src) = assign {
          f.push(Store { src_base: [src, Reg(off)], off: 0, hint: MemHint::Arr });
          Reg(0)
        } else {
          let dst = self.reg();
          f.push(Load { dst, base: [Reg(off)], off: 0, hint: MemHint::Arr });
          Reg(dst)
        };
        f.push(Jmp { label: after });
        self.re(INDEX_OUT_OF_BOUND, f.push(Label { label: err }));
        f.push(Label { label: after });
        ret
      }
      IntLit(i) => Const(*i),
      BoolLit(b) => Const(*b as i32),
      StringLit(s) => {
        let dst = self.reg();
        f.push(LoadStr { dst, s: self.define_str(s) });
        Reg(dst)
      }
      NullLit(_) => Const(0),
      Call(c) => {
        let fu = self.expr(c.func.deref(), f, alloc);
//        println!("Func: {:?}", fu);
        let ret = if let Some(_) = c.func.ty.get().return_val() { Some(self.reg()) } else { None };
        let args = c.arg.iter().map(|a| self.expr(a, f, alloc)).collect::<Vec<_>>();

        // fu should be a register containing address to the function/lambda object
        // *(fu + 0) is the function, *(fu + 4) is the object, if any
//        println!("Args len {}", args.len());
        let hint = CallHint {
          arg_obj: c.arg.iter().any(|a| a.ty.get().is_class()),
          arg_arr: c.arg.iter().any(|a| a.ty.get().arr > 0),
        };
        let owner = self.reg();
        f.push(Load { dst: owner, base: [fu], off: INT_SIZE, hint: MemHint::Obj });
        let fu_ptr = self.reg();
        f.push(Load { dst: fu_ptr, base: [fu], off: 0, hint: MemHint::Immutable });
        f.push(Param { src: [Reg(owner)] });
        // for lambdas push the captured vars
        if let Some(l) = c.lambda_ref.get() {
          let p = self.reg();
          for (i, _) in l.captured_vars.borrow().iter().enumerate() {
            f.push(Load { dst: p, base: [fu], off: INT_SIZE * (2 + i as i32), hint: MemHint::Immutable });
            f.push(Param { src: [Reg(p)] });
          }
        }
        for a in args { f.push(Param { src: [a] }); }
        if let ExprKind::VarSel(v) = &c.func.kind {
          if let Some(func_def) = v.func.get() {
            if func_def.static_ { f.push(Tac::Call { dst: ret, kind: CallKind::Static(self.func_info[&Ref(func_def)].idx, hint) }); }
            else { f.push(Tac::Call { dst: ret, kind: CallKind::Virtual([Reg(fu_ptr)], hint) }); }
          } else { f.push(Tac::Call { dst: ret, kind: CallKind::Virtual([Reg(fu_ptr)], hint) }); }
        } else { f.push(Tac::Call { dst: ret, kind: CallKind::Virtual([Reg(fu_ptr)], hint) }); }
        Reg(ret.unwrap_or(0))

            //TODO: another version
//        match &c.func.ty.get() {
//          Ty { arr: _, kind: TyKind::Length(_) } => {
//            // func length assigned to some var
//            // *(fu + 0) = nothing, *(fu + 1) = owner
//            let arr = self.reg();
//            f.push( Load { dst: arr, base: [fu], off: INT_SIZE, hint: MemHint::Immutable });
//            self.length(Reg(arr), f)
//          }
//          Ty { arr: _, kind: _ } => {
//            // some_array.length()
////            let arr = self.expr(v.owner.unwrap().deref(), f);
////            self.length(arr, f);
//            let arr = self.reg();
//            f.push( Load { dst: arr, base: [fu], off: INT_SIZE, hint: MemHint::Immutable });
//            self.length(Reg(arr), f)
//          }
//          Ty { arr: 0, kind: TyKind::Func(params) } => if let ExprKind::VarSel(v) = &c.func.kind {
//            if let Some(func_def) = v.func.get() {
//              let ret = if func_def.ret_ty() != Ty::void() { Some(self.reg()) } else { None };
//              let args = c.arg.iter().map(|a| self.expr(a, f)).collect::<Vec<_>>();
//              let hint = CallHint {
//                arg_obj: c.arg.iter().any(|a| a.ty.get().is_class()) || !func_def.static_,
//                arg_arr: c.arg.iter().any(|a| a.ty.get().arr > 0),
//              };
//              if func_def.static_ {
//                for a in args { f.push(Param { src: [a] }); }
//                f.push(Tac::Call { dst: ret, kind: CallKind::Static(self.func_info[&Ref(func_def)].idx, hint) });
//              } else {
//                // Reg(0) is `this`
//                let owner = v.owner.as_ref().map(|o| self.expr(o, f)).unwrap_or(Reg(0));
//                f.push(Param { src: [owner] });
//                for a in args { f.push(Param { src: [a] }); }
//                let slot = self.reg();
//                // the offset in v-table
//                let off = self.func_info[&Ref(func_def)].off;
//                // TODO: what does this do ?????
//                f.push(Load { dst: slot, base: [owner], off: 0, hint: MemHint::Immutable })
//                    .push(Load { dst: slot, base: [Reg(slot)], off: off as i32 * INT_SIZE, hint: MemHint::Immutable });
//                f.push(Tac::Call { dst: ret, kind: CallKind::Virtual([Reg(slot)], hint) });
//              }
//              Reg(ret.unwrap_or(0)) // if ret is None, the result can't be assigned to others, so 0 will not be used
//            } else { unreachable!("Function without definition!") }
//          } else { unimplemented!() }
//          Ty { arr: 0, kind: TyKind::Lambda(params) } => {
//            // TODO: how to get lambda_def???
//
////            let ret = if fu.ret_ty() != Ty::void() { Some(self.reg()) } else { None };
////            let args = c.arg.iter().map(|a| self.expr(a, f)).collect::<Vec<_>>();
//
//            unimplemented!()
//          }
//          _ => { unreachable!("Not callable!") }
//        }

        //TODO: choose
//        if let ExprKind::VarSel(v) = &c.func.kind {
//          match &v.owner {
//            Some(o) if o.ty.get().is_arr() => {
//              let arr = self.expr(o, f);
//              self.length(arr, f)
//            }
//            // TODO: handle lambda call and var call
//            // TODO: what is assigned to v.func.kind if lambda or var???
//            _ => {
//              if let Some(fu) = c.lambda_ref.get() {
//                let ret = if fu.ret_ty() != Ty::void() { Some(self.reg()) } else { None };
//                let args = c.arg.iter().map(|a| self.expr(a, f)).collect::<Vec<_>>();
//                let hint = CallHint {
//                  arg_obj: c.arg.iter().any(|a| a.ty.get().is_class()),
//                  arg_arr: c.arg.iter().any(|a| a.ty.get().arr > 0),
//                };
//                // TODO: push captured vars onto f
//                // this
////              let owner = v.owner.as_ref().map(|o| self.expr(o, f)).unwrap_or(Reg(0));
////              f.push(Param { src: [owner] });
//                // push other captured vars
//
//
//                // push args
//                for a in args { f.push(Param { src: [a] }); }
//                // make call
//                // TODO: add lambda to list of lambdas?????
//                f.push(Tac::Call { dst: ret, kind: CallKind::Lambda([Reg(0)], hint) });
//
//                Reg(ret.unwrap_or(0)) // if ret is None, the result can't be assigned to others, so 0 will not be used
//              } else if let Some(fu) = c.func_ref.get() {
//                let ret = if fu.ret_ty() != Ty::void() { Some(self.reg()) } else { None };
//                let args = c.arg.iter().map(|a| self.expr(a, f)).collect::<Vec<_>>();
//                let hint = CallHint {
//                  arg_obj: c.arg.iter().any(|a| a.ty.get().is_class()) || !fu.static_,
//                  arg_arr: c.arg.iter().any(|a| a.ty.get().arr > 0),
//                };
//                if fu.static_ {
//                  for a in args { f.push(Param { src: [a] }); }
//                  f.push(Tac::Call { dst: ret, kind: CallKind::Static(self.func_info[&Ref(fu)].idx, hint) });
//                } else {
//                  // Reg(0) is `this`
//                  let owner = v.owner.as_ref().map(|o| self.expr(o, f)).unwrap_or(Reg(0));
//                  f.push(Param { src: [owner] });
//                  for a in args { f.push(Param { src: [a] }); }
//                  let slot = self.reg();
//                  // the offset in v-table
//                  let off = self.func_info[&Ref(fu)].off;
//                  // TODO: what does this do ?????
//                  f.push(Load { dst: slot, base: [owner], off: 0, hint: MemHint::Immutable })
//                      .push(Load { dst: slot, base: [Reg(slot)], off: off as i32 * INT_SIZE, hint: MemHint::Immutable });
//                  f.push(Tac::Call { dst: ret, kind: CallKind::Virtual([Reg(slot)], hint) });
//                }
//                Reg(ret.unwrap_or(0)) // if ret is None, the result can't be assigned to others, so 0 will not be used
//              } else {
//                if let TyKind::Length(_) = c.func.ty.get().kind {
//                  // var c = some_array.length; c();
//                  // TODO: how to get the original array???
//                  let owner = if let Some(vardef) = v.var.get() {
//                    if let ExprKind::VarSel(ori_v) = &vardef.init().unwrap().kind {
//                      ori_v.owner.as_ref()
//                    } else { unimplemented!() }
//                  } else { unimplemented!() };
//                  let arr = self.expr(owner.unwrap().as_ref(), f);
//                  self.length(arr, f)
//                } else {
//                  unreachable!("Invalid function call!\n")
//                }
//              }
//            }
//          } // end
//        } else {
//          let fu = self.expr(c.func.deref(), f);
//
//        }
      }
      Unary(u) => {
        let (r, dst) = (self.expr(&u.r, f, alloc), self.reg());
        f.push(Un { op: u.op, dst, r: [r] });
        Reg(dst)
      }
      Binary(b) => {
        let (l, r) = (self.expr(&b.l, f, alloc), self.expr(&b.r, f, alloc));
        match b.op {
          Eq | Ne if b.l.ty.get() == Ty::string() => {
            f.push(Param { src: [l] }).push(Param { src: [r] });
            let dst = self.intrinsic(_StringEqual, f).unwrap();
            if b.op == Ne {
              f.push(Un { op: Not, dst, r: [Reg(dst)] });
            }
            Reg(dst)
          }
          Div | Mod => {
            let ok = if let Operand::Const(i) = r {
              if i == 0 {
                self.re(DIV_BY_0, f);
                self.intrinsic(_Halt, f);
                false
              } else { true }
            } else { true };
            let dst = self.reg();
            if ok { f.push(Bin { op: b.op, dst, lr: [l, r] }); }
            Reg(dst)
          }
          op => {
            let dst = self.reg();
            f.push(Bin { op, dst, lr: [l, r] });
            Reg(dst)
          }
        }
      }
      This(_) => Reg(0),
      ReadInt(_) => Reg(self.intrinsic(_ReadInt, f).unwrap()),
      ReadLine(_) => Reg(self.intrinsic(_ReadLine, f).unwrap()),
      NewClass(n) => {
        let dst = self.reg();
        // by design, a class's new func in functions have the same index as its vtbl in vtbls
        f.push(Tac::Call { dst: Some(dst), kind: CallKind::Static(self.class_info[&Ref(n.class.get().unwrap())].idx, CallHint { arg_obj: false, arg_arr: false }) });
        Reg(dst)
      }
      NewArray(n) => {
        let len = self.expr(&n.len, f, alloc);
        let (ok, before_cond, before_body) = (self.label(), self.label(), self.label());
        let (cmp, ptr) = (self.reg(), self.reg());
        f.push(Bin { op: Lt, dst: cmp, lr: [len, Const(0)] })
          .push(Jif { label: ok, z: true, cond: [Reg(cmp)] });
        self.re(NEW_ARR_NEG, f);
        f.push(Label { label: ok });
        let arr = self.intrinsic(_Alloc, f
          .push(Bin { op: Mul, dst: ptr, lr: [len, Const(INT_SIZE)] })
          .push(Bin { op: Add, dst: ptr, lr: [Reg(ptr), Const(INT_SIZE)] }) // now ptr = bytes to allocate
          .push(Param { src: [Reg(ptr)] })).unwrap();
        f.push(Bin { op: Add, dst: ptr, lr: [Reg(arr), Reg(ptr)] }); // now ptr = end of array
        f.push(Bin { op: Add, dst: arr, lr: [Reg(arr), Const(INT_SIZE)] }); // now arr = begin of array([0])
        f.push(Jmp { label: before_cond }) // loop(reversely), set all to 0
          .push(Label { label: before_body })
          .push(Bin { op: Sub, dst: ptr, lr: [Reg(ptr), Const(INT_SIZE)] })
          .push(Store { src_base: [Const(0), Reg(ptr)], off: 0, hint: MemHint::Arr })
          .push(Label { label: before_cond })
          .push(Bin { op: Eq, dst: cmp, lr: [Reg(ptr), Reg(arr)] })
          .push(Jif { label: before_body, z: true, cond: [Reg(cmp)] }); // when ptr == arr, loop end
        f.push(Store { src_base: [len, Reg(arr)], off: -INT_SIZE, hint: MemHint::Immutable }); // arr[-1] = len
        Reg(arr)
      }
      ClassTest(t) => {
        let obj = self.expr(&t.expr, f, alloc);
        self.check_cast(obj, self.class_info[&Ref(t.class.get().unwrap())].idx, f)
      }
      ClassCast(t) => {
        let obj = self.expr(&t.expr, f, alloc);
        let check = self.check_cast(obj, self.class_info[&Ref(t.class.get().unwrap())].idx, f);
        let (msg, vtbl, ok) = (self.reg(), self.reg(), self.label());
        f.push(Jif { label: ok, z: false, cond: [check] });
        let s = self.define_str(BAD_CAST1); // borrow checker...
        self.intrinsic(_PrintString, f.push(LoadStr { dst: msg, s }).push(Param { src: [Reg(msg)] }));
        self.intrinsic(_PrintString, f.push(Load { dst: vtbl, base: [obj], off: 0, hint: MemHint::Immutable })
          .push(Load { dst: msg, base: [Reg(vtbl)], off: INT_SIZE as i32, hint: MemHint::Immutable }).push(Param { src: [Reg(msg)] }));
        let s = self.define_str(BAD_CAST2);
        self.intrinsic(_PrintString, f.push(LoadStr { dst: msg, s }).push(Param { src: [Reg(msg)] }));
        let s = self.define_str(t.name);
        self.intrinsic(_PrintString, f.push(LoadStr { dst: msg, s }).push(Param { src: [Reg(msg)] }));
        let s = self.define_str(BAD_CAST3);
        self.intrinsic(_PrintString, f.push(LoadStr { dst: msg, s }).push(Param { src: [Reg(msg)] }));
        self.intrinsic(_Halt, f);
        f.push(Label { label: ok });
        obj
      }
        // TODO: lambda
      Lambda(l) => {
        // store the current states
        self.reg_num_stack.push(self.reg_num);
        self.label_num_stack.push(self.label_num);
        self.lambda_stack.push(l);
        self.reg_num = 0;
        self.label_num = 0;

        // parse function
        let mut idx = 1 + l.captured_vars.borrow().len() as u32;
        for p in l.param.iter() {
          self.var_info.insert(Ref(p), VarInfo { off: idx });
          idx += 1;
        }
        self.reg_num = idx;
        let name = format!("Lambda{}", self.lambda_cnt);
        self.lambda_cnt += 1;
        let mut fc = TacFunc::empty(alloc, name, self.reg_num);
        if let Some(b) = &l.body.body {
          self.block(b, &mut fc, alloc);
          if l.ret_ty() == Ty::void() { fc.push(Tac::Ret{ src: None }); }
        } else if let Some(e) = &l.body.expr {
          let r = self.expr(e, &mut fc, alloc);
          fc.push(Tac::Ret{ src: Some([r]) });
        }
        fc.reg_num = self.reg_num;

        // push to tp.func
        self.lambda_funcs.push(fc);
        self.lambda_info.insert(Ref(l), LambdaInfo { idx: self.num_functions });
        self.num_functions += 1;

        // restore states
        self.lambda_stack.pop();
        self.reg_num = self.reg_num_stack.pop().unwrap();
        self.label_num = self.label_num_stack.pop().unwrap();

        // generate lambda object
        // 0-function pointer 1-this? 2-... captured vars
        let len = 2 + l.captured_vars.borrow().len() as i32;
        f.push(Param { src: [Const(len * INT_SIZE)] });
        let ret = self.intrinsic(_Alloc, f).unwrap();
        // load function ptr
        let func_ptr = self.reg();
        f.push(LoadFunc { dst: func_ptr, f: self.lambda_info[&Ref(l)].idx });
        f.push(Store { src_base: [Reg(func_ptr), Reg(ret)], off: 0, hint: MemHint::Immutable });
        if let Some(_c) = l.this.get() { // load "this"
          // Reg(0) suppposed to be "this"
          f.push(Store { src_base: [Reg(0), Reg(ret)], off: INT_SIZE, hint: MemHint::Immutable });
        } else {
          f.push(Store { src_base: [Const(0), Reg(ret)], off: INT_SIZE, hint: MemHint::Immutable });
        }
        // load captured vars
//        println!("In lambda {}", self.lambda_info[&Ref(l)].idx);
//        for (def, info) in self.var_info.iter() {
//          print!("{}@{:?}:{:?}, ", def.name, def.loc, info.off);
//        }
//        println!();
        for (i, vardef) in l.captured_vars.borrow().iter().enumerate() {
//          print!("{}@{:?}:{:?}  ", vardef.name, vardef.loc, Reg(self.var_info[&Ref(*vardef)].off));
//          f.push(Store { src_base: [Reg(self.var_info[&Ref(*vardef)].off), Reg(ret)], off: (2 + i as i32) * INT_SIZE, hint: MemHint::Immutable });
          if let Some(l_tmp) = self.lambda_stack.last() {
            if vardef.loc > l_tmp.loc { // local
              f.push(Store { src_base: [Reg(self.var_info[&Ref(*vardef)].off), Reg(ret)], off: (2 + i as i32) * INT_SIZE, hint: MemHint::Immutable });
            } else { // captured var
              for (j, vardef_tmp) in l_tmp.captured_vars.borrow().iter().enumerate() {
                if vardef_tmp.loc == vardef.loc {
                  let r = self.reg();
                  f.push( Tac::Assign { dst: r, src: [Reg(1 + j as u32)] });
                  f.push(Store { src_base: [Reg(r), Reg(ret)], off: (2 + i as i32) * INT_SIZE, hint: MemHint::Immutable });
                  break
                }
              }
            }
          } else {
            f.push(Store { src_base: [Reg(self.var_info[&Ref(*vardef)].off), Reg(ret)], off: (2 + i as i32) * INT_SIZE, hint: MemHint::Immutable });
          }
        }
//        println!();
        Reg(ret)
      }
    }
  }
}

impl<'a> TacGen<'a> {
  // define a string in str pool and return its id, this id can be used in Tac::LoadStr
  fn define_str(&mut self, s: &'a str) -> u32 { self.str_pool.insert_full(s).0 as u32 }

  fn reg(&mut self) -> u32 { (self.reg_num, self.reg_num += 1).0 }

  fn label(&mut self) -> u32 { (self.label_num, self.label_num += 1).0 }

  // if you don't need to modify the returned register, it is more recommended to use Const(i)
  fn int(&mut self, i: i32, f: &mut TacFunc<'a>) -> u32 {
    let dst = self.reg();
    f.push(Tac::Assign { dst, src: [Const(i)] });
    dst
  }

  // perform an intrinsic call, return value is Some if this intrinsic call has return value
  fn intrinsic(&mut self, i: Intrinsic, f: &mut TacFunc<'a>) -> Option<u32> {
    let dst = if i.has_ret() { Some(self.reg()) } else { None };
    f.push(Tac::Call { dst, kind: CallKind::Intrinsic(i) });
    dst
  }

  // read the length of `arr` (caller should guarantee `arr` is really an array)
  fn length(&mut self, arr: Operand, f: &mut TacFunc<'a>) -> Operand {
    let dst = self.reg();
    f.push(Load { dst, base: [arr], off: -(INT_SIZE as i32), hint: MemHint::Immutable });
    Reg(dst)
  }

  // re is short for for runtime error; this function prints a message and call halt
  fn re(&mut self, msg: &'static str, f: &mut TacFunc<'a>) {
    let src = self.reg();
    let s = self.define_str(msg);
    self.intrinsic(_PrintString, f.push(LoadStr { dst: src, s }).push(Param { src: [Reg(src)] }));
    self.intrinsic(_Halt, f);
  }

  fn check_cast(&mut self, obj: Operand, vtbl_idx: u32, f: &mut TacFunc<'a>) -> Operand {
    // ret = 0
    // while (cur)
    //   ret = (cur == target)
    //   if ret = 1
    //     break
    //   cur = cur->parent
    let (ret, cur, target) = (self.int(0, f), self.reg(), self.reg());
    let (before_cond, after_body) = (self.label(), self.label());
    f.push(LoadVTbl { dst: target, v: vtbl_idx });
    f.push(Load { dst: cur, base: [obj], off: 0, hint: MemHint::Immutable });
    f.push(Label { label: before_cond });
    f.push(Jif { label: after_body, z: true, cond: [Reg(cur)] });
    f.push(Bin { op: Eq, dst: ret, lr: [Reg(cur), Reg(target)] }).push(Jif { label: after_body, z: false, cond: [Reg(ret)] });
    f.push(Load { dst: cur, base: [Reg(cur)], off: 0, hint: MemHint::Immutable });
    f.push(Jmp { label: before_cond });
    f.push(Label { label: after_body });
    Reg(ret)
  }
}

impl<'a> TacGen<'a> {
  // `idx` in ClassInfo & FuncInfo is not determined here, just set them to a meaningless value (0)
  // all functions (static & virtual) are inserted into self.func_info
  // this function relies on the fact that no cyclic inheritance exist, which is guaranteed in typeck
  fn resolve_field(&mut self, c: &'a ClassDef<'a>) {
    // add c to list of classes
    if !self.class_info.contains_key(&Ref(c)) {
      // parse parent if any
      let (mut field_num, mut vtbl) = if let Some(p) = c.parent_ref.get() {
        self.resolve_field(p);
        let p = &self.class_info[&Ref(p)];
        (p.field_num, p.vtbl.clone())
      } else { (1, IndexMap::default()) };
      // parse all the fields
      for f in &c.field {
        match f {
          FieldDef::FuncDef(f) => if !f.abstract_ {
            if !f.static_ { // !abstract & !static
              if let Some((idx, _, p_f)) = vtbl.get_full_mut(f.name) {
                // + 2, because 0 is parent vtbl, 1 is class name
                self.func_info.insert(Ref(f), FuncInfo { off: idx as u32 + 2, idx: 0 });
                *p_f = f; // override
              } else { // !static
                self.func_info.insert(Ref(f), FuncInfo { off: vtbl.len() as u32 + 2, idx: 0 });
                vtbl.insert(f.name, f);
              }
            } else {
              // `off` is useless for static functions
              self.func_info.insert(Ref(f), FuncInfo { off: 0, idx: 0 });
            } // abstract methods do not get an entry
          }
          FieldDef::VarDef(v) => {
            self.var_info.insert(Ref(v), VarInfo { off: field_num });
            field_num += 1;
            // changed!: to store function objects
//            match v.ty.get().kind {
//              TyKind::Func(_) | TyKind::Lambda(_) => {
//                //TODO: allocate memory to store function and obj pointers
//                self.var_info.insert(Ref(v), VarInfo { off: field_num });
//                field_num += 2;
//              }
//              _ => {
//                self.var_info.insert(Ref(v), VarInfo { off: field_num });
//                field_num += 1;
//              }
//            }
          }
        }
      }
      // idx set later in function "program"
      self.class_info.insert(Ref(c), ClassInfo { field_num, idx: 0, vtbl });
    }
  }

  fn build_new(&mut self, c: &'a ClassDef<'a>, alloc: &'a Arena<TacNode<'a>>) -> TacFunc<'a> {
    self.reg_num = 0;
    let ClassInfo { field_num, idx, .. } = self.class_info[&Ref(c)];
    let mut f = TacFunc::empty(alloc, format!("_{}._new", c.name), 0);
    f.push(Param { src: [Const(field_num as i32 * INT_SIZE)] });
    let ret = self.intrinsic(_Alloc, &mut f).unwrap();
    let vtbl = self.reg();
    f.push(LoadVTbl { dst: vtbl, v: idx });
    f.push(Store { src_base: [Reg(vtbl), Reg(ret)], off: 0, hint: MemHint::Immutable });
//    for i in 1..field_num {
//      f.push(Store { src_base: [Const(0), Reg(ret)], off: i as i32 * INT_SIZE, hint: MemHint::Obj });
//    }
    let mut i = 1;
    for field in &c.field {
      if let FieldDef::VarDef(v) = field {
        match &v.ty.get().kind {
          TyKind::Func(_) | TyKind::Lambda(_) => {
            f.push(Param { src: [Const(2 * INT_SIZE)] });
            let reg = self.intrinsic(_Alloc, &mut f).unwrap();
            f.push(Store { src_base: [Reg(reg), Reg(ret)], off: i as i32 * INT_SIZE, hint: MemHint::Obj });
          }
          _ => {
            f.push(Store { src_base: [Const(0), Reg(ret)], off: i as i32 * INT_SIZE, hint: MemHint::Obj });
          }
        }
        i = i + 1;
      }
    }
    f.push(Ret { src: Some([Reg(ret)]) });
    f.reg_num = self.reg_num;
    f
  }
}