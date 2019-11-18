use crate::{TypeCk, TypeCkTrait};
use common::{ErrorKind::*, Loc, LENGTH, BinOp, UnOp, ErrorKind, Ref, HashSet, HashMap};
use syntax::ast::*;
use syntax::{ScopeOwner, Symbol, ty::*};
use std::ops::{Deref, DerefMut};
use std::iter;
use std::cell::RefCell;
use std::cell::Cell;
use std::borrow::Borrow;

pub(crate) struct TypePass<'a>(pub TypeCk<'a>);

impl<'a> Deref for TypePass<'a> {
  type Target = TypeCk<'a>;
  fn deref(&self) -> &Self::Target { &self.0 }
}

impl<'a> DerefMut for TypePass<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<'a> TypePass<'a> {
  pub fn program(&mut self, p: &'a Program<'a>) {
    for c in &p.class { self.class_def(c); }
  }

  fn class_def(&mut self, c: &'a ClassDef<'a>) {
//    println!("Class {}", c.name);
    self.cur_class = Some(c);
    self.scoped(ScopeOwner::Class(c), |s| for f in &c.field {
      if let FieldDef::FuncDef(f) = f {
        s.cur_func = Some(f);
        if !f.abstract_ { // if not abstract
          let ret = s.scoped(ScopeOwner::Param(f), |s| s.block(&f.body.as_ref().unwrap()));
          if !ret && f.ret_ty() != Ty::void() { s.issue(f.body.as_ref().unwrap().loc, ErrorKind::NoReturn) }
        }
      };
    });
  }

  fn block(&mut self, b: &'a Block<'a>) -> bool {
//    println!("In block @ {:?}", b.loc);
    let mut ret = false;
    self.scoped(ScopeOwner::Local(b), |s| for st in &b.stmt { ret = s.stmt(st); });
    ret
  }

  // return whether this stmt has a return value
  fn stmt(&mut self, s: &'a Stmt<'a>) -> bool {
//    println!("Statement @ {:?}", s.loc);
    match &s.kind {
      StmtKind::Assign(a) => {
        let (l, r) = (self.expr(&a.dst), self.expr(&a.src));
        if !r.assignable_to(l) { self.issue(s.loc, IncompatibleBinary { l, op: "=", r }) }
        // TODO: check for wrong reference
        if self.lambda_cnt > 0 {
          if let ExprKind::VarSel(v) = &a.dst.kind {
//            println!("{}: ", v.name);
//            for s in &self.scopes.stack {
//              let name = match s {
//                ScopeOwner::Global(_) => "Global",
//                ScopeOwner::Local(_) => "Block",
//                ScopeOwner::Class(c) => c.name,
//                ScopeOwner::Param(f) => f.name,
//                ScopeOwner::Lambda(_) => "lambda",
//              };
//              println!("{}", name);
//            }
            if let None = v.owner {
              let mut has_escaped_lambda = false;
              let mut is_error = false;
              for scope in self.scopes.stack.iter().rev() {
                if scope.is_lambda() {
                  // 1 defined in lambda's parameters
                  if let Some(t) = scope.scope().get(v.name) { break }
                  has_escaped_lambda = true;
                } else if scope.is_local() {
                  // 2 defined locally
                  if let Some(t) = scope.scope().get(v.name) {
                    if t.loc() > a.dst.loc || has_escaped_lambda {
                      is_error = true;
                      break
                    } else { break }
                  }
                } else if scope.is_class() {
                  // defined in class
                  if let Some(t) = scope.scope().get(v.name) { break }
                }
              }
              if is_error { self.issue(s.loc, NoAssignLambda) }
            }
          }
        } else {
          if let ExprKind::VarSel(v) = &a.dst.kind {
            if let Some(f) = v.func.get() {
              self.issue(s.loc, NoAssignMemberMethod(f.name))
            }
          }
        }
        false
      }
      StmtKind::LocalVarDef(v) => {
//        println!("Vardef finish loc {:?}", v.finish_loc);
        if let Some((loc, e)) = &v.init {
          let (l, r) = (v.ty.get(), self.expr(e));
          // TODO: how to assign inferred def to var???
          if v.syn_ty.kind == SynTyKind::Var {
            v.ty.set( r.clone());
            if v.ty.get().kind == TyKind::Void { self.issue(v.loc, VoidVar(v.name)) }
          } else if !r.assignable_to(l) { self.issue(*loc, IncompatibleBinary { l, op: "=", r }) }
        }
        false
      }
      StmtKind::ExprEval(e) => {
        self.expr(e);
        false
      }
      StmtKind::Skip(_) => false,
      StmtKind::If(i) => {
        self.check_bool(&i.cond);
        // `&` is not short-circuit evaluated
        self.block(&i.on_true) & i.on_false.as_ref().map(|b| self.block(b)).unwrap_or(false)
      }
      StmtKind::While(w) => {
        self.check_bool(&w.cond);
        self.loop_cnt += 1;
        self.block(&w.body);
        self.loop_cnt -= 1;
        false
      }
      StmtKind::For(f) => self.scoped(ScopeOwner::Local(&f.body), |s| {
        s.stmt(&f.init);
        s.check_bool(&f.cond);
        s.stmt(&f.update);
        for st in &f.body.stmt { s.stmt(st); } // not calling block(), because the scope is already opened
        false
      }),
      StmtKind::Return(r) => {
        let actual = r.as_ref().map(|e| self.expr(e)).unwrap_or(Ty::void());
        if self.lambda_cnt == 0 {
          let expect = self.cur_func.unwrap().ret_ty();
          if !actual.assignable_to(expect) { self.issue(s.loc, ReturnMismatch { actual, expect }) }
        }
        actual != Ty::void()
      }
      StmtKind::Print(p) => {
        for (i, e) in p.iter().enumerate() {
          let ty = self.expr(e);
          if ty != Ty::bool() && ty != Ty::int() && ty != Ty::string() {
            ty.error_or(|| self.issue(e.loc, BadPrintArg { loc: i as u32 + 1, ty }))
          }
        }
        false
      }
      StmtKind::Break(_) => {
        if self.loop_cnt == 0 { self.issue(s.loc, BreakOutOfLoop) }
        false
      }
      StmtKind::Block(b) => self.block(b),
    }
  }

  // e.ty is set to the return value
  fn expr(&mut self, e: &'a Expr<'a>) -> Ty<'a> {
//    println!("Expr @ {:?}", e.loc);
    use ExprKind::*;
    let ty = match &e.kind {
      VarSel(v) => self.var_sel(v, e.loc),
      IndexSel(i) => {
        let (arr, idx) = (self.expr(&i.arr), self.expr(&i.idx));
        if idx != Ty::int() { idx.error_or(|| self.issue(e.loc, IndexNotInt)) }
        match arr {
          Ty { arr, kind } if arr > 0 => Ty { arr: arr - 1, kind },
          e => e.error_or(|| self.issue(i.arr.loc, IndexNotArray)),
        }
      }
      IntLit(_) | ReadInt(_) => Ty::int(), BoolLit(_) => Ty::bool(), StringLit(_) | ReadLine(_) => Ty::string(), NullLit(_) => Ty::null(),
      Call(c) => self.call(c, e.loc),
      Unary(u) => {
        let r = self.expr(&u.r);
        let (ty, op) = match u.op { UnOp::Neg => (Ty::int(), "-"), UnOp::Not => (Ty::bool(), "!"), };
        if r != ty { r.error_or(|| self.issue(e.loc, IncompatibleUnary { op, r })) }
        ty
      }
      Binary(b) => {
        use BinOp::*;
        let (l, r) = (self.expr(&b.l), self.expr(&b.r));
        if l == Ty::error() || r == Ty::error() {
          // not using wildcard match, so that if we add new operators in the future, compiler can tell us
          match b.op { Add | Sub | Mul | Div | Mod => Ty::int(), And | Or | Eq | Ne | Lt | Le | Gt | Ge => Ty::bool() }
        } else {
          let (ret, ok) = match b.op {
            Add | Sub | Mul | Div | Mod => (Ty::int(), l == Ty::int() && r == Ty::int()),
            Lt | Le | Gt | Ge => (Ty::bool(), l == Ty::int() && r == Ty::int()),
            Eq | Ne => (Ty::bool(), l.assignable_to(r) || r.assignable_to(l)),
            And | Or => (Ty::bool(), l == Ty::bool() && r == Ty::bool())
          };
          if !ok { self.issue(e.loc, IncompatibleBinary { l, op: b.op.to_op_str(), r }) }
          ret
        }
      }
      This(_) => {
        if self.cur_func.unwrap().static_ { self.issue(e.loc, ThisInStatic) }
        Ty::mk_obj(self.cur_class.unwrap())
      }
      NewClass(n) => if let Some(c) = self.scopes.lookup_class(n.name) {
        // class cannot be abstract
        if c.abstract_ { self.issue(e.loc, CannotNewAbstract(c.name)) }
        n.class.set(Some(c));
        Ty::mk_obj(c)
      } else { self.issue(e.loc, NoSuchClass(n.name)) },
      NewArray(n) => {
        let len = self.expr(&n.len);
        if len != Ty::int() { len.error_or(|| self.issue(n.len.loc, NewArrayNotInt)) }
        self.ty(&n.elem, true)
      }
      ClassTest(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(e.loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          Ty::bool()
        } else { self.issue(e.loc, NoSuchClass(c.name)) }
      }
      ClassCast(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(e.loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          Ty::mk_obj(cl)
        } else { self.issue(e.loc, NoSuchClass(c.name)) }
      }
      // TODO: add lambda
      Lambda(l) => {
        // now only inference of ret type is performed here
        // but more could be added
        let mut ty = Ty::new(TyKind::Void);
        if let Some(b) = &l.body.expr {
          println!("Parsing lambda expr @ {:?}", b.loc);
          self.lambda_cnt += 1;
          self.scopes.open(ScopeOwner::Lambda(l));
          ty = self.expr(b.deref());
          self.scopes.close();
          self.lambda_cnt -= 1;
        } else if let Some(b) = &l.body.body {
          // deal with lambda body
          println!("Parsing lambda block @{:?}", b.loc);
          self.lambda_cnt += 1;
          self.scopes.open(ScopeOwner::Lambda(l));
          let have_ret = self.block(b);
          self.scopes.close();
          self.lambda_cnt -= 1;
          if have_ret { println!("Have ret"); } else { println!("have no ret"); }

          let (have_conflict, ret_ty) = self.dfs_lambda(b);
          println!("Max return: {:?}", ret_ty);
          if !have_ret && ret_ty != Ty::void() { self.issue(b.loc, NoReturn) }
          if have_conflict { self.issue(b.loc, BadReturnInBlock) }
          ty = self.get_block_ret(b);
        };
        let ret_param_ty = iter::once(ty).chain(l.param.iter().map(|v| v.ty.get()));
        let ret_param_ty = self.alloc.ty.alloc_extend(ret_param_ty);
        l.ret_param_ty.set(Some(ret_param_ty));
        Ty::new(TyKind::Lambda(ret_param_ty))
      }
    };
    e.ty.set(ty);
    ty
  }

  fn dfs_lambda(&mut self, b: &'a Block<'a>) -> (bool, Ty<'a>) {
    let mut st = vec![];
    let mut ret_ty = vec![];
    st.push(b);
    while !st.is_empty() {
      let block = st.pop().unwrap();
      for stmt in &block.stmt {
        match &stmt.kind {
          StmtKind::If(i) => {
            st.push(&i.on_true);
            if let Some(blk) = &i.on_false { st.push(blk); }
          },
          StmtKind::While(w) => { st.push(&w.body); },
          StmtKind::Return(r) => {
            match r {
              Some(e) => { ret_ty.push(&e.ty); },
              None => {}
            }
          },
          StmtKind::For(fo) => { st.push(&fo.body); },
          StmtKind::Block(block) => { st.push(&block) },
          _ => {}
        }
      }
    }
    if ret_ty.is_empty() {
      (false, Ty::new(TyKind::Void))
    } else {
      let mut max_type = ret_ty[0];
      for types in &ret_ty { if types.get() != Ty::void() { max_type = types; break } }
      if max_type.get() == Ty::void() { return (false, Ty::void()); }
      for types in &ret_ty {
        if types.get().assignable_to(max_type.get()) {}
        else if max_type.get().assignable_to(types.get()) {
          max_type = types;
        } else {
//          self.issue(b.loc, BadReturnInBlock)
            return (true, max_type.get());
        }
      }
      (false, max_type.get())
    }
  }

  fn block_has_ret(&mut self, b: &'a Block<'a>) -> (bool, Ty<'a>) {
    let mut ret_ty = vec![];
    for stmt in &b.stmt {
      match &stmt.kind {
        StmtKind::If(i) => {
          let (hc, ret) = self.block_has_ret(&i.on_true);
          if hc { return (true, Ty::void()); }
          ret_ty.push(ret);
          if let Some(blk) = &i.on_false {
            let (hc, ret) = self.block_has_ret(blk);
            if hc { return (true, Ty::void()); }
            ret_ty.push(ret);
          }
        },
        StmtKind::While(w) => {
          let (hc, ret) =  self.block_has_ret(&w.body);
          if hc { return (true, Ty::void()); }
          ret_ty.push(ret);
        },
        StmtKind::For(fo) => {
          let (hc, ret) =  self.block_has_ret(&fo.body);
          if hc { return (true, Ty::void()); }
          ret_ty.push(ret);
        }
        StmtKind::Return(r) => {
          match r {
            Some(e) => { ret_ty.push(e.ty.get()); },
            None => {}
          }
        },
        StmtKind::Block(block) => {
          let (hc, ret) =  self.block_has_ret(block);
          if hc { return (true, Ty::void()); }
          ret_ty.push(ret);
        },
        _ => {}
      }
    }
    let mut ret = &Ty::void();
    // find first non-void
    for t in &ret_ty { if *t != Ty::void() && *t != Ty::error() { ret = t; break } }
    if *ret == Ty::void() { return (false, Ty::void()) }
    for t in &ret_ty {
      if *t == Ty::error() { continue }
      // find max ret type
      if ret.assignable_to(*t) { ret = t; }
      else if t.assignable_to(*ret) {}
      else { return (true, Ty::void()) ; }
    }

    (false, *ret)
  }

  fn get_block_ret(&mut self, b: &'a Block<'a>) -> Ty<'a> {
    let mut ret_ty = Ty::void();
    for stmt in &b.stmt {
      match &stmt.kind {
        StmtKind::If(i) => {
          if let Some(blk) = &i.on_false { ret_ty = self.get_block_ret(blk); }
          else { ret_ty = Ty::void(); }
        },
        StmtKind::While(w) => { ret_ty = Ty::void(); },
        StmtKind::For(fo) => { ret_ty = Ty::void(); }
        StmtKind::Return(r) => {
          match r {
            Some(e) => { ret_ty = e.ty.get(); },
            None => { ret_ty = Ty::void(); }
          }
        },
        StmtKind::Block(block) => { ret_ty = self.get_block_ret(block); },
        _ => { ret_ty = Ty::void(); }
      }
    }
    ret_ty
  }

  fn var_sel(&mut self, v: &'a VarSel<'a>, loc: Loc) -> Ty<'a> {
    // (no owner)not_found_var / ClassName(no field) / (no owner)method => UndeclaredVar
    // object.not_found_var => NoSuchField
    // (no owner)field_var && cur function is static => RefInStatic
    // <not object>.a (e.g.: Class.a, 1.a) / object.method => BadFieldAccess
    // object.field_var, where object's class is not self or any of ancestors => PrivateFieldAccess

    if let Some(owner) = &v.owner {
      println!("Varsel {:?}.{} @ {:?}", owner.loc, v.name, loc);
      self.cur_used = true;
      let owner = self.expr(owner);
      self.cur_used = false;
      // adding support for selecting class methods
      if owner == Ty::error() { return Ty::error(); }
      else if owner.is_arr() && v.name == LENGTH {
        // TODO: set funcdef for arr
        let ret_param_ty = vec![Ty::int()];
        let ret_param_ty = self.alloc.ty.alloc_extend(ret_param_ty);
        return Ty::new(TyKind::Length(ret_param_ty));
      }
      match owner {
        Ty { arr: 0, kind: TyKind::Object(Ref(c)) } | Ty { arr: 0, kind: TyKind::Class(Ref(c)) } => {
          if let Some(sym) = c.lookup(v.name) {
            println!("Found {:?} in {}", sym, c.name);
            match sym {
              Symbol::Var(var) => {
                // only allow self & descendants to access field
                if owner.is_class() { self.issue(loc, BadFieldAccess { name: v.name, owner }) }
                else if !self.cur_class.unwrap().extends(c) { self.issue(loc, PrivateFieldAccess { name: v.name, owner }) }
                else { v.var.set(Some(var)); }
                var.ty.get()
              },
              Symbol::Func(f) => {
                let mut ok = true;
                if owner.is_class() && !f.static_ {
                  // Class.not_static_method()
                  ok = false;
                  self.issue(loc, BadFieldAccess { name: v.name, owner })
                }
                if v.owner.is_none() {
                  let cur = self.cur_func.unwrap();
                  if cur.static_ && !f.static_ {
                    ok = false;
                    self.issue(loc, RefInStatic { field: f.name, func: cur.name })
                  }
                }
                if ok { v.func.set(Some(f)); }
                Ty::new(TyKind::Func(f.ret_param_ty.get().unwrap()))
              },
              _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
            }
          } else { self.issue(loc, NoSuchField { name: v.name, owner }) }
        },
        e => e.error_or(|| self.issue(loc, BadFieldAccess { name: v.name, owner })),
      }
    } else {
      println!("Varsel (no owner) {} @ {:?}", v.name, loc);
      // if this stmt is in an VarDef, it cannot access the variable that is being declared
      // TODO: need to check for special access
      if let Some(sym) = self.scopes.lookup_before(v.name, loc) {
        print!("Potential Conflict {} @ {:?}   ", v.name, loc);
        println!("Found {:?}", sym);
        match sym {
          Symbol::Var(var) => {
            if var.finish_loc < loc {
              let mut ok = true;
              if var.owner.get().unwrap().is_class() {
                let cur = self.cur_func.unwrap();
                if cur.static_{ ok = false; self.issue(loc, RefInStatic { field: v.name, func: cur.name }) }
              }
              if ok { v.var.set(Some(var)); }
              var.ty.get()
            } else {
              self.issue(loc, UndeclaredVar(v.name))
            }
          }
          Symbol::Class(c) if self.cur_used => { Ty::mk_class(c) },
          Symbol::Func(func) => {
            // search for func in cur class
            let owner = self.cur_class.unwrap();
            if let Some(sym) = owner.lookup(func.name) {
              let cur = self.cur_func.unwrap();
              if cur.static_ && !func.static_ { self.issue(loc, RefInStatic { field: v.name, func: cur.name }) }
              else if let Symbol::Func(f) = sym {
                  v.func.set(Some(func));
                  Ty::new(TyKind::Func(f.ret_param_ty.get().unwrap()))
              } else { self.issue(loc, NotFunc { name: v.name, owner: Ty::mk_obj(owner) }) }
            } else { self.issue(loc, NoSuchField { name: v.name, owner: Ty::mk_obj(owner) }) }
          },
          _ => { self.issue(loc, UndeclaredVar(v.name))},
        }
        } else { self.issue(loc, UndeclaredVar(v.name)) }
      }
    }

  fn call(&mut self, c: &'a Call<'a>, loc: Loc) -> Ty<'a> {
    println!("Call at ({}, {})", loc.0, loc.1);
    // TODO: make this work
//    let v = if let ExprKind::VarSel(v) = &c.func.kind { v }
////      else if let ExprKind::Lambda(l) = &c.func.kind { l }
//      else { self.issue(loc, NotCallable { var: Ty::error() }); return Ty::error(); };
    let ty = self.expr(c.func.deref());
    println!("Caller type {:?}", ty);
    let ret_ty = match &ty {
//      ExprKind::VarSel(v) => {
//        ty = self.var_sel(&v, loc);
//        if ty == Ty::error() { return ty; }
//        if ty == Ty::int() {
//          if !c.arg.is_empty() {
//            self.issue(Loc(loc.0, loc.1 - 6), LengthWithArgument(c.arg.len() as u32))
//          }
//          return ty;
//        }
//        match &ty {
      Ty { arr: _, kind: TyKind::Length(_) } => {
        if !c.arg.is_empty() {
          self.issue(loc, LengthWithArgument(c.arg.len() as u32))
        } else { return Ty::int(); }
      }
      Ty { arr: len, kind: _ } if *len > 0 => {
        if let ExprKind::VarSel(v) = &c.func.kind {
          if v.name == LENGTH {
            if !c.arg.is_empty() {
              self.issue(loc, LengthWithArgument(c.arg.len() as u32))
            } else { return Ty::int(); }
          } else { self.issue(loc, NoSuchField { name: v.name, owner: ty }) }
        } else { self.issue(loc, NotCallable { var: ty }) }
      },
      Ty { arr: 0, kind: TyKind::Func(param) } => {
        let v = if let ExprKind::VarSel(v) = &c.func.kind { v } else { unimplemented!() };
        let owner = if let Some(owner) = &v.owner { owner.ty.get() }  else { Ty::mk_obj(self.cur_class.unwrap()) };
        match owner {
          Ty { arr: 0, kind: TyKind::Object(Ref(cl)) } | Ty { arr: 0, kind: TyKind::Class(Ref(cl)) } => {
            if let Some(sym) = cl.lookup(v.name) {
              match sym {
                Symbol::Func(f) => {
                  c.func_ref.set(Some(f));
                  if owner.is_class() && !f.static_ {
                    // Class.not_static_method()
                    self.issue(loc, BadFieldAccess { name: v.name, owner })
                  }
                  if v.owner.is_none() {
                    let cur = self.cur_func.unwrap();
                    if cur.static_ && !f.static_ {
                      self.issue(loc, RefInStatic { field: f.name, func: cur.name })
                    }
                  }
                  self.check_arg_param(&c.arg, f.ret_param_ty.get().unwrap(), f.name, loc)
                }
                _ => self.issue(loc, NotFunc { name: v.name, owner }),
              }
            } else { self.issue(loc, NoSuchField { name: v.name, owner }) }
          }
          _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
        }
      },
      Ty { arr: 0, kind: TyKind::Lambda(param) } => {
        if let ExprKind::VarSel(v) = &c.func.kind { self.check_arg_param(&c.arg, param, v.name, loc)
        } else { self.check_lambda_param(&c.arg, param, loc)}
      },
      Ty { arr: _, kind: TyKind::Error } => { Ty::error() }
      _ => { self.issue(loc, NotCallable { var: ty })}//self.issue(loc, NotCallable { var: ty }); }
    };
  ret_ty
  }
}
//    let v = if let ExprKind::VarSel(v) = &c.func.kind { v } else { unimplemented!() };
//    // get owner
//    let owner = if let Some(owner) = &v.owner {
//      self.cur_used = true;
//      let owner = self.expr(owner);
//      self.cur_used = false;
//      if owner == Ty::error() { return Ty::error(); }
//      // array length
//      if v.name == LENGTH && owner.is_arr() {
//        if !c.arg.is_empty() {
//          self.issue(loc, LengthWithArgument(c.arg.len() as u32))
//        }
//        return Ty::int();
//      }
//      owner
//    } else { Ty::mk_obj(self.cur_class.unwrap()) };
//    match owner {
//      Ty { arr: 0, kind: TyKind::Object(Ref(cl)) } | Ty { arr: 0, kind: TyKind::Class(Ref(cl)) } => {
//        if let Some(sym) = cl.lookup(v.name) {
//          match sym {
//            Symbol::Func(f) => {
//              c.func_ref.set(Some(f));
//              if owner.is_class() && !f.static_ {
//                // Class.not_static_method()
//                self.issue(loc, BadFieldAccess { name: v.name, owner })
//              }
//              if v.owner.is_none() {
//                let cur = self.cur_func.unwrap();
//                if cur.static_ && !f.static_ {
//                  self.issue(loc, RefInStatic { field: f.name, func: cur.name })
//                }
//              }
//              self.check_arg_param(&c.arg, f.ret_param_ty.get().unwrap(), f.name, loc)
//            }
//            _ => self.issue(loc, NotFunc { name: v.name, owner }),
//          }
//        } else { self.issue(loc, NoSuchField { name: v.name, owner }) }
//      }
//      _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
//    }
//  }

impl<'a> TypePass<'a> {
  fn check_bool(&mut self, e: &'a Expr<'a>) {
    let ty = self.expr(e);
    if ty != Ty::bool() { ty.error_or(|| self.issue(e.loc, TestNotBool)) }
  }

  fn check_arg_param(&mut self, arg: &'a [Expr<'a>], ret_param: &[Ty<'a>], name: &'a str, loc: Loc) -> Ty<'a> {
    let (ret, param) = (ret_param[0], &ret_param[1..]);
    if param.len() != arg.len() {
      self.issue(loc, ArgcMismatch { name, expect: param.len() as u32, actual: arg.len() as u32 })
    }
    for (idx, arg0) in arg.iter().enumerate() {
      let arg = self.expr(arg0);
      if let Some(&param) = param.get(idx) {
        if !arg.assignable_to(param) {
          self.issue(arg0.loc, ArgMismatch { loc: idx as u32 + 1, arg, param })
        }
      }
    }
    ret
  }

  fn check_lambda_param(&mut self, arg: &'a [Expr<'a>], ret_param: &[Ty<'a>], loc: Loc) -> Ty<'a> {
    let (ret, param) = (ret_param[0], &ret_param[1..]);
    if param.len() != arg.len() {
      self.issue(loc, LambdaArgcMismatch { expect: param.len() as u32, actual: arg.len() as u32 })
    }
    for (idx, arg0) in arg.iter().enumerate() {
      let arg = self.expr(arg0);
      if let Some(&param) = param.get(idx) {
        if !arg.assignable_to(param) {
          self.issue(arg0.loc, ArgMismatch { loc: idx as u32 + 1, arg, param })
        }
      }
    }
    ret
  }
}