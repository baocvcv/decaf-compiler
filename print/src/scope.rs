use common::{IndentPrinter, IgnoreResult};
use syntax::{ast::*, Scope};
use std::fmt::Write;
use std::borrow::Borrow;

fn show_scope(s: &Scope, p: &mut IndentPrinter) {
  let mut s = s.iter().map(|(_, &sym)| sym).collect::<Vec<_>>();
  s.sort_unstable_by_key(|x| x.loc());
  if s.is_empty() { write!(p, "<empty>").ignore(); } else { for s in s { write!(p, "{:?}", s).ignore(); } }
}

pub fn program(pr: &Program, p: &mut IndentPrinter) {
  write!(p, "GLOBAL SCOPE:").ignore();
  p.indent(|p| {
    show_scope(&pr.scope.borrow(), p);
    for c in &pr.class { class_def(c, p); }
  });
}

pub fn class_def(c: &ClassDef, p: &mut IndentPrinter) {
  write!(p, "CLASS SCOPE OF '{}':", c.name).ignore();
  p.indent(|p| {
    show_scope(&c.scope.borrow(), p);
    for f in &c.field {
      if let FieldDef::FuncDef(f) = f { func_def(f, p); }
    }
  });
}

pub fn func_def(f: &FuncDef, p: &mut IndentPrinter) {
  write!(p, "FORMAL SCOPE OF '{}':", f.name).ignore();
  p.indent(|p| {
    show_scope(&f.scope.borrow(), p);
    //TODO: modify for abstract function
    if !f.abstract_ { block(&f.body.as_ref().unwrap(), p); }
  });
}

pub fn block(b: &Block, p: &mut IndentPrinter) {
  write!(p, "LOCAL SCOPE:").ignore();
  p.indent(|p| {
    show_scope(&b.scope.borrow(), p);
    for s in &b.stmt {
      match &s.kind {
        StmtKind::Assign(a) => { expr(&a.dst, p); expr(&a.src, p); }
        StmtKind::LocalVarDef(v) => if let Some( e) = v.init() { expr(e, p); }
        StmtKind::ExprEval(e) => expr(e, p),
        StmtKind::If(i) => {
          block(&i.on_true, p);
          if let Some(on_false) = &i.on_false { block(on_false, p); }
        }
        StmtKind::While(w) => block(&w.body, p),
        StmtKind::For(f) => block(&f.body, p),
        StmtKind::Return(r) => if let Some(e) = &r { expr(e, p); }
        StmtKind::Print(v) => { for e in v { expr(e, p) } }
        StmtKind::Block(b) => block(b, p),
        _ => {}
      }
    }
  });
}

pub fn lambda(l: &Lambda, p: &mut IndentPrinter) {
  write!(p, "FORMAL SCOPE OF 'lambda@{:?}':", l.loc).ignore();
  p.indent(|p| {
    show_scope(&l.scope.borrow(), p);
    if let Some(b) = &l.body.body { block(b, p); }
    else if let Some(e) = &l.body.expr {
      write!(p, "LOCAL SCOPE:").ignore();
      p.indent(|pp| {
        show_scope(&e.scope.borrow(), pp);
        expr(e, pp);
      });
    }
  });
}

pub fn expr(e: &Expr, p: &mut IndentPrinter) {
  match &e.kind {
    ExprKind::VarSel(v) => if let Some(owner) = &v.owner { expr(owner.as_ref(), p); }
    ExprKind::IndexSel(i) => { expr(&i.arr, p); expr(&i.idx, p); }
    ExprKind::Call(c) => { expr(c.func.as_ref(), p); for pr in &c.arg { expr(pr, p); } }
    ExprKind::Unary(u) => expr(u.r.borrow(), p),
    ExprKind::Binary(b) => { expr(b.l.borrow(), p); expr(b.r.borrow(), p); },
    ExprKind::NewArray(n) => expr(&n.len, p),
    ExprKind::Lambda(l) => lambda(l, p),
    _ => {}
  }
}
