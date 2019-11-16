use driver::*;

fn main() {
    println!("{:?}", compile(r#"
abstract class A {
    int u;
    abstract void a();
    abstract void b();
    abstract void c();
    abstract void d();
}

abstract class B extends A {
    int v;
    abstract void a(int x);
    void b() { Print("B.b()"); }
    abstract void e();
    void f() { Print("B.f()"); }
}

class C extends B {
    void a() { Print("C.a()"); }
    void c() { Print("C.c()"); }
    void e() { Print("C.e()"); }
    void f() { Print("C.f()"); }
}

abstract class D extends C {
    abstract void a();
    void c() { Print("D.c()"); }
    static void d() { Print("D.d()"); }
    void e() { Print("D.e()"); }
    void f() { Print("D.f()"); }
    abstract void g(int x, bool y);
    abstract class C h(class D d, class E e);
}

class E extends C {
    int v;
    int a() { Print("E.a()"); }
    static void d() { Print("E.d()"); }
    void g(int x, bool x) { Print("E.g()"); }
}

abstract class F extends D {
    abstract class F h(class A a, class B b);
}

class Main extends F {
    void a() { Print("Main.a()"); }
    void d() { Print("Main.d()"); }
    void g(int x, bool y) { Print("Main.g()"); }
    class D h(class B b, class C c) { Print("Main.h()"); }
    static void main() {
        class A a = new A();
        class B b = new B();
        class C c = new C();
        class D d = new D();
        class E e = new E();
    }
}

    "#, &Alloc::default(), Pa::Pa2.to_cfg()));
}
