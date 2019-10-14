use driver::*;

fn main() {
    println!("{:?}", compile(r#"
        Class Main {
            static void main() {
                int(int) f1 = 1;
            }
        }
    "#, &Alloc::default(), Pa::Pa1a.to_cfg()));
}
