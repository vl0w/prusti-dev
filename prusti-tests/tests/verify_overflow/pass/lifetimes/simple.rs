use prusti_contracts::*;

struct T {
    val: i32
}

fn mutate_local() {
    let mut a = T { val: 3 };
    let x = &mut a;
    x.val = 4;
}

fn mutate_local_branch(c: bool) {
    let mut a = T { val: 3 };
    let mut b = T { val: 4 };
    let x;
    if c {
        x = &mut a;
    } else {
        x = &mut b;
    }
    x.val = 4;
}

fn main() {}

