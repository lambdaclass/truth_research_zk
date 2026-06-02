// Parametric Rust harness for trzk-generated kernels.
// The generated file is imported via #[path] so no proc-macro wiring is needed.
// Arity is selected by `--cfg arity="N"` at compile time so the call signature
// matches the kernel exactly; field is selected by `--cfg field="..."` (single
// value `babybear` today; ready for step 3 to add more).
// `--cfg matrix` selects a matrix-returning kernel; without it the kernel
// returns a single u32 (scalar / arith ops).

#[path = "./generated.rs"]
mod generated;

use generated::arith_spec;

// --- scalar arith arms ---

#[cfg(all(not(matrix), arity = "1", field = "babybear"))]
fn call(xs: &[u32]) -> Vec<u32> {
    match xs {
        [x0] => vec![arith_spec(*x0)],
        _ => { eprintln!("expected 1 u32 arg, got {}", xs.len()); std::process::exit(2); }
    }
}

#[cfg(all(not(matrix), arity = "2", field = "babybear"))]
fn call(xs: &[u32]) -> Vec<u32> {
    match xs {
        [x0, x1] => vec![arith_spec(*x0, *x1)],
        _ => { eprintln!("expected 2 u32 args, got {}", xs.len()); std::process::exit(2); }
    }
}

#[cfg(all(not(matrix), arity = "4", field = "babybear"))]
fn call(xs: &[u32]) -> Vec<u32> {
    match xs {
        [x0, x1, x2, x3] => vec![arith_spec(*x0, *x1, *x2, *x3)],
        _ => { eprintln!("expected 4 u32 args, got {}", xs.len()); std::process::exit(2); }
    }
}

#[cfg(all(not(matrix), arity = "8", field = "babybear"))]
fn call(xs: &[u32]) -> Vec<u32> {
    match xs {
        [x0, x1, x2, x3, x4, x5, x6, x7] =>
            vec![arith_spec(*x0, *x1, *x2, *x3, *x4, *x5, *x6, *x7)],
        _ => { eprintln!("expected 8 u32 args, got {}", xs.len()); std::process::exit(2); }
    }
}

// --- matrix arms (function returns [u32; N]) ---

#[cfg(all(matrix, arity = "4", field = "babybear"))]
fn call(xs: &[u32]) -> Vec<u32> {
    match xs {
        [x0, x1, x2, x3] => arith_spec(*x0, *x1, *x2, *x3).to_vec(),
        _ => { eprintln!("expected 4 u32 args, got {}", xs.len()); std::process::exit(2); }
    }
}

#[cfg(all(matrix, arity = "8", field = "babybear"))]
fn call(xs: &[u32]) -> Vec<u32> {
    match xs {
        [x0, x1, x2, x3, x4, x5, x6, x7] =>
            arith_spec(*x0, *x1, *x2, *x3, *x4, *x5, *x6, *x7).to_vec(),
        _ => { eprintln!("expected 8 u32 args, got {}", xs.len()); std::process::exit(2); }
    }
}

// BabyBear modulus, mirrors the Lean side (TRZK.BabyBear.p = 2^31 - 2^27 + 1).
#[cfg(field = "babybear")]
const P: u32 = 2013265921;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let xs: Vec<u32> = args
        .iter()
        .map(|s| {
            let v: u32 = s.parse().expect("argv must be u32");
            assert!(v < P, "argv {} out of field range [0, {})", v, P);
            v
        })
        .collect();

    let ys = call(&xs);
    let out: Vec<String> = ys.iter().map(|v| v.to_string()).collect();
    println!("{}", out.join(" "));
}
