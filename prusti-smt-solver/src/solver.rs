use async_std::process::{Command, Stdio};
use context::Context;
use futures::try_join;

use subprocess::{communicate, pass_error};

mod context;
mod subprocess;

#[async_std::main]
async fn main() -> Result<(), std::io::Error> {
    let z3_path = std::env::var("PRUSTI_ORIGINAL_SMT_SOLVER_PATH").unwrap();
    let context = Context::new().await;
    for arg in std::env::args() {
        context.write_to_log("init", &format!("{}\n", arg)).await?;
    }
    context.write_config_to_log().await?;
    let args: Vec<_> = std::env::args().skip(1).collect();
    let mut cmd = Command::new(z3_path);
    cmd.args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if let Some(z3_trace_path) = &context.z3_trace_path {
        cmd.arg("trace=true")
            .arg("proof=true")
            .arg(format!("trace_file_name={}", z3_trace_path))
            .arg("smt.qi.profile=true")
            .arg("smt.qi.profile_freq=10000");
    }
    context.write_to_log("z3", &format!("{:?}\n", cmd)).await?;
    let solver = cmd.spawn()?;
    let solver_stdin = solver.stdin.expect("failed to create stdin pipe with Z3");
    let solver_stdout = solver.stdout.expect("failed to create stdout pipe with Z3");
    let solver_stderr = solver.stderr.expect("failed to create stderr pipe with Z3");
    let communicate = communicate(&context, solver_stdin, solver_stdout);
    let error = pass_error(&context, solver_stderr);
    try_join!(communicate, error)?;
    Ok(())
}
