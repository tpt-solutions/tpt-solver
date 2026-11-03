//! End-to-end tests for the `tpt-solver` binary: exit codes, output modes, proof
//! export and the standalone `check` subcommand.

use std::path::PathBuf;
use std::process::{Command, Output};

const UNSAT_CNF: &str = "p cnf 3 4\n1 2 0\n-1 3 0\n-2 3 0\n-3 0\n";
const SAT_CNF: &str = "p cnf 2 2\n1 0\n-2 0\n";
const LRA_UNSAT: &str = "(set-logic QF_LRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n\
(assert (<= (+ x y) 1))\n(assert (>= x 2))\n(assert (>= y 0))\n(check-sat)\n";

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_tpt-solver"))
}

fn scratch(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name)
}

fn write(name: &str, contents: &str) -> PathBuf {
    let path = scratch(name);
    std::fs::write(&path, contents).expect("write scratch file");
    path
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn code(out: &Output) -> i32 {
    out.status.code().expect("process exited with a code")
}

#[test]
fn competition_sat_exits_10_with_model() {
    let file = write("cli_sat.cnf", SAT_CNF);
    let out = bin()
        .arg(&file)
        .args(["--output", "competition"])
        .output()
        .unwrap();
    assert_eq!(code(&out), 10);
    let text = stdout(&out);
    assert!(text.starts_with("s SATISFIABLE"), "got: {text}");
    assert!(text.contains("v 1 -2 0"), "got: {text}");
}

#[test]
fn competition_unsat_exits_20() {
    let file = write("cli_unsat.cnf", UNSAT_CNF);
    let out = bin()
        .arg(&file)
        .args(["--output", "competition"])
        .output()
        .unwrap();
    assert_eq!(code(&out), 20);
    assert!(stdout(&out).starts_with("s UNSATISFIABLE"));
}

#[test]
fn json_output_reports_checker_verdict() {
    let file = write("cli_json.cnf", SAT_CNF);
    let out = bin()
        .arg(&file)
        .args(["--output", "json"])
        .output()
        .unwrap();
    assert_eq!(code(&out), 0);
    let text = stdout(&out);
    assert!(text.contains("\"result\":\"sat\""), "got: {text}");
    assert!(text.contains("\"checker\":\"accept\""), "got: {text}");
}

#[test]
fn proof_round_trips_through_check() {
    let problem = write("cli_roundtrip.cnf", UNSAT_CNF);
    let proof = scratch("cli_roundtrip.drat");
    let out = bin()
        .arg(&problem)
        .arg("--emit-proof")
        .arg(&proof)
        .output()
        .unwrap();
    assert_eq!(code(&out), 0);
    let check = bin()
        .arg("check")
        .arg(&problem)
        .arg(&proof)
        .output()
        .unwrap();
    assert_eq!(code(&check), 0);
    assert!(stdout(&check).starts_with("s VERIFIED"));
}

#[test]
fn tampered_cnf_proof_is_rejected() {
    // SAT_CNF is satisfiable, so no sound proof of UNSAT exists. The empty clause is
    // not derivable by unit propagation from it, and the checker must refuse it.
    let problem = write("cli_tamper.cnf", SAT_CNF);
    let proof = write("cli_tamper.drat", "0\n");
    let out = bin()
        .arg("check")
        .arg(&problem)
        .arg(&proof)
        .output()
        .unwrap();
    assert_eq!(code(&out), 1);
    assert!(!stdout(&out).starts_with("s VERIFIED"));
}

#[test]
fn farkas_proof_round_trips_and_tampering_is_rejected() {
    let problem = write("cli_lra.smt2", LRA_UNSAT);
    let proof = scratch("cli_lra.farkas");
    let out = bin()
        .arg(&problem)
        .arg("--emit-proof")
        .arg(&proof)
        .output()
        .unwrap();
    assert_eq!(code(&out), 0);
    let ok = bin()
        .arg("check")
        .arg(&problem)
        .arg(&proof)
        .output()
        .unwrap();
    assert_eq!(code(&ok), 0, "genuine certificate should verify");

    let forged = write("cli_lra_forged.farkas", "# forged\n0 0\n");
    let bad = bin()
        .arg("check")
        .arg(&problem)
        .arg(&forged)
        .output()
        .unwrap();
    assert_eq!(code(&bad), 1, "an empty certificate must not verify");
}

#[test]
fn parse_error_reports_the_line() {
    let file = write("cli_bad.cnf", "p cnf 2 1\n1 x 0\n");
    let out = bin().arg(&file).output().unwrap();
    assert_eq!(code(&out), 2);
    let err = String::from_utf8_lossy(&out.stderr).into_owned();
    assert!(err.contains("line 2"), "got: {err}");
}

#[test]
fn unsupported_smt_command_is_an_error() {
    let file = write(
        "cli_push.smt2",
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n(push 1)\n(assert (> x 0))\n",
    );
    let out = bin().arg(&file).output().unwrap();
    assert_eq!(code(&out), 2);
    assert!(String::from_utf8_lossy(&out.stderr).contains("push"));
}

#[test]
fn stdin_input_with_explicit_format() {
    use std::io::Write;
    let mut child = bin()
        .args(["-", "--format", "dimacs", "--output", "competition"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(SAT_CNF.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert_eq!(code(&out), 10);
}

#[test]
fn undetectable_format_is_an_error() {
    let file = write("cli_junk.txt", "hello world\n");
    let out = bin().arg(&file).output().unwrap();
    assert_eq!(code(&out), 2);
}

#[test]
fn explain_core_is_irreducible_for_cnf() {
    let file = write("cli_explain.cnf", "p cnf 1 3\n1 0\n-1 0\n1 2 0\n");
    let out = bin()
        .arg(&file)
        .args(["--explain", "--output", "json"])
        .output()
        .unwrap();
    assert_eq!(code(&out), 0);
    let text = stdout(&out);
    // The two unit clauses are the contradiction. The third clause is unnecessary.
    assert!(text.contains("\"core\":[0,1]"), "got: {text}");
}
