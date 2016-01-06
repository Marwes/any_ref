#![cfg(features = "test")]
extern crate compiletest_rs as compiletest;

#[cfg(feature = "test")]
use std::path::PathBuf;

#[cfg(feature = "test")]
fn run_mode(mode: &'static str) {
    let mut config = compiletest::default_config();
    let cfg_mode = mode.parse().ok().expect("Invalid mode");

    config.mode = cfg_mode;
    config.src_base = PathBuf::from(format!("tests/{}", mode));
    config.target_rustcflags = Some("-L target/debug -L target/debug/deps".to_string());

    compiletest::run_tests(&config);
}

#[test]
#[cfg(feature = "test")]
fn compile_test() {
    run_mode("compile-fail");
}
