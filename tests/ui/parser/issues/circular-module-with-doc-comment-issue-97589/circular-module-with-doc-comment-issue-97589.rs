// Regression test for #97589: a doc-comment on a circular module bypassed cycle detection

#![crate_type = "lib"]


//~? ERROR circular modules: $DIR/recursive.rs -> $DIR/recursive.rs
