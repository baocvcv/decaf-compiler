# Introduction

This is the course project for Principles of Compilers.

A compiler for the `decaf` language is developed in Rust.

# Project Guide

[decaf-doc](https://mashplant.gitbook.io/decaf-doc/)

# Build & Run

You need a nightly rust compiler. It is tested on `rustc 1.38.0-nightly`, there is no guarantee about any older version (I believe that a newer version won't break the code).

Run:

```
cargo run --bin test # for testing your implemetation using the testcase folder
# or
cargo run --bin decaf # for a command line app
```

The command line app (with name `decaf`) support the following arguments:

```
<input> # required, the input decaf file path
--target=<target> # required, <target> can be pa1a, pa1b, pa2, pa3, pa4, pa5
--output=<output> # optional, the output path; if not specified, it prints to stdout
```
