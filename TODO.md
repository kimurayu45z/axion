# Axion Language - Roadmap

## v0.x: Bootstrap Compiler (Rust Implementation)

- [ ] Lexer (UTF-8 source -> Tokens, INDENT/DEDENT)
- [ ] Parser (Tokens -> CST -> AST)
- [ ] Name Resolution
- [ ] Type Inference (HM-based)
- [ ] Effect Checking
- [ ] Region Inference
- [ ] Borrow Checking
- [ ] Monomorphization
- [ ] MIR Generation
- [ ] Optimization Passes
- [ ] Code Generation (LLVM IR -> Machine Code)
- [ ] Standard Library (core modules)
- [ ] Package Manager (`axpkg`)
- [ ] Language Server Protocol (LSP)

## v1.0: Self-Hosted Compiler

- [ ] Rewrite the compiler in Axion itself
- [ ] Full standard library in Axion
- [ ] Self-hosted package manager
- [ ] Bootstrap verification (compiler compiles itself)
