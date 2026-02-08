# Axion Compiler - Build Notes

## LLVM Setup (Required for axion-codegen)

The `axion-codegen` package requires LLVM 18 to be installed.

### macOS (Homebrew)

```bash
brew install llvm@18 zstd
```

### Environment Variables

Set these when building or testing anything that depends on `axion-codegen`:

```bash
export LLVM_SYS_180_PREFIX=/opt/homebrew/Cellar/llvm@18/18.1.8
export LIBRARY_PATH=/opt/homebrew/lib
```

### Build Commands

```bash
# Build the full workspace
LLVM_SYS_180_PREFIX=/opt/homebrew/Cellar/llvm@18/18.1.8 LIBRARY_PATH=/opt/homebrew/lib cargo build

# Run all tests
LLVM_SYS_180_PREFIX=/opt/homebrew/Cellar/llvm@18/18.1.8 LIBRARY_PATH=/opt/homebrew/lib cargo test

# Build just the codegen package
LLVM_SYS_180_PREFIX=/opt/homebrew/Cellar/llvm@18/18.1.8 LIBRARY_PATH=/opt/homebrew/lib cargo build -p axion-codegen

# Run codegen tests only
LLVM_SYS_180_PREFIX=/opt/homebrew/Cellar/llvm@18/18.1.8 LIBRARY_PATH=/opt/homebrew/lib cargo test -p axion-codegen
```

### Using the Driver

```bash
# Compile an Axion source file to an executable
cargo run -p axion-driver -- build hello.ax -o hello

# Emit LLVM IR for debugging
cargo run -p axion-driver -- build hello.ax --emit-llvm-ir

# Type-check only
cargo run -p axion-driver -- check hello.ax
```

### Troubleshooting

- **`library 'zstd' not found`**: Install zstd (`brew install zstd`) and set `LIBRARY_PATH=/opt/homebrew/lib`
- **`LLVM_SYS_180_PREFIX` not set**: The `llvm-sys` crate needs to know where LLVM 18 is installed. Check `brew --prefix llvm@18` for the path.
- **LLVM version mismatch**: `inkwell` 0.5 with feature `llvm18-0` requires exactly LLVM 18. Check with `llvm-config --version` (use the brew-installed one: `/opt/homebrew/opt/llvm@18/bin/llvm-config --version`).
