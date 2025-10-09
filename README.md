# sans, composable coroutine-based programming

[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![crates.io Version](https://img.shields.io/crates/v/sans.svg)](https://crates.io/crates/sans)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.85.0+-lightgray.svg)](#rust-version-requirements-msrv)

sans is a coroutine combinators library written in Rust. Its goal is to provide tools
to build composable, resumable computations without compromising on speed, safety, or ergonomics.
To that end, it uses Rust's *strong typing* and *ownership system* to produce
correct, efficient programs, and provides functions, traits and combinators to abstract
the error-prone plumbing of stateful computation.

*sans will help you build pipelines that yield, resume, and compose beautifully*

<!-- toc -->

- [Example](#example)
- [Documentation](#documentation)
- [Why use sans?](#why-use-sans)
  - [Interactive Protocols](#interactive-protocols)
  - [Streaming Pipelines](#streaming-pipelines)
  - [State Machines](#state-machines)
  - [Incremental Computation](#incremental-computation)
- [Coroutine Combinators](#coroutine-combinators)
- [Technical Features](#technical-features)
- [Rust Version Requirements (MSRV)](#rust-version-requirements-msrv)
- [Installation](#installation)
- [Module Organization](#module-organization)

<!-- tocstop -->

## Example

Interactive calculator that maintains state across inputs:

```rust
use sans::prelude::*;

// Build a stateful calculator that accumulates results
let mut total = 0_i64;
let calculator = init_repeat(0_i64, move |delta: i64| {
    total += delta;
    total
})
.map_input(|cmd: &str| -> i64 {
    let mut parts = cmd.split_whitespace();
    let op = parts.next().expect("operation");
    let amount: i64 = parts.next().expect("amount").parse().expect("number");
    match op {
        "add" => amount,
        "sub" => -amount,
        _ => panic!("unknown operation"),
    }
})
.map_yield(|value: i64| format!("total={}", value));

// Execute the pipeline
let (initial, mut stage) = calculator.init().unwrap_yielded();
println!("{}", initial);  // "total=0"

println!("{}", stage.next("add 5").unwrap_yielded());   // "total=5"
println!("{}", stage.next("sub 3").unwrap_yielded());   // "total=2"
println!("{}", stage.next("add 10").unwrap_yielded());  // "total=12"
```

Chained pipeline with transformation:

```rust
use sans::prelude::*;

let pipeline = init_once(10, |x: i32| x * 2)
    .map_yield(|x| x + 5)
    .chain(once(|x: i32| x * 3))
    .map_return(|x| format!("Result: {}", x));

let result = handle(pipeline, |output| {
    println!("Step: {}", output);
    output  // Pass through
});

println!("{}", result);  // "Result: 45"
```

## Documentation

- [API Documentation](https://docs.rs/sans)
- [Examples directory](https://github.com/your-repo/sans/tree/main/examples) *(coming soon)*

## Why use sans?

If you want to write:

### Interactive Protocols

sans was designed for building interactive protocols where computation happens in stages,
each stage can yield intermediate results, and the next step depends on external input.
Compared to handwritten state machines, sans pipelines are:

- Composable and reusable
- Type-safe with compile-time guarantees
- Free from manual state management bugs
- Easy to test in isolation

**Use cases:**
- Network protocols with request-response cycles
- REPLs and interactive command processors
- Multi-step wizards and forms
- Game state machines

### Streaming Pipelines

sans excels at processing data in stages where each stage can transform, filter, or
accumulate results. The type system ensures stages compose correctly, and the
coroutine model makes it easy to handle partial data:

- Transform data through multiple processing stages
- Maintain state across stream elements
- Handle backpressure and control flow
- Compose transformations declaratively

**Use cases:**
- Data processing pipelines
- Stream transformations
- Event sourcing systems
- ETL processes

### State Machines

Building explicit state machines with sans is natural and type-safe. Each state
is a coroutine that can transition to the next state or complete:

- Explicit state transitions
- Type-safe state representation
- Easy to visualize and debug
- Composable substates

**Use cases:**
- Protocol implementations
- Workflow engines
- Game AI
- UI navigation flows

### Incremental Computation

sans makes it easy to build computations that can be paused, resumed, and
composed with other computations:

- Pause computation and resume later
- Compose sub-computations
- Cancel or short-circuit pipelines
- Handle errors at any stage

**Use cases:**
- Async workflows
- Background jobs that can be paused
- Cooperative multitasking
- Cancellable operations

## Coroutine Combinators

Coroutine combinators are an approach to stateful computation that uses
small, composable functions instead of complex state machines. Instead of
writing a monolithic state machine with explicit state tracking, you compose
very small functions with specific purposes like "multiply by 2", or
"add 1 and complete", and assemble them into meaningful pipelines.

The resulting code is:
- Small and focused
- Easy to understand
- Close to the specification you'd write naturally
- Highly composable and reusable

This has several advantages:

- **Easy to write**: Each stage is simple and focused on one task
- **Easy to test**: Test stages in isolation with unit tests
- **Easy to reuse**: Stages can be used in multiple pipelines
- **Type-safe**: The compiler ensures stages compose correctly
- **Composable**: Build complex behavior from simple pieces

## Technical Features

sans provides:
- [x] **Type-safe composition**: Strong typing ensures stages compose correctly
- [x] **Zero-copy**: Coroutines don't copy data unnecessarily
- [x] **Flexible execution**: Both synchronous and asynchronous execution
- [x] **Concurrent execution**: Run multiple coroutines concurrently with `join`
- [x] **Memory efficient**: Stages are dropped after completion to free resources
- [x] **Transformations**: Map inputs, outputs, and return values
- [x] **Method chaining**: Fluent API for building pipelines
- [x] **No unsafe code**: The entire library is `#![forbid(unsafe_code)]`
- [x] **Well tested**: Comprehensive test suite with doctests

## Rust Version Requirements (MSRV)

sans requires **Rustc version 1.85 or greater**.

## Installation

sans is available on [crates.io](https://crates.io/crates/sans) and can be included in your Cargo enabled project like this:

```toml
[dependencies]
sans = "0.1.0-alpha.2"
```

Then in your code:

```rust
use sans::prelude::*;
```

## Module Organization

sans is organized by **capability** - what you want to accomplish:

| Module | Purpose | Key Functions |
|--------|---------|---------------|
| **`sans::build`** | Creating coroutine stages | `once`, `repeat`, `from_fn`, `init_once`, `init_repeat` |
| **`sans::compose`** | Combining coroutines | `chain`, `map_input`, `map_yield`, `map_return` |
| **`sans::concurrent`** | Concurrent execution | `poll`, `join`, `join_vec` |
| **`sans::sequential`** | Sequential execution | `many` |
| **`sans::run`** | Executing pipelines | `handle`, `handle_async` |
| **`sans::prelude`** | Common imports | All frequently used items |

### Quick Examples

```rust
use sans::prelude::*;

// Build: Create stages
let stage = once(|x: i32| x * 2);
let stage = repeat(|x: i32| x + 1);
let stage = init_once(42, |x: i32| x * 2);

// Compose: Chain and transform
let pipeline = stage1.chain(stage2);
let transformed = stage.map_yield(|x| x * 2);

// Run: Execute to completion
let result = handle(pipeline, |output| output + 1);

// Concurrent: Run multiple stages
use sans::concurrent::*;
let mut joined = join([stage1, stage2, stage3]);
```

### Core Types

**`Sans<I, O>`** - A coroutine that:
- Takes input of type `I`
- Yields output of type `O`
- Eventually completes with a `Return` value

**`InitSans<I, O>`** - A coroutine that:
- Provides an initial output before processing input
- Then becomes a `Sans<I, O>` coroutine

**`Step<Y, D>`** - The result of each step:
- `Yielded(Y)` - Continue with intermediate value
- `Complete(D)` - Finished with final value

## Design Decisions

sans is built with a clear set of principles:

### Minimal Dependencies

The library maintains as few dependencies as possible. Currently, sans only depends on [`either`](https://crates.io/crates/either) for the `Either<L, R>` type used in generic trait implementations. This keeps the dependency tree small, improves compilation times, and reduces supply chain risk.

### No Unsafe Code

sans is `#![forbid(unsafe_code)]` - the entire library leverages Rust's type system and ownership model to provide safe abstractions. This ensures memory safety and prevents undefined behavior without sacrificing performance.

### Coroutine Compatibility

The library's design stays similar to Rust's [nightly coroutine syntax](https://doc.rust-lang.org/beta/unstable-book/language-features/coroutines.html) and semantics. This intentional alignment means that when coroutines stabilize, sans can potentially interoperate with native coroutine syntax, providing a migration path and compatibility layer.

### Stable Rust Only

sans compiles on stable Rust (MSRV 1.65+) without requiring any nightly features. This ensures the library can be used in production environments and maintains compatibility with stable toolchains.

### Zero-Cost Abstractions

Coroutines are designed to be as zero-cost as possible:
- No allocations in core combinators (`once`, `repeat`, `chain`, `map_*`)
- Stack-based state machines
- Inlining and optimization friendly
- States are dropped immediately after completion to free resources

The only allocations occur in dynamic-size operations (`join_vec`, `init_join_vec`) which require `Vec` for runtime-determined numbers of coroutines. Fixed-size operations use stack-allocated arrays.

## Inspiration

sans draws inspiration from several excellent projects in the Rust ecosystem:

- **[nom](https://github.com/rust-bakery/nom)** - The parser combinator library that pioneered composable, type-safe parsing in Rust. sans applies similar principles to stateful computation and coroutine pipelines.

- **[genawaiter](https://github.com/whatisaphone/genawaiter)** - Generator implementation that explores yielding and resumption patterns in Rust.

- **[corosensei](https://github.com/Amanieu/corosensei)** - Stackful coroutine library demonstrating low-level coroutine control in Rust.

- **[propane](https://github.com/withoutboats/propane)** - Generator and coroutine exploration focusing on ergonomic async patterns.

While these libraries focus on different aspects (parsing, stackful coroutines, async generators), sans synthesizes ideas from all of them to provide a coroutine combinator library focused on composability, type safety, and explicit control flow.

## Contributing

- TBD

## License

See the LICENSE file in the repository for licensing information.
