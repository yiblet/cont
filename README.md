# Cont

A Rust library for composable continuation-based programming.

## Overview

Cont provides traits and utilities for building composable computations using continuations. It enables you to create stages of computation that can yield intermediate values and resume execution based on external input.

## Core Concepts

### `Cont<A>` Trait

The fundamental continuation trait that represents a computation stage:

```rust
pub trait Cont<A> {
    type Yield;  // Type of intermediate values yielded
    type Done;   // Type of final result
    fn next(&mut self, input: A) -> Either<Self::Yield, Self::Done>;
}
```

### `First<A>` Trait

Represents computations that can provide an initial yield before processing any input:

```rust
pub trait First<A> {
    type Next: Cont<A>;
    fn first(self) -> Either<(<Self::Next as Cont<A>>::Yield, Self::Next), <Self::Next as Cont<A>>::Done>;
}
```

## Key Components

### Building Blocks

- **`Once<F>`** - Execute a function once, then complete
- **`Repeat<F>`** - Execute a function repeatedly
- **`Chain<L, R>`** - Chain two stages sequentially

### Transformations

- **`MapInput<S, F>`** - Transform input before processing
- **`MapYield<S, F>`** - Transform yielded values
- **`MapDone<S, F>`** - Transform final result

### Handlers

Execution utilities for running continuation stages:

- `handle_cont_sync()` - Run continuation synchronously
- `handle_cont_async()` - Run continuation asynchronously
- `handle_first_sync()` - Run First stage synchronously
- `handle_first_async()` - Run First stage asynchronously
- `handle()` / `handle_async()` - Convenience functions

## Usage Examples

### Simple Fibonacci Generator

```rust
use cont::*;

let mut prev = 1;
let fib = first_repeat(1, move |n: u128| {
    let next = prev + n;
    prev = next;
    next
});

let (initial, mut stage) = fib.first().unwrap_left();
for i in 1..11 {
    let current = stage.next(1).unwrap_left();
    println!("Fibonacci {}: {}", i + 1, current);
}
```

### Chained Computation

```rust
use cont::*;

let initializer = first_once(10_u32, |input: u32| input + 5);
let multiplier = repeat(|input: u32| input * 2);
let chain = initializer.chain(multiplier);

let result = handle(chain, |yielded| yielded + 1);
```

### Input/Output Transformation Pipeline

```rust
use cont::*;

let mut total = 0_i64;
let calculator = first_repeat(0_i64, move |delta: i64| {
    total += delta;
    total
})
.map_input(|cmd: &str| -> i64 {
    let mut parts = cmd.split_whitespace();
    let op = parts.next().expect("operation");
    let amount: i64 = parts.next().expect("amount").parse().expect("valid number");
    match op {
        "add" => amount,
        "sub" => -amount,
        _ => panic!("unsupported operation"),
    }
})
.map_yield(|value: i64| format!("total={}", value));

let (initial, mut stage) = calculator.first().unwrap_left();
println!("{}", initial); // "total=0"
println!("{}", stage.next("add 5").unwrap_left()); // "total=5"
println!("{}", stage.next("sub 3").unwrap_left()); // "total=2"
```

## Extension Traits

Both `ContExt` and `FirstExt` provide convenient builder methods:

- `.chain(other)` - Chain with another stage
- `.chain_once(f)` - Chain with a one-time function
- `.chain_repeat(f)` - Chain with a repeating function
- `.map_input(f)` - Transform input
- `.map_yield(f)` - Transform yields
- `.map_done(f)` - Transform final result

## Dependencies

- `either` - For `Either<L, R>` enum representing two possible values

## License

See the license file in the repository for licensing information.