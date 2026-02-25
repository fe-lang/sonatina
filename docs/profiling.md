# Sonatina Profiling

Sonatina uses [`tracing`](https://crates.io/crates/tracing) spans to profile compilation phases.

The instrumentation is always compiled in, but it is low-overhead unless a subscriber is installed.

## Instrumented phases

Sonatina emits nested spans for:

- parser pipeline (`sonatina.parse_*`)
- verifier pipeline (`sonatina.verify_*`)
- optimization pipeline and per-pass execution (`sonatina.optim.pipeline.*`)
- object compilation and section linking (`sonatina.codegen.object.*`, `sonatina.codegen.link_section.*`)
- EVM lowering and stackify/memory-planning phases (`sonatina.codegen.evm.*`)

## Basic subscriber setup

Install a subscriber in your binary or test harness to see spans.

```rust
use tracing_subscriber::{EnvFilter, fmt};

fn init_tracing() {
    let _ = fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| EnvFilter::new("sonatina=info")),
        )
        .try_init();
}
```

Example filters:

- `sonatina=info`: high-level phase timing
- `sonatina=debug`: per-step/per-function detail
- `sonatina=trace`: fine-grained internal spans (pass internals, stackify analysis boundaries)

## Chrome trace output

Use [`tracing-chrome`](https://crates.io/crates/tracing-chrome) to inspect traces in `chrome://tracing`.

```rust
use tracing_chrome::ChromeLayerBuilder;
use tracing_subscriber::{EnvFilter, prelude::*, registry};

fn init_chrome_tracing() -> tracing_chrome::FlushGuard {
    let (chrome_layer, guard) = ChromeLayerBuilder::new()
        .file("sonatina-trace.json")
        .build();

    let subscriber = registry()
        .with(EnvFilter::new("sonatina=trace"))
        .with(chrome_layer);

    let _ = tracing::subscriber::set_global_default(subscriber);
    guard
}
```

Keep the returned `FlushGuard` alive until shutdown so traces are fully written.

## Tracy live profiling

Use [`tracing-tracy`](https://crates.io/crates/tracing-tracy) for live timeline profiling.

```rust
use tracing_subscriber::{EnvFilter, prelude::*, registry};
use tracing_tracy::TracyLayer;

fn init_tracy() {
    let subscriber = registry()
        .with(EnvFilter::new("sonatina=trace"))
        .with(TracyLayer::new());

    let _ = tracing::subscriber::set_global_default(subscriber);
}
```

Run the Tracy UI while the instrumented binary runs to view spans in real time.
