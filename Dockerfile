# Container image for the tpt-solver command line.
#
# Build:  docker build -t tpt-solver .
# Run:    docker run --rm -v "$PWD:/work" -w /work tpt-solver problem.cnf
#
# Not yet built or tested in CI: Docker was not available where this file was
# written. The toolchain matches rust-toolchain.toml (1.85).

FROM rust:1.85-slim AS build
WORKDIR /src
COPY . .
RUN cargo build --release --locked -p tpt-solver --bin tpt-solver

FROM debian:bookworm-slim
COPY --from=build /src/target/release/tpt-solver /usr/local/bin/tpt-solver
ENTRYPOINT ["tpt-solver"]
