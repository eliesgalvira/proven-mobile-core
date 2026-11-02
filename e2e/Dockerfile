# The core image: the kernel binary (bend kernel/main.bend -o build/kernel)
# and the edge (cargo build --release), both built on the host by run.sh and
# copied in. Both link only against glibc and libm.
FROM debian:bookworm-slim@sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3
COPY kernel edge /usr/local/bin/
ENTRYPOINT ["/usr/local/bin/edge"]
