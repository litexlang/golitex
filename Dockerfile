FROM debian:bookworm-slim
ARG TARGETARCH
COPY litex-${TARGETARCH} /usr/local/bin/litex
COPY std /usr/share/litex/std
RUN chmod +x /usr/local/bin/litex
ENTRYPOINT ["litex"]
