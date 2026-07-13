FROM debian:bookworm-slim
ARG TARGETARCH
COPY litex-${TARGETARCH} /usr/local/bin/litex
RUN chmod +x /usr/local/bin/litex
ENTRYPOINT ["litex"]
