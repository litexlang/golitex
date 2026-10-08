FROM debian:bookworm-slim
ARG TARGETARCH
COPY --chmod=755 litex-${TARGETARCH} /usr/local/bin/litex
COPY std /usr/share/litex/std
ENV LITEX_STD_PATH=/usr/share/litex/std
ENTRYPOINT ["litex"]
