# This file is Dockerfile for the modified why3 and statwhy.
# It can be used to check dependencies of why3 and statwhy.
#
# Running why3-ide using this docker image is bit difficult because
# it require X Window System in user's environment.
#
# Example:
#   build: docker build -t mystatwhy .
#   run: docker run -it mystatwhy /bin/sh

ARG mirror=http://deb.debian.org/debian

FROM debian:trixie
ARG mirror

RUN echo "deb-src ${mirror} trixie main" > /etc/apt/sources.list.d/deb-src.list \
  && echo 'Dpkg::Use-Pty "0";\nquiet "2";\nAPT::Install-Recommends "0";' > /etc/apt/apt.conf.d/99autopilot \
  && echo 'Acquire::HTTP::No-Cache "True";' > /etc/apt/apt.conf.d/99no-cache \
  && apt-get update \
  && apt-get install \
      opam \
      wget \
      git \
      rsync \
      ca-certificates \
      build-essential \
      libsqlite3-dev \
      libssl-dev \
      pkgconf \
      autoconf \
      cvc5 \
      libgmp-dev \
      libcairo2-dev \
      libgtk-3-dev \
      libgtksourceview-3.0-dev \
  && rm -rf /var/lib/apt/lists/*

# sandbox(bubblewrap) don't work in Docker
# modify ~/.profile.
RUN opam init --bare --disable-sandboxing --shell-setup

WORKDIR /a

COPY . /why3

RUN cd /why3 && ./statwhy-install.sh /a statwhy
