# This file is Dockerfile for the modified why3 and statwhy.
# It lauches Debian XFCE desktop that why3-py is installed
#
# Usage:
#   build: docker build -t mystatwhy .
#   run: docker run -p 6080:6080 -it mystatwhy
#   desktop URL: http://localhost:6080/vnc.html
#   export image: docker save | gzip -c > why3-py-docker-image.tar.gz
#   import image: gzip -dc why3-py-docker-image.tar.gz | docker load
#
# Minimum usage to use pre-build image:
#   % gzip -dc why3-py-docker-image.tar.gz | docker load
#   % docker run -p 6080:6080 -it mystatwhy
#   Access the desktop URL in a browser: http://localhost:6080/vnc.html
#   It should show noVNC page which can connect to the desktop.
#

ARG mirror=http://deb.debian.org/debian

FROM debian:trixie
ARG mirror

ENV DEBIAN_FRONTEND=noninteractive

RUN echo "deb-src ${mirror} trixie main" > /etc/apt/sources.list.d/deb-src.list \
  && echo 'Dpkg::Use-Pty "0";\nquiet "2";\nAPT::Install-Recommends "0";' > /etc/apt/apt.conf.d/99autopilot \
  && echo 'Acquire::HTTP::No-Cache "True";' > /etc/apt/apt.conf.d/99no-cache \
  && apt-get update \
  && apt-get install -y \
      xfce4 \
      xfce4-terminal \
      tigervnc-standalone-server \
      novnc \
      websockify \
      dbus-x11 \
      vim \
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

RUN useradd -m -s /bin/bash guest

COPY start-desktop-in-docker.sh /start-desktop-in-docker.sh
RUN chmod +x /start-desktop-in-docker.sh
CMD ["/start-desktop-in-docker.sh"]

EXPOSE 6080 5901

COPY . /home/guest/why3
RUN chown -R guest:guest /home/guest/why3

USER guest
WORKDIR /home/guest

RUN mkdir -p /home/guest/.config/tigervnc && \
    printf '#!/bin/sh\nstartxfce4\n' > /home/guest/.config/tigervnc/xstartup && \
    chmod +x /home/guest/.config/tigervnc/xstartup

# sandbox(bubblewrap) don't work in Docker
# modify ~/.profile.
RUN opam init --bare --disable-sandboxing --shell-setup

RUN cd /home/guest/why3 && ./statwhy-install.sh /home/guest/statwhy statwhy

USER root
