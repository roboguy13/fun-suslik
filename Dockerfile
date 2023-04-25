# syntax=docker/dockerfile:1
FROM debian:11.6


RUN apt-get update && apt-get install -y build-essential curl libffi-dev libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo6 libnuma-dev scala apt-transport-https curl gnupg -yqq
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian all main" | tee /etc/apt/sources.list.d/sbt.list \
  && (echo "deb https://repo.scala-sbt.org/scalasbt/debian /" | tee /etc/apt/sources.list.d/sbt_old.list) \
  && (curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x2EE0EA64E40A89B84B2DF73499E82A75642AC823" | gpg --no-default-keyring --keyring gnupg-ring:/etc/apt/trusted.gpg.d/scalasbt-release.gpg --import) \
  && chmod 644 /etc/apt/trusted.gpg.d/scalasbt-release.gpg \
  && apt-get update \
  && apt-get install -y sbt \
  && (curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_MINIMAL=1 sh)

COPY . /app

ENV PATH=${PATH}:/root/.ghcup/bin

RUN ghcup install ghc 9.2.5 && ghcup install cabal && ghcup set ghc 9.2.5

RUN cabal update

WORKDIR /app
RUN ./setup.sh
RUN ./build.sh

