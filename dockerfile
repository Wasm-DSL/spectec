FROM ubuntu:20.04

RUN apt-get update
RUN apt-get upgrade --yes
RUN apt-get install git make python3 python3-pip opam libgmp-dev --yes
ARG DEBIAN_FRONTEND=noninteractive
RUN TZ=Etc/UTC apt-get install texlive-full --yes
RUN pip3 install sphinx six
RUN opam init --disable-sandboxing
RUN opam switch create 5.0.0
RUN opam install dune menhir mdx zarith --yes
RUN eval $(opam env)


WORKDIR /home
RUN git clone https://github.com/Wasm-DSL/spectec.git
WORKDIR /home/spectec/spectec
RUN git checkout artifact


# Automate `eval $(opam env)`
ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]
