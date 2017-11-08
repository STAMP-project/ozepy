FROM buildpack-deps:jessie

RUN apt-get update && \
    apt-get install --no-install-recommends -y \
        unzip && \
    apt-get install --reinstall python-pkg-resources && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /root

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.5.0/z3-4.5.0-x64-debian-8.5.zip && \
    unzip z3-4.5.0-x64-debian-8.5.zip

WORKDIR /root/z3-4.5.0-x64-debian-8.5

RUN mkdir bin/python/z3/lib && \
    cp bin/lib* bin/python/z3/lib/ && \
    cp bin/z3 bin/python/z3/lib/ && \
    cp -rf bin/python/z3 /usr/lib/python2.7/

CMD ["/bin/bash"]

