FROM ubuntu:19.10

LABEL description="Latest Kratos build"
LABEL maintainer="keyi@cs.stanford.edu"


RUN apt-get update \
    && apt-get install -y --no-install-recommends python3.7 python3-pip && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

WORKDIR .
COPY wheelhouse/ /

RUN pip3 install *.whl && rm -rf *.whl
