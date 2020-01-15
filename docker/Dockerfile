FROM ubuntu:rolling

LABEL description="Latest Kratos build"
LABEL maintainer="keyi@cs.stanford.edu"


RUN apt-get update && \
    apt-get install -y --no-install-recommends python3 python3-pip && apt-get clean

WORKDIR .
COPY dist/ /

RUN pip3 install *.whl && rm -rf *.whl
