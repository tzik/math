FROM ubuntu:rolling

RUN apt-get update && apt-get -y install agda agda-stdlib
RUN useradd -m tester && mkdir -p /home/tester/src
