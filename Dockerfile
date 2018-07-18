FROM ubuntu:rolling

RUN apt-get update && apt-get -y install agda agda-stdlib
