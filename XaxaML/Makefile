.PHONY: all build fmt tests lint

all: build fmt tests lint

build:
	dune build

fmt:
	dune fmt

tests:
	dune runtest

lint:
	zanuda -no-top_file_license -dir .
