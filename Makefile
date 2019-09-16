.PHONY: all clean

build: Pigeonhole.v
	coqc Pigeonhole.v

all: build doc

clean:
	git clean -fx .

doc: Pigeonhole.v
	coqdoc --latex Pigeonhole.v
