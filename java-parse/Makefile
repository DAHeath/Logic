all: configure build

configure:
	oasis setup
	ocaml setup.ml -configure

build:
	ocaml setup.ml -build

clean:
	ocaml setup.ml -clean || true
	find -name '*.mllib' -delete
	find -name '*.mldylib' -delete
	find -name '*.byte' -delete
	rm -rf bin/*
	rm -f setup.ml
	git clean -dfx

.PHONY: all clean configure build
