native:
	ocamlbuild ck.native

byte:
	ocamlbuild ck.byte

clean:
	rm -rf *.native *.byte _build
