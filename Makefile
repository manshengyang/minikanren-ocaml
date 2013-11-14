native:
	ocamlbuild ck.native

byte:
	ocamlbuild ck.byte

debug:
	ocamlbuild ck.d.byte

clean:
	rm -rf *.native *.byte _build
