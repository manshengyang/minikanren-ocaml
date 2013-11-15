native:
	ocamlbuild main.native

byte:
	ocamlbuild main.byte

debug:
	ocamlbuild main.d.byte

clean:
	rm -rf *.native *.byte _build
