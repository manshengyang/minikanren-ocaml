native:
	ocamlbuild mini_kanren.native

byte:
	ocamlbuild mini_kanren.byte

clean:
	rm -rf *.native
	rm -rf *.byte
