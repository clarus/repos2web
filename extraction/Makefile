build:
	ocamlbuild repo2web.native -use-ocamlfind -package io-effects-unix,lwt,lwt.unix

clean:
	ocamlbuild -clean

serve:
	ruby -run -e httpd html/ -p 8000
