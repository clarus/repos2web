build:
	ocamlbuild repo2web.native -use-ocamlfind -package lwt,lwt.unix

serve:
	ruby -run -e httpd html/ -p 8000
