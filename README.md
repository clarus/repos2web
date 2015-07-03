# Repos2Web
The website of the OPAM packages for Coq.

## Run
Install the dependencies:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install -j4 coq:io:system

Compile the Coq code:

    ./configure.sh
    make

Compile the extracted OCaml code:

    cd extraction/
    curl -L https://github.com/clarus/coq-red-css/releases/download/coq-blog.1.0.2/style.min.css >html/style.min.css
    make

Clone a Coq OPAM repository:

    cd extraction/
    git clone https://github.com/coq/opam-coq-archive

Run the program (you need to install the `dpkg` tool, which should be available even on non-Debian based distributions):

    cd extraction/
    ./repos2web.native opam-coq-archive/released
    make serve

You can now browse the result on [localhost:8000](http://localhost:8000/).
