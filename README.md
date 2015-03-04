# Repos2Web
The website of the OPAM packages for Coq.

## Run
Install the dependencies:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam install -j4 coq:io:system

Compile the Coq code:

    ./configure.sh
    make

Compile the extracted OCaml code:

    cd extraction/
    curl -L https://github.com/clarus/coq-red-css/releases/download/coq-blog.1.0.2/style.min.css >html/style.min.css
    make

Clone an Coq OPAM repository:

    cd extraction/
    git clone https://github.com/coq/repo-stable

Run the program:

    cd extraction/
    ./repos2web.native opam-repository
    make serve

You can now browse the result on [localhost:8000](http://localhost:8000/).
