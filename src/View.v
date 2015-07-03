(** Render a model to HTML. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.
Require Import ListPlus.All.
Require Import ListString.All.
Require Import FunctionNinjas.All.
Require Import Model.

Import ListNotations.

(** The header of the HTML page. *)
Definition header : LString.t :=
  LString.s "<!DOCTYPE html>
<html lang=""en"">
  <head>
    <meta charset=""utf-8"">
    <meta name=""viewport"" content=""width=device-width, initial-scale=1"">
    <title>Coq OPAM</title>
    <link rel=""stylesheet"" href=""style.min.css"" type=""text/css"" />
    <!-- HTML5 Shim and Respond.js IE8 support of HTML5 elements and media queries -->
    <!-- WARNING: Respond.js doesn't work if you view the page via file:// -->
    <!--[if lt IE 9]>
      <script src=""https://oss.maxcdn.com/html5shiv/3.7.2/html5shiv.min.js""></script>
      <script src=""https://oss.maxcdn.com/respond/1.4.2/respond.min.js""></script>
    <![endif]-->
  </head>
  <body>
    <div class=""container-fluid"">
      <div class=""navbar navbar-default"" role=""navigation"">
        <div class=""navbar-header"">
          <a class=""navbar-brand"" href=""/"">Coq OPAM</a>
        </div>
      </div>
      <div class=""row"">
        <div class=""col-md-12"">
".

(** The title with the number of packages. *)
Definition title (packages : FullPackages.t) : LString.t :=
  let nb_packages : N := N.of_nat @@ FullPackages.nb_packages packages in
  let nb_versions : N := N.of_nat @@ FullPackages.nb_versions packages in
  LString.s "          <h1>" ++ LString.of_N 10 10 None nb_packages ++
  LString.s " packages <small>" ++ LString.of_N 10 10 None nb_versions ++
  LString.s " versions</small></h1>
        <p>Activate the released or extra-dev repositories:</p>
        <pre>opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev</pre>
        <p>Install a package:</p>
        <pre>opam install -j4 coq:package</pre>
".

(** A row in the table of packages. *)
Definition row (package : FullPackage.t) : LString.t :=
  let (name, _, last_version) := package in
  match last_version with
  | None => LString.s ""
  | Some version => LString.s
"              <tr>
                <td>" ++ Name.name name ++ LString.s "</td>
                <td>" ++ Version.id version ++ LString.s "</td>
                <td>" ++ LString.trim (Version.description version) ++ LString.s "</td>
              </tr>
"
  end.

(** The table of packages. *)
Definition table (packages : FullPackages.t) : LString.t :=
  let packages := packages |> Sort.sort (fun a b =>
    let a := Name.name @@ FullPackage.name a in
    let b := Name.name @@ FullPackage.name b in
    match LString.compare a b with
    | Lt | Eq => true
    | Gt => false
    end) in
  LString.s
"         <h2>Table</h2>
          <table class=""table table-striped text-center"">
            <thead>
              <tr>
                <td><strong>Name</strong></td>
                <td><strong>Version</strong></td>
                <td><strong>Description</strong></td>
              </tr>
            </thead>
            <tbody>
" ++ LString.join [] (List.map row packages) ++ LString.s
"            </tbody>
          </table>
".

(** The footer of the page. *)
Definition footer : LString.t :=
  LString.s
"        </div>
      </div>
      <hr/>
      <div class=""footer"">
        <p class=""text-center"">
          <small>Sources are on <a href=""https://github.com/clarus/repos2web"">GitHub</a>. © Guillaume Claret</small>
        </p>
      </div>
    </div>
  </body>
</html>
".

(** The index page. *)
Definition index (packages : FullPackages.t) : LString.t :=
  header ++ title packages ++ table packages ++ footer.
