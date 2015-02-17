Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import FunctionNinjas.All.

Import ListNotations.
Local Open Scope char.

Module Package.
  Record t := New {
    name : LString.t;
    versions : list LString.t}.

  Definition to_string (package : t) : LString.t :=
    name package ++ LString.s ": " ++
    LString.join (LString.s ", ") (versions package).

  Definition of_folders (name : LString.t) (folders : list LString.t) : t :=
    New name @@ List.fold_left (fun versions folder =>
      match LString.split_limit folder "." 2 with
      | [_; version] => version :: versions
      | _ => versions
      end)
      folders [].

  Definition to_folders (package : t) : list LString.t :=
    versions package |> List.map (fun version =>
      name package ++ ["."] ++ version).

  Lemma of_to_folders (package : t)
    : of_folders (name package) (to_folders package) = package.
  Admitted.
End Package.

Module Packages.
  Definition t := list Package.t.

  Definition to_string (packages : t) : LString.t :=
    LString.join [LString.Char.n] (List.map Package.to_string packages).

  Definition to_folders (packages : t) : list LString.t :=
    List.map Package.name packages.
End Packages.

Module Version.
  Record t := New {
    id : LString.t;
    description : LString.t }.
End Version.

Module FullPackage.
  Record t := New {
    name : LString.t;
    versions : list Version.t(*;
    last_version : option Version.t*)}.

  (*Fixpoint last_version_aux (versions : list Version.t) : option Version.t :=
    match versions with
    | [] => None
    | version :: versions =>
      match last_version_aux with
      | None => version
      | Some version' =>
      end
    end.*)

  Definition basic (package : t) : Package.t :=
    Package.New (name package) (versions package |> List.map Version.id).
End FullPackage.

Module FullPackages.
  Definition t := list FullPackage.t.

  Definition basic (packages : t) : Packages.t :=
    List.map FullPackage.basic packages.
End FullPackages.
