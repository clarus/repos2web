Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import FunctionNinjas.All.

Import ListNotations.
Local Open Scope char.

(** The name of a package, without the `coq:` prefix. *)
Module Name.
  (** A name is a string put into a record so that both types are not equal. *)
  Record t := New {
    name : LString.t }.

  (** Try to parse a string starting with the `coq:` prefix. *)
  Definition of_string (s : LString.t) : option t :=
    match s with
    | "c" :: "o" :: "q" :: ":" :: s => Some (New s)
    | _ => None
    end.

  (** Convert a name to a string with the `coq:` prefix. *)
  Definition to_string (n : t) : LString.t :=
    LString.s "coq:" ++ name n.

  (** The list of strings which can be parsed. *)
  Definition of_strings (ss : list LString.t) : list Name.t :=
    List.map_filter of_string ss.

  (** Get back a list of strings from a list of names. *)
  Definition to_strings (ns : list Name.t) : list LString.t :=
    List.map to_string ns.

  (** The functions `of_strings` is the inverse of `to_strings`. *)
  Fixpoint of_to_strings (ns : list Name.t) : of_strings (to_strings ns) = ns.
    destruct ns as [|n ns].
    - reflexivity.
    - unfold of_strings in *; simpl.
      rewrite (of_to_strings ns).
      now destruct n.
  Qed.
End Name.

(** One package. *)
Module Package.
  (** A package is a package name with a list of versions. *)
  Record t := New {
    name : Name.t;
    versions : list LString.t}.

  (** Extract the versions from a list of folders. *)
  Definition of_folders (name : Name.t) (folders : list Name.t) : t :=
    New name @@ List.fold_left (fun versions folder =>
      match LString.split_limit (Name.name folder) "." 2 with
      | [_; version] => version :: versions
      | _ => versions
      end)
      folders [].

  (** The list of folder names for each version of the package. *)
  Definition to_folders (package : t) : list Name.t :=
    versions package |> List.map (fun version =>
      Name.New (Name.name (name package) ++ ["."] ++ version)).

  (** The function `of_folders` is the inverse of `to_folders`. *)
  Lemma of_to_folders (package : t)
    : of_folders (name package) (to_folders package) = package.
  Admitted.
End Package.

(** A set of packages. *)
Module Packages.
  (** A set of packages is a list of packages. *)
  Definition t := list Package.t.

  (** The list of folder names for a set of packages. *)
  Definition to_folders (packages : t) : list Name.t :=
    List.map Package.name packages.
End Packages.

(** A single version of a package. *)
Module Version.
  (** A version is a version id and a description. *)
  Record t := New {
    id : LString.t;
    description : LString.t }.
End Version.

(** A package with its descriptions. *)
Module FullPackage.
  (** A full package is a name, a list of versions with descriptions and an
      optional last version. *)
  Record t := New {
    name : Name.t;
    versions : list Version.t;
    last_version : option Version.t}.

  (** Force the last version to be the head of the list of versions. *)
  Definition last_version_hd (package : t) : t :=
    let (name, versions, _) := package in
    New name versions (List.hd_error versions).

  (** Extract a basic package from a full package. *)
  Definition basic (package : t) : Package.t :=
    Package.New (name package) (versions package |> List.map Version.id).
End FullPackage.

(** A set of full packages. *)
Module FullPackages.
  (** A set of full packages is a list of full packages. *)
  Definition t := list FullPackage.t.

  (** Force the last version of each package to be the head of the list of
      versions. *)
  Definition last_version_hd (packages : t) : t :=
    List.map FullPackage.last_version_hd packages.

  (** Extract the basic set of packages from a set of full packages. *)
  Definition basic (packages : t) : Packages.t :=
    List.map FullPackage.basic packages.
End FullPackages.
