Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import FunctionNinjas.All.

Import ListNotations.
Local Open Scope char.

Module Name.
  Record t := New {
    name : LString.t }.

  Definition to_string (n : t) : LString.t :=
    LString.s "coq:" ++ name n.

  Definition of_string (s : LString.t) : option t :=
    match s with
    | "c" :: "o" :: "q" :: ":" :: s => Some (New s)
    | _ => None
    end.

  Definition of_strings (ss : list LString.t) : list Name.t :=
    List.map_filter of_string ss.

  Definition to_strings (ns : list Name.t) : list LString.t :=
    List.map to_string ns.

  Fixpoint of_to_strings (ns : list Name.t) : of_strings (to_strings ns) = ns.
    destruct ns as [|n ns].
    - reflexivity.
    - unfold of_strings in *; simpl.
      rewrite (of_to_strings ns).
      now destruct n.
  Qed.
End Name.

Module Package.
  Record t := New {
    name : Name.t;
    versions : list LString.t}.

  Definition to_string (package : t) : LString.t :=
    Name.to_string (name package) ++ LString.s ": " ++
    LString.join (LString.s ", ") (versions package).

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

  Lemma of_to_folders (package : t)
    : of_folders (name package) (to_folders package) = package.
  Admitted.

  (*Lemma filter_coq_files_of_version_folders (package : Package.t)
    : Name.of_strings (to_folders package) = to_folders package.
  Admitted.*)
End Package.

Module Packages.
  Definition t := list Package.t.

  Definition to_string (packages : t) : LString.t :=
    LString.join [LString.Char.n] (List.map Package.to_string packages).

  Definition to_folders (packages : t) : list Name.t :=
    List.map Package.name packages.
End Packages.

Module Version.
  Record t := New {
    id : LString.t;
    description : LString.t }.
End Version.

Module FullPackage.
  Record t := New {
    name : Name.t;
    versions : list Version.t;
    last_version : option Version.t}.

  Definition last_version_hd (package : t) : t :=
    let (name, versions, _) := package in
    New name versions (List.hd_error versions).

  Definition basic (package : t) : Package.t :=
    Package.New (name package) (versions package |> List.map Version.id).
End FullPackage.

Module FullPackages.
  Definition t := list FullPackage.t.

  Definition last_version_hd (packages : t) : t :=
    List.map FullPackage.last_version_hd packages.

  Definition basic (packages : t) : Packages.t :=
    List.map FullPackage.basic packages.
End FullPackages.
