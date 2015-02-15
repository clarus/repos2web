(** The definition of computations, used to represent interactive programs. *)
Require Import ListString.All.

Local Open Scope type.

(** External calls. *)
Module Command.
  Inductive t :=
  (** List the folders of a directory. *)
  | ListFolders (directory : LString.t)
  (** Update (or create) a file with some content. *)
  | WriteFile (file_name : LString.t) (content : LString.t)
  (** Evaluate a command. *)
  | Eval (command : LString.t)
  (** Write a message on the standard output. *)
  | Log (message : LString.t).

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | ListFolders _ => option (list LString.t)
    | WriteFile _ _ => bool
    | Eval _ => option LString.t
    | Log _ => unit
    end.
End Command.

(** Computations with I/Os. *)
Module C.
  (** A computation can either return a pure value, or do a system call and wait
      for the answer to run another computation. *)
  Inductive t : Type -> Type :=
  | Ret : forall {A : Type} (x : A), t A
  | Call : forall {A : Type} (command : Command.t),
    (Command.answer command -> t A) -> t A
  | Join : forall {A B : Type}, t A -> t B -> t (A * B).

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition ret {A : Type} (x : A) : t A :=
      Ret x.

    (** A nicer notation for `Join`. *)
    Definition join {A B : Type} (x : t A) (y : t B) : t (A * B) :=
      Join x y.

    (** We define an explicit apply function so that Coq does not try to expand
        the notations everywhere. *)
    Definition apply {A B} (f : A -> B) (x : A) := f x.

    (** System call. *)
    Notation "'call!' answer ':=' command 'in' X" :=
      (Call command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    (** System call with typed answer. *)
    Notation "'call!' answer : A ':=' command 'in' X" :=
      (Call command (fun (answer : A) => X))
      (at level 200, answer ident, command at level 100, A at level 200, X at level 200).

    (** System call ignoring the answer. *)
    Notation "'do_call!' command 'in' X" :=
      (Call command (fun _ => X))
      (at level 200, command at level 100, X at level 200).

    (** This notation is useful to compose computations which wait for a
        continuation. We do not have an explicit bind operator to simplify the
        language and the proofs. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (apply X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (apply X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the answer. *)
    Notation "'do_let!' X 'in' Y" :=
      (apply X (fun _ => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End C.
