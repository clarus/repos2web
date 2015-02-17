Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint merge {A : Type} (le : A -> A -> bool) (l1 l2 : list A) : list A :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | a1::l1', a2::l2' =>
      if le a1 a2 then
        a1 :: merge le l1' l2
      else
        a2 :: merge_aux l2'
  end
  in merge_aux l2.


Fixpoint merge_list_to_stack {A} (le : A -> A -> bool) stack l :=
  match stack with
  | [] => [Some l]
  | None :: stack' => Some l :: stack'
  | Some l' :: stack' => None :: merge_list_to_stack le stack' (merge le l' l)
  end.

Fixpoint merge_stack {A} (le : A -> A -> bool) stack :=
  match stack with
  | [] => []
  | None :: stack' => merge_stack le stack'
  | Some l :: stack' => merge le l (merge_stack le stack')
  end.

Fixpoint iter_merge {A} (le : A -> A -> bool) stack l :=
  match l with
  | [] => merge_stack le stack
  | a::l' => iter_merge le (merge_list_to_stack le stack [a]) l'
  end.

Definition sort {A : Type} (le : A -> A -> bool) : list A -> list A :=
  iter_merge le [].
