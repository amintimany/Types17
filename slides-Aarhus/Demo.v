Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Inductive list (A : Type) :=
| nil : list A
| cons : A -> list A -> list A.

Print list.

Section listlift.
  Universe i j.
  Constraint i < j.

  Definition L_lift A (l : list@{i} A) : list@{j} A := l.

  Definition L_lower A (l : list@{j} A) : list@{i} A := l.

  Definition list_eq A : list@{i} A = list@{j} A := eq_refl.

End listlift.

Record Category : Type :=
{
  (** Type of Objects *)
  Obj : Type;

  (** Type of morphism beween two objects *)
  Hom : Obj -> Obj -> Type;

  (** composition of morphisms: *)
  compose : forall {a b c : Obj}, (Hom a b) -> (Hom b c) -> (Hom a c);

  (** associativity of composition: *)
  assoc : forall {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
            (compose f (compose g h)) = (compose f (compose g h));

  (** symmetric form of associativity: *)
  assoc_sym : forall {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
                (compose f (compose g h )) = (compose f (compose g h));

  (** identity morphisms: *)
  id : forall {a : Obj}, Hom a a;

  (** id left unit: *)
  id_unit_left : forall (a b : Obj) (h : Hom a b), compose h id = h;

  (** id right unit: *)
  id_unit_right : forall (a b : Obj) (h : Hom a b), compose id h = h
}.

Print Category.

Section Catlift.
  Universe i j k l.
  Constraint i < k, j < l.

  Definition C_lift (C : Category@{i j}) : Category@{k l} := C.

  Fail Definition C_lower (C : Category@{k l}) : Category@{i j} := C.

  Fail Definition cat_eq A : Category@{i j} A = Category@{k l} A := eq_refl.

End Catlift.

Inductive nat@{i} : Type@{i} :=
| O : nat
| S : nat -> nat.

Print nat.

Section natlift.
  Universe i j.
  Constraint i < j.

  Definition N_lift (n : nat@{i}) : nat@{j} := n.

  Definition N_lower (n : nat@{j}) : nat@{j} := n.

  Definition N_eq : nat@{i} = nat@{j} := eq_refl.

End natlift.