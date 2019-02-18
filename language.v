(** Basics of languages. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export tools.
Delimit Scope lang_scope with lang.

(* begin hide *)
Global Instance sem_eq_op
       {A : Type} (R S : relation A) (op : A -> A -> A)
       `{Equivalence _ R}
       `{PreOrder _ S}
       `{PartialOrder _ R S}
       `{Proper _ (S ==> S ==> S) op}
  : Proper (R ==> R ==> R) op.
Proof.
  intros e f E g h F.
  eapply partial_order_equivalence in E as (E1&E2).
  eapply partial_order_equivalence in F as (F1&F2).
  eapply partial_order_equivalence;unfold Basics.flip in *;split.
  - now rewrite E1,F1.
  - now rewrite E2,F2.
Qed.
(* end hide *)

(** A language over the alphabet [Σ] is a predicate over lists of
[Σ]. *)
Definition language := fun (Σ : Set) => list Σ -> Prop.

Notation " x ∊ L " := ((L : language _) x) (at level 60).

Section defs.
  Hypothesis Σ : Set.

  (** We define the equality and containment of language as follows: *)
  Global Instance lang_eq : SemEquiv (language Σ) :=
    fun l m => forall w, w ∊ l <-> w ∊ m.

  Global Instance lang_incl : SemSmaller (language Σ) :=
    fun l m => forall w, w ∊ l -> w ∊ m.

  (** Equality is an equivalence relation, and containment is a partial order.*)
  Global Instance lang_eq_Equivalence : Equivalence sequiv.
  Proof. split;intro;unfold lang_eq;firstorder. Qed.

  Global Instance lang_incl_PreOrder : PreOrder ssmaller.
  Proof. split;intro;unfold lang_incl;firstorder. Qed.

  Global Instance lang_incl_PartialOrder :
    PartialOrder sequiv ssmaller.
  Proof. split;intro;unfold lang_incl;firstorder. Qed.

  (** We now define the elementary operations on languages. *)
  Definition prod (l m : language Σ) : language Σ:=
    fun w => exists u v, u ∊ l /\ v ∊ m /\ w = u++v.
  
  Definition union (l m : language Σ) : language Σ:=
    fun w => w ∊ l \/ w ∊ m.

  Definition intersection (l m : language Σ) : language Σ:=
    fun w => w ∊ l /\ w ∊ m.

  Definition mirror (l : language Σ) : language Σ:=
    fun w => (rev w) ∊ l.

  Definition unit : language Σ := fun w => w = [].

  Definition empty : language Σ := fun _ => False.

  Fixpoint iter_prod (l : language Σ) n : language Σ :=
    match n with
    | 0 => unit
    | S n => prod l (iter_prod l n)
    end.

  Definition iter (l : language Σ) : language Σ :=
    fun u => exists n, u ∊ iter_prod l (S n).
  
  (** These operations are monotone. *)
  Global Instance prod_lang_incl :
    Proper (ssmaller ==> ssmaller ==> ssmaller) prod.
  Proof.
    intros e f E g h F w (u&v&Iu&Iv&->);exists u;exists v;
    repeat split;auto.
  Qed.

  Global Instance union_lang_incl :
    Proper (ssmaller ==> ssmaller ==> ssmaller) union.
  Proof.
    intros e f E g h F w [I|I];[left|right];auto.
  Qed.

  Global Instance intersection_lang_incl :
    Proper (ssmaller ==> ssmaller ==> ssmaller) intersection.
  Proof.
    intros e f E g h F w (I1&I2);repeat split;auto.
  Qed.

  Global Instance mirror_lang_incl :
    Proper (ssmaller ==> ssmaller) mirror.
  Proof.
    intros e f E w I;unfold mirror in *;apply E;auto.
  Qed.

  Global Instance iter_prod_lang_incl :
    Proper (ssmaller ==> eq ==> ssmaller) iter_prod.
  Proof.
    intros l m I n ? <-;induction n;simpl.
    - reflexivity.
    - intros ? (u1&u2&I1&I2&->).
      exists u1,u2;repeat split;auto.
  Qed.

  Global Instance iter_lang_incl :
    Proper (ssmaller ==> ssmaller) iter.
  Proof.
    intros l m I u (n&Iu);exists n.
    eapply iter_prod_lang_incl;eauto.
  Qed.
  
  Global Instance union_lang_eq :
    Proper (sequiv ==> sequiv ==> sequiv) union.
  Proof.
     eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto).
  Qed.

  Global Instance prod_lang_eq :
    Proper (sequiv ==> sequiv ==> sequiv) prod.
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.

  Global Instance intersection_lang_eq :
    Proper (sequiv ==> sequiv ==> sequiv) intersection.
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.

  Global Instance mirror_lang_eq :
    Proper (sequiv ==> sequiv) mirror.
  Proof.
    intros e f E w;split;unfold mirror in *;apply E;auto.
  Qed.

  Global Instance iter_prod_lang_eq : 
    Proper (sequiv ==> eq ==> sequiv) iter_prod.
  Proof. intros e f E n ? <- w;split;apply iter_prod_lang_incl;try rewrite E;reflexivity. Qed.

  Global Instance iter_lang_eq : 
    Proper (sequiv ==> sequiv) iter.
  Proof. intros e f E w;split;apply iter_lang_incl;try rewrite E;reflexivity. Qed.
  
End defs.

(** The empty words belongs to a language exactly when it belongs to
its mirror image. *)
Lemma mirror_nil {Σ : Set} (L : language Σ) : mirror L [] <-> L [].
Proof.
  unfold mirror;simpl;tauto.
Qed.

(** An assignment of type [X→Σ] is a map from variables in [X] to
languages over [Σ]. *)
Definition assignment (X Σ : Set) := X -> language Σ.

Notation " 𝕬[ X → Σ ] " := (assignment X Σ).
(** [σ] is test-compatible with [A], written [A ⊢ σ], if for every
variable [a] in [A] the empty list belongs to [σ(a)]. *)
Definition test_compatible {Σ X} (σ : 𝕬[X→Σ]) (A : list X) :=
  forall a : X, a ∈ A -> [] ∊ σ a.

Notation " A ⊢ σ " := (test_compatible σ A) (at level 70).

(** Being test-compatible with a concatenation of two lists means
being compatible with both lists. *)
Lemma test_compatible_app  {Σ X} A B (σ : 𝕬[X→Σ]): A++B ⊢ σ <-> A ⊢ σ /\ B ⊢ σ.
Proof.
  unfold test_compatible;setoid_rewrite in_app_iff;firstorder.
Qed.

(** The ordering on languages can be lifted to assignments. *)
Global Instance incl_assign {X A} : SemSmaller 𝕬[X → A] :=
  fun σ τ => forall x, σ x ≲ τ x.

Global Instance eq_assign {X A} : SemEquiv 𝕬[X → A] :=
  fun σ τ => forall x, σ x ≃ τ x.

Global Instance incl_assign_PreOrder {X A} : PreOrder (@ssmaller 𝕬[X → A] _).
Proof.
  split.
  - intros σ x;reflexivity.
  - intros σ1 σ2 σ3 E1 E2 x;transitivity (σ2 x);auto.
Qed.

Global Instance eq_assign_Equivalence {X A} : Equivalence (@sequiv 𝕬[X → A] _).
Proof.
  split.
  - intros σ x;reflexivity.
  - intros σ τ E x;symmetry;auto.
  - intros σ1 σ2 σ3 E1 E2 x;transitivity (σ2 x);auto.
Qed.

Global Instance incl_assign_PartialOrder {X A} : PartialOrder _ (@ssmaller 𝕬[X → A] _).
Proof.
  intros σ τ;split;unfold Basics.flip.
  - intro E;split;intro x;rewrite (E x);reflexivity.
  - intros (E1&E2) x;apply lang_incl_PartialOrder;unfold Basics.flip;split;auto.
Qed.

(* begin hide *)
Arguments empty { Σ } w.
Arguments unit { Σ } w.
(* end hide *)

Infix " ⋅ " := prod (at level 40) : lang_scope.
Infix " ∩ " := intersection (at level 45) : lang_scope.
Infix " + " := union (left associativity, at level 50) : lang_scope.
Notation " L ¯ " := (mirror L) (at level 25) : lang_scope.
Notation " L ^{ n } " := (iter_prod L n) (at level 25) : lang_scope.
Notation " L ⁺ " := (iter L) (at level 25) : lang_scope.
Notation " 0 " := empty : lang_scope.
Notation " 1 " := unit : lang_scope.

Lemma lang_iter_prod_last {Σ}(l: language Σ) n : (l ^{S n} ≃ l ^{n} ⋅ l)%lang.
Proof.
  induction n.
  - simpl;intros w;split;intros (u&v&I1&I2&->).
    + rewrite I2,app_nil_r;exists [],u;split;reflexivity||auto.
    + rewrite I1;exists v,[];rewrite app_nil_r;repeat split;auto.
  - intros x;split.
    + intros (u&?&I1&I2&->).
      apply IHn in I2 as (v&w&I2&I3&->).
      exists (u++v),w;rewrite app_ass;repeat split;auto.
      exists u,v;tauto.
    + intros (?&w&(u&v&I1&I2&->)&I3&->).
      cut (l^{S n}%lang (v++w));[|apply IHn;exists v,w;tauto].
      intro I';exists u,(v++w);rewrite app_ass;repeat split;auto.
Qed.

(* begin hide *)
Arguments empty { Σ } w.
Arguments unit { Σ } w.
Hint Unfold union prod intersection mirror unit iter empty lang_incl lang_eq: semantics.
(* end hide *)
