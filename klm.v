(** This module defines the full signature of language algebra we
consider here, and its finite complete axiomatization. We also define
here some normalisation functions, and list some of their properties. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language.
  
Delimit Scope lat_scope with lat.
Open Scope lat_scope.


Section s.
  (** * Main definitions *)
  Variable X : Set.
  Variable dec_X : decidable_set X.

  (** [𝐄'' X] is the type of expressions with variables ranging over the
  type [X]. They are built out of the constant [0], the
  concatenation (also called sequential product) [⋅], the intersection
  [∩], the union [+], and the non-zero iteration, denoted by [⁺]. *)
  Inductive 𝐄'' : Set :=
  | 𝐄''_zero : 𝐄''
  | 𝐄''_var : X -> 𝐄''
  | 𝐄''_seq : 𝐄'' -> 𝐄'' -> 𝐄''
  | 𝐄''_inter : 𝐄'' -> 𝐄'' -> 𝐄''
  | 𝐄''_plus : 𝐄'' -> 𝐄'' -> 𝐄''
  | 𝐄''_iter : 𝐄'' -> 𝐄''.

  Notation "x ⋅ y" := (𝐄''_seq x y) (at level 40) : lat_scope.
  Notation "x + y" := (𝐄''_plus x y) (left associativity, at level 50) : lat_scope.
  Notation "x ∩ y" := (𝐄''_inter x y) (at level 45) : lat_scope.
  Notation "x ⁺" := (𝐄''_iter x) (at level 25) : lat_scope.
  Notation " 0 " := 𝐄''_zero : lat_scope.

  (** The size of an expression is the number of nodes in its syntax
  tree. *)
  Global Instance size_𝐄'' : Size 𝐄'' :=
    fix 𝐄''_size (e: 𝐄'') : nat :=
      match e with
      | 0 | 𝐄''_var _ => 1%nat
      | e + f | e ∩ f | e ⋅ f => S (𝐄''_size e + 𝐄''_size f)
      | e ⁺ => S (𝐄''_size e)
      end.
  (* begin hide *)
  Lemma 𝐄''_size_zero : |0| = 1%nat. trivial. Qed.
  Lemma 𝐄''_size_var a : |𝐄''_var a| = 1%nat. trivial. Qed.
  Lemma 𝐄''_size_seq e f : |e⋅f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄''_size_inter e f : |e∩f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄''_size_plus e f : |e+f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄''_size_iter e : |e⁺| = S(|e|). trivial. Qed.
  Hint Rewrite 𝐄''_size_zero 𝐄''_size_var 𝐄''_size_seq
       𝐄''_size_inter 𝐄''_size_plus 𝐄''_size_iter
    : simpl_typeclasses.
  Fixpoint eqb e f :=
    match (e,f) with
    | (0,0) => true
    | (𝐄''_var a,𝐄''_var b) => eqX a b
    | (e⁺,f⁺) => eqb e f
    | (e1 + e2,f1 + f2)
    | (e1 ⋅ e2,f1 ⋅ f2)
    | (e1 ∩ e2,f1 ∩ f2) => eqb e1 f1 && eqb e2 f2
    | _ => false
    end.
  Lemma eqb_reflect e f : reflect (e = f) (eqb e f).
  Proof.
    apply iff_reflect;symmetry;split;
      [intro h;apply Is_true_eq_left in h;revert f h
      |intros <-;apply Is_true_eq_true];induction e;
        try destruct f;simpl;autorewrite with quotebool;firstorder.
    - apply Is_true_eq_true,eqX_correct in h as ->;auto.
    - erewrite IHe1;[|eauto]; erewrite IHe2;[|eauto];auto.
    - erewrite IHe1;[|eauto]; erewrite IHe2;[|eauto];auto.
    - erewrite IHe1;[|eauto]; erewrite IHe2;[|eauto];auto.
    - erewrite IHe;[|eauto];auto.
    - apply Is_true_eq_left,eqX_correct;auto.
  Qed.
  (* end hide *)

  (** If the set of variables [X] is decidable, then so is the set of
  expressions. _Note that we are here considering syntactic equality,
  as no semantic or axiomatic equivalence relation has been defined
  for expressions_. *)
  Global Instance 𝐄''_decidable_set : decidable_set 𝐄''.
  Proof. exact (Build_decidable_set eqb_reflect). Qed.

  (** The following are the axioms of the algebra of languages over
  this signature.*)
  Inductive ax : 𝐄'' -> 𝐄'' -> Prop :=
  (* first line *)
  | ax_inter_assoc e f g : ax (e∩(f ∩ g)) ((e∩f)∩g)
  | ax_inter_comm e f : ax (e∩f) (f∩e)
  | ax_inter_idem e : ax (e ∩ e) e
  (* second line *)
  | ax_plus_inter e f g: ax (e ∩ (f + g)) ((e∩f) + (e∩g))
  | ax_plus_inter_id e f : ax (e ∩ (e + f)) e
  | ax_inter_plus_id e f : ax (e + (e ∩ f)) e
  (* third line *)
  | ax_plus_ass e f g : ax (e+(f+g)) ((e+f)+g)
  | ax_plus_com e f : ax (e+f) (f+e)
  | ax_plus_idem e : ax (e+e) e
  (* fourth line *)                              
  | ax_seq_assoc e f g : ax (e⋅(f ⋅ g)) ((e⋅f)⋅g)
  | ax_seq_plus e f g: ax (e⋅(f + g)) (e⋅f + e⋅g)
  | ax_plus_seq e f g: ax ((e + f)⋅g) (e⋅g + f⋅g)
  | ax_plus_0 e : ax (e+0) e
  | ax_seq_0 e : ax (e⋅0) 0
  | ax_0_seq e : ax (0⋅e) 0
  (* fifth line *)
  | ax_iter_left e : ax (e⁺) (e + e⋅e⁺)
  | ax_iter_right e : ax (e⁺) (e + e⁺ ⋅e).

  Inductive ax_impl : 𝐄'' -> 𝐄'' -> 𝐄'' -> 𝐄'' -> Prop:=
  | ax_right_ind e f : ax_impl (e⋅f + f) f (e⁺⋅f + f) f
  | ax_left_ind e f : ax_impl (f ⋅ e + f) f (f ⋅e⁺ + f) f.

  (** We use these axioms to generate an axiomatic equivalence
  relation and an axiomatic order relations. *)
  Inductive 𝐄''_eq : Equiv 𝐄'' :=
  | eq_refl e : e ≡ e
  | eq_trans f e g : e ≡ f -> f ≡ g -> e ≡ g
  | eq_sym e f : e ≡ f -> f ≡ e
  | eq_plus e f g h : e ≡ g -> f ≡ h -> (e + f) ≡ (g + h)
  | eq_seq e f g h : e ≡ g -> f ≡ h -> (e ⋅ f) ≡ (g ⋅ h)
  | eq_inter e f g h : e ≡ g -> f ≡ h -> (e ∩ f) ≡ (g ∩ h)
  | eq_iter e f : e ≡ f -> (e⁺) ≡ (f⁺)
  | eq_ax e f : ax e f -> e ≡ f
  | eq_ax_impl e f g h : ax_impl e f g h -> e ≡ f -> g ≡ h.
  Global Instance 𝐄''_Equiv : Equiv 𝐄'' := 𝐄''_eq.

  Global Instance 𝐄''_Smaller : Smaller 𝐄'' := (fun e f => e + f ≡ f).

  Hint Constructors 𝐄''_eq ax ax_impl.

  Global Instance ax_equiv : subrelation ax equiv. 
  Proof. intros e f E;apply eq_ax,E. Qed.

End s.

(* begin hide *)
Arguments 𝐄''_zero {X}.
Arguments eqb {X} {dec_X} e%lat f%lat.
Hint Constructors 𝐄''_eq ax ax_impl.
Hint Rewrite @𝐄''_size_zero @𝐄''_size_var @𝐄''_size_seq
     @𝐄''_size_inter @𝐄''_size_plus @𝐄''_size_iter
  : simpl_typeclasses.
(* end hide *)

Infix " ⋅ " := 𝐄''_seq (at level 40) : lat_scope.
Infix " + " := 𝐄''_plus (left associativity, at level 50) : lat_scope.
Infix " ∩ " := 𝐄''_inter (at level 45) : lat_scope.
Notation "x ⁺" := (𝐄''_iter x) (at level 25) : lat_scope.
Notation " 0 " := 𝐄''_zero : lat_scope.

Section language.
  (** * Language interpretation *)
  Context { X : Set }.

  (** We interpret expressions as languages in the obvious way: *)
  Global Instance to_lang_𝐄'' {Σ}: semantics 𝐄'' language X Σ :=
    fix to_lang_𝐄'' σ e:=
      match e with
      | 0 => 0%lang
      | 𝐄''_var a => (σ a)
      | e + f => ((to_lang_𝐄'' σ e) + (to_lang_𝐄'' σ f))%lang
      | e ⋅ f => ((to_lang_𝐄'' σ e) ⋅ (to_lang_𝐄'' σ f))%lang
      | e ∩ f => ((to_lang_𝐄'' σ e) ∩ (to_lang_𝐄'' σ f))%lang
      | e⁺ => (to_lang_𝐄'' σ e)⁺%lang
      end.

  (* begin hide *)
  Global Instance semSmaller_𝐄'' : SemSmaller (𝐄'' X) :=
    (@semantic_containment _ _ _ _ _).
  Global Instance semEquiv_𝐄'' : SemEquiv (𝐄'' X) :=
    (@semantic_equality _ _ _ _ _).
  Hint Unfold semSmaller_𝐄'' semEquiv_𝐄'' : semantics.
  
  Section rsimpl.
    Context { Σ : Set }{σ : 𝕬[X→Σ] }.
    Lemma 𝐄''_union e f : (⟦ e+f ⟧σ) = ((⟦e⟧σ) + ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄''_prod e f :  (⟦ e⋅f ⟧σ) = ((⟦e⟧σ) ⋅ ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄''_intersection e f : (⟦ e∩f ⟧σ) = ((⟦e⟧σ) ∩ ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄''_iter_l e :  (⟦ e⁺⟧σ) = (⟦e⟧σ)⁺%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄''_variable a : (⟦𝐄''_var a⟧ σ) = σ a.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄''_empty : (⟦0⟧σ) = 0%lang.
    Proof. unfold interprete;simpl;auto. Qed.
  End rsimpl.
  Hint Rewrite @𝐄''_empty @𝐄''_variable @𝐄''_intersection
       @𝐄''_prod @𝐄''_union @𝐄''_iter_l
    : simpl_typeclasses.
  (* end hide *)
  Theorem klm_completeness : forall e f : 𝐄'' X, e ≡ f <-> e ≃ f.
  Admitted.

  Corollary klm_completeness_inf : forall e f : 𝐄'' X, e ≤ f <-> e ≲ f.
  Proof.
    intros e f;unfold smaller,𝐄''_Smaller;rewrite klm_completeness.
    split.
    - intros E A ? u Ie;apply E;now left.
    - intros E A ? u;split;rsimpl.
      + intros [I|I];auto.
        apply E,I.
      + intros I;now right.
  Qed.
End language.
Hint Rewrite @𝐄''_empty @𝐄''_variable @𝐄''_intersection
     @𝐄''_prod @𝐄''_union @𝐄''_iter_l
  : simpl_typeclasses.

Close Scope lat_scope.


(*  LocalWords:  subunits
 *)






