(** This module defines the full signature of language algebra we
consider here, and its finite complete axiomatization. We also define
here some normalisation functions, and list some of their properties. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language.

Delimit Scope expr_scope with expr.
Open Scope expr_scope.

Section s.
  (** * Main definitions *)
  Variable X : Set.
  Variable dec_X : decidable_set X.

  (** [𝐄 X] is the type of expressions with variables ranging over the
  type [X]. They are built out of the constants [0] and [1], the
  concatenation (also called sequential product) [⋅], the intersection
  [∩], the union [+], the mirror image, denoted by the postfix
  operator [̅], and the non-zero iteration, denoted by [⁺]. *)
  Inductive 𝐄 : Set :=
  | 𝐄_one : 𝐄
  | 𝐄_zero : 𝐄
  | 𝐄_var : X -> 𝐄
  | 𝐄_seq : 𝐄 -> 𝐄 -> 𝐄
  | 𝐄_inter : 𝐄 -> 𝐄 -> 𝐄
  | 𝐄_plus : 𝐄 -> 𝐄 -> 𝐄
  | 𝐄_conv : 𝐄 -> 𝐄
  | 𝐄_iter : 𝐄 -> 𝐄.

  Notation "x ⋅ y" := (𝐄_seq x y) (at level 40) : expr_scope.
  Notation "x + y" := (𝐄_plus x y) (left associativity, at level 50) : expr_scope.
  Notation "x ∩ y" := (𝐄_inter x y) (at level 45) : expr_scope.
  Notation "x ¯" := (𝐄_conv x) (at level 25) : expr_scope.
  Notation "x ⁺" := (𝐄_iter x) (at level 25) : expr_scope.
  Notation " 1 " := 𝐄_one : expr_scope.
  Notation " 0 " := 𝐄_zero : expr_scope.

  (** The size of an expression is the number of nodes in its syntax
  tree. *)
  Global Instance size_𝐄 : Size 𝐄 :=
    fix 𝐄_size (e: 𝐄) : nat :=
      match e with
      | 0 | 1 | 𝐄_var _ => 1%nat
      | e + f | e ∩ f | e ⋅ f => S (𝐄_size e + 𝐄_size f)
      | e ¯ | e ⁺ => S (𝐄_size e)
      end.
  (* begin hide *)
  Lemma 𝐄_size_one : |1| = 1%nat. trivial. Qed.
  Lemma 𝐄_size_zero : |0| = 1%nat. trivial. Qed.
  Lemma 𝐄_size_var a : |𝐄_var a| = 1%nat. trivial. Qed.
  Lemma 𝐄_size_seq e f : |e⋅f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄_size_inter e f : |e∩f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄_size_plus e f : |e+f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄_size_conv e : |e ¯| = S(|e|). trivial. Qed.
  Lemma 𝐄_size_iter e : |e⁺| = S(|e|). trivial. Qed.
  Hint Rewrite 𝐄_size_one 𝐄_size_zero 𝐄_size_var 𝐄_size_seq
       𝐄_size_inter 𝐄_size_plus 𝐄_size_conv 𝐄_size_iter
    : simpl_typeclasses.
  Fixpoint eqb e f :=
    match (e,f) with
    | (1,1) | (0,0) => true
    | (𝐄_var a,𝐄_var b) => eqX a b
    | (e ¯,f ¯) | (e⁺,f⁺) => eqb e f
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
    - erewrite IHe;[|eauto];auto.
    - apply Is_true_eq_left,eqX_correct;auto.
  Qed.
  (* end hide *)

  (** If the set of variables [X] is decidable, then so is the set of
  expressions. _Note that we are here considering syntactic equality,
  as no semantic or axiomatic equivalence relation has been defined
  for expressions_. *)
  Global Instance 𝐄_decidable_set : decidable_set 𝐄.
  Proof. exact (Build_decidable_set eqb_reflect). Qed.

  (** The set of variables of an expressions can be computed
  inductively as follows. *)
  Fixpoint Vars e :=
    match e with
    | 0 | 1 => []
    | 𝐄_var a => [a]
    | e + f | e ∩ f | e ⋅ f => Vars e ++ Vars f
    | e ⁺ | e ¯ => Vars e
    end.

  (** The following are the axioms of the algebra of languages over
  this signature.*)
  Inductive ax : 𝐄 -> 𝐄 -> Prop :=
  (** [⟨𝐄,⋅,1⟩] is a monoid. *)
  | ax_seq_assoc e f g : ax (e⋅(f ⋅ g)) ((e⋅f)⋅g)
  | ax_seq_1 e : ax (1⋅e) e
  | ax_1_seq e : ax (e⋅1) e
  (** [⟨𝐄,+,0⟩] is a commutative monoid. *)
  | ax_plus_com e f : ax (e+f) (f+e)
  | ax_plus_ass e f g : ax (e+(f+g)) ((e+f)+g)
  | ax_plus_0 e : ax (e+0) e
  (** [⟨𝐄,⋅,+,1,0⟩] is an idempotent semiring. *)
  | ax_seq_0 e : ax (e⋅0) 0
  | ax_0_seq e : ax (0⋅e) 0
  | ax_plus_seq e f g: ax ((e + f)⋅g) (e⋅g + f⋅g)
  | ax_seq_plus e f g: ax (e⋅(f + g)) (e⋅f + e⋅g)
  (** [⟨𝐄,∩⟩] is a commutative and idempotent semigroup. *)
  | ax_inter_assoc e f g : ax (e∩(f ∩ g)) ((e∩f)∩g)
  | ax_inter_comm e f : ax (e∩f) (f∩e)
  | ax_inter_idem e : ax (e ∩ e) e
  (** [⟨𝐄,+,∩⟩] forms a distributive lattice, and [0] is absorbing for
  [∩]. *)
  | ax_plus_inter e f g: ax ((e + f)∩g) (e∩g + f∩g)
  | ax_inter_plus e f : ax ((e∩f)+e) e
  (** [¯] is an involution that flips concatenations and commutes with
  every other operation. *)
  | ax_conv_conv e : ax (e ¯¯) e
  | ax_conv_plus e f: ax ((e + f)¯) (e ¯ + f ¯)
  | ax_conv_seq e f: ax ((e ⋅ f)¯) (f ¯ ⋅ e ¯)
  | ax_conv_inter e f: ax ((e∩f)¯) (e ¯ ∩ f ¯)
  | ax_conv_iter e : ax (e⁺¯) (e ¯⁺)
  (** The axioms for [⁺] are as follow: *)
  | ax_iter_left e : ax (e⁺) (e + e⋅e⁺)
  | ax_iter_right e : ax (e⁺) (e + e⁺ ⋅e)
  (** The five laws that follow are the most interesting ones. They
  concern _subunits_, terms that are smaller than [1]. With our
  signature, any term can be projected to a subunit using the
  operation [1 ∩ _ ]. *)
  (** - For subunits, intersection and concatenation coincide. *)
  | ax_inter_1_seq e f : ax (1 ∩ (e⋅f)) (1 ∩ (e ∩ f))
  (** - Mirror image is the identity on subunits. *)
  | ax_inter_1_conv e : ax (1 ∩ (e ¯)) (1 ∩ e)
  (** - Subunits commute with every term. *)
  | ax_inter_1_comm_seq e f : ax ((1 ∩ e)⋅f) (f⋅(1 ∩ e))
  (** - This law is less intuitive, but with the previous ones,
  it allows one to extract from any union-free expressions a single
  global subunit.*)
  | ax_inter_1_inter e f g : ax (((1 ∩ e)⋅f) ∩ g) ((1 ∩ e)⋅(f ∩ g))
  | ax_inter_1_iter e f g : ax ((g + (1 ∩ e) ⋅ f)⁺) (g⁺ + (1 ∩ e) ⋅ (g + f)⁺).

  (** Additionally, we need these two implications: *)
  Inductive ax_impl : 𝐄 -> 𝐄 -> 𝐄 -> 𝐄 -> Prop:=
  | ax_right_ind e f : ax_impl (e⋅f + f) f (e⁺⋅f + f) f
  | ax_left_ind e f : ax_impl (f ⋅ e + f) f (f ⋅e⁺ + f) f.

  (** We use these axioms to generate an axiomatic equivalence
  relation and an axiomatic order relations. *)
  Inductive 𝐄_eq : Equiv 𝐄 :=
  | eq_refl e : e ≡ e
  | eq_trans f e g : e ≡ f -> f ≡ g -> e ≡ g
  | eq_sym e f : e ≡ f -> f ≡ e
  | eq_plus e f g h : e ≡ g -> f ≡ h -> (e + f) ≡ (g + h)
  | eq_seq e f g h : e ≡ g -> f ≡ h -> (e ⋅ f) ≡ (g ⋅ h)
  | eq_inter e f g h : e ≡ g -> f ≡ h -> (e ∩ f) ≡ (g ∩ h)
  | eq_conv e f : e ≡ f -> (e ¯) ≡ (f ¯)
  | eq_iter e f : e ≡ f -> (e⁺) ≡ (f⁺)
  | eq_ax e f : ax e f -> e ≡ f
  | eq_ax_impl e f g h : ax_impl e f g h -> e ≡ f -> g ≡ h.
  Global Instance 𝐄_Equiv : Equiv 𝐄 := 𝐄_eq.

  Global Instance 𝐄_Smaller : Smaller 𝐄 := (fun e f => e + f ≡ f).

  Hint Constructors 𝐄_eq ax ax_impl.

  Global Instance ax_equiv : subrelation ax equiv. 
  Proof. intros e f E;apply eq_ax,E. Qed.

  (** * Some elementary properties of this algebra *)

  (** It is immediate to check that the equivalence we defined is
  indeed an equivalence relation, that the order relation is a
  preorder, and that every operator is monotone for both relations. *)
  Global Instance equiv_Equivalence : Equivalence equiv.
  Proof. split;intro;eauto. Qed.

  Global Instance inter_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄_inter.
  Proof. now intros e f hef g h hgh;apply eq_inter. Qed.

  Global Instance plus_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄_plus.
  Proof. now intros e f hef g h hgh;apply eq_plus. Qed.

  Global Instance seq_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄_seq.
  Proof. now intros e f hef g h hgh;apply eq_seq. Qed.
  
  Global Instance conv_equiv :
    Proper (equiv ==> equiv) 𝐄_conv.
  Proof. now intros e f hef;apply eq_conv. Qed.
  
  Global Instance iter_equiv :
    Proper (equiv ==> equiv) 𝐄_iter.
  Proof. now intros e f hef;apply eq_iter. Qed.

  
  Lemma plus_idem e : e+e ≡ e.
  Proof.
    rewrite <- (ax_inter_idem e) at 1.
    rewrite ax_inter_plus;reflexivity.
  Qed.
  Hint Resolve plus_idem.

  Global Instance smaller_PreOrder : PreOrder smaller.
  Proof.
    split;intro;unfold smaller,𝐄_Smaller;intros.
    - auto.
    - transitivity (y + z);[|auto].
      transitivity (x + y + z);[|auto].
      transitivity (x + (y + z));[|auto].
      auto.
  Qed.

  Global Instance smaller_PartialOrder : PartialOrder equiv smaller.
  Proof.
    intros e f;split;unfold smaller,𝐄_Smaller;unfold Basics.flip.
    - intros E;split.
      + rewrite E;auto.
      + rewrite E;auto.
    - intros (E1&E2).
      rewrite <- E1.
      rewrite <- E2 at 1;auto.
  Qed.

  Global Instance smaller_equiv : subrelation equiv smaller.
  Proof. intros e f E;apply smaller_PartialOrder in E as (E&_);apply E. Qed.

  (** From the axioms, we can infer the following simple laws. *)
  Lemma equiv_0_inter e : (0∩e) ≡ 0.
  Proof. rewrite <- (ax_plus_0 (0∩e));auto. Qed.

  Lemma inter_plus e f g : (e∩(f + g)) ≡ (e∩f + e∩g).
  Proof.
    rewrite (eq_ax (ax_inter_comm _ _)).
    rewrite (eq_ax (ax_plus_inter _ _ _));auto.
  Qed.

  Global Instance inter_smaller :
    Proper (smaller ==> smaller ==> smaller) 𝐄_inter.
  Proof.
    intros e f hef g h hgh;unfold smaller,𝐄_Smaller in *.
    rewrite <- hef,<-hgh.
    repeat rewrite inter_plus.
    repeat rewrite (ax_inter_comm (e+f) g).
    repeat rewrite (ax_inter_comm (e+f) h).
    repeat rewrite inter_plus.
    rewrite (ax_inter_comm e g).
    repeat rewrite (ax_plus_ass _ _ _).
    auto.
  Qed.
  
  Global Instance plus_smaller :
    Proper (smaller ==> smaller ==> smaller) 𝐄_plus.
  Proof.
    intros e f hef g h hgh;unfold smaller,𝐄_Smaller in *.
    transitivity (e + g + (h + f));[auto|].
    transitivity (e + (g + (h + f)));[auto|].
    transitivity (e + (g + h + f));[auto|].
    transitivity (e + (h + f));[auto|].
    transitivity (e + (f + h));[auto|].
    transitivity (e + f + h);auto.
  Qed.

  Global Instance seq_smaller :
    Proper (smaller ==> smaller ==> smaller) 𝐄_seq.
  Proof.
    intros e f hef g h hgh;unfold smaller,𝐄_Smaller in *.
    rewrite <- hef,<-hgh.
    rewrite (eq_ax (ax_seq_plus _ _ _)).
    repeat rewrite (eq_ax (ax_plus_seq _ _ _)).
    repeat rewrite (eq_ax (ax_plus_ass _ _ _)).
    auto.
  Qed.

  Global Instance conv_smaller :
    Proper (smaller ==> smaller) 𝐄_conv.
  Proof.
    intros e f hef;unfold smaller,𝐄_Smaller in *.
    rewrite <- (eq_ax (ax_conv_plus _ _)),hef;reflexivity.
  Qed.

  Lemma iter_left e : e ⋅ e⁺ ≤ e ⁺.
  Proof.
    unfold smaller,𝐄_Smaller.
    rewrite (eq_ax(ax_iter_left _)) at 2 3.
    transitivity (e ⋅ e ⁺ + e + e ⋅ e ⁺);[auto|].
    transitivity (e + e ⋅ e ⁺ + e ⋅ e ⁺);[auto|].
    transitivity (e + (e ⋅ e ⁺ + e ⋅ e ⁺));auto.
  Qed.
  Lemma iter_incr e : e ≤ e ⁺.
  Proof.
    unfold smaller,𝐄_Smaller.
    rewrite (eq_ax(ax_iter_left _)).
    transitivity (e + e + e ⋅ e ⁺);auto.
  Qed.

  Lemma iter_seq e : e ⁺⋅e ⁺ ≤ e⁺.
  Proof. apply (eq_ax_impl (ax_right_ind _ _)),iter_left. Qed.

  Lemma iter_idempotent e : e ⁺ ⁺ ≡ e ⁺.
  Proof.
    rewrite (eq_ax (ax_iter_right _)).
    rewrite (eq_ax (ax_plus_com _ _)).
    apply (eq_ax_impl (ax_right_ind _ _)).
    apply iter_seq.
  Qed.

  Lemma right_ind e f : e⋅f ≤ f -> e⁺⋅f≤f.
  Proof. intro h;eapply eq_ax_impl,h;auto. Qed.
  Lemma left_ind e f : e⋅f ≤ e -> e⋅f⁺≤e.
  Proof. intro h;eapply eq_ax_impl,h;auto. Qed.

  Lemma plus_inf e f g : e ≤ g -> f ≤ g -> e + f ≤ g.
  Proof.
    intros h1 h2;unfold smaller,𝐄_Smaller in *. 
    rewrite <- h1,<-h2 at 2;auto.
  Qed.
  Lemma plus_left e f g : e ≤ f -> e ≤ f + g.
  Proof.
    intros h1;unfold smaller,𝐄_Smaller in *.
    transitivity (e+f+g);auto.
  Qed.
  Lemma plus_right e f g : e ≤ g -> e ≤ f + g.
  Proof.
    intros h1;unfold smaller,𝐄_Smaller in *.
    transitivity (f+g+e);auto.
    transitivity (f+(g+e));auto.
    transitivity (f+(e+g));auto.
  Qed.
  
  Global Instance iter_smaller :
    Proper (smaller ==> smaller) 𝐄_iter.
  Proof.
    intros e f hef.
    rewrite (eq_ax(ax_iter_right e)) at 1.
    apply plus_inf.
    - rewrite hef.
      rewrite (eq_ax(ax_iter_right f)).
      apply plus_left;reflexivity.
    - rewrite hef at 2.
      rewrite (iter_incr f) at 1.
      apply right_ind.
      rewrite hef.
      apply iter_left.
  Qed.

  Lemma zero_minimal e : 0 ≤ e.
  Proof.
    unfold smaller,𝐄_Smaller.
    transitivity (e + 0);auto.
  Qed.
  
  Lemma inf_ax_inter_l e f : e ∩ f ≤ e.
  Proof. apply (eq_ax (ax_inter_plus _ _)). Qed.

  Lemma inf_ax_inter_r e f : e ∩ f ≤ f.
  Proof. rewrite ax_inter_comm,inf_ax_inter_l;reflexivity. Qed.

  Lemma inter_glb e f g : g ≤ e -> g ≤ f -> g ≤ e ∩ f.
  Proof. intros <- <- ;apply smaller_equiv;auto. Qed.

  Proposition smaller_inter e f : e ≤ f <-> e∩f ≡ e.
  Proof.
    split;[|intros <-;apply inf_ax_inter_r].
    intros E.
    apply smaller_PartialOrder;unfold Basics.flip;split;[apply inf_ax_inter_l|].
    apply inter_glb;[reflexivity|assumption].
  Qed.

  (** Mirror is actually more than monotone, it is bijective. *)
  Lemma smaller_conv_iff e f :
    e ≤ f <-> e ¯ ≤ f ¯.
  Proof.
    split;[apply conv_smaller|].
    rewrite <- (eq_ax (ax_conv_conv e)) at 2.
    rewrite <- (eq_ax (ax_conv_conv f)) at 2.
    apply conv_smaller.
  Qed.

  (** We establish few properties of subunits. *)
  Lemma inter_1_abs e f : ((1 ∩ e)⋅(1 ∩ f)) ≡ (1 ∩ (e ∩ f)).
  Proof.
    transitivity ((1∩1)∩(e∩f));auto.
    transitivity ((1∩1∩1)∩(e∩f));auto.
    transitivity (((1∩1)∩(1∩(e∩f))));auto.
    transitivity (((1∩1)∩((1∩e)∩f)));auto.
    transitivity (((1∩1)∩(1∩e)∩f));auto.
    transitivity ((1∩(1∩(1∩e))∩f));auto.
    transitivity ((1∩((1∩e)∩1)∩f));auto.
    transitivity (1∩((1∩e)∩1∩f));auto.
    transitivity (1∩((1∩e)∩(1∩f)));auto.
    transitivity (1∩((1∩e)⋅(1∩f)));auto.
    apply smaller_PartialOrder;unfold Basics.flip;split;auto.
    - rewrite <- ax_inter_idem at 1.
      apply inter_smaller;[|reflexivity].
      transitivity (1⋅1);[|apply smaller_equiv;auto].
      apply seq_smaller;apply inf_ax_inter_l.
    - apply inf_ax_inter_r.
  Qed.
    
  Lemma inter_onel e : (1 ∩ e + (1 ∩ e)⋅e) ≡ ((1 ∩ e)⋅e).
  Proof.
    assert (E1:(1 ∩ e) + e ≡ e) by eauto.
    assert (E2:(1 ∩ e) ≡ (1 ∩ e)⋅(1 ∩ e))
      by (transitivity (1 ∩ (e ∩ e));auto using inter_1_abs).
    rewrite E2 at 1.
    rewrite <- (ax_seq_plus _ _ _ ).
    rewrite E1;auto.
  Qed.

  Lemma inter_oner e : (1 ∩ e + e⋅(1 ∩ e)) ≡ (e⋅(1 ∩ e)).
  Proof.
    rewrite <- (eq_ax (ax_inter_1_comm_seq _ _)).
    apply inter_onel.
  Qed.                      

  (** A product is larger than [1] if and only if both its arguments are.*)
  Lemma split_one e f : 1 ≤ e⋅f <-> 1 ≤ e /\ 1 ≤ f.
  Proof.
    split;[|intros (<-&<-);apply smaller_equiv;auto].
    intro E.
    apply smaller_inter in E.
    rewrite (eq_ax (ax_inter_1_seq _ _)) in E.
    rewrite <- E;split;auto.
    - rewrite <-(inf_ax_inter_l e f) at 2;auto.
      apply inf_ax_inter_r.
    - rewrite <-(inf_ax_inter_r e f) at 2;auto.
      apply inf_ax_inter_r.
  Qed.

  Lemma iter_0 : 0 ⁺ ≡ 0.
  Proof. rewrite ax_iter_left;transitivity (0+0);auto. Qed.

  Lemma iter_1 : 1 ⁺ ≡ 1.
  Proof.
    rewrite ax_iter_left.
    rewrite ax_plus_com.
    apply (eq_ax_impl (ax_left_ind _ _)).
    transitivity (1+1);auto.
  Qed.

  Lemma conv_0 : 0¯ ≡ 0.
  Proof.
    rewrite <- (ax_plus_0 (0¯)).
    rewrite <- (ax_conv_conv 0) at 2.
    rewrite <- ax_conv_plus.
    rewrite ax_plus_com,ax_plus_0,ax_conv_conv.
    reflexivity.
  Qed.
  
  Lemma conv_1 : 1¯ ≡ 1.
  Proof.
    rewrite <- ax_seq_1.
    rewrite <- (ax_conv_conv 1) at 1.
    rewrite <- ax_conv_seq.
    rewrite ax_seq_1,ax_conv_conv.
    reflexivity.
  Qed.
  
  (** * Sum of a list of elements *)

  (** The expression [Σ [e1;e2;...;en]] is [e1+(e2+...(en)...)]*)
  Fixpoint Σ L :=
    match L with
    | [] => 0
    | [a] => a
    | a::L => a + Σ L
    end.

  Lemma sum_fold L : Σ L ≡ fold_right 𝐄_plus 0 L.
  Proof.
    induction L as [|e L];[reflexivity|].
    simpl;rewrite <- IHL;clear IHL;destruct L;simpl;auto.
  Qed.
  
  (** This operator satisfies some simple distributivity properties. *)
  Lemma sum_app l m : Σ (l++m) ≡ Σ l + Σ m.
  Proof.
    repeat rewrite sum_fold;rewrite fold_right_app.
    generalize dependent (fold_right 𝐄_plus 0 m);clear m.
    induction l;simpl;intro e;auto.
    - transitivity (e+0);auto.
    - rewrite IHl;auto.
  Qed.
  
  Lemma seq_distr l m : Σ l ⋅ Σ m ≡ Σ (bimap (fun e f : 𝐄 => e ⋅ f) l m).
  Proof.
    repeat rewrite sum_fold;revert m;induction l;simpl;auto.
    intro m.
    repeat rewrite <-sum_fold;rewrite sum_app.
    repeat rewrite sum_fold;rewrite <-IHl.
    transitivity (a⋅Σ m+ Σ l⋅Σ m);repeat rewrite sum_fold;auto.
    apply eq_plus;auto.
    clear IHl;induction m;simpl;auto.
    rewrite <- IHm;auto.
  Qed.

  Lemma inter_distr l m : Σ l ∩ Σ m ≡ Σ  (bimap (fun e f : 𝐄 => e ∩ f) l m).
  Proof.
    repeat rewrite sum_fold;revert m;induction l;simpl;auto.
    + intros;transitivity 0;eauto.
    + intro m;repeat rewrite <-sum_fold;rewrite sum_app;
        repeat rewrite sum_fold; rewrite <-IHl.
      transitivity (a ∩ Σ m + Σ l ∩ Σ m);repeat rewrite sum_fold;auto.
      apply eq_plus;auto.
      clear IHl;induction m as [|b m];simpl;auto.
      * rewrite ax_inter_comm;apply equiv_0_inter.
      * rewrite <- IHm.
        transitivity ((b + Σ m) ∩ a);repeat rewrite sum_fold;auto.
        transitivity (b ∩ a + Σ m ∩ a);repeat rewrite sum_fold;auto.
  Qed.

  (** If [l⊆m], then [Σ l ≤ Σ m]*)
  Global Instance Σ_incl_smaller : Proper ((@incl 𝐄) ==> smaller) Σ.
  Proof.
    intros l m I;repeat rewrite sum_fold;revert m I;induction l;simpl;intros m L;[apply zero_minimal|].
    rewrite (IHl m).
    - assert (I:a ∈ m) by (now apply L;left).
      clear l L IHl.
      induction m as [|b m];simpl in *;try tauto.
      destruct I as [->|I];eauto.
      -- apply smaller_equiv.
         transitivity (a + a + Σ m);repeat rewrite sum_fold;auto.
      -- rewrite <- (IHm I) at 2.
         apply smaller_equiv.
         transitivity (a + b + Σ m);repeat rewrite sum_fold;auto.
         transitivity (b + a + Σ m);repeat rewrite sum_fold;auto.
    - now intros x I;apply L;right.
  Qed.

  Global Instance Σ_equiv : Proper ((@equivalent 𝐄) ==> equiv) Σ.
  Proof. intros L M E;apply antisymmetry;apply Σ_incl_smaller;rewrite E;reflexivity. Qed.
  

  (** If [a] appears in [m], then the following identity holds: *)
  Lemma split_list a m :
    a ∈ m ->Σ m ≡ a +Σ (rm a m).
  Proof.
    intro h;transitivity (Σ (a::rm a m));repeat rewrite sum_fold;auto;
      apply smaller_PartialOrder;split;repeat rewrite <-sum_fold.
    - apply Σ_incl_smaller.
      intros x I;destruct_eqX x a.
      -- left;auto.
      -- right; apply in_rm;tauto.
    - apply Σ_incl_smaller;intros x [->|I];auto.
      apply in_rm in I as (_&I);auto.
  Qed.

  Lemma Σ_small e L : (forall f, f ∈ L -> f ≤ e) -> Σ L ≤ e.
  Proof.
    repeat rewrite sum_fold;induction L;simpl;intros hyp.
    - apply zero_minimal.
    - apply plus_inf.
      + apply hyp;auto.
      + apply IHL.
        intros;apply hyp;auto.
  Qed.

  Lemma Σ_big e L f : f ∈ L -> e ≤ f -> e ≤ Σ L.
  Proof.
    intros I E.
    rewrite (split_list I).
    rewrite E;apply plus_left;reflexivity.
  Qed.                                  

  (** * Tests *)  
  Definition test := fold_right (fun a => 𝐄_inter (𝐄_var a ∩ 𝐄_var a ¯)) 1.

  Lemma test_sub_id A : test A ≤ 1.
  Proof.
    induction A as [|a A];simpl;[reflexivity|].
    rewrite IHA,inf_ax_inter_r;reflexivity.
  Qed.

  Corollary test_inter_1 A : test A ≡ 1 ∩ test A.
  Proof. rewrite ax_inter_comm;symmetry;apply smaller_inter,test_sub_id. Qed.
  
  Lemma test_var a A : a ∈ A -> test A ≤ 𝐄_var a ∩ 𝐄_var a ¯.
  Proof.
    intro Ia;induction A as [|b m];simpl.
    - simpl in Ia;tauto.
    - destruct Ia as [->|Ia].
      + apply inf_ax_inter_l.
      + apply IHm in Ia as ->.
        apply inf_ax_inter_r.
  Qed.
    
  Global Instance test_incl : Proper ((@incl X) ==> Basics.flip smaller) test.
  Proof.
    unfold Basics.flip;intros l m I;induction l as [|a l];simpl.
    - apply test_sub_id.
    - assert (ih : l ⊆ m) by (intros x Ix;apply I;now right).
      apply IHl in ih as <-.
      apply inter_glb;[|reflexivity].
      apply test_var, I;now left.
  Qed.

  Global Instance test_equivalent : Proper (@equivalent X ==> equiv) test.
  Proof.
    intros l m E;apply incl_PartialOrder in E as (I1&I2);apply smaller_PartialOrder;
      apply test_incl in I1;apply test_incl in I2;unfold Basics.flip in *.
    split;tauto.
  Qed.
  
  Lemma test_dup A : test A ≡ test A ⋅ test A.
  Proof.
    pose proof (test_sub_id A) as E;apply smaller_inter in E as <-.
    repeat rewrite (ax_inter_comm _ 1).
    rewrite inter_1_abs,ax_inter_idem;reflexivity.
  Qed.

  Lemma test_seq A e : test A ⋅ e ≡ e ⋅ test A.
  Proof.
    pose proof (test_sub_id A) as E;apply smaller_inter in E as <-.
    repeat rewrite (ax_inter_comm _ 1).
    rewrite ax_inter_1_comm_seq;reflexivity.
  Qed.

  Lemma test_inter_left A e f : test A ⋅ (e ∩ f) ≡ (test A ⋅ e)∩ f.
  Proof.
    pose proof (test_sub_id A) as E;apply smaller_inter in E.
    rewrite (ax_inter_comm (test A) 1) in E;rewrite <- E;clear E.
    rewrite <- ax_inter_1_inter;reflexivity.
  Qed.
  
  Lemma test_inter A e f : test A ⋅ (e ∩ f) ≡ (test A ⋅ e)∩(test A ⋅ f).
  Proof.
    rewrite test_dup at 1;rewrite <-ax_seq_assoc.
    rewrite test_inter_left,(ax_inter_comm _ f),test_inter_left;auto.
  Qed.

  Lemma test_conv A : test A ¯ ≡ test A.
  Proof.
    pose proof (test_sub_id A) as E;apply smaller_inter in E.
    rewrite (ax_inter_comm (test A) 1) in E;rewrite <- E;clear E.
    rewrite ax_conv_inter,conv_1.
    rewrite ax_inter_1_conv;reflexivity.
  Qed.

  Lemma test_iter A : test A ⁺ ≡ test A.
  Proof.
    rewrite ax_iter_left,ax_plus_com.
    apply (eq_ax_impl (ax_left_ind _ _)).
    rewrite <- test_dup;auto.
  Qed.

  Lemma test_prod_cap A B : test A ∩ test B ≡ test A ⋅ test B.
  Proof.
    pose proof (test_sub_id A) as e1.
    pose proof (test_sub_id B) as e2.
    apply smaller_inter in e1 as <-.
    apply smaller_inter in e2 as <-.
    repeat rewrite (ax_inter_comm _ 1).
    rewrite inter_1_abs.
    transitivity (1 ∩ 1 ∩ (test A∩test B));auto.
    transitivity (1 ∩ (1 ∩ (test A∩test B)));auto.
    transitivity (1 ∩ ((1 ∩ test A)∩test B));auto.
    transitivity (((1 ∩ test A)∩test B) ∩ 1);auto.
    transitivity ((1 ∩ test A)∩(test B ∩ 1));auto.
  Qed.

  Lemma test_app A B : test (A++B) ≡ test A ∩ test B.
  Proof.
    induction A;simpl.
    - rewrite ax_inter_comm.
      symmetry;apply smaller_inter,test_sub_id.
    - rewrite IHA;auto.
  Qed.

  (** * Computation of [1∩e] *)
  Fixpoint inter_1 e :=
    match e with
    | 0 => []
    | 1 => [[]]
    | 𝐄_var a => [[a]]
    | e+f => inter_1 e ++ inter_1 f
    | e⋅f | e∩f => bimap (@app X) (inter_1 e) (inter_1 f)
    | e⁺ | e ¯ => inter_1 e
    end.
  
  Lemma inter_1_spec e : 1 ∩ e ≡ Σ (map test (inter_1 e)).
  Proof.
    induction e.
    - simpl;transitivity 1;auto.
    - simpl;auto.
      rewrite ax_inter_comm;apply equiv_0_inter.
    - simpl. 
      transitivity (1 ∩ (𝐄_var x ∩ 𝐄_var x ¯));auto.
      transitivity (1 ∩ 1 ∩ (𝐄_var x ∩ 𝐄_var x ¯));auto.
      transitivity (1 ∩ (1 ∩ (𝐄_var x ∩ 𝐄_var x ¯)));auto.
      transitivity (1 ∩ ((1 ∩ 𝐄_var x) ∩ 𝐄_var x ¯));auto.
      transitivity (1 ∩ (1 ∩ 𝐄_var x) ∩ 𝐄_var x ¯);auto.
      transitivity ((1 ∩ 𝐄_var x) ∩ 1 ∩ 𝐄_var x ¯);auto.
      transitivity ((1 ∩ 𝐄_var x) ∩ (1 ∩ 𝐄_var x ¯));auto.
      transitivity ((1 ∩ 𝐄_var x) ∩ (1 ∩ 𝐄_var x));auto.
    - transitivity (1∩(e1∩e2));auto.
      transitivity (1∩1∩(e1∩e2));auto.
      transitivity (1∩(1∩(e1∩e2)));auto.
      transitivity (1∩((1∩e1)∩e2));auto.
      transitivity (1∩(1∩e1)∩e2);auto.
      transitivity ((1∩e1)∩1∩e2);auto.
      transitivity ((1∩e1)∩(1∩e2));auto.
      rewrite IHe1,IHe2.
      rewrite inter_distr;simpl.
      rewrite map_bimap.
      generalize (inter_1 e2);generalize (inter_1 e1); clear IHe1 IHe2 e1 e2.
      induction l;intro m;simpl;auto.
      repeat rewrite sum_app.
      apply eq_plus;[|apply IHl].
      rewrite map_map.
      apply smaller_PartialOrder;unfold Basics.flip;split;
        apply Σ_small;intros f If;apply in_map_iff in If as (b&<-&Ib);
          (eapply Σ_big;[apply in_map_iff;exists b;eauto|]);rewrite test_app;reflexivity.
    - transitivity (1∩1∩(e1∩e2));auto.
      transitivity (1∩(1∩(e1∩e2)));auto.
      transitivity (1∩((1∩e1)∩e2));auto.
      transitivity (1∩(1∩e1)∩e2);auto.
      transitivity ((1∩e1)∩1∩e2);auto.
      transitivity ((1∩e1)∩(1∩e2));auto.
      rewrite IHe1,IHe2.
      rewrite inter_distr;simpl.
      rewrite map_bimap.
      generalize (inter_1 e2);generalize (inter_1 e1); clear IHe1 IHe2 e1 e2.
      induction l;intro m;simpl;auto.
      repeat rewrite sum_app.
      apply eq_plus;[|apply IHl].
      rewrite map_map.
      apply smaller_PartialOrder;unfold Basics.flip;split;
        apply Σ_small;intros f If;apply in_map_iff in If as (b&<-&Ib);
          (eapply Σ_big;[apply in_map_iff;exists b;eauto|]);rewrite test_app;reflexivity.
    - rewrite ax_inter_comm,ax_plus_inter;repeat rewrite (ax_inter_comm _ 1).
      rewrite IHe1,IHe2;simpl;rewrite map_app,sum_app;reflexivity.
    - rewrite ax_inter_1_conv,IHe;reflexivity.
    - simpl;rewrite <- IHe;clear IHe.
      rewrite ax_iter_left.
      rewrite ax_inter_comm,ax_plus_inter.
      repeat rewrite (ax_inter_comm _ 1).
      rewrite ax_inter_1_seq.
      pose proof (iter_incr e) as E.
      apply smaller_inter in E as ->;auto.
  Qed.

  (** * Normalisation of expressions *)

  Definition NF := list (list X * option 𝐄).

  Definition nf_to_term p :=
    match p with
    | (A,None) => test A
    | (A,Some e') => test A ⋅ e'
    end.
  
  Definition seq_nf l1 l2 : NF :=
    bimap (fun p1 p2 =>
             match p1,p2 with
             | (A,Some e),(B,Some f) => (A++B,Some (e⋅f))
             | (A,Some e),(B,None)
             | (A,None),(B,Some e) => (A++B,Some e)
             | (A,None),(B,None) => (A++B,None)
             end)
          l1 l2.

  
  Definition inter_nf l1 l2 : NF :=
    concat (bimap (fun p1 p2 =>
                     match p1,p2 with
                     | (A,Some e),(B,Some f) => [(A++B,Some (e ∩ f))]
                     | (A,Some e),(B,None)
                     | (A,None),(B,Some e) => map (fun C => (A++B++C,None)) (inter_1 e)
                     | (A,None),(B,None) => [(A++B,None)]
                     end)
                  l1 l2).

  Definition NF_tests : NF -> list (list X) :=
    flat_map (fun p => match p with (A,None) => [A] | _ => [] end).

  Definition NF_pos : NF -> list (list X * 𝐄) :=
    flat_map (fun p => match p with (A,Some e) => [(A,e)] | _ => [] end).

  Lemma NF_split_lst N : N ≈ ((map (fun A => (A,None)) (NF_tests N))
                                ++(map (fun p => (fst p,Some (snd p))) (NF_pos N))).
  Proof.
    induction N as [|(A,[e|]) N];simpl.
    - reflexivity.
    - rewrite IHN at 1;intro x;mega_simpl;simpl;tauto.
    - rewrite IHN at 1;intro x;mega_simpl;simpl;tauto.
  Qed.

  Corollary NF_split N :
    Σ (map nf_to_term N) ≡ Σ (map test (NF_tests N)) + Σ (map (fun p => test (fst p) ⋅ snd p)
                                                              (NF_pos N)).
  Proof.
    rewrite NF_split_lst at 1.
    rewrite map_app,map_map,map_map;simpl.
    rewrite sum_app;reflexivity.
  Qed.
      
  Definition iter_tests (N : NF) :=
    filter (fun p => match p with (_,None) => true | _ => false end) N.

  Definition iter_pos (N : NF) :=
    map (fun L => (flat_map fst L,Some (Σ(map snd L)⁺)))
        (subsets (NF_pos N)).

  Lemma iter_tests_NF_tests N : iter_tests N = map (fun A => (A,None)) (NF_tests N).
  Proof. induction N as [|(A&[])];simpl;congruence||auto. Qed.
    
  Fixpoint expand e : NF :=
    match e with
    | 0 => []
    | 1 => [([],None)]
    | 𝐄_var a => [([],Some (𝐄_var a))]
    | e + f => (expand e) ++ (expand f)
    | e ⋅ f => seq_nf (expand e) (expand f)
    | e ∩ f => inter_nf (expand e) (expand f)
    | e⁺ => (* iter_nf [] (expand e) *)
      iter_tests (expand e) ++ iter_pos (expand e)
    | e ¯ => map (fun p => match snd p with None =>(fst p,None)
                                  | Some e' => (fst p,Some (e' ¯)) end)
               (expand e)
    end.

  Lemma iter_nf_aux B L: 
    Σ (map nf_to_term (map (fun p => (B ++ fst p, snd p)) L))
      ≡ test B ⋅ Σ (map nf_to_term L).
  Proof.
    repeat rewrite sum_fold;induction L as [|(A,[f|]) m];simpl;auto.
    -- rewrite test_app,test_prod_cap,ax_seq_plus.
       repeat rewrite ax_seq_assoc.
       rewrite IHm;reflexivity.
    -- rewrite test_app,test_prod_cap,ax_seq_plus.
       repeat rewrite ax_seq_assoc.
       rewrite IHm;reflexivity.
  Qed.
      
  Lemma expand_eq e : e ≡ Σ (map nf_to_term (expand e)).
  Proof.
    induction e;simpl;auto.
    - rewrite IHe1,IHe2,seq_distr at 1;clear IHe1 IHe2.
      generalize (expand e1);generalize (expand e2);intros m l.
      apply smaller_PartialOrder;unfold Basics.flip;simpl;split;apply Σ_small;intros e Ie.
      + apply in_bimap in Ie as (f&g&<-&If&Ig).
        apply in_map_iff in If as ((A&F)&<-&Il).
        apply in_map_iff in Ig as ((B&G)&<-&Im).
        destruct F as [f|],G as [g|].
        * apply Σ_big with (f := nf_to_term (A++B,Some (f⋅g))).
          -- apply in_map_iff;exists (A++B,Some (f⋅g));split;[reflexivity|].
             apply in_bimap;exists (A,Some f),(B,Some g);split;[reflexivity|tauto].
          -- simpl;rewrite test_app,test_prod_cap.
             apply smaller_equiv.
             transitivity (test A ⋅ (test B ⋅ (f ⋅ g)));auto.
             transitivity (test A ⋅ (test B ⋅ f ⋅ g));auto.
             rewrite (test_seq B f).
             transitivity (test A ⋅ (f ⋅ (test B ⋅ g)));auto.
        * apply Σ_big with (f := nf_to_term (A++B,Some f)).
          -- apply in_map_iff;exists (A++B,Some f);split;[reflexivity|].
             apply in_bimap;exists (A,Some f),(B,None);split;[reflexivity|tauto].
          -- simpl;rewrite test_app,test_prod_cap.
             apply smaller_equiv.
             transitivity (test A ⋅ (test B ⋅ f));auto.
             rewrite (test_seq B f);auto.
        * apply Σ_big with (f := nf_to_term (A++B,Some g)).
          -- apply in_map_iff;exists (A++B,Some g);split;[reflexivity|].
             apply in_bimap;exists (A,None),(B,Some g);split;[reflexivity|tauto].
          -- simpl;rewrite test_app,test_prod_cap.
             apply smaller_equiv;auto.
        * apply Σ_big with (f := nf_to_term (A++B,None)).
          -- apply in_map_iff;exists (A++B,None);split;[reflexivity|].
             apply in_bimap;exists (A,None),(B,None);split;[reflexivity|tauto].
          -- simpl;rewrite test_app,test_prod_cap;reflexivity.
      + apply in_map_iff in Ie as ((?,?)&<-&I);unfold seq_nf in I.
        apply in_bimap in I as ((A,F)&(B,G)&<-&Il&Im).
        apply Σ_big with (f := nf_to_term (A,F) ⋅ nf_to_term (B,G)).
        * apply in_bimap;exists (nf_to_term (A,F)),(nf_to_term (B,G));split;[reflexivity|].
          split;apply in_map_iff;eexists;eauto.
        * destruct F as [f|],G as [g|];simpl.
          -- simpl;rewrite test_app,test_prod_cap.
             apply smaller_equiv.
             transitivity (test A ⋅ (test B ⋅ (f ⋅ g)));auto.
             transitivity (test A ⋅ (test B ⋅ f ⋅ g));auto.
             rewrite (test_seq B f).
             transitivity (test A ⋅ (f ⋅ (test B ⋅ g)));auto.
          -- simpl;rewrite test_app,test_prod_cap.
             apply smaller_equiv.
             transitivity (test A ⋅ (test B ⋅ f));auto.
             rewrite (test_seq B f);auto.
          -- simpl;rewrite test_app,test_prod_cap.
             apply smaller_equiv;auto.
          -- simpl;rewrite test_app,test_prod_cap;reflexivity.
    - rewrite IHe1,IHe2,inter_distr at 1;clear IHe1 IHe2.
      generalize (expand e1);generalize (expand e2);intros m l.
      apply smaller_PartialOrder;unfold Basics.flip;simpl;split;apply Σ_small;intros e Ie.
      + apply in_bimap in Ie as (f&g&<-&If&Ig).
        apply in_map_iff in If as ((A&F)&<-&Il).
        apply in_map_iff in Ig as ((B&G)&<-&Im).
        destruct F as [f|],G as [g|].
        * apply Σ_big with (f := nf_to_term (A++B,Some (f∩g))).
          -- apply in_map_iff;exists (A++B,Some (f∩g));split;[reflexivity|].
             apply in_concat;exists [(A++B,Some (f∩g))];split;[simpl;tauto|].
             apply in_bimap;exists (A,Some f),(B,Some g);split;[reflexivity|tauto].
          -- simpl;rewrite test_app, test_prod_cap.
             rewrite (ax_inter_comm f g),<-ax_seq_assoc.
             rewrite test_inter_left,(ax_inter_comm _ f),test_inter_left;reflexivity.
        * simpl;rewrite <- test_inter_left.
          pose proof (test_sub_id B) as E;apply smaller_inter in E;rewrite ax_inter_comm in E.
          rewrite <- E,ax_inter_assoc,(ax_inter_comm f 1).
          rewrite inter_1_spec.
          transitivity (Σ (map (fun C => test (A ++ B ++ C)) (inter_1 f))).
          -- repeat rewrite sum_fold;clear;induction (inter_1 f);clear f;simpl.
             ++ rewrite equiv_0_inter,ax_seq_0;reflexivity.
             ++ rewrite <- IHl.
                rewrite ax_plus_inter,ax_seq_plus.
                apply plus_smaller;[|reflexivity].
                rewrite test_app,(test_prod_cap _ (B++a)).
                apply seq_smaller;[reflexivity|].
                rewrite test_app;apply smaller_equiv;auto.
          -- clear E;simpl;unfold inter_nf.
             apply Σ_small;intros g Ig;apply in_map_iff in Ig as (C&<-&IC).
             apply Σ_big with (f:= nf_to_term (A++B++C,None)).
             ++ apply in_map_iff;exists (A++B++C,None);split;[reflexivity|].
                apply in_concat;exists (map (fun C0 : list X => (A ++ B ++ C0, None)) (inter_1 f)).
                split;[apply in_map_iff;exists C;tauto|].
                apply in_bimap;exists (A,Some f),(B,None);tauto.
             ++ reflexivity.
        * simpl.
          rewrite ax_inter_comm,<- test_inter_left,ax_inter_comm.
          pose proof (test_sub_id A) as E;apply smaller_inter in E.
          rewrite <- E,<-ax_inter_assoc;clear E.
          rewrite inter_1_spec.
          transitivity (Σ (map (fun C => test (A ++ B ++ C)) (inter_1 g))).
          -- repeat rewrite sum_fold;clear;induction (inter_1 g);clear g;simpl.
             ++ rewrite ax_inter_comm,equiv_0_inter,ax_seq_0;reflexivity.
             ++ rewrite <- IHl.
                rewrite ax_inter_comm,ax_plus_inter,ax_seq_plus,
                (ax_inter_comm (fold_right _ _ _)).
                apply plus_smaller;[|reflexivity].
                rewrite ax_inter_comm at 1.
                rewrite <- test_app,<-test_prod_cap.
                rewrite ax_inter_comm,<-test_app,app_ass.
                apply smaller_equiv,test_equivalent;intro;repeat rewrite in_app_iff;tauto.
          -- simpl;unfold inter_nf.
             apply Σ_small;intros f If;apply in_map_iff in If as (C&<-&IC).
             apply Σ_big with (f:= nf_to_term (A++B++C,None)).
             ++ apply in_map_iff;exists (A++B++C,None);split;[reflexivity|].
                apply in_concat;exists (map (fun C0 : list X => (A ++ B ++ C0, None)) (inter_1 g)).
                split;[apply in_map_iff;exists C;tauto|].
                apply in_bimap;exists (A,None),(B,Some g);tauto.
             ++ reflexivity.
        * apply Σ_big with (f := nf_to_term (A++B,None)).
          -- apply in_map_iff;exists (A++B,None);split;[reflexivity|].
             apply in_concat;exists [(A++B,None)];split;[simpl;tauto|].
             apply in_bimap;exists (A,None),(B,None);split;[reflexivity|tauto].
          -- simpl;rewrite test_app,test_prod_cap;reflexivity.
      + apply in_map_iff in Ie as ((?,?)&<-&I);unfold seq_nf in I.
        unfold inter_nf in I.
        apply in_concat in I as (L&IL&I).
        apply in_bimap in I as ((A,F)&(B,G)&<-&Il&Im).
        apply Σ_big with (f := nf_to_term (A,F) ∩ nf_to_term (B,G)).
        * apply in_bimap;exists (nf_to_term (A,F)),(nf_to_term (B,G));split;[reflexivity|].
          split;apply in_map_iff;eexists;eauto.
        * destruct F as [f|],G as [g|];simpl.
          -- destruct IL as [E|E];inversion E;subst;clear E.
             rewrite <- test_inter_left,(ax_inter_comm f (_⋅_)),<-test_inter_left.
             rewrite ax_inter_comm,ax_seq_assoc.
             rewrite test_app,test_prod_cap;reflexivity.
          -- apply in_map_iff in IL as (C&E&IC);inversion E;subst;clear E.
             rewrite test_app,<-test_inter_left,test_prod_cap.
             apply seq_smaller;[reflexivity|].
             pose proof (test_sub_id B) as E;apply smaller_inter in E;
               rewrite ax_inter_comm in E.
             rewrite <- E,ax_inter_assoc,(ax_inter_comm f 1).
             rewrite test_app,ax_inter_comm;apply inter_smaller;[|reflexivity].
             rewrite inter_1_spec;apply Σ_big with (f:=test C);[|reflexivity].
             apply in_map_iff;exists C;tauto.
          -- apply in_map_iff in IL as (C&E&IC);inversion E;subst;clear E.
             pose proof (test_sub_id A) as E;apply smaller_inter in E;
               rewrite ax_inter_comm in E.
             rewrite ax_inter_comm,<-test_inter_left.
             rewrite <- E,ax_inter_assoc,(ax_inter_comm g 1).
             repeat rewrite test_app.
             rewrite ax_inter_assoc,(ax_inter_comm (test A)),<-ax_inter_assoc.
             rewrite <- test_app,test_prod_cap,test_app,ax_inter_comm.
             apply seq_smaller;[|apply inter_smaller];try reflexivity.
             rewrite inter_1_spec;apply Σ_big with (f:=test C);[|reflexivity].
             apply in_map_iff;exists C;tauto.
          -- destruct IL as [E|E];inversion E;subst;clear E.
             simpl;rewrite test_app,test_prod_cap;reflexivity.
    - rewrite IHe1,IHe2 at 1.
      rewrite map_app,sum_app;reflexivity.
    - rewrite IHe at 1;simpl;clear.
      repeat rewrite sum_fold.
      induction (expand e) as [|(A&[e'|]) l];simpl;auto.
      + apply conv_0.
      + rewrite ax_conv_plus,ax_conv_seq,test_conv,test_seq,IHl;reflexivity.
      + rewrite ax_conv_plus,test_conv,IHl;reflexivity.
    - rewrite IHe at 1;generalize (expand e);clear e IHe.
      intros N;rewrite map_app,sum_app.
      rewrite NF_split at 1.
      rewrite iter_tests_NF_tests,map_map.
      unfold iter_pos,nf_to_term.
      rewrite map_map.
      generalize (NF_tests N);generalize (NF_pos N);clear N.
      intros T E.
      repeat rewrite sum_fold;induction E;simpl;repeat rewrite <- sum_fold in *.
      + transitivity (Σ (map (fun p : list X * 𝐄 => test (fst p) ⋅ snd p) T) ⁺);
          [apply eq_iter;eauto|].
        rewrite ax_plus_com,ax_plus_0.
        cut (forall (A : list X) (e : 𝐄),
                test A ⋅ (Σ (map (fun p : list X * 𝐄 => test (fst p) ⋅ snd p) T) + e) ⁺
                     ≡ Σ
                     (map
                        (fun x : list (list X * 𝐄) => test (A ++ flat_map fst x) ⋅
                                                        (e + Σ (map snd x)) ⁺)
                        (subsets T))).
        * intros h.
          etransitivity;[|etransitivity;[apply (h [] 0)|]];simpl.
          -- rewrite ax_plus_0,ax_seq_1;reflexivity.
          -- clear;repeat rewrite sum_fold;induction (subsets T) as [|];simpl in *;
               repeat rewrite <- sum_fold in *.
             ++ reflexivity.
             ++ rewrite IHl,(ax_plus_com 0),ax_plus_0;reflexivity.
        * intros A e;repeat rewrite sum_fold;revert A e;
            induction T as [|(A,e)];intros B f;simpl in *;repeat rewrite <- sum_fold in *.
          -- rewrite ax_plus_0,ax_plus_com,app_nil_r;reflexivity.
          -- rewrite map_app,map_map,sum_app.
             rewrite (test_inter_1 A).
             rewrite <- ax_plus_ass,ax_plus_com,ax_inter_1_iter,<-ax_plus_ass.
             rewrite <- test_inter_1.
             rewrite ax_seq_plus,ax_seq_assoc.
             rewrite <-test_prod_cap,<- test_app.
             repeat rewrite sum_fold.
             repeat rewrite IHT.
             repeat rewrite <- sum_fold.
             rewrite ax_plus_com.
             apply eq_plus;auto.
             clear;repeat rewrite sum_fold;induction (subsets T) as [|];simpl in *;
               repeat rewrite <- sum_fold in *;auto.
             rewrite app_ass;apply eq_plus;auto.
             apply eq_seq;auto;clear.
             destruct (map snd a);auto.
      + repeat rewrite <- ax_plus_ass.
        rewrite <- IHE;clear IHE.
        generalize (Σ (map test E) + Σ (map (fun p : list X * 𝐄 => test (fst p) ⋅ snd p) T)).
        intros e.
        rewrite <- (ax_1_seq (test a)),ax_plus_com at 1.
        pose proof (test_sub_id a) as h.
        apply smaller_inter in h.
        rewrite ax_inter_comm in h.
        rewrite <- h.
        rewrite ax_inter_1_iter.
        cut ((e + 1)⁺ ≡ e⁺ + 1).
        * intros ->.
          rewrite ax_seq_plus,ax_1_seq.
          apply antisymmetry;repeat apply plus_inf.
          -- apply plus_right;reflexivity.
          -- apply plus_right;rewrite test_sub_id,ax_inter_idem,ax_seq_1;reflexivity.
          -- apply plus_left;reflexivity.
          -- apply plus_right;apply plus_right;reflexivity.
          -- apply plus_left;reflexivity.
        * apply antisymmetry.
          -- transitivity ((e + 1) ⁺⋅(e⁺+1)).
             ++ rewrite ax_seq_plus,ax_1_seq.
                apply plus_right;reflexivity.
             ++ apply right_ind.
                repeat rewrite ax_plus_seq||rewrite ax_seq_plus
                ||rewrite ax_seq_1||rewrite ax_1_seq.
                rewrite iter_left.
                rewrite (iter_incr e) at 2.
                repeat apply plus_inf;(apply plus_left;reflexivity)
                                      ||(apply plus_right;reflexivity).
          -- rewrite <- iter_1 at 1;apply plus_inf;apply iter_smaller;
               [apply plus_left|apply plus_right];reflexivity.
  Qed.
  
  Fixpoint one_free e :=
    match e with
    | 1 => false
    | e + f | e ∩ f | e ⋅ f => one_free e && one_free f
    | e ⁺ | e ¯ => one_free e
    | _ => true
    end.

  Lemma one_free_sum L : (forall f, f ∈ L -> one_free f = true) -> one_free (Σ L) = true.
  Proof.
    induction L;simpl;auto.
    intros h.
    destruct L.
    - apply h;auto.
    - simpl in *;rewrite IHL,h;auto.
  Qed.

  Lemma one_free_expand e : forall A f, (A,Some f) ∈ expand e -> one_free f = true.
  Proof.
    induction e;simpl.
    - intros ? ? [E|E];inversion E.
    - tauto.
    - intros ? ? [E|E];inversion E;subst;clear E;reflexivity.
    - unfold seq_nf;intros x y I.
      apply in_bimap in I as ((A&[f|])&(B&[g|])&E&I1&I2);symmetry in E;inversion E;subst;clear E.
      + simpl;apply andb_true_iff;split;[eapply IHe1|eapply IHe2];eassumption.
      + eapply IHe1;eassumption.
      + eapply IHe2;eassumption.
    - unfold inter_nf;intros x y I.
      apply in_concat in I as (L&IL&I).
      apply in_bimap in I as ((A&[f|])&(B&[g|])&<-&I1&I2).
      + destruct IL as [E|E];inversion E.
        simpl;apply andb_true_iff;split;[eapply IHe1|eapply IHe2];eassumption.
      + apply in_map_iff in IL as (C&E&IC);inversion E.
      + apply in_map_iff in IL as (C&E&IC);inversion E.
      + destruct IL as [E|E];inversion E.
    - intros x y I.
      apply in_app_iff in I as [I|I].
      + eapply IHe1;eassumption.
      + eapply IHe2;eassumption.
    - intros A f I.
      apply in_map_iff in I as ((B&[g|])&E&I);inversion E;subst;clear E.
      simpl;eapply IHe;eassumption.
    - intros A f If.
      mega_simpl.
      + unfold iter_tests in If;apply filter_In in If as (_&F);discriminate.
      + unfold iter_pos in If.
        apply in_map_iff in If as (L&E&IL).
        inversion E;subst;clear E.
        simpl;apply one_free_sum.
        intros f If.
        apply in_map_iff in If as ((A&g)&<-&Ig);simpl.
        apply subsets_In in IL.
        apply IL in Ig.
        unfold NF_pos in Ig;apply in_flat_map in Ig as ((B&[G|])&IG&Ig);
          simpl in Ig;[destruct Ig as [Ig|Ig]|];inversion Ig;subst.
        eapply IHe,IG.
  Qed.
  
  Close Scope expr_scope.
End s.
(* begin hide *)
Arguments 𝐄_one {X}.
Arguments 𝐄_zero {X}.
Arguments inter_1 {X}.
Arguments expand {X}.
Arguments eqb {X} {dec_X} e%expr f%expr.
Hint Constructors 𝐄_eq ax ax_impl.
Hint Rewrite @𝐄_size_one @𝐄_size_zero @𝐄_size_var @𝐄_size_seq
     @𝐄_size_inter @𝐄_size_plus @𝐄_size_conv @𝐄_size_iter
  : simpl_typeclasses.

(* end hide *)

Infix " ⋅ " := 𝐄_seq (at level 40) : expr_scope.
Infix " + " := 𝐄_plus (left associativity, at level 50) : expr_scope.
Infix " ∩ " := 𝐄_inter (at level 45) : expr_scope.
Notation "x ¯" := (𝐄_conv x) (at level 25) : expr_scope.
Notation "x ⁺" := (𝐄_iter x) (at level 25) : expr_scope.
Notation " 1 " := 𝐄_one : expr_scope.
Notation " 0 " := 𝐄_zero : expr_scope.




