Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language lklc.

Section bounded.
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Notation " e ⋆ " := (1 + e⁺) (at level 25).

  Lemma star_dup (e : 𝐄 X) : e⋆⋅e⋆ ≡ e⋆.
  Proof.
    rewrite ax_seq_plus.
    repeat rewrite ax_plus_seq||rewrite ax_seq_1 ||rewrite ax_1_seq.
    apply antisymmetry.
    - repeat apply plus_inf.
      + apply plus_left;reflexivity.
      + apply plus_right;reflexivity.
      + apply plus_right;reflexivity.
      + rewrite iter_seq;apply plus_right;reflexivity.
    - apply plus_left;reflexivity.
  Qed.

  Lemma star_conv (e : 𝐄 X) : e ⋆¯≡ e ¯⋆.
  Proof. rewrite ax_conv_plus,conv_1,ax_conv_iter;reflexivity. Qed.

  Lemma iter_plus_1 (e : 𝐄 X) : (1+e)⁺≡ 1+e⁺.
  Proof.
    apply antisymmetry.
    - transitivity (e⋆⋅(1+e)⁺).
      + rewrite <- ax_seq_1 at 1.
        apply seq_smaller;[apply plus_left|];reflexivity.
      + apply left_ind.
        repeat rewrite ax_seq_plus||rewrite ax_plus_seq||rewrite ax_seq_1 ||rewrite ax_1_seq.
        rewrite <- ax_iter_right.
        apply plus_inf;[|apply plus_right];reflexivity.
    - apply plus_inf.
      + rewrite (iter_incr 1) at 1.
        apply iter_smaller,plus_left;reflexivity.
      + apply iter_smaller,plus_right;reflexivity.
  Qed.

  Lemma star_iter (e : 𝐄 X) : e ⋆⁺≡ e⋆.
  Proof. rewrite iter_plus_1,iter_idempotent;reflexivity. Qed.
    
  Definition Full (A : list X) := (Σ (flat_map (fun a => [𝐄_var a;𝐄_var a ¯]) A))⋆.

  Lemma Full_conv A : Full A ≡ Full A ¯.
  Proof.
    unfold Full;rewrite star_conv.
    apply eq_plus,eq_iter;[reflexivity|].
    induction A;[symmetry;apply conv_0|].
    rewrite sum_fold in *;simpl.
    repeat rewrite ax_conv_plus.
    rewrite <- IHA,<- sum_fold;clear IHA.
    repeat rewrite ax_plus_ass.
    rewrite ax_conv_conv.
    apply eq_plus;[apply eq_ax,ax_plus_com|reflexivity].
  Qed.
    
  Lemma Full_spec A e : Vars e ⊆ A -> e ≤ Full A.
  Proof.
    induction e;simpl.
    - intros _;apply plus_left;reflexivity.
    - intros _;apply zero_minimal.
    - simpl;intros I;apply plus_right.
      rewrite <- iter_incr;eapply Σ_big;eauto.
      + apply in_flat_map;exists x;split;auto.
        * apply I;now left.
        * now left.
      + reflexivity.
    - intros I;apply incl_app_split in I as (I1&I2).
      apply IHe1 in I1 as ->;apply IHe2 in I2 as ->.
      apply smaller_equiv,star_dup.
    - intros I;apply incl_app_split in I as (I1&I2).
      apply IHe1 in I1 as ->;apply IHe2 in I2 as ->.
      rewrite ax_inter_idem;reflexivity.
    - intros I;apply incl_app_split in I as (I1&I2).
      apply IHe1 in I1 as ->;apply IHe2 in I2 as ->.
      rewrite plus_idem;reflexivity.
    - intros I;apply IHe in I as ->.
      rewrite <- Full_conv;reflexivity.
    - intros I;apply IHe in I as ->.
      unfold Full;rewrite star_iter;reflexivity.
  Qed.
    
  
End bounded.
Notation " e ⋆ " := (1 + e⁺) (at level 25) : expr_scope.


Delimit Scope top_scope with top.
Open Scope top_scope.

Section top.
  (** * Main definitions *)
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Inductive 𝐄t : Set :=
  | 𝐄t_one : 𝐄t
  | 𝐄t_zero : 𝐄t
  | 𝐄t_top : 𝐄t
  | 𝐄t_var : X -> 𝐄t
  | 𝐄t_seq : 𝐄t -> 𝐄t -> 𝐄t
  | 𝐄t_inter : 𝐄t -> 𝐄t -> 𝐄t
  | 𝐄t_plus : 𝐄t -> 𝐄t -> 𝐄t
  | 𝐄t_conv : 𝐄t -> 𝐄t
  | 𝐄t_iter : 𝐄t -> 𝐄t.

  Notation "x ⋅ y" := (𝐄t_seq x y) (at level 40) : top_scope.
  Notation "x + y" := (𝐄t_plus x y) (left associativity, at level 50) : top_scope.
  Notation "x ∩ y" := (𝐄t_inter x y) (at level 45) : top_scope.
  Notation "x ¯" := (𝐄t_conv x) (at level 25) : top_scope.
  Notation "x ⁺" := (𝐄t_iter x) (at level 25) : top_scope.
  Notation " ⊤ " := 𝐄t_top : top_scope.
  Notation " 1 " := 𝐄t_one : top_scope.
  Notation " 0 " := 𝐄t_zero : top_scope.

  (** The size of an expression is the number of nodes in its syntax
  tree. *)
  Global Instance size_𝐄t : Size 𝐄t :=
    fix 𝐄t_size (e: 𝐄t) : nat :=
      match e with
      | ⊤ | 0 | 1 | 𝐄t_var _ => 1%nat
      | e + f | e ∩ f | e ⋅ f => S (𝐄t_size e + 𝐄t_size f)
      | e ¯ | e ⁺ => S (𝐄t_size e)
      end.
  (* begin hide *)
  Lemma 𝐄t_size_one : |1| = 1%nat. trivial. Qed.
  Lemma 𝐄t_size_zero : |0| = 1%nat. trivial. Qed.
  Lemma 𝐄t_size_var a : |𝐄t_var a| = 1%nat. trivial. Qed.
  Lemma 𝐄t_size_seq e f : |e⋅f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄t_size_inter e f : |e∩f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄t_size_plus e f : |e+f| = S(|e|+|f|). trivial. Qed.
  Lemma 𝐄t_size_conv e : |e ¯| = S(|e|). trivial. Qed.
  Lemma 𝐄t_size_iter e : |e⁺| = S(|e|). trivial. Qed.
  Hint Rewrite 𝐄t_size_one 𝐄t_size_zero 𝐄t_size_var 𝐄t_size_seq
       𝐄t_size_inter 𝐄t_size_plus 𝐄t_size_conv 𝐄t_size_iter
    : simpl_typeclasses.
  Fixpoint eqb e f :=
    match (e,f) with
    | (⊤,⊤) | (1,1) | (0,0) => true
    | (𝐄t_var a,𝐄t_var b) => eqX a b
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
  Global Instance 𝐄t_decidable_set : decidable_set 𝐄t.
  Proof. exact (Build_decidable_set eqb_reflect). Qed.

  (** The following are the axioms of the algebra of languages over
  this signature.*)
  Inductive ax : 𝐄t -> 𝐄t -> Prop :=
  | ax_top e : ax (e∩⊤) e
  | ax_seq_assoc e f g : ax (e⋅(f ⋅ g)) ((e⋅f)⋅g)
  | ax_seq_1 e : ax (1⋅e) e
  | ax_1_seq e : ax (e⋅1) e
  | ax_plus_com e f : ax (e+f) (f+e)
  | ax_plus_ass e f g : ax (e+(f+g)) ((e+f)+g)
  | ax_plus_0 e : ax (e+0) e
  | ax_seq_0 e : ax (e⋅0) 0
  | ax_0_seq e : ax (0⋅e) 0
  | ax_plus_seq e f g: ax ((e + f)⋅g) (e⋅g + f⋅g)
  | ax_seq_plus e f g: ax (e⋅(f + g)) (e⋅f + e⋅g)
  | ax_inter_assoc e f g : ax (e∩(f ∩ g)) ((e∩f)∩g)
  | ax_inter_comm e f : ax (e∩f) (f∩e)
  | ax_inter_idem e : ax (e ∩ e) e
  | ax_plus_inter e f g: ax ((e + f)∩g) (e∩g + f∩g)
  | ax_inter_plus e f : ax ((e∩f)+e) e
  | ax_conv_conv e : ax (e ¯¯) e
  | ax_conv_plus e f: ax ((e + f)¯) (e ¯ + f ¯)
  | ax_conv_seq e f: ax ((e ⋅ f)¯) (f ¯ ⋅ e ¯)
  | ax_conv_inter e f: ax ((e∩f)¯) (e ¯ ∩ f ¯)
  | ax_conv_iter e : ax (e⁺¯) (e ¯⁺)
  | ax_iter_left e : ax (e⁺) (e + e⋅e⁺)
  | ax_iter_right e : ax (e⁺) (e + e⁺ ⋅e)
  | ax_inter_1_seq e f : ax (1 ∩ (e⋅f)) (1 ∩ (e ∩ f))
  | ax_inter_1_conv e : ax (1 ∩ (e ¯)) (1 ∩ e)
  | ax_inter_1_comm_seq e f : ax ((1 ∩ e)⋅f) (f⋅(1 ∩ e))
  | ax_inter_1_inter e f g : ax (((1 ∩ e)⋅f) ∩ g) ((1 ∩ e)⋅(f ∩ g))
  | ax_inter_1_iter e f g : ax ((g + (1 ∩ e) ⋅ f)⁺) (g⁺ + (1 ∩ e) ⋅ (g + f)⁺).

  Inductive ax_impl : 𝐄t -> 𝐄t -> 𝐄t -> 𝐄t -> Prop:=
  | ax_right_ind e f : ax_impl (e⋅f + f) f (e⁺⋅f + f) f
  | ax_left_ind e f : ax_impl (f ⋅ e + f) f (f ⋅e⁺ + f) f.

  Inductive 𝐄t_eq : Equiv 𝐄t :=
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
  Global Instance 𝐄t_Equiv : Equiv 𝐄t := 𝐄t_eq.

  Global Instance 𝐄t_Smaller : Smaller 𝐄t := (fun e f => e + f ≡ f).

  Hint Constructors 𝐄t_eq ax ax_impl.

  Global Instance ax_equiv : subrelation ax equiv. 
  Proof. intros e f E;apply eq_ax,E. Qed.

  (** * Some elementary properties of this algebra *)

  (** It is immediate to check that the equivalence we defined is
  indeed an equivalence relation, that the order relation is a
  preorder, and that every operator is monotone for both relations. *)
  Global Instance equiv_Equivalence : Equivalence equiv.
  Proof. split;intro;eauto. Qed.

  Global Instance inter_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄t_inter.
  Proof. now intros e f hef g h hgh;apply eq_inter. Qed.

  Global Instance plus_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄t_plus.
  Proof. now intros e f hef g h hgh;apply eq_plus. Qed.

  Global Instance seq_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄t_seq.
  Proof. now intros e f hef g h hgh;apply eq_seq. Qed.
  
  Global Instance conv_equiv :
    Proper (equiv ==> equiv) 𝐄t_conv.
  Proof. now intros e f hef;apply eq_conv. Qed.
  
  Global Instance iter_equiv :
    Proper (equiv ==> equiv) 𝐄t_iter.
  Proof. now intros e f hef;apply eq_iter. Qed.

  
  Lemma plus_idem e : e+e ≡ e.
  Proof.
    rewrite <- (ax_inter_idem e) at 1.
    rewrite ax_inter_plus;reflexivity.
  Qed.
  Hint Resolve plus_idem.

  Global Instance smaller_PreOrder : PreOrder smaller.
  Proof.
    split;intro;unfold smaller,𝐄t_Smaller;intros.
    - auto.
    - transitivity (y + z);[|auto].
      transitivity (x + y + z);[|auto].
      transitivity (x + (y + z));[|auto].
      auto.
  Qed.

  Global Instance smaller_PartialOrder : PartialOrder equiv smaller.
  Proof.
    intros e f;split;unfold smaller,𝐄t_Smaller;unfold Basics.flip.
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
    Proper (smaller ==> smaller ==> smaller) 𝐄t_inter.
  Proof.
    intros e f hef g h hgh;unfold smaller,𝐄t_Smaller in *.
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
    Proper (smaller ==> smaller ==> smaller) 𝐄t_plus.
  Proof.
    intros e f hef g h hgh;unfold smaller,𝐄t_Smaller in *.
    transitivity (e + g + (h + f));[auto|].
    transitivity (e + (g + (h + f)));[auto|].
    transitivity (e + (g + h + f));[auto|].
    transitivity (e + (h + f));[auto|].
    transitivity (e + (f + h));[auto|].
    transitivity (e + f + h);auto.
  Qed.

  Global Instance seq_smaller :
    Proper (smaller ==> smaller ==> smaller) 𝐄t_seq.
  Proof.
    intros e f hef g h hgh;unfold smaller,𝐄t_Smaller in *.
    rewrite <- hef,<-hgh.
    rewrite (eq_ax (ax_seq_plus _ _ _)).
    repeat rewrite (eq_ax (ax_plus_seq _ _ _)).
    repeat rewrite (eq_ax (ax_plus_ass _ _ _)).
    auto.
  Qed.

  Global Instance conv_smaller :
    Proper (smaller ==> smaller) 𝐄t_conv.
  Proof.
    intros e f hef;unfold smaller,𝐄t_Smaller in *.
    rewrite <- (eq_ax (ax_conv_plus _ _)),hef;reflexivity.
  Qed.

  Lemma iter_left e : e ⋅ e⁺ ≤ e ⁺.
  Proof.
    unfold smaller,𝐄t_Smaller.
    rewrite (eq_ax(ax_iter_left _)) at 2 3.
    transitivity (e ⋅ e ⁺ + e + e ⋅ e ⁺);[auto|].
    transitivity (e + e ⋅ e ⁺ + e ⋅ e ⁺);[auto|].
    transitivity (e + (e ⋅ e ⁺ + e ⋅ e ⁺));auto.
  Qed.
  Lemma iter_incr e : e ≤ e ⁺.
  Proof.
    unfold smaller,𝐄t_Smaller.
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
    intros h1 h2;unfold smaller,𝐄t_Smaller in *. 
    rewrite <- h1,<-h2 at 2;auto.
  Qed.
  Lemma plus_left e f g : e ≤ f -> e ≤ f + g.
  Proof.
    intros h1;unfold smaller,𝐄t_Smaller in *.
    transitivity (e+f+g);auto.
  Qed.
  Lemma plus_right e f g : e ≤ g -> e ≤ f + g.
  Proof.
    intros h1;unfold smaller,𝐄t_Smaller in *.
    transitivity (f+g+e);auto.
    transitivity (f+(g+e));auto.
    transitivity (f+(e+g));auto.
  Qed.
  
  Global Instance iter_smaller :
    Proper (smaller ==> smaller) 𝐄t_iter.
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
    unfold smaller,𝐄t_Smaller.
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

  Lemma top_max e : e ≤ ⊤.
  Proof. apply smaller_inter;auto. Qed.

  Lemma top_seq : ⊤ ⋅ ⊤ ≡ ⊤.
  Proof.
    apply antisymmetry;[apply top_max|].
    rewrite <- ax_seq_1 at 1.
    apply seq_smaller;apply top_max.
  Qed.

  Lemma top_conv : ⊤ ¯ ≡ ⊤.
  Proof.
    apply antisymmetry;[apply top_max|].
    rewrite <- ax_conv_conv at 1.
    apply conv_smaller,top_max.
  Qed.

  Lemma top_iter : ⊤ ⁺ ≡ ⊤.
  Proof. apply antisymmetry;[apply top_max|apply iter_incr]. Qed.

  Fixpoint Vars e :=
    match e with
    | ⊤ | 0 | 1 => []
    | 𝐄t_var a => [a]
    | e + f | e ∩ f | e ⋅ f => Vars e ++ Vars f
    | e ⁺ | e ¯ => Vars e
    end.
  
End top.
(* begin hide *)
Arguments 𝐄t_one {X}.
Arguments 𝐄t_top {X}.
Arguments 𝐄t_zero {X}.
Arguments eqb {X} {dec_X} e%top f%top.
Hint Constructors 𝐄t_eq ax ax_impl.
Hint Rewrite @𝐄t_size_one @𝐄t_size_zero @𝐄t_size_var @𝐄t_size_seq
     @𝐄t_size_inter @𝐄t_size_plus @𝐄t_size_conv @𝐄t_size_iter
  : simpl_typeclasses.

(* end hide *)

Infix " ⋅ " := 𝐄t_seq (at level 40) : top_scope.
Infix " + " := 𝐄t_plus (left associativity, at level 50) : top_scope.
Infix " ∩ " := 𝐄t_inter (at level 45) : top_scope.
Notation "x ¯" := (𝐄t_conv x) (at level 25) : top_scope.
Notation "x ⁺" := (𝐄t_iter x) (at level 25) : top_scope.
Notation " 1 " := 𝐄t_one : top_scope.
Notation " ⊤ " := 𝐄t_top : top_scope.
Notation " 0 " := 𝐄t_zero : top_scope.

Section s.
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Context {A : list X}.
  
  Definition elts A := { x : X | inb x A = true}.

  Lemma elts_eq (a b : elts A) : a = b <-> π{a} = π{b}.
  Proof.
    split;[intros ->;reflexivity|].
    intros E.
    destruct a as (a&pA),b as (b&pB);simpl in *;subst.
    f_equal.
    apply UIP.
  Qed.

  Lemma inject_elts (x : X) :
    { a : option (elts A) | (x ∈ A /\ exists b, a = Some b /\ π{b} = x) \/ (~ x ∈ A /\ a = None)}.
  Proof.
    case_eq (inb x A);intro p.
    - exists (Some (exist _ x p));left;split.
      + apply inb_spec,p.
      + exists (exist _ x p);simpl;auto.
    - exists None; rewrite inb_false in p.
      right;split;auto.
  Qed.
    
  Lemma finite_elts : { B | forall a : elts A, a ∈ B}.
  Proof.
    exists (flat_map (fun a => match π{inject_elts a} with Some b => [b] | None => [] end) A).
    intros (a&p).
    pose proof p as I;apply inb_spec in I.
    apply in_flat_map.
    exists a;split;[assumption|].
    destruct (inject_elts a) as (b&[(I'&x&->&E')|(I'&->)]);simpl.
    + left;apply elts_eq;rewrite E';reflexivity.
    + tauto.
  Qed.

  Definition 𝚺 := (None::(map Some π{finite_elts})).
  
  Lemma Vars_incl (e : 𝐄 (option (elts A))) : lklc.Vars e ⊆ 𝚺.
  Proof.
    unfold 𝚺.
    destruct finite_elts as (B&hB);simpl.
    intros [a|] _;[|now left].
    right;apply in_map_iff;exists a;split;[reflexivity|apply hB].
  Qed.
  
  Fixpoint from_elts (e : 𝐄 (option (elts A))) : 𝐄t X :=
    match e with
    | 0%expr => 0
    | 1%expr => 1
    | 𝐄_var None => ⊤
    | 𝐄_var (Some x)%expr => 𝐄t_var (π{x})
    | (e+f)%expr => from_elts e + from_elts f
    | (e⋅f)%expr => from_elts e ⋅ from_elts f
    | (e∩f)%expr => from_elts e ∩ from_elts f
    | e ⁺%expr => from_elts e ⁺
    | e ¯%expr => from_elts e ¯
    end.

  Fixpoint to_elts (e : 𝐄t X) : 𝐄 (option (elts A)) :=
    match e with
    | 0 => 0%expr
    | 1 => 1%expr
    | ⊤ => Full 𝚺
    | 𝐄t_var x => match π{inject_elts x} with
                | Some y => 𝐄_var (Some y)
                | None => 0%expr
                end       
    | e+f => (to_elts e + to_elts f)%expr
    | e⋅f => (to_elts e ⋅ to_elts f)%expr
    | e∩f => (to_elts e ∩ to_elts f)%expr
    | e ⁺ => to_elts e ⁺%expr
    | e ¯ => to_elts e ¯%expr
    end.
          
  Lemma from_to_elts_spec e :
    Vars e ⊆ A -> from_elts (to_elts e) ≡ e.
  Proof.
    induction e;simpl.
    - intros _;reflexivity.
    - intros _;reflexivity.
    - intros _;apply antisymmetry;[apply top_max|].
      apply plus_right.
      rewrite iter_incr at 1.
      apply iter_smaller,plus_left;reflexivity.
    - intros I.
      destruct (inject_elts x) as (a&[(I'&b&->&E')|(I'&->)]);simpl.
      + rewrite E';reflexivity.
      + exfalso;apply I',I;now left.
    - intros I;apply incl_app_split in I as (I1&I2).
      apply IHe1 in I1 as ->;apply IHe2 in I2 as ->;reflexivity.
    - intros I;apply incl_app_split in I as (I1&I2).
      apply IHe1 in I1 as ->;apply IHe2 in I2 as ->;reflexivity.
    - intros I;apply incl_app_split in I as (I1&I2).
      apply IHe1 in I1 as ->;apply IHe2 in I2 as ->;reflexivity.
    - intros I;apply IHe in I as ->;reflexivity.
    - intros I;apply IHe in I as ->;reflexivity.
  Qed.

  Lemma to_elts_equiv e f : e ≡ f -> to_elts e ≡ to_elts f.
  Proof.
    intros E;induction E;simpl;auto.
    - eauto.
    - destruct H;simpl;auto.
      apply antisymmetry;[apply lklc.inf_ax_inter_l|].
      apply lklc.inter_glb;[reflexivity|].
      apply Full_spec.
      + set (T := fun a b : option (elts A) =>
                    match a,b with
                    | None,None => true
                    | Some a,Some b => eqX (π{a})(π{b})
                    | _,_ => false
                    end).
        apply (@Build_decidable_set _ T).
        intros [x|] [y|];simpl;try (apply ReflectF;discriminate).
        * apply iff_reflect;rewrite eqX_correct,<-elts_eq.
          split;[intro E;inversion E|intros ->];reflexivity.
        * apply ReflectT;reflexivity.
      + apply Vars_incl.
    - destruct H;simpl in *;eauto.
  Qed.
  
  Lemma from_elts_equiv e f : e ≡ f -> from_elts e ≡ from_elts f.
  Proof.
    intros E;induction E;simpl;auto.
    - eauto.
    - destruct H;simpl;auto.
    - destruct H;simpl in *;eauto.
  Qed.

  Proposition to_elts_injective e f :
    Vars e ⊆ A -> Vars f ⊆ A -> e ≡ f <-> to_elts e ≡ to_elts f.
  Proof.
    split;[apply to_elts_equiv|].
    intro E;apply from_elts_equiv in E.
    repeat rewrite from_to_elts_spec in E by assumption.
    assumption.
  Qed.
End s.
Arguments to_elts : clear implicits.
Arguments to_elts {X} {dec_X} A e.

Section reduction.
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Theorem reduction_top :
    forall e f : 𝐄t X, e ≡ f <-> to_elts (Vars e ++ Vars f) e ≡ to_elts (Vars e ++ Vars f) f.
  Proof. intros e f;apply to_elts_injective;intro;mega_simpl. Qed.
End reduction.




