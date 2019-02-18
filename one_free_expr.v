(** This module defines the language algebra without the constant 1, and its finite complete axiomatization.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language.

Delimit Scope one_scope with one.
Open Scope one_scope.

Section s.
  (** * Main definitions *)
  Variable X : Set.
  Variable dec_X : decidable_set X.

  (** [𝐄' X] is the type of expressions with variables ranging over the
  type [X]. They are built out of the constant [0], the
  concatenation (also called sequential product) [⋅], the intersection
  [∩], the union [+], the mirror image, denoted by the postfix
  operator [̅], and the non-zero iteration, denoted by [⁺]. *)
  Inductive 𝐄' : Set :=
  | 𝐄'_zero : 𝐄'
  | 𝐄'_var : X -> 𝐄'
  | 𝐄'_seq : 𝐄' -> 𝐄' -> 𝐄'
  | 𝐄'_inter : 𝐄' -> 𝐄' -> 𝐄'
  | 𝐄'_plus : 𝐄' -> 𝐄' -> 𝐄'
  | 𝐄'_conv : 𝐄' -> 𝐄'
  | 𝐄'_iter : 𝐄' -> 𝐄'.

  Notation "x ⋅ y" := (𝐄'_seq x y) (at level 40) : one_scope.
  Notation "x + y" := (𝐄'_plus x y) (left associativity, at level 50) : one_scope.
  Notation "x ∩ y" := (𝐄'_inter x y) (at level 45) : one_scope.
  Notation "x ¯" := (𝐄'_conv x) (at level 25) : one_scope.
  Notation "x ⁺" := (𝐄'_iter x) (at level 25) : one_scope.
  Notation " 0 " := 𝐄'_zero : one_scope.

  (** The following are the axioms of the algebra of languages over
  this signature.*)
  Inductive ax : 𝐄' -> 𝐄' -> Prop :=
  (** [⟨𝐄',⋅,1⟩] is a monoid. *)
  | ax_seq_assoc e f g : ax (e⋅(f ⋅ g)) ((e⋅f)⋅g)
  (** [⟨𝐄',+,0⟩] is a commutative idempotent monoid. *)
  | ax_plus_com e f : ax (e+f) (f+e)
  | ax_plus_idem e : ax (e+e) e
  | ax_plus_ass e f g : ax (e+(f+g)) ((e+f)+g)
  | ax_plus_0 e : ax (e+0) e
  (** [⟨𝐄',⋅,+,1,0⟩] is an idempotent semiring. *)
  | ax_seq_0 e : ax (e⋅0) 0
  | ax_0_seq e : ax (0⋅e) 0
  | ax_plus_seq e f g: ax ((e + f)⋅g) (e⋅g + f⋅g)
  | ax_seq_plus e f g: ax (e⋅(f + g)) (e⋅f + e⋅g)
  (** [⟨𝐄',∩⟩] is a commutative and idempotent semigroup. *)
  | ax_inter_assoc e f g : ax (e∩(f ∩ g)) ((e∩f)∩g)
  | ax_inter_comm e f : ax (e∩f) (f∩e)
  | ax_inter_idem e : ax (e ∩ e) e
  (** [⟨𝐄',+,∩⟩] forms a distributive lattice, and [0] is absorbing for
  [∩]. *)
  | ax_plus_inter e f g: ax ((e + f)∩g) (e∩g + f∩g)
  | ax_inter_plus e f : ax ((e∩f)+e) e
  | ax_inter_0 e : ax (e∩0) 0
  (** [¯] is an involution that flips concatenations and commutes with
  every other operation. *)
  | ax_conv_conv e : ax (e ¯¯) e
  | ax_conv_0 : ax (0¯) 0
  | ax_conv_plus e f: ax ((e + f)¯) (e ¯ + f ¯)
  | ax_conv_seq e f: ax ((e ⋅ f)¯) (f ¯ ⋅ e ¯)
  | ax_conv_inter e f: ax ((e∩f)¯) (e ¯ ∩ f ¯)
  | ax_conv_iter e : ax (e⁺¯) (e ¯⁺)
  (** The axioms for [⁺] are as follow: *)
  | ax_iter_left e : ax (e⁺) (e + e⋅e⁺)
  | ax_iter_right e : ax (e⁺) (e + e⁺ ⋅e).

  (** Additionally, we need these two implications: *)
  Inductive ax_impl : 𝐄' -> 𝐄' -> 𝐄' -> 𝐄' -> Prop:=
  | ax_right_ind e f : ax_impl (e⋅f + f) f (e⁺⋅f + f) f
  | ax_left_ind e f : ax_impl (f ⋅ e + f) f (f ⋅e⁺ + f) f.

  (** We use these axioms to generate an axiomatic equivalence
  relation and an axiomatic order relations. *)
  Inductive 𝐄'_eq : Equiv 𝐄' :=
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
  Global Instance 𝐄'_Equiv : Equiv 𝐄' := 𝐄'_eq.

  Global Instance 𝐄'_Smaller : Smaller 𝐄' := (fun e f => e + f ≡ f).

  Hint Constructors 𝐄'_eq ax ax_impl.

  Global Instance ax_equiv : subrelation ax equiv. 
  Proof. intros e f E;apply eq_ax,E. Qed.

  (** * Some elementary properties of this algebra *)

  (** It is immediate to check that the equivalence we defined is
  indeed an equivalence relation, that the order relation is a
  preorder, and that every operator is monotone for both relations. *)
  Global Instance equiv_Equivalence : Equivalence equiv.
  Proof. split;intro;eauto. Qed.

  Global Instance inter_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄'_inter.
  Proof. now intros e f hef g h hgh;apply eq_inter. Qed.

  Global Instance plus_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄'_plus.
  Proof. now intros e f hef g h hgh;apply eq_plus. Qed.

  Global Instance seq_equiv :
    Proper (equiv ==> equiv ==> equiv) 𝐄'_seq.
  Proof. now intros e f hef g h hgh;apply eq_seq. Qed.
  
  Global Instance conv_equiv :
    Proper (equiv ==> equiv) 𝐄'_conv.
  Proof. now intros e f hef;apply eq_conv. Qed.
  
  Global Instance iter_equiv :
    Proper (equiv ==> equiv) 𝐄'_iter.
  Proof. now intros e f hef;apply eq_iter. Qed.

  Global Instance smaller_PreOrder : PreOrder smaller.
  Proof.
    split;intro;unfold smaller,𝐄'_Smaller;intros.
    - auto.
    - transitivity (y + z);[|auto].
      transitivity (x + y + z);[|auto].
      transitivity (x + (y + z));[|auto].
      auto.
  Qed.

  Global Instance smaller_PartialOrder : PartialOrder equiv smaller.
  Proof.
    intros e f;split;unfold smaller,𝐄'_Smaller;unfold Basics.flip.
    - intros E;split.
      + rewrite E;auto.
      + rewrite E;auto.
    - intros (E1&E2).
      rewrite <- E1.
      rewrite <- E2 at 1;auto.
  Qed.

  Global Instance smaller_equiv : subrelation equiv smaller.
  Proof. intros e f E;apply smaller_PartialOrder in E as (E&_);apply E. Qed.
End s.
(* begin hide *)
Arguments 𝐄'_zero {X}.
Hint Constructors 𝐄'_eq ax ax_impl.
(* end hide *)
Infix " ⋅ " := 𝐄'_seq (at level 40) : one_scope.
Infix " + " := 𝐄'_plus (left associativity, at level 50) : one_scope.
Infix " ∩ " := 𝐄'_inter (at level 45) : one_scope.
Notation "x ¯" := (𝐄'_conv x) (at level 25) : one_scope.
Notation "x ⁺" := (𝐄'_iter x) (at level 25) : one_scope.
Notation " 0 " := 𝐄'_zero : one_scope.


  
Section language.
  (** * Language interpretation *)
  Context { X : Set }.

  (** We interpret expressions as languages in the obvious way: *)
  Global Instance to_lang_𝐄' {Σ}: semantics 𝐄' language X Σ :=
    fix to_lang_𝐄' σ e:=
      match e with
      | 0 => 0%lang
      | 𝐄'_var a => (σ a)
      | e + f => ((to_lang_𝐄' σ e) + (to_lang_𝐄' σ f))%lang
      | e ⋅ f => ((to_lang_𝐄' σ e) ⋅ (to_lang_𝐄' σ f))%lang
      | e ∩ f => ((to_lang_𝐄' σ e) ∩ (to_lang_𝐄' σ f))%lang
      | e ¯ => (to_lang_𝐄' σ e)¯%lang
      | e⁺ => (to_lang_𝐄' σ e)⁺%lang
      end.

  (* begin hide *)
  Global Instance semSmaller_𝐄' : SemSmaller (𝐄' X) :=
    (@semantic_containment _ _ _ _ _).
  Global Instance semEquiv_𝐄' : SemEquiv (𝐄' X) :=
    (@semantic_equality _ _ _ _ _).
  Hint Unfold semSmaller_𝐄' semEquiv_𝐄' : semantics. 

  Section rsimpl.
    Context { Σ : Set }{σ : 𝕬[X→Σ] }.
    Lemma 𝐄'_union e f : (⟦ e+f ⟧σ) = ((⟦e⟧σ) + ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄'_prod e f :  (⟦ e⋅f ⟧σ) = ((⟦e⟧σ) ⋅ ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄'_intersection e f : (⟦ e∩f ⟧σ) = ((⟦e⟧σ) ∩ ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄'_mirror e :  (⟦ e ¯⟧σ) = (⟦e⟧σ)¯%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄'_iter_l e :  (⟦ e⁺⟧σ) = (⟦e⟧σ)⁺%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄'_variable a : (⟦𝐄'_var a⟧ σ) = σ a.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄'_empty : (⟦0⟧σ) = 0%lang.
    Proof. unfold interprete;simpl;auto. Qed.
  End rsimpl.
  Hint Rewrite @𝐄'_empty @𝐄'_variable @𝐄'_intersection
       @𝐄'_prod @𝐄'_union @𝐄'_mirror @𝐄'_iter_l
    : simpl_typeclasses.

  
  Global Instance sem_incl_𝐄'_plus :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (@𝐄'_plus X).
  Proof.
    intros e f E g h F ? ?;simpl;rsimpl;revert E F;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄'_fois :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (@𝐄'_seq X).
  Proof.
    intros e f E g h F Σ σ;simpl;revert E F;rsimpl;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄'_inter :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (@𝐄'_inter X).
  Proof.
    intros e f E g h F Σ σ;simpl;revert E F;rsimpl;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄'_conv :
    Proper (ssmaller ==> ssmaller) (@𝐄'_conv X).
  Proof.
    intros e f E Σ σ;simpl;revert E;rsimpl;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄'_iter :
    Proper (ssmaller ==> ssmaller) (@𝐄'_iter X).
  Proof.
    intros e f E Σ σ;simpl.
    autorewrite with simpl_typeclasses.
    apply iter_lang_incl,E.
  Qed.
  Global Instance sem_eq_𝐄'_plus :
    Proper (sequiv ==> sequiv ==> sequiv) (@𝐄'_plus X).
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.
  Global Instance sem_eq_𝐄'_seq :
    Proper (sequiv ==> sequiv ==> sequiv) (@𝐄'_seq X).
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.
  Global Instance sem_eq_𝐄'_inter :
    Proper (sequiv ==> sequiv ==> sequiv) (@𝐄'_inter X).
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.
  Global Instance sem_eq_𝐄'_conv :
    Proper (sequiv ==> sequiv) (@𝐄'_conv X).
  Proof.
    intros e f E Σ σ;simpl;autounfold;rsimpl.
    intro w;rewrite (E Σ σ (rev w));tauto.
  Qed.
  Global Instance sem_eq_𝐄'_iter :
    Proper (sequiv ==> sequiv) (@𝐄'_iter X).
  Proof.
    intros e f E Σ σ;simpl.
    autorewrite with simpl_typeclasses.
    apply iter_lang_eq,E.
  Qed.
  Global Instance 𝐄'_sem_equiv :
    Equivalence (fun e f : 𝐄' X => e ≃ f).
  Proof. once (typeclasses eauto). Qed.
  Global Instance 𝐄'_sem_PreOrder :
    PreOrder (fun e f : 𝐄' X => e ≲ f).
  Proof. once (typeclasses eauto). Qed.
  Global Instance 𝐄'_sem_PartialOrder :
    PartialOrder (fun e f : 𝐄' X => e ≃ f)
                 (fun e f : 𝐄' X => e ≲ f).
  Proof.
    eapply semantic_containment_PartialOrder;once (typeclasses eauto).
  Qed.

  (* end hide *)
  
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

  (** This interpretation is sound in the sense that axiomatically
  equivalent expressions are semantically equivalent. Differently put,
  the axioms we imposed hold in every algebra of languages. *)
  Theorem soundness_𝐄' : forall e f : 𝐄' X, e ≡ f ->  e ≃ f.
  Proof.
    assert (dumb : forall A (w:list A), rev w = nil <-> w = nil)
      by (intros A w;split;[intro h;rewrite <-(rev_involutive w),h
                           |intros ->];reflexivity).
    intros e f E Σ σ;induction E;rsimpl;try firstorder.
    - apply iter_lang_eq,IHE.
    -  destruct H;rsimpl;repeat autounfold with semantics;try (now firstorder).
       + intro w;firstorder.
         * rewrite H1,H3;clear x0 w H1 H3;rewrite<- app_ass.
           eexists;eexists;split;[eexists;eexists;split;[|split]
                                 |split];eauto.
         * rewrite H1,H3;clear x w H1 H3;rewrite app_ass.
           eexists;eexists;split;
             [|split;[eexists;eexists;split;[|split]|]];eauto.
       + intro w;rewrite rev_involutive;tauto.
       + intro w;firstorder.
         * rewrite <- (rev_involutive w),H1,rev_app_distr;eauto.
           exists (rev x0);exists (rev x).
           setoid_rewrite rev_involutive;auto.
         * rewrite H1,rev_app_distr;eauto.
       + intros w;split.
         * intros (n&Iu);exists n.
           generalize dependent (S n);clear n;intros n;revert w.
           induction n;intro w;[simpl;apply dumb|].
           intro I;apply lang_iter_prod_last in I as (u&v&Iu&Iv&E).
           replace w with (rev v++rev u) in * by (now rewrite <- rev_app_distr,<-E,rev_involutive).
           clear w E.
           exists (rev v),(rev u);rewrite rev_involutive.
           repeat split;auto.
           apply IHn;rewrite rev_involutive;assumption.
         * intros (n&Iu);exists n.
           generalize dependent (S n);clear n;intros n;revert w.
           induction n;intro w;[simpl;apply dumb|].
           intro I;apply lang_iter_prod_last in I as (u&v&Iu&Iv&->).
           exists (rev v),(rev u);rewrite rev_app_distr.
           repeat split;auto.
       + intros w;split.
         * intros ([]&Iu).
           -- left;destruct Iu as (u'&?&Iu&->&->).
              rewrite app_nil_r;assumption.
           -- right;destruct Iu as (u&v&Iu&Iv&->).
              exists u,v;repeat split;auto.
              exists n;assumption.
         * intros [Iu|(u&v&Iu&(m&Iv)&->)].
           -- exists 0%nat,w,[];rewrite app_nil_r;repeat split;assumption.
           -- exists (S m),u,v;tauto.
       + intros w;split.
         * intros ([]&Iu).
           -- left;destruct Iu as (u'&?&Iu&->&->).
              rewrite app_nil_r;assumption.
           -- apply lang_iter_prod_last in Iu.
              right;destruct Iu as (u&v&Iu&Iv&->).
              exists u,v;repeat split;auto.
              exists n;assumption.
         * intros [Iu|(u&v&(m&Iu)&Iv&->)].
           -- exists 0%nat,w,[];rewrite app_nil_r;repeat split;assumption.
           -- exists (S m);apply lang_iter_prod_last.
              exists u,v;tauto.
    - destruct H.
      + assert (ih : ⟦e⋅f⟧σ≲⟦f⟧σ) by (intros u Iu;apply (IHE u);left;apply Iu);clear IHE.
        cut (⟦e⁺⋅f⟧σ≲⟦f⟧σ);[intros E u;split;[intros [I|I];[apply E|]|intro;right];assumption|].
        intros w (u&v&(n&Iu)&Iv&->).
        revert u v Iu Iv;induction n;intros u v Iu Iv.
        * destruct Iu as (u'&?&Iu&->&->).
          rewrite app_nil_r;apply ih;exists u',v;tauto.
        * apply lang_iter_prod_last in Iu as (u1&u2&Iu1&Iu2&->);rewrite app_ass.
          apply IHn;[assumption|].
          apply ih;exists u2,v;tauto.
      + assert (ih : ⟦f⋅e⟧σ≲⟦f⟧σ) by (intros u Iu;apply (IHE u);left;apply Iu);clear IHE.
        cut (⟦f⋅e⁺⟧σ≲⟦f⟧σ);[intros E u;split;[intros [I|I];[apply E|]|intro;right];assumption|].
        intros w (u&v&Iu&(n&Iv)&->).
        revert u v Iu Iv;induction n;intros u v Iu Iv.
        * destruct Iv as (v'&?&Iv&->&->).
          rewrite app_nil_r;apply ih;exists u,v';tauto.
        * destruct Iv as (v1&v2&Iv1&Iv2&->);rewrite <- app_ass.
          apply IHn;[|assumption].
          apply ih;exists u,v1;tauto.
  Qed.

  (** This extends to ordering as well. *)
  Lemma soundness_inf_𝐄' (e f : 𝐄' X) : e ≤ f -> e ≲ f.
  Proof.
    intro E;apply smaller_equiv,soundness_𝐄' in E.
    intros Σ σ w I;apply E;rsimpl;left;left;auto.
  Qed.

End language.
Hint Rewrite @𝐄'_empty @𝐄'_variable @𝐄'_intersection
     @𝐄'_prod @𝐄'_union @𝐄'_mirror @𝐄'_iter_l
  : simpl_typeclasses.
