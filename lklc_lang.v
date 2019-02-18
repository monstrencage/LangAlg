Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language lklc.

Section language.
  (** * Language interpretation *)
  Context { X : Set }.

  (** We interpret expressions as languages in the obvious way: *)
  Global Instance to_lang_𝐄 {Σ}: semantics 𝐄 language X Σ :=
    fix to_lang_𝐄 σ e:=
      match e with
      | 1 => 1%lang
      | 0 => 0%lang
      | 𝐄_var a => (σ a)
      | e + f => ((to_lang_𝐄 σ e) + (to_lang_𝐄 σ f))%lang
      | e ⋅ f => ((to_lang_𝐄 σ e) ⋅ (to_lang_𝐄 σ f))%lang
      | e ∩ f => ((to_lang_𝐄 σ e) ∩ (to_lang_𝐄 σ f))%lang
      | e ¯ => (to_lang_𝐄 σ e)¯%lang
      | e⁺ => (to_lang_𝐄 σ e)⁺%lang
      end.

  (* begin hide *)
  Global Instance semSmaller_𝐄 : SemSmaller (𝐄 X) :=
    (@semantic_containment _ _ _ _ _).
  Global Instance semEquiv_𝐄 : SemEquiv (𝐄 X) :=
    (@semantic_equality _ _ _ _ _).
  Hint Unfold semSmaller_𝐄 semEquiv_𝐄 : semantics. 

  Section rsimpl.
    Context { Σ : Set }{σ : 𝕬[X→Σ] }.
    Lemma 𝐄_union e f : (⟦ e+f ⟧σ) = ((⟦e⟧σ) + ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_prod e f :  (⟦ e⋅f ⟧σ) = ((⟦e⟧σ) ⋅ ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_intersection e f : (⟦ e∩f ⟧σ) = ((⟦e⟧σ) ∩ ⟦f⟧σ)%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_mirror e :  (⟦ e ¯⟧σ) = (⟦e⟧σ)¯%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_iter_l e :  (⟦ e⁺⟧σ) = (⟦e⟧σ)⁺%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_variable a : (⟦𝐄_var a⟧ σ) = σ a.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_unit : (⟦1⟧σ) = 1%lang.
    Proof. unfold interprete;simpl;auto. Qed.
    Lemma 𝐄_empty : (⟦0⟧σ) = 0%lang.
    Proof. unfold interprete;simpl;auto. Qed.
  End rsimpl.
  Hint Rewrite @𝐄_unit @𝐄_empty @𝐄_variable @𝐄_intersection
       @𝐄_prod @𝐄_union @𝐄_mirror @𝐄_iter_l
    : simpl_typeclasses.

  Global Instance sem_incl_𝐄_plus :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (@𝐄_plus X).
  Proof.
    intros e f E g h F ? ?;simpl;rsimpl;revert E F;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄_fois :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (@𝐄_seq X).
  Proof.
    intros e f E g h F Σ σ;simpl;revert E F;rsimpl;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄_inter :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (@𝐄_inter X).
  Proof.
    intros e f E g h F Σ σ;simpl;revert E F;rsimpl;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄_conv :
    Proper (ssmaller ==> ssmaller) (@𝐄_conv X).
  Proof.
    intros e f E Σ σ;simpl;revert E;rsimpl;
      repeat autounfold with semantics;firstorder.
  Qed.
  Global Instance sem_incl_𝐄_iter :
    Proper (ssmaller ==> ssmaller) (@𝐄_iter X).
  Proof.
    intros e f E Σ σ;simpl.
    autorewrite with simpl_typeclasses.
    apply iter_lang_incl,E.
  Qed.
  Global Instance sem_eq_𝐄_plus :
    Proper (sequiv ==> sequiv ==> sequiv) (@𝐄_plus X).
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.
  Global Instance sem_eq_𝐄_seq :
    Proper (sequiv ==> sequiv ==> sequiv) (@𝐄_seq X).
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.
  Global Instance sem_eq_𝐄_inter :
    Proper (sequiv ==> sequiv ==> sequiv) (@𝐄_inter X).
  Proof. eapply (@sem_eq_op _ _ ssmaller);once (typeclasses eauto). Qed.
  Global Instance sem_eq_𝐄_conv :
    Proper (sequiv ==> sequiv) (@𝐄_conv X).
  Proof.
    intros e f E Σ σ;simpl;autounfold;rsimpl.
    intro w;rewrite (E Σ σ (rev w));tauto.
  Qed.
  Global Instance sem_eq_𝐄_iter :
    Proper (sequiv ==> sequiv) (@𝐄_iter X).
  Proof.
    intros e f E Σ σ;simpl.
    autorewrite with simpl_typeclasses.
    apply iter_lang_eq,E.
  Qed.
  Global Instance 𝐄_sem_equiv :
    Equivalence (fun e f : 𝐄 X => e ≃ f).
  Proof. once (typeclasses eauto). Qed.
  Global Instance 𝐄_sem_PreOrder :
    PreOrder (fun e f : 𝐄 X => e ≲ f).
  Proof. once (typeclasses eauto). Qed.
  Global Instance 𝐄_sem_PartialOrder :
    PartialOrder (fun e f : 𝐄 X => e ≃ f)
                 (fun e f : 𝐄 X => e ≲ f).
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
  Theorem 𝐄_eq_equiv_lang : forall e f : 𝐄 X, e ≡ f ->  e ≃ f.
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
       + intro w;firstorder subst.
         * simpl in *;auto.
         * exists nil;exists w;simpl;auto.
       + intro w;firstorder subst.
         * rewrite app_nil_r;auto.
         * exists w;exists nil;rewrite app_nil_r;auto.
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
       + intros w;firstorder subst.
         * destruct x;[|destruct x0];auto; discriminate. 
         * destruct x;destruct x0;try discriminate;auto.
         * exists [];exists [];subst;auto.
       + intro w;firstorder subst;simpl in *;auto.
       + intro w;firstorder subst;simpl in *. 
         * exists x0;exists [];rewrite app_nil_r;auto.
         * exists [];exists x;rewrite app_nil_r;auto. 
       + intro w;firstorder subst;simpl in *;auto.
       + intros w;split.
         * intros (n&In);revert w In;induction n;intros w Iw.
           -- destruct Iw as (u&v&Iu&->&->);rewrite app_nil_r.
              destruct Iu as [Iu|(v&w&(->&Iv)&Iw&->)].
              ++ left;exists 0%nat,u,[];rewrite app_nil_r;repeat split;auto.
              ++ right;exists [],w;repeat split;auto.
                 exists 0%nat,w,[];rewrite app_nil_r;repeat split;auto.
           -- destruct Iw as (u&v&Iu&Iv&->).
              apply IHn in Iv.
              destruct Iv as [(m&Iv)|(v1&v2&(->&Iv1)&(m&Im)&->)];
                destruct Iu as [Iu|(?&u'&(->&I1)&I2&->)];simpl;repeat rewrite app_nil_r. 
              ++ left;exists (S m),u,v;repeat split;auto.
              ++ right;exists [],(u'++v);repeat split;auto.
                 exists (S m),u',v;repeat split;auto.
                 assert (⟦ g ⟧ σ ≲ ⟦g + f⟧ σ) as E
                   by (rsimpl;repeat autounfold with semantics;intuition).
                 eapply (iter_prod_lang_incl E) in Iv;try reflexivity;clear E.
                 apply Iv.
              ++ right;exists [],(u++v2);split;[tauto|split;[|tauto]].
                 exists (S m),u,v2;tauto.
              ++ right;exists [],(u'++v2);split;[tauto|split;[|tauto]].
                 exists (S m),u',v2;tauto.
         * intros [I|I].
           -- assert (g≲ g + (1∩e)⋅f) as E
                 by (intro;intros;rsimpl;repeat autounfold with semantics;intuition).
              pose proof (E _ σ) as E';clear E.
              apply iter_lang_incl in E'.
              apply E',I. 
           -- destruct I as (?&u&(->&Ie)&I&->);simpl.
              assert (⟦g+f⟧ σ≲ ⟦g + (1∩e)⋅f⟧σ) as E.
              ++ intros v [Iv|Iv];[left;apply Iv|right;exists [],v;repeat split;assumption].
              ++ apply iter_lang_incl in E.
                 apply E,I.
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
  Lemma 𝐄_inf_incl_lang (e f : 𝐄 X) : e ≤ f -> e ≲ f.
  Proof.
    intro E;apply smaller_equiv,𝐄_eq_equiv_lang in E.
    intros Σ σ w I;apply E;rsimpl;left;left;auto.
  Qed.

  (** A word is in the language of a sum if and only if it is in the
  language of one of its components. *)
  Lemma sum_lang l A (σ:𝕬[X→A]) w :
    (w ∊ ⟦Σ l⟧ σ) <-> (exists t : 𝐄 X, t ∈ l /\ (⟦ t ⟧ σ) w).
  Proof.
    rewrite (𝐄_eq_equiv_lang (sum_fold _) _ _).
    induction l;simpl;rsimpl;autounfold with semantics.
    - firstorder.
    - split;[intros [h|IH];[|apply IHl in IH as (t&I&IH)]
            |intros (t&[<-|I]&IH)];auto.
      -- exists a;split;auto.
      -- exists t;split;auto.
      -- right;apply IHl;eauto.
  Qed.

  Global Instance incl_assign A : SemSmaller 𝕬[X → A] :=
    fun σ τ => forall x, σ x ≲ τ x.
  Global Instance eq_assign A : SemEquiv 𝕬[X → A] :=
    fun σ τ => forall x, σ x ≃ τ x.

  Global Instance incl_assign_PreOrder A : PreOrder (@ssmaller 𝕬[X → A] _).
  Proof.
    split.
    - intros σ x;reflexivity.
    - intros σ1 σ2 σ3 E1 E2 x;transitivity (σ2 x);auto.
  Qed.

  Global Instance eq_assign_Equivalence A : Equivalence (@sequiv 𝕬[X → A] _).
  Proof.
    split.
    - intros σ x;reflexivity.
    - intros σ τ E x;symmetry;auto.
    - intros σ1 σ2 σ3 E1 E2 x;transitivity (σ2 x);auto.
  Qed.
  Global Instance incl_assign_PartialOrder A : PartialOrder _ (@ssmaller 𝕬[X → A] _).
  Proof.
    intros σ τ;split;unfold Basics.flip.
    - intro E;split;intro x;rewrite (E x);reflexivity.
    - intros (E1&E2) x;apply lang_incl_PartialOrder;unfold Basics.flip;split;auto.
  Qed.

  Global Instance assign_monotone A :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (fun (σ : 𝕬[X → A]) e => ⟦e⟧σ).
  Proof.
    intros σ τ E e f E'.
    transitivity (⟦e⟧τ).
    - clear f E'.
      induction e;rsimpl;reflexivity||auto.
      + rewrite IHe1,IHe2;reflexivity.
      + rewrite IHe1,IHe2;reflexivity.
      + rewrite IHe1,IHe2;reflexivity.
      + rewrite IHe;reflexivity.
      + rewrite IHe;reflexivity.
    - apply E'.
  Qed.
  
  Global Instance assign_morph A :
    Proper (sequiv ==> sequiv ==> sequiv) (fun (σ : 𝕬[X → A]) e => ⟦e⟧σ).
  Proof.
    intros σ τ E e f E'.
    apply lang_incl_PartialOrder;unfold Basics.flip;split;apply assign_monotone;auto.
    - rewrite E;reflexivity.
    - rewrite E';reflexivity.
    - rewrite E;reflexivity.
    - rewrite E';reflexivity.
  Qed.

  Lemma test_is_one (A : list X) 𝐀 (σ : 𝕬[X→𝐀]) :
    A ⊢ σ -> ⟦ test A ⟧ σ ≃ 1%lang.
  Proof.
    induction A;simpl;[reflexivity|].
    - intros h;rsimpl.
      assert ([] ∊ σ a /\ A ⊢ σ) as (Ia&V)
          by (split;[apply h;now left|intros b Ib;apply h;now right]).
      apply IHA in V;rewrite <- V.
      intros u;split;intro Iu;repeat split;auto.
      + rsimpl;destruct Iu as ((I&_)&I');auto.
      + apply V in Iu as ->;auto.
      + apply V in Iu as ->;auto.
  Qed.

  Lemma test_is_one_inv (A : list X) 𝐀 (σ : 𝕬[X→𝐀]) :
    forall u, u ∊ (⟦ test A ⟧ σ) -> A ⊢ σ /\ u = [].
  Proof.
    intros u;induction A as [|a A].
    - intros ->;split;auto.
      intros ? F;exfalso;apply F.
    - simpl;rsimpl.
      intros ((Ia&_)&Ih).
      apply IHA in Ih as (V&->);split;auto.
      intros b [<-|Ib];auto.
  Qed.

  Context {decX : decidable_set X}.
  Lemma nil_lang {𝐀 : Set} (σ : 𝕬[X→𝐀]) e :
    [] ∊ (⟦e⟧σ) <-> exists A, test A ≤ e /\ A ⊢ σ.
  Proof.
    split;
      [|intros (A&E&V);eapply 𝐄_inf_incl_lang;[eauto|apply test_is_one;[assumption
                                                                       |reflexivity]]].
    induction e;rsimpl.
    - intros _; exists [];split.
      + reflexivity.
      + intros a;simpl;tauto.
    - intros F;exfalso;apply F.
    - rsimpl;intros I;exists [x];split;simpl.
      + repeat rewrite inf_ax_inter_l;reflexivity.
      + intros ? [<-|F];simpl in *;tauto.
    - intros (u1&u2&I1&I2&E).
      symmetry in E;apply app_eq_nil in E as (->&->).
      apply IHe1 in I1 as (A1&T1&V1).
      apply IHe2 in I2 as (A2&T2&V2).
      exists (A1++A2);split.
      + repeat rewrite test_app.
        rewrite <-T1,<-T2,test_prod_cap;reflexivity.
      + apply test_compatible_app;auto.
    - intros (I1&I2).
      apply IHe1 in I1 as (A1&T1&V1);apply IHe2 in I2 as (A2&T2&V2).
      exists (A1++A2);split.
      + repeat rewrite test_app.
        apply inter_smaller;assumption.
      + apply test_compatible_app;auto.
    - intros [I1|I2];[apply IHe1 in I1 as (A&T&V)|apply IHe2 in I2 as (A&T&V)];
        exists A;rewrite T;(split;[|assumption]);[apply plus_left|apply plus_right];reflexivity.
    - intros I.
      apply IHe in I as (A&T&V).
      exists A;split;[rewrite <- T,test_conv;reflexivity|assumption].
    - intros (n&x&y&I&_&E).
      symmetry in E;apply app_eq_nil in E as (->&_);clear n y.
      apply IHe in I as (A&T&V).
      exists A;split;[rewrite <- T,test_iter;reflexivity|assumption].
  Qed.

End language.
(* begin hide *)
Hint Rewrite @𝐄_unit @𝐄_empty @𝐄_variable @𝐄_intersection
     @𝐄_prod @𝐄_union @𝐄_mirror @𝐄_iter_l
  : simpl_typeclasses.
(* end hide *)
