Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language lklc lklc_lang.

Open Scope expr_scope.

Section reduction.
  Context { X : Set } {decX : decidable_set X} .

  Section pad.
    Context { Σ : Set } {σ : 𝕬[X→Σ]}.
    Context { α : X -> Prop}.
    
    Definition Σ' : Set := option Σ.

    Notation " ⋄ " := (None).

    Definition unpad : list Σ' -> list Σ :=
      flat_map (fun a => match a with Some a => [a] | _ => [] end).

    Definition σ' : 𝕬[X → Σ'] := fun x w => (α x -> exists u, w = ⋄::u) /\ σ x (unpad w).

    Definition unpad_lang : language Σ' -> language Σ :=
      fun L w => exists u, L u /\ w = unpad u.

    Global Instance unpad_lang_smaller : Proper (ssmaller ==> ssmaller) unpad_lang.
    Proof. intros L M E u (v&Iv&->);exists v;split;auto. Qed.
    Global Instance unpad_lang_equiv : Proper (sequiv ==> sequiv) unpad_lang.
    Proof.
      intros L M E;apply antisymmetry;apply unpad_lang_smaller;rewrite E;reflexivity.
    Qed.
    
    Lemma unpad_app u v : unpad (u++v) = unpad u ++ unpad v.
    Proof. induction u as [|[|]];simpl;congruence. Qed.

    Fixpoint more_pad (u v : list Σ') :=
      match u,v with
      | [],[] => True
      | ⋄::u,⋄::v | u,⋄::v => more_pad u v
      | Some a::u,Some b::v => a = b /\ more_pad u v
      | _,_ => False
      end.

    Lemma more_pad_extra_diamond u v : more_pad u v -> more_pad u (⋄::v).
    Proof.
      revert v; induction u as [|[a|] u];intros [|[b|] v];try (simpl;tauto).
      intro h;simpl;apply IHu,h.
    Qed.

    Reserved Notation " u ⊑ v " (at level 80).
    
    Inductive inf_words : relation (list Σ') :=
    | inf_w_refl u : u ⊑ u
    | inf_w_trans u v w : u ⊑ v -> v ⊑ w -> u ⊑ w
    | inf_w_app u1 u2 v1 v2 : u1 ⊑ v1 -> u2 ⊑ v2 -> (u1++u2) ⊑ (v1++v2)
    | inf_w_pad u : u ⊑ ⋄::u
    where " u ⊑ v " := (inf_words u v).
    Hint Constructors inf_words.

    Lemma inf_words_length u v : u ⊑ v -> #u <= #v.
    Proof. intros U;induction U;simpl;repeat rewrite app_length; lia. Qed.
    
    Global Instance preorder_inf_words : PreOrder inf_words.
    Proof. split;eauto. Qed.

    Global Instance app_inf_words : Proper (inf_words ==> inf_words ==> inf_words) (@app Σ').
    Proof. intros ? ? ? ? ?;eauto. Qed.
    Global Instance cons_inf_words a : Proper (inf_words ==> inf_words) (cons a).
    Proof. intros ? ? E;replace (cons a) with (app [a]) by reflexivity;auto. Qed.
    
    Lemma inf_words_more_pad u v : u ⊑ v <-> more_pad u v.
    Proof.
      split.
      - intro U;induction U.
        + induction u as [|[|]];simpl;auto.
        + clear U1 U2; revert u v IHU1 IHU2;induction w as [|[a|]].
          * intros [|[|]] [|[|]];simpl;try tauto.
          * intros [|[c|]] [|[b|]];simpl;try tauto.
            intros (->&I1) (->&I2);split;auto.
            apply (IHw _ _ I1 I2).
          * intros [|[c|]] [|[b|]];simpl;try tauto.
            -- apply IHw.
            -- intros (->&I1) I2.
               apply (IHw _ (Some b :: l0));auto.
               split;auto.
            -- intros I1 I2;eapply IHw;eauto.
            -- apply IHw.
        + clear U1 U2;revert u1 IHU1 u2 v2 IHU2.
          induction v1 as [|[a|]];intros [|[b|] v] ih w1 w2 E;
            try (simpl in *;tauto).
          * simpl in *.
            destruct ih as (->&ih).
            split;auto.

          * simpl;apply more_pad_extra_diamond;simpl in ih.
            rewrite <- (app_nil_l w1).
            apply IHv1;auto.
          * simpl in *.
            rewrite app_comm_cons.
            apply IHv1;auto.
          * simpl in *.
            apply IHv1;auto.
        + apply more_pad_extra_diamond.
          induction u as [|[|]];simpl;auto.
      - revert u;induction v as [|[a|] v];simpl;intros [|[b|] u];
          try tauto||auto.
        + intros (->&h).
          rewrite (IHv _ h);reflexivity.
        + intro h;apply IHv in h as ->;auto.
        + intro h;apply IHv in h as ->;auto.
        + intro h;apply IHv in h as ->;auto.
    Qed.

    Global Instance partialorder_inf_words : PartialOrder Logic.eq inf_words.
    Proof.
      intros u v;split;[intros ->;split;reflexivity|].
      unfold Basics.flip;intros (I1&I2).
      rewrite inf_words_more_pad in I1,I2; revert v I1 I2;
        induction u as [|[a|] u];intros [|[b|] v];simpl;try tauto.
      - intros (->&I1) (_&I2);f_equal;apply IHu;auto.
      - intros;f_equal;apply IHu;auto.
    Qed.
    
    Global Instance rev_inf_words : Proper (inf_words ==> inf_words) (@rev Σ').
    Proof.
      intros u v U;induction U.
      - reflexivity.
      - eauto.
      - repeat rewrite rev_app_distr;auto.
      - simpl;rewrite <- app_nil_r at 1.
        apply inf_w_app;auto.
    Qed.
        
    Lemma inf_words_unpad u v : u ⊑ v -> unpad u = unpad v.
    Proof.
      intros U;induction U.
      - reflexivity.
      - etransitivity;eassumption.
      - repeat rewrite unpad_app;congruence.
      - simpl;auto.
    Qed.

    Lemma inf_words_app_invert u1 u2 v :
      u1 ++ u2 ⊑ v -> exists v1 v2, v = v1 ++ v2 /\ u1 ⊑ v1 /\ u2 ⊑ v2.
    Proof.
      remember (u1++u2) as u;intro U;revert u1 u2 Hequ;induction U.
      - intros u1 u2 ->;exists u1,u2;auto.
      - intros u1 u2 ->.
        destruct (IHU1 u1 u2) as (v1&v2&->&I1&I2);auto.
        destruct (IHU2 v1 v2) as (w1&w2&->&I3&I4);auto.
        exists w1,w2;eauto.
      - intros w1 w2 E;apply Levi in E as (w&[(->&->)|(->&->)]).
        + destruct (IHU1 w1 w) as (t1&t2&->&I1&I2);auto.
          exists t1,(t2++v2);rewrite app_ass;repeat split;auto.
        + destruct (IHU2 w w2) as (t1&t2&->&I1&I2);auto.
          exists (v1++t1),t2;rewrite app_ass;repeat split;auto.
      - intros u1 u2 ->;exists (⋄::u1),u2;repeat split;auto.
    Qed.
    
    Lemma min_words u : (map Some (unpad u)) ⊑ u.
    Proof.
      induction u as [|[a|] u];simpl;auto.
      - rewrite IHu;reflexivity.
      - rewrite IHu;auto.
    Qed.

    Lemma unpad_cons_inf_words a w v :
      a :: w = unpad v -> exists v1 v2 : list (Σ'), v = v1 ++ [Some a] ++ v2 /\ [] ⊑ v1.
    Proof.
      induction v as [|[b|]].
      - discriminate.
      - intros E';inversion E' as [[EE E]];subst.
        exists [],v;simpl;auto.
      - intros ih;apply IHv in ih as (v1&v2&->&I).
        exists (⋄::v1),v2;split;auto.
        rewrite I;auto.
    Qed.
      
    Lemma lub_more_pad u v :
      unpad u = unpad v -> exists w, u ⊑ w /\ v ⊑ w /\ forall t, u ⊑ t -> v ⊑ t -> w ⊑ t.
    Proof.
      revert v;induction u as [|[a|]u].
      - intros v Ev;exists v;repeat split.
        + induction v as [|[a|]];simpl in *;try discriminate;auto.
          rewrite IHv;auto.
        + reflexivity.
        + intuition.
      - intros [|[b|]v];try discriminate.
        + intros E';inversion E' as [[E'' E]];subst;clear E'.
          apply IHu in E as (w&E1&E2&M);clear IHu.
          exists (Some b::w);repeat split;auto.
          * rewrite E1;auto.
          * rewrite E2;auto.
          * intros t;induction t as [|[a|]].
            -- repeat rewrite inf_words_more_pad;simpl;tauto.
            -- intros I1 I2;rewrite inf_words_more_pad in I1,I2.
               destruct I1 as (->&I1),I2 as (_&I2).
               rewrite <- inf_words_more_pad in I1,I2.
               rewrite (M t I1 I2);reflexivity.
            -- intros;rewrite IHt;auto;rewrite inf_words_more_pad in *;simpl;auto.
        + simpl;intro E'.
          destruct (unpad_cons_inf_words E') as (v1&v2&->&Iv1).
          repeat rewrite unpad_app in E'.
          rewrite <- (inf_words_unpad Iv1) in E';simpl in E'.
          inversion E' as [[E]];subst;clear E'.
          apply IHu in E as (w&E1&E2&M);clear IHu.
          exists (⋄::v1++Some a:: w);repeat split;auto.
          * rewrite <- Iv1,<-E1;simpl;auto.
          * rewrite <- E2;reflexivity.
          * intros t I1' I2.
            destruct (unpad_cons_inf_words (inf_words_unpad I1')) as (t1&t2&->&It1).
            destruct t1 as [|[b|]];simpl in *;
              try (rewrite inf_words_more_pad in *;simpl in *;tauto).
            cut (v1 ⊑ t1 /\ w ⊑ t2);[intros (->&->);auto|].
            cut (v1 ⊑ t1 /\ v2 ⊑ t2 /\ u ⊑ t2);[intros (->&(h1&h2));split;auto|].
            clear w E1 E2 M.
            repeat rewrite inf_words_more_pad in *;simpl in *.
            revert u v1 v2 t2 Iv1 It1 I1' I2;induction t1 as [|[b|] t1];simpl;
              try tauto.
            -- intros u [|[|] v1] v2 t2;simpl;try tauto.
            -- intros u [|[|] v1] v2 t2;simpl;try tauto.
               ++ intros I1 I2 I3 I4;apply IHt1;simpl;auto.
               ++ intros I1 I2 I3 I4;apply IHt1;simpl;auto.
      - simpl;intros [|[b|] v] E.
        + exists (⋄::u);repeat split;auto.
          clear IHu;simpl;auto.
          induction u as [|[|]];simpl in *;try discriminate||auto.
          rewrite IHu;auto.
        + apply IHu in E as (w&E1&E2&M);clear IHu.
          exists (⋄::w);repeat split.
          * rewrite E1;reflexivity.
          * rewrite <- E2;simpl;auto.
          * intros t I1 I2.
            destruct t as [|[|]];rewrite inf_words_more_pad in I1,I2;simpl in *;try tauto.
            rewrite <- inf_words_more_pad in I1,I2.
            rewrite (M _ I1 I2);reflexivity.
        + simpl in E.
          apply IHu in E as (w&E1&E2&M);clear IHu.
          exists (⋄::w);repeat split.
          * rewrite E1;reflexivity.
          * rewrite <- E2;reflexivity.
          * intros t I1 I2.
            destruct t as [|[|]];rewrite inf_words_more_pad in I1,I2;simpl in *;try tauto.
            rewrite <- inf_words_more_pad in I1,I2.
            rewrite (M _ I1 I2);reflexivity.
    Qed.
        
    Definition pad_closed (L : language Σ') := forall u v, L u -> u ⊑ v -> L v.

    Lemma pad_closed_rat e : one_free e = true -> pad_closed (⟦e⟧σ').
    Proof.
      induction e;rsimpl;
        discriminate
        ||(rewrite andb_true_iff;intros (ih1&ih2);apply IHe1 in ih1;apply IHe2 in ih2;
          clear IHe1 IHe2)
        ||(intros ih;apply IHe in ih;clear IHe)
        ||intros _ ;intros u v Iu L.
      - apply Iu.
      - destruct Iu as (h1&h2);split.
        + intros h;apply h1 in h as (u'&->).
          rewrite inf_words_more_pad in L.
          destruct v as [|[]];simpl in *;tauto||eauto.
        + rewrite <- (inf_words_unpad L);assumption.
      - destruct Iu as (u1&u2&I1&I2&->).
        apply inf_words_app_invert in L as (v1&v2&->&L1&L2).
        exists v1,v2;repeat split.
        + now eapply ih1,L1.
        + now eapply ih2,L2.
      - destruct Iu as (I1&I2);split.
        + now eapply ih1,L.
        + now eapply ih2,L.
      - destruct Iu as [Iu|Iu].
        + now left;eapply ih1,L.
        + now right;eapply ih2,L.
      - now eapply ih,rev_inf_words,L.
      - destruct Iu as (n&In);exists n;revert u v In L;induction n;simpl.
        + intros u' v (u&?&I&->&->) L;exists v,[];rewrite app_nil_r in *;repeat split.
          now eapply ih,L.
        + intros u v (u1&u2&I1&I2&->) L.
          apply inf_words_app_invert in L as (v1&v2&->&L1&L2).
          exists v1,v2;repeat split.
          * now eapply ih,L1.
          * now eapply IHn,L2.
    Qed.
    
    Open Scope lang.
    Lemma unpad_prod L M :
      unpad_lang (L ⋅ M) ≃ unpad_lang L⋅unpad_lang M.
    Proof.
      intros u;split.
      - intros (w&(u1&u2&I1&I2&->)&->).
        rewrite unpad_app.
        exists (unpad u1),(unpad u2);repeat split.
        + exists u1;tauto.
        + exists u2;tauto.
      - intros (w1&w2&(u1&I1&->)&(u2&I2&->)&->).
        rewrite <- unpad_app.
        exists (u1++u2);split;[exists u1,u2|];tauto.
    Qed.
    Lemma unpad_union L M :
      unpad_lang (L + M) ≃ unpad_lang L+unpad_lang M.
    Proof.
      intros u;split.
      - intros (w&[I|I]&->).
        + left;exists w;auto.
        + right;exists w;auto.
      - intros [(w&I&->)|(w&I&->)];exists w;split;[left| |right|];auto.
    Qed.
    Lemma unpad_inter L M :
      pad_closed L -> pad_closed M ->
      unpad_lang (L ∩ M) ≃ unpad_lang L ∩ unpad_lang M.
    Proof.
      intros P1 P2 u;split.
      - intros (w&(I1&I2)&->);split;exists w;auto.
      - intros ((u1&I1&->)&(u2&I2&E)).
        apply lub_more_pad in E as (w&Iw1&Iw2&Min).
        exists w;repeat split.
        + eapply P1;eauto.
        + eapply P2;eauto.
        + apply inf_words_unpad,Iw1.
    Qed.  
    Lemma unpad_power L n : unpad_lang (L^{S n}) ≃ (unpad_lang L)^{S n}.
    Proof.
      induction n;rsimpl.
      - intros u;split.
        + intros (?&(w&?&Iw&->&->)&->).
          exists (unpad w),[];repeat rewrite app_nil_r;repeat split;auto.
          exists w;tauto.
        + intros (u'&?&(w&Iw&->)&->&->).
          exists w;split;[exists w,[]|];rewrite app_nil_r;repeat split;auto.
      - simpl in IHn;rewrite <- IHn;clear IHn.
        rewrite unpad_prod;reflexivity.
    Qed.
        
    Lemma unpad_iter L : unpad_lang (L⁺) ≃ (unpad_lang L)⁺.
    Proof.
      intros u;split.
      - intros (w&(n&Iw)&->).
        exists n;apply unpad_power;exists w;tauto.
      - intros (n&In).
        apply unpad_power in In as (w&Iw&->).
        exists w;split;[exists n|];auto.
    Qed.

    Lemma unpad_rev u : rev (unpad u) = unpad (rev u).
    Proof.
      induction u as [|[|]];simpl;try rewrite unpad_app;try rewrite IHu;
        try rewrite app_nil_r;simpl;auto.
    Qed.
    
    Lemma unpad_conv L : unpad_lang (L ¯) ≃ (unpad_lang L)¯.
    Proof.
      intros u;split.
      - intros (v&Iv&->).
        exists (rev v).
        rewrite unpad_rev;auto.
      - intros (v&Iv&E).
        exists (rev v).
        rewrite <-unpad_rev,<-E.
        unfold mirror;repeat rewrite rev_involutive;auto.
    Qed.
      
    Close Scope lang.
      
    Lemma σ'_spec e : one_free e = true -> ⟦e⟧σ ≃ unpad_lang (⟦e⟧σ').
    Proof.
      induction e;rsimpl;
        discriminate
        ||(rewrite andb_true_iff;intros (O1&O2);
          rewrite (IHe1 O1),(IHe2 O2);clear IHe1 IHe2)
        ||(intros ih;apply IHe in ih as ->;clear IHe)
        ||intros _ .
      - intros u;split.
        + intros F;exfalso;apply F.
        + intros (?&F&_);apply F.
      - intros u;rsimpl;split.
        + intros Iu;exists (⋄::map Some u).
          cut (u = unpad (⋄ :: map Some u));[intros E;split;[|assumption]|].
          * split;[|rewrite <-E;assumption].
            intros Ix;exists (map Some u);reflexivity.
          * clear;simpl;induction u;simpl;congruence.
        + intros (w&(_&Iw)&->);assumption.
      - symmetry;apply unpad_prod.
      - symmetry;apply unpad_inter;auto using pad_closed_rat.
      - symmetry;apply unpad_union.
      - symmetry;apply unpad_conv.
      - symmetry;apply unpad_iter.
    Qed.
  End pad.
  Hint Constructors inf_words.
  
  Proposition one_free_sem e f :
    one_free e = true -> one_free f = true ->
    e ≃ f <-> forall A, forall σ : 𝕬[X → A], (forall a, ~ [] ∊ σ a) -> ⟦e⟧σ≃⟦f⟧σ.
  Proof.
    intros Oe Of;split;[intros E A σ _;apply E|].
    intros hyp A σ.
    set (α := (fun _ : X => True)).
    rewrite (@σ'_spec _ _ α _ Oe),(@σ'_spec _ _ α _ Of).
    set (σ0 := @σ' _ σ α).
    cut (forall a : X, ~ σ0  a []).
    - intros h;apply hyp in h as ->;reflexivity.
    - intros a ((v&Iv)&_).
      + exact I.
      + discriminate.
  Qed.
    
  Proposition one_free_sem_inf e f :
    one_free e = true ->
    e ≲ f <-> forall A, forall σ : 𝕬[X → A], (forall a, ~ [] ∊ σ a) -> ⟦e⟧σ≲⟦f⟧σ.
  Proof.
    intros Oe;split;[intros E A σ _;apply E|].
    intros hyp A σ.
    set (α := (fun _ : X => True)).
    rewrite (@σ'_spec _ _ α _ Oe).
    intros u (w&Iw&->).
    apply hyp in Iw as Iw';[|intros a ((v&Iv)&_);simpl;unfold α;[tauto|discriminate]].
    set (σ'' := fun a w => σ a (unpad w)).
    cut (w∊ ⟦f⟧ σ'');
      [|eapply assign_monotone,Iw';[|reflexivity];intros a u (_&Iu);apply Iu].
    clear;revert w;induction f;simpl;intro w;rsimpl.
    - intros ->;reflexivity.
    - intros F;apply F.
    - tauto.
    - intros (u1&u2&I1&I2&->).
      rewrite unpad_app.
      exists (unpad u1),(unpad u2);repeat split;auto.
    - intros (I1&I2);split;auto.
    - intros [I|I];[left|right];auto.
    - unfold mirror.
      rewrite unpad_rev;apply IHf.
    - intros (n&In);exists n;revert w In;induction n.
      + intros w (u&?&Iu&->&->).
        rewrite unpad_app;exists (unpad u),[];repeat split;auto.
      + rsimpl;intros w (u1&u2&Iu1&Iu2&->);rewrite unpad_app.
        exists (unpad u1),(unpad u2);repeat split;auto.
        apply IHn,Iu2.
  Qed.

  Definition positive e : 𝐄 X := Σ (flat_map (fun nf => match nf with
                                                     | ([],Some f)=> [f]
                                                     | _ => []
                                                     end) (expand e)).
  Notation " ⦗ e ⦘ " := (positive e).

  Lemma one_free_positive e : one_free ⦗e⦘ = true.
  Proof.
    apply one_free_sum.
    unfold positive.
    intros f If;apply in_flat_map in If as (([]&[g|])&Ig&If);simpl in *;auto.
    destruct If as [->|F];auto.
    apply one_free_expand in Ig;auto.
  Qed.
  
  Lemma positive_inf e : ⦗e⦘ ≤ e.
  Proof.
    rewrite (expand_eq _ e) at 2.
    apply Σ_small;intros f If.
    apply in_flat_map in If as (([]&[g|])&Ig&If);simpl in If;try tauto.
    destruct If as [<-|F];try tauto.
    assert (I' : nf_to_term ([], Some g) ∈ (map (nf_to_term (X:=X)) (expand e)))
      by (apply in_map_iff;eauto).
    apply (Σ_big _ I');simpl.
    rewrite ax_seq_1;reflexivity.
  Qed.

  Lemma positive_spec e f :
    one_free e = true -> e ≲ f -> e ≲ ⦗f⦘.
  Proof.
    intros Oe Ie.
    apply (one_free_sem_inf _ Oe).
    intros Ξ σ hσ u Iu.
    cut (u <> []).
    - intros N;apply Ie in Iu.
      apply (𝐄_eq_equiv_lang (expand_eq _ f)) in Iu.
      apply sum_lang in Iu as (F&If&Iu).
      apply in_map_iff in If as ((B&g)&<-&Ig);destruct g as [g|];[destruct B|];simpl in *.
      + rsimpl in *;destruct Iu as (?&?&->&Iu&E).
        symmetry in E;simpl in E;subst.
        apply sum_lang;exists g;repeat split;auto.
        apply in_flat_map;exists ([],Some g);simpl;auto.
      + exfalso;rsimpl in Iu.
        destruct Iu as (?&?&((F&_)&E)&_).
        apply test_is_one_inv in E as (_&->).
        eapply hσ,F.
      + exfalso;apply test_is_one_inv in Iu as (_&->);tauto.
    - clear f Ie.
      revert u Iu;induction e;simpl in *;rsimpl in *;intros u.
      + discriminate.
      + intros Iu _;apply Iu.
      + intros Iu ->;eapply hσ,Iu.
      + apply andb_true_iff in Oe as (O1&O2).
        intros (u1&u2&I1&I2&->) E;apply app_eq_nil in E as (->&->).
        apply IHe1 in I1;auto.
      + apply andb_true_iff in Oe as (O1&O2).
        intros (I1&I2) ->.
        apply IHe1 in I1;auto.
      + apply andb_true_iff in Oe as (O1&O2).
        intros [I1|I2].
        * apply IHe1 in I1;auto.
        * apply IHe2 in I2;auto.
      + intros Iu ->.
        apply IHe in Iu;auto.
      + intros (n&u1&u2&Iu&_&E) ->.
        symmetry in E;apply app_eq_nil in E as (->&_).
        apply IHe in Iu;auto.
  Qed.
          

  Reserved Notation " ⟨ e ⟩ A " (at level 20).
  
  Fixpoint reduce A e :=
    match e with
    | 0 => 0
    | 1 => 1
    | 𝐄_var a => if inb a A then 𝐄_var a + 1 else 𝐄_var a
    | e+f => ⟨e⟩A + ⟨f⟩A
    | e⋅f => ⟨e⟩A ⋅ ⟨f⟩A
    | e∩f => ⟨e⟩A ∩ ⟨f⟩A
    | e⁺ => ⟨e⟩A ⁺
    | e ¯ => ⟨e⟩A ¯
    end
  where " ⟨ e ⟩ A " := (reduce A e).

  Lemma reduce_sup A e : e ≤ ⟨e⟩A.
  Proof.
    induction e.
    - reflexivity.
    - reflexivity.
    - simpl;destruct (inb x A);[apply plus_left|];reflexivity.
    - simpl;rewrite IHe1,IHe2 at 1;reflexivity.
    - simpl;rewrite IHe1,IHe2 at 1;reflexivity.
    - simpl;rewrite IHe1,IHe2 at 1;reflexivity.
    - simpl;rewrite IHe at 1;reflexivity.
    - simpl;rewrite IHe at 1;reflexivity.
  Qed.

  Lemma reduce_inf A e : test A ⋅ ⟨e⟩A ≤ e.
  Proof.
    induction e;simpl.
    - rewrite test_sub_id,ax_seq_1;reflexivity.
    - rewrite test_sub_id,ax_seq_1;reflexivity.
    - case_eq (inb x A).
      + rewrite inb_spec,ax_seq_plus,ax_1_seq.
        rewrite test_sub_id,ax_seq_1 at 1.
        intros Ia;apply plus_inf;[reflexivity|].
        rewrite (test_var Ia),inf_ax_inter_l;reflexivity.
      + rewrite test_sub_id,ax_seq_1 at 1;reflexivity.
    - rewrite test_dup,<-ax_seq_assoc.
      rewrite (ax_seq_assoc _ (⟨e1⟩A)),(test_seq _ (⟨e1⟩A)).
      repeat rewrite ax_seq_assoc.
      rewrite IHe1,<-ax_seq_assoc,IHe2.
      reflexivity.
    - rewrite test_inter,IHe1,IHe2;reflexivity.
    - rewrite ax_seq_plus,IHe1,IHe2;reflexivity.
    - rewrite test_seq,<-test_conv,<-ax_conv_seq,IHe;reflexivity.
    - rewrite <- IHe at 2.
      transitivity (0⁺+test A⋅(0+⟨e⟩A)⁺).
      + rewrite iter_0;repeat rewrite (ax_plus_com 0),ax_plus_0.
        reflexivity.
      + rewrite test_inter_1, <- ax_inter_1_iter,<- test_inter_1.
        rewrite (ax_plus_com 0),ax_plus_0;reflexivity.
  Qed.


  Lemma reduce_lang A e :
    forall 𝐀,forall σ τ: 𝕬[X→𝐀],
        (forall a, ~ σ a []) ->
        (forall a, a ∈ A -> τ a []) ->
        (forall a w, ~ a ∈ A \/ w <> [] -> σ a w <-> τ a w) ->
        ⟦⟨e⟩A⟧σ≃⟦⟨e⟩A⟧τ.
  Proof.
    intros ? ? ? h1 h2 E.
    apply antisymmetry;
      [apply assign_monotone;
       [intros a w Iw;destruct w;
        [case_eq (inb a A);[|rewrite <- not_true_iff_false];rewrite inb_spec;intros Ia;
         [apply h2,Ia|apply E,Iw;now left]
        |apply E,Iw;right;discriminate]
       |reflexivity]|].
    induction e;simpl;rsimpl.
    - reflexivity.
    - reflexivity.
    - case_eq (inb x A);[|rewrite <- not_true_iff_false];rewrite inb_spec;intros Ix;rsimpl.
      + intros w [Iw | ->];[|right;reflexivity].
        destruct w as [|a w].
        * right;reflexivity.
        * left;apply E,Iw;right;discriminate.
      + intros w Iw;apply E,Iw;left;intros Ix';apply Ix,Ix'.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe1,IHe2;reflexivity.
    - rewrite IHe;reflexivity.
    - rewrite IHe;reflexivity.
  Qed.

  Lemma reduce_spec A e f :
    one_free e = true -> test A ⋅ e ≲ ⟨ f ⟩ A -> e ≲ ⟨ f ⟩ A.
  Proof.
    intros O I.
    apply (one_free_sem_inf _ O).
    intros Ξ σ hσ u Iu.
    set (σ' := (fun a w => (a ∈ A /\ w = []) \/ σ a w) : 𝕬[X→Ξ]).
    cut (u ∊ ⟦⟨f⟩A⟧σ').
    - intros Iu';eapply reduce_lang,Iu'.
      + apply hσ.
      + intros a Ia;left;split;auto.
      + intros a w [Ia|N];split;intro Iw.
        * right;assumption.
        * destruct Iw as [(F&_)|Iw];tauto.
        * right;assumption.
        * destruct Iw as [(_&->)|Iw];tauto.
    - apply I;rsimpl;exists [],u.
      repeat split.
      + apply test_is_one;[|reflexivity].
        intros a Ia;left;tauto.
      + eapply assign_monotone,Iu;[|reflexivity].
        intros a w Iw;right;assumption.
  Qed.

  Proposition reduction_inf A f : test A ⋅ ⦗⟨f⟩A⦘ ≤ f.
  Proof.
    rewrite <- (reduce_inf A f) at 2.
    rewrite positive_inf;reflexivity.
  Qed.

  Proposition reduction_one_free A f : one_free ⦗⟨f⟩A⦘ = true.
  Proof. apply one_free_positive. Qed.

  Proposition reduction_spec A e f :
    one_free e = true -> test A ⋅ e ≲ f -> e ≲ ⦗⟨f⟩A⦘.
  Proof.
    intros O I.
    rewrite (𝐄_inf_incl_lang (reduce_sup A f)) in I.
    apply (positive_spec O).
    apply (reduce_spec O),I.
  Qed.

End reduction.

Notation " ⦗ e ⦘ " := (positive e).
Notation " ⟨ e ⟩ A " := (reduce A e) (at level 20).
  