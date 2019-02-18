(** We finally arrive to the main result of this development: the
proof that our axiomatization is complete for the equational theory of
languages. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools language klm one_free_expr prime_set.
Require Import lklc lklc_lang lklc_reduction.

Section s.
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Fixpoint E_to_E' (e : 𝐄 X) : 𝐄' X :=
    match e with
    | 0 | 1 => 0%one
    | 𝐄_var x => 𝐄'_var x
    | e+f => (E_to_E' e + E_to_E' f)%one
    | e⋅f => (E_to_E' e ⋅ E_to_E' f)%one
    | e∩f => (E_to_E' e ∩ E_to_E' f)%one
    | e⁺ => (E_to_E' e⁺)%one
    | e ¯ => (E_to_E' e ¯)%one
    end.

  Fixpoint E'_to_E (e : 𝐄' X) : 𝐄 X :=
    match e with
    | 0%one => 0
    | 𝐄'_var x => 𝐄_var x
    | (e+f)%one => (E'_to_E e + E'_to_E f)
    | (e⋅f)%one => (E'_to_E e ⋅ E'_to_E f)
    | (e∩f)%one => (E'_to_E e ∩ E'_to_E f)
    | e⁺%one => (E'_to_E e⁺)
    | e ¯%one => (E'_to_E e ¯)
    end.

  Lemma one_free_E'_to_E e : one_free (E'_to_E e) = true.
  Proof. induction e;simpl;try rewrite IHe1,IHe2||rewrite IHe;reflexivity. Qed.
  
  Lemma inject_E'_to_E e f : e ≡ f -> E'_to_E e ≡ E'_to_E f.
  Proof.
    intros E;induction E;simpl;auto.
    - eauto.
    - destruct H;simpl;try (now apply eq_ax;auto).
      + apply plus_idem.
      + rewrite ax_inter_comm;apply equiv_0_inter.
      + apply conv_0.
    - destruct H;simpl in *;eauto.
  Qed.

  Lemma inject_E'_to_E_inf e f : e ≤ f -> E'_to_E e ≤ E'_to_E f.
  Proof. intro E;apply inject_E'_to_E in E;simpl in E;apply E. Qed.

  Lemma E_to_E'_and_back e : one_free e = true -> E'_to_E (E_to_E' e) = e.
  Proof.
    induction e;simpl;
      discriminate||reflexivity
      ||(rewrite andb_true_iff;intros (h1&h2);apply IHe1 in h1 as -> ;
        apply IHe2 in h2 as ->)||(intro h;apply IHe in h as ->);reflexivity.
  Qed.

  Lemma E_to_E'_lang {A} (σ : 𝕬[X→A]) e :
    one_free e = true -> ⟦E_to_E' e⟧σ ≃ ⟦e⟧σ.
  Proof.
    induction e;simpl;rsimpl;
      discriminate||reflexivity
      ||(rewrite andb_true_iff;intros (h1&h2);apply IHe1 in h1 as -> ;
        apply IHe2 in h2 as ->)||(intro h;apply IHe in h as ->);reflexivity.
  Qed.

  Lemma E'_to_E_lang {A} (σ : 𝕬[X→A]) e :
    ⟦E'_to_E e⟧σ ≃ ⟦e⟧σ.
  Proof. induction e;simpl;rsimpl;try rewrite IHe1,IHe2||rewrite IHe;reflexivity. Qed.

  Proposition rm_nil (e f : 𝐄' X) :
    e ≃ f <-> forall A, forall σ : 𝕬[X → A], (forall a, ~ [] ∊ σ a) -> ⟦e⟧σ≃⟦f⟧σ.
  Proof.
    split;[intros E A σ _;apply E|].
    intros h A σ.
    repeat rewrite <- E'_to_E_lang.
    apply one_free_sem;auto using one_free_E'_to_E.
    clear A σ.
    intros A σ hσ.
    repeat rewrite E'_to_E_lang.
    apply h,hσ.
  Qed.
End s.

Section t.
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Close Scope expr.
  Open Scope one.
  
  Fixpoint E'_to_E'' (e : 𝐄' X) : 𝐄'' X :=
    match e with
    | 0 => 0%lat
    | 𝐄'_var x => 𝐄''_var x
    | e+f => (E'_to_E'' e + E'_to_E'' f)%lat
    | e⋅f => (E'_to_E'' e ⋅ E'_to_E'' f)%lat
    | e∩f => (E'_to_E'' e ∩ E'_to_E'' f)%lat
    | e⁺ => (E'_to_E'' e⁺)%lat
    | e ¯ => (E'_to_E'' e)%lat
    end.

  Fixpoint E''_to_E' (e : 𝐄'' X) : 𝐄' X :=
    match e with
    | 0%lat => 0
    | 𝐄''_var x => 𝐄'_var x
    | (e+f)%lat => (E''_to_E' e + E''_to_E' f)
    | (e⋅f)%lat => (E''_to_E' e ⋅ E''_to_E' f)
    | (e∩f)%lat => (E''_to_E' e ∩ E''_to_E' f)
    | e⁺%lat => (E''_to_E' e⁺)
    end.

  Fixpoint simple (e : 𝐄' X) :=
    match e with
    | _ ¯ => false
    | e⋅f | e + f | e ∩ f => simple e && simple f
    | e ⁺ => simple e
    | _ => true
    end.

  Lemma simple_E''_to_E' e : simple (E''_to_E' e) = true.
  Proof. induction e;simpl;try rewrite IHe1,IHe2||rewrite IHe;reflexivity. Qed.
  
  Lemma inject_E''_to_E' e f : e ≡ f -> E''_to_E' e ≡ E''_to_E' f.
  Proof.
    intros E';induction E';simpl;auto.
    - eauto.
    - destruct H;simpl;auto.
      + repeat rewrite (one_free_expr.ax_inter_comm (E''_to_E' e));auto.
      + rewrite (one_free_expr.ax_inter_comm (E''_to_E' e));auto.
        rewrite one_free_expr.ax_plus_inter.
        rewrite one_free_expr.ax_inter_idem.
        rewrite one_free_expr.ax_plus_com.
        rewrite (one_free_expr.ax_inter_comm (E''_to_E' f));auto.
      + rewrite one_free_expr.ax_plus_com;auto.
    - destruct H;simpl in *;eauto.
  Qed.

  Lemma inject_E''_to_E'_inf e f : e ≤ f -> E''_to_E' e ≤ E''_to_E' f.
  Proof. intro E';apply inject_E''_to_E' in E';simpl in E';apply E'. Qed.

  Lemma E'_to_E''_and_back e : simple e = true -> E''_to_E' (E'_to_E'' e) = e.
  Proof.
    induction e;simpl;
      discriminate||reflexivity
      ||(rewrite andb_true_iff;intros (h1&h2);apply IHe1 in h1 as -> ;
        apply IHe2 in h2 as ->)||(intro h;apply IHe in h as ->);reflexivity.
  Qed.

  Lemma E'_to_E''_lang {A} (σ : 𝕬[X→A]) e :
    simple e = true -> ⟦E'_to_E'' e⟧σ ≃ ⟦e⟧σ.
  Proof.
    induction e;simpl;rsimpl;
      discriminate||reflexivity
      ||(rewrite andb_true_iff;intros (h1&h2);apply IHe1 in h1 as -> ;
        apply IHe2 in h2 as ->)||(intro h;apply IHe in h as ->);reflexivity.
  Qed.

  Lemma E''_to_E'_lang {A} (σ : 𝕬[X→A]) e :
    ⟦E''_to_E' e⟧σ ≃ ⟦e⟧σ.
  Proof. induction e;simpl;rsimpl;try rewrite IHe1,IHe2||rewrite IHe;reflexivity. Qed.

  Proposition rm_nil' (e f : 𝐄'' X) :
    e ≃ f <-> forall A, forall σ : 𝕬[X → A], (forall a, ~ [] ∊ σ a) -> ⟦e⟧σ≃⟦f⟧σ.
  Proof.
    split;[intros E' A σ _;apply E'|].
    intros h A σ.
    repeat rewrite <- E''_to_E'_lang.
    apply rm_nil;auto. 
    clear A σ.
    intros A σ hσ.
    repeat rewrite E''_to_E'_lang.
    apply h,hσ.
  Qed.
End t.
    
Section mirror.

  Context { X : Set }{dec_X: decidable_set X}.

  Open Scope one.
  Fixpoint is_clean (e : 𝐄' X) : bool :=
    match e with
    | 0 | 𝐄'_var _ | (𝐄'_var _)¯ => true
    | e + f | e ⋅ f | e ∩ f => is_clean e && is_clean f
    | e ⁺ => is_clean e
    | _ ¯ => false
    end.

  Fixpoint comb e (dir : bool) : 𝐄' X:=
    match e with
    | 0 => 0
    | e + f => (comb e dir + comb f dir)
    | e ∩ f => ((comb e dir) ∩ (comb f dir))
    | e ¯ => comb e (negb dir)
    | e ⁺ => (comb e dir)⁺
    | 𝐄'_var a => if dir then 𝐄'_var a else 𝐄'_var a ¯
    | e ⋅ f =>
      if dir
      then ((comb e dir)⋅(comb f dir))
      else ((comb f dir)⋅(comb e dir))
    end.
    
  Fixpoint prime (e : 𝐄' X) : 𝐄'' X′ :=
    match e with
    | 𝐄'_var a => 𝐄''_var (a,true)
    | 𝐄'_var a ¯ => 𝐄''_var (a,false)
    | e + f => (prime e + prime f)%lat
    | e ⋅ f => (prime e ⋅ prime f)%lat
    | e ∩ f => (prime e ∩ prime f)%lat
    | e ⁺ => (prime e ⁺)%lat
    | _ => 0%lat
    end.
  
  Fixpoint unprime (e : 𝐄'' X′) :=
    match e with
    | 0%lat => 0
    | 𝐄''_var (a,true) => 𝐄'_var a
    | 𝐄''_var (a,false) => 𝐄'_var a ¯
    | (e + f)%lat => unprime e + unprime f
    | (e ⋅ f)%lat => unprime e ⋅ unprime f
    | (e ∩ f)%lat => unprime e ∩ unprime f
    | (e ⁺)%lat => unprime e ⁺
    end.

    Lemma is_clean_unprime e : is_clean (unprime e) = true.
    Proof.
      induction e as [|(?&[])| | | |];simpl;repeat rewrite andb_true_iff;auto.
    Qed.
    Lemma is_clean_comb e d : is_clean (comb e d) = true.
    Proof.
      revert d;induction e;intros d;simpl;auto;
        destruct d;simpl;repeat rewrite andb_true_iff;auto.
    Qed.
    
    Lemma comb_id_aux e : comb e true ≡ e /\ comb e false ≡ e ¯.
    Proof.
      induction e;simpl;try (destruct IHe1 as (-> & ->),IHe2 as (-> & ->))
                        ||destruct IHe as (-> & ->);split;auto.
    Qed.

    Lemma comb_id e : comb e true ≡ e.
    Proof. apply comb_id_aux. Qed.

    Lemma unprime_prime_id e : is_clean e = true -> unprime (prime e) = e.
    Proof.
      induction e as [| | | | |[]| ];simpl;
        discriminate||auto;repeat rewrite andb_true_iff;
          (intros (h1&h2);apply IHe1 in h1 as ->;apply IHe2 in h2 as ->)
          || (intro h;apply IHe in h as ->);auto.
    Qed.
      
    Global Instance unprime_morph : Proper (equiv ==> equiv) unprime.
    Proof.
      intros e f E;induction E;simpl;eauto.
      - destruct H;simpl;auto.
        + repeat rewrite (one_free_expr.ax_inter_comm (unprime e));auto.
        + rewrite (one_free_expr.ax_inter_comm (unprime e));auto.
          rewrite one_free_expr.ax_plus_inter.
          rewrite one_free_expr.ax_inter_idem.
          rewrite one_free_expr.ax_plus_com.
          rewrite (one_free_expr.ax_inter_comm (unprime f));auto.
        + rewrite one_free_expr.ax_plus_com;auto.
      - destruct H;simpl;eauto.
    Qed.

    Section s.
      Context {Σ : Set}.
      Context {σ : 𝕬[X′ → Σ]}.
      Context {hσ : forall a, ~ [] ∊ σ a}.
      
      Notation " ∙ " := (None).
      Notation Σ' := (option Σ)%type.

      Definition encode u : list Σ' := flat_map (fun a => [∙;Some a]) u.

      Definition decode (u : list Σ') :=
        flat_map (fun a => match a with Some a => [a] | _ => [] end) u.

      Lemma encode_decode u : decode (encode u) = u.
      Proof. induction u;simpl;congruence. Qed.

      Lemma encode_app u v : encode (u++v) = encode u++encode v.
      Proof.
        unfold encode;repeat rewrite flat_map_concat_map;simpl.
        rewrite map_app,concat_app;reflexivity.
      Qed.

      Definition σ' : 𝕬[X → Σ'] := fun a w => (exists u, w = encode u /\ σ (a,true) u)
                                           \/ (exists u, w = rev (encode u) /\ σ (a,false) u).

      Definition ϕ : language Σ' -> language Σ := fun L w => L (encode w).

      Global Instance ϕ_smaller : Proper (ssmaller ==> ssmaller) ϕ.
      Proof. intros L M I w Iu;apply I,Iu. Qed.
      
      Global Instance ϕ_equiv : Proper (sequiv ==> sequiv) ϕ.
      Proof. intros L M E;apply antisymmetry;apply ϕ_smaller;rewrite E;reflexivity. Qed.

      Lemma σ'_var_true a : σ (a,true) ≃ ϕ (σ' a).
      Proof.
        intro u;split;intros Iu.
        - left;exists u;tauto.
        - destruct Iu as [(v&E&I)|(v&E&I)].
          + rewrite <- encode_decode,E,encode_decode;assumption.
          + exfalso.
            destruct v as [|x v].
            * eapply hσ,I.
            * simpl in E.
              revert E;generalize (rev (encode v) ++ [Some x]);clear;induction u;intro.
              -- intros E;symmetry in E;apply app_eq_nil in E as (_&E);discriminate.
              -- intro E;simpl in E.
                 destruct l as [|? [|]];inversion E;subst.
                 apply IHu in H2;tauto.
      Qed.
      Lemma σ'_var_false a : σ (a,false) ≃ ϕ (σ' a ¯)%lang.
      Proof.
        intro u;split;intros Iu.
        - right;exists u;tauto.
        - destruct Iu as [(v&E&I)|(v&E&I)].
          + exfalso.
            destruct v as [|x v].
            * eapply hσ,I.
            * simpl in E.
              revert E;generalize (Some x::(encode v));clear;induction u;intro.
              -- discriminate.
              -- simpl.
                 destruct (rev(encode u)) as [|];simpl.
                 ++ discriminate.
                 ++ intro E;inversion E;subst.
                    apply (IHu l0);reflexivity.
          + rewrite <- encode_decode,<-(rev_involutive (encode _)).
            rewrite E,rev_involutive,encode_decode;assumption.
      Qed.

      Inductive valid : language Σ' :=
      | valid_encode u : u <> [] -> valid (encode u)
      | valid_rev u : valid u -> valid (rev u)
      | valid_app u v : valid u -> valid v -> valid (u++v).
      
      Fixpoint validb (u : list Σ') :=
        match u with
        | [∙;Some _] | [Some _;∙]  => true
        | ∙::Some _:: u | Some _ :: ∙ :: u => validb u
        | _ => false
        end.
      Fixpoint even n :=
        match n with
        | 0%nat => True
        | 1%nat => False
        | S (S n) => even n
        end.
      
      Lemma even_dec n : {even n} + {~even n}.
      Proof.
        cut ({even n /\ ~ even (S n)} + {~ even n /\ even (S n)});[|induction n];simpl;tauto.
      Qed.
                           
      Lemma even_iff n : even n <-> exists k, 2*k =n.
      Proof.
        cut (forall m, m <= n -> even m <-> exists k, 2*k = m).
        - intros h;apply h;lia.
        - induction n;simpl.
          + intros m I;replace m with O by lia.
            simpl;split;auto.
            intros _;exists 0%nat;reflexivity.
          + intros [|[|m]];intros I;[apply IHn;lia| |].
            * simpl;split;[tauto|].
              intros (k&E);lia.
            * simpl;rewrite IHn by lia;clear IHn.
              firstorder subst.
              -- exists (S x);lia.
              -- destruct x;[discriminate|].
                 exists x;lia.
      Qed.
      
      Lemma validb_even u : validb u = true -> even (# u).
      Proof.
        induction u as [|[|][|[|] u] ih] using len_induction;simpl;try discriminate.
        - intro E;destruct u;[|apply ih];simpl;auto.
        - intro E;destruct u;[|apply ih];simpl;auto.
      Qed.

      Lemma validb_app u v : even (# u) \/ even (# v)-> u <> [] -> v <> [] ->
                             validb (u++v) = validb u && validb v.
      Proof.
        intro hyp.
        destruct (even_dec (#u)) as [E|O].
        - clear hyp;revert E;induction u as [|[|] [|[|]u] ih] using len_induction;simpl;
            try tauto.
          + intros E _ Nv.
          assert (u = [] \/ u <> []) as [->|Nu]
              by (destruct u;[left;reflexivity|right;discriminate]).
            * simpl;destruct v;[tauto|reflexivity].
            * rewrite ih;simpl;auto.
              destruct u;simpl;[tauto|reflexivity].
          + intros E _ Nv.
            assert (u = [] \/ u <> []) as [->|Nu]
                by (destruct u;[left;reflexivity|right;discriminate]).
            * simpl;destruct v;[tauto|reflexivity].
            * rewrite ih;simpl;auto.
              destruct u;simpl;[tauto|reflexivity].
        - destruct hyp as [hyp|hyp];[tauto|].
          case_eq (validb u);simpl.
          + intro V;apply validb_even in V;tauto.
          + case_eq (validb (u++v));[|reflexivity].
            intros V;apply validb_even in V.
            rewrite app_length in V.
            exfalso.
            rewrite even_iff in V,O,hyp.
            destruct hyp as (k&E1),V as (k'&E2);apply O;exists (k'-k);lia.
      Qed.
            
      Lemma validb_encode u : u <> [] -> validb (encode u) = true.
      Proof.
         induction u as [|a [|b u]].
         - tauto.
         - simpl;auto.
         - intros _;apply IHu;discriminate.
      Qed.

      Lemma validb_rev u : validb (rev u) = validb u.
      Proof.
        induction u as [|a [|b u] ih] using len_induction;simpl;try tauto.
        rewrite app_ass.
        destruct (even_dec (#u)) as [E|O].
        - rewrite <- rev_length in E.
          assert (u = [] \/ rev u <> []) as [->|Nu]
              by (repeat rewrite <- length_zero_iff_nil;rewrite rev_length;
                  destruct (#u);[left;reflexivity|right;discriminate]).
          + simpl;destruct a as [|],b as [|];reflexivity.
          + rewrite validb_app;simpl;discriminate||auto.
            rewrite ih by (simpl;auto).
            destruct (validb u);simpl.
            * destruct a as [|],b as [|];reflexivity||(destruct u;reflexivity).
            * destruct a as [|],b as [|];
                try reflexivity||(destruct u;[tauto|reflexivity]).
        - case_eq (validb u);[intro V;apply validb_even in V;tauto|intros _].
          case_eq (validb (rev u++[b]++[a])).
          + intro V;exfalso.
            apply validb_even in V.
            rewrite app_length in V.
            cut (even (S(S (#u)))).
            * simpl;tauto.
            * rewrite rev_length in V;simpl in V.
              replace (S (S (#u))) with (#u+2)%nat by lia;assumption.
          + destruct u;[simpl in O;tauto|].
            intros _;destruct a as [|],b as [|];reflexivity.
      Qed.
      
      Lemma validb_spec : valid ≃ (fun u => validb u = true).
      Proof.
        intro u;split.
        - intro V;induction V.
          + apply validb_encode;auto.
          + rewrite validb_rev,IHV;reflexivity.
          + rewrite validb_app,IHV1,IHV2;auto.
            * left;apply validb_even;auto.
            * destruct u;discriminate.
            * destruct v;discriminate.
        - induction u as [|a [|b u] ih] using len_induction;simpl;try discriminate.
          + destruct a as [|];discriminate.
          + intro h.
            cut(valid [a;b]).
            * intros V'.
              assert (u = [] \/ u <> []) as [->|Nu]
                  by (destruct u;[left;reflexivity|right;discriminate]);auto.
              cut (valid ([a;b]++u));[tauto|].
              apply valid_app;auto.
              apply ih;simpl;auto.
              revert h;destruct (validb u);simpl;[reflexivity|].
              destruct a as [a|],b as [b|];try discriminate
                                               ||(destruct u;[tauto|discriminate]).
            * destruct a as [a|],b as [b|];try discriminate.
              -- replace [Some a;∙] with (rev(encode [a])) by reflexivity.
                 apply valid_rev,valid_encode;discriminate.
              -- replace [∙;Some b] with (encode [b]) by reflexivity.
                 apply valid_encode;discriminate.
      Qed.
      
      Lemma valid_reg (e : 𝐄' X) : ⟦e⟧σ' ≲ valid.
      Proof.
        induction e;rsimpl.
        - intros u F;exfalso;apply F.
        - intros u [I|I];destruct I as (v&->&I).
          + apply valid_encode.
            intros ->;eapply hσ,I.
          + apply valid_rev,valid_encode.
            intros ->;eapply hσ,I.
        - rewrite IHe1,IHe2.
          intros u (u1&u2&V1&V2&->);apply valid_app;auto.
        - rewrite IHe1;intros ? (I&_);auto.
        - rewrite IHe1,IHe2;intros u [V|V];auto.
        - rewrite IHe;intros u V.
          rewrite <- rev_involutive;apply valid_rev,V.
        - rewrite IHe;intros u (n&V);revert u V;clear.
          induction n;simpl.
          + intros u (u1&?&V&->&->).
            rewrite app_nil_r;assumption.
          + intros u (u1&u2&V1&V2&->).
            apply valid_app;auto.
      Qed.

      Lemma valid_encode_app u u1 u2:
        valid u1 -> valid u2 -> encode u = u1 ++ u2 ->
        exists v1 v2, u1 = encode v1 /\ u2 = encode v2 /\ u = v1++v2.
      Proof.
        clear σ hσ.
        revert u1 u2;induction u;simpl.
        - intros ? ? V _ E;symmetry in E;apply app_eq_nil in E as (->&_).
          apply validb_spec in V;discriminate.
        - intros [|x [|y u1 ]] u2 V1 V2 EE;
            try (apply validb_spec in V1;
                 discriminate||(destruct x as [|];discriminate)).
          inversion EE as [[E0 E1 E]];subst;clear EE;revert V1.
          assert (u1 = [] \/ u1 <> []) as [->|Nu]
              by (destruct u1;[left;reflexivity|right;discriminate]);auto.
          * intros _;exists [a],u;repeat split;auto.
          * intro V1;apply IHu in E as (v1&v2&->&->&->);auto.
            -- exists (a::v1),v2;simpl;auto.
            -- apply validb_spec in V1;simpl in V1.
               apply validb_spec.
               destruct u1;[tauto|apply V1].
      Qed.

      Lemma pad_unpad_expr e : is_clean e = true -> ⟦prime e⟧σ ≃ ϕ(⟦e⟧ σ').
      Proof.
        induction e as [| | | | |[]|];try discriminate;simpl;
          (rewrite andb_true_iff;intros (ih1&ih2);
           apply IHe1 in ih1;apply IHe2 in ih2)
          || (intro ih;apply IHe in ih)
          || intros _;simpl;rsimpl.
        - intros w;split.
          + intros F;exfalso;apply F.
          + intros F;exfalso;apply F.
        - apply σ'_var_true.
        - rewrite ih1,ih2;clear ih1 ih2 IHe1 IHe2.
          intros u;split.
          + intros (u1&u2&h1&h2&->).
            exists (encode u1),(encode u2);repeat split;auto using encode_app.
          + intros (u1&u2&h1&h2&E).
            pose proof h1 as V1;pose proof h2 as V2.
            apply valid_reg in V1;apply valid_reg in V2.
            destruct (valid_encode_app V1 V2 E) as (v1&v2&->&->&->).
            exists v1,v2;auto.
        - rewrite ih1,ih2;reflexivity.
        - rewrite ih1,ih2;reflexivity.
        - apply σ'_var_false.
        - rewrite ih;clear ih IHe.
          cut (forall n,(ϕ (⟦ e ⟧ σ') ^{n})%lang ≃ ϕ ((⟦ e ⟧ σ') ^{n})%lang);
            [intros h u;split;intros (n&In);exists n;apply h,In|].
          induction n;simpl.
          + split;[intros ->;reflexivity|intros E].
            destruct w;[reflexivity|discriminate].
          + rewrite IHn.
            intros u;split.
            * intros (u1&u2&I1&I2&->).
              exists (encode u1),(encode u2);repeat split;auto using encode_app.
            * intros (u1&u2&h1&h2&E).
              destruct n.
              -- rewrite h2,app_nil_r in E;subst.
                 exists u,[];rewrite app_nil_r;repeat split;auto.
              -- pose proof h1 as V1;apply valid_reg in V1.
                 assert (V2 : (⟦ e ⁺⟧ σ') u2) by (exists n;apply h2).
                 apply valid_reg in V2.
                 destruct (valid_encode_app V1 V2 E) as (v1&v2&->&->&->).
                 exists v1,v2;auto.
      Qed.

    End s.

    Proposition Completeness_one_free :
      forall e f : 𝐄' X , e ≡ f <-> e ≃ f.
    Proof.
      intros e f.
      split.
      - apply soundness_𝐄'.
      - intros E.
        rewrite <- comb_id,<-(comb_id f).
        rewrite <- unprime_prime_id by apply is_clean_comb.
        rewrite <- (unprime_prime_id (is_clean_comb e _)).
        apply unprime_morph.
        apply klm_completeness.
        apply rm_nil'. 
        intros Σ σ hσ.
        rewrite (@pad_unpad_expr _ _ hσ) by apply is_clean_comb.
        rewrite (@pad_unpad_expr _ _ hσ) by apply is_clean_comb.
        rewrite (soundness_𝐄' (comb_id e) _),(E _),<-(soundness_𝐄' (comb_id f) _).
        reflexivity.
    Qed.

    Corollary Completeness_one_free_inf :
      forall e f : 𝐄' X , e ≤ f <-> e ≲ f.
    Proof.
      intros e f;unfold smaller,𝐄'_Smaller;
        rewrite Completeness_one_free.
      split.
      - intros E A ? u Ie;apply E;now left.
      - intros E A ? u;split;rsimpl.
        + intros [I|I];auto.
          apply E,I.
        + intros I;now right.
    Qed.

End mirror.

Section main.
  Variable X : Set.
  Variable dec_X : decidable_set X.

  Proposition completeness_inf :
    forall e f : 𝐄 X, e ≤ f <-> e ≲ f.
  Proof.
    intros e f;split;[apply 𝐄_inf_incl_lang|].
    intros E.
    rewrite (expand_eq dec_X e).
    rewrite (𝐄_eq_equiv_lang (expand_eq dec_X e)) in E.
    apply Σ_small;intros g Ig.
    apply in_map_iff in Ig as ((A&[e'|])&<-&Ig);simpl.
    - rewrite <- (reduction_inf A f).
      apply seq_smaller;[reflexivity|].
      pose proof Ig as Oe.
      apply one_free_expand in Oe.
      pose proof (reduction_one_free A f) as Of.
      rewrite <- (E_to_E'_and_back Oe),<- (E_to_E'_and_back Of).
      apply inject_E'_to_E_inf,Completeness_one_free_inf.
      cut (e' ≲ ⦗ ⟨ f ⟩ A ⦘).
      + intros E' ? σ;repeat rewrite E_to_E'_lang by assumption;apply E'.
      + apply (reduction_spec Oe).
        rewrite <- E;apply 𝐄_inf_incl_lang.
        eapply Σ_big;eauto;[|reflexivity].
        apply in_map_iff;exists (A,Some e');auto. 
    - transitivity (1∩f);[|apply inf_ax_inter_r].
      pose proof (inter_1_spec dec_X f) as Ef.
      rewrite Ef.
      cut (test A ≲ 1∩f).
      + intros If.
        apply 𝐄_eq_equiv_lang in Ef;rewrite Ef in If.
        set (σ := (fun a (w : list False) => a ∈ A /\ w = []) : 𝕬[X→False]).
        cut ([]∊⟦test A⟧σ).
        * intros I;apply If,sum_lang in I as (t&It&Iu).
          apply in_map_iff in It as (B&<-&IB).
          apply test_is_one_inv in Iu as (hB&_).
          eapply Σ_big;eauto.
          -- apply in_map_iff;exists B;split;eauto.
          -- apply test_incl;intros b Ib.
             apply hB in Ib as (Ia&_);assumption.
        * apply test_is_one;[|reflexivity].
          intros a Ia;split;auto.
      + rewrite <- E;apply 𝐄_inf_incl_lang.
        rewrite test_inter_1.
        apply inter_smaller;[reflexivity|].
        eapply Σ_big;[eauto|apply in_map_iff;exists (A,None);auto|reflexivity].
  Qed.

  Theorem Completeness_of_Reversible_Kleene_Lattices :
    forall e f : 𝐄 X, e ≡ f <-> e ≃ f. 
  Proof.
    intros e f.
    rewrite (smaller_PartialOrder e f).
    unfold relation_conjunction,predicate_intersection,Basics.flip;simpl.
    repeat rewrite completeness_inf;symmetry.
    apply 𝐄_sem_PartialOrder.
  Qed.
    
End main.

