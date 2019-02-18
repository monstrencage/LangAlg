Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import language.

Section prime.
  Context { X : Set } {decX : decidable_set X}.
  Definition X' : Set := (X*bool)%type.
  Global Instance dec_X' : decidable_set X' := dec_prod decX Boolean.

  Definition balanced (A : list X') := forall a, (a,true) ∈ A <-> (a,false) ∈ A.
  Definition is_balanced (A : list X') :=
    forallb (fun a => inb (a,true) A && inb (a,false) A)(map fst A).

  Lemma is_balanced_spec A : is_balanced A = true <-> balanced A.
  Proof.
    unfold balanced,is_balanced;rewrite forallb_forall.
    setoid_rewrite andb_true_iff.
    setoid_rewrite inb_spec.
    setoid_rewrite in_map_iff.
    firstorder;subst.
    - destruct x0 as (a,[]);simpl;firstorder.
    - destruct x0 as (a,[]);simpl;firstorder.
  Qed.

  Definition prime_lst (A : list X) : list X' :=
    flat_map (fun a => [(a,true);(a,false)]) A.
  Definition unprime_lst : list X' -> list X := map fst.
  
  Lemma prime_lst_balanced A : balanced (prime_lst A).
  Proof.
    intro a;unfold prime_lst;repeat rewrite in_flat_map;simpl.
    split;intros (x&I&E);repeat destruct E as [E|E];inversion E;subst;exists a;auto.
  Qed.

  Lemma prime_unprime_incr A : A ⊆ prime_lst (unprime_lst A).
  Proof.
    intros (a,b) Ia;apply in_flat_map.
    exists a;split.
    - apply in_map_iff;exists (a,b);tauto.
    - destruct b;simpl;tauto.
  Qed.
  
  Lemma balanced_prime_unprime A : balanced A <-> prime_lst (unprime_lst A) ≈ A.
  Proof.
    unfold balanced,prime_lst,unprime_lst,equivalent.
    setoid_rewrite in_flat_map. 
    setoid_rewrite in_map_iff.
    split.
    - intros I (a,[]);(split;[intros (b&((x1&[])&<-&Ia)&[<-|[<-|F]])|]);simpl in *;
        try apply Ia || apply I,Ia || tauto.
      + intros Ia; exists a;split;[exists (a,true)|];tauto.
      + intros Ia; exists a;split;[exists (a,false)|];tauto.
    - intros h a;split;intros Ia;apply h;exists a;(split;[eexists;split;[|eassumption]|]);
        simpl;auto.
  Qed.
  Corollary balanced_In_unprime A : balanced A <-> forall a b, (a,b) ∈ A <-> a ∈ unprime_lst A.
  Proof.
    rewrite balanced_prime_unprime.
    split.
    - intros I a b;rewrite <- (I (a,b)) at 1.
      unfold prime_lst,unprime_lst.
      rewrite in_flat_map;setoid_rewrite in_map_iff;simpl.
      firstorder subst.
      + inversion H0;subst;eauto.
      + inversion H0;subst;eauto.
      + exists (fst x);split;[eauto|];destruct x as (?&[]),b;simpl;tauto.
    - intros I (a,b);rewrite (I a b).
      unfold prime_lst,unprime_lst.
      rewrite in_flat_map;setoid_rewrite in_map_iff;simpl.
      firstorder subst.
      + inversion H0;subst;eauto.
      + inversion H0;subst;eauto.
      + exists (fst x);split;[eauto|];destruct x as (?&[]),b;simpl;tauto.
  Qed.
  
  Global Instance flat_map_incl {A B : Set} f :
    Proper ((@incl A) ==> (@incl B)) (flat_map f).
  Proof.
    intros l m I;induction l;simpl.
    - apply incl_nil.
    - rewrite IHl by (intros b Ib;apply I;right;apply Ib).
      intros b Ib;apply in_app_iff in Ib as [Ib|Ib];[|apply Ib].
      apply in_flat_map;exists a;split;[|apply Ib].
      apply I;now left.
  Qed.
  
  Global Instance prime_lst_incl : Proper ((@incl X) ==> (@incl X')) prime_lst.
  Proof. unfold prime_lst;intros A B ->;reflexivity. Qed.

  Global Instance prime_lst_eq : Proper ((@equivalent X) ==> (@equivalent X')) prime_lst.
  Proof.
    unfold prime_lst;intros A B I;apply antisymmetry;apply prime_lst_incl;
      rewrite I;reflexivity.
  Qed.
  
  Global Instance unprime_lst_incl : Proper ((@incl X') ==> (@incl X)) unprime_lst.
  Proof. unfold prime_lst;intros A B ->;reflexivity. Qed.

  Global Instance unprime_lst_eq :
    Proper ((@equivalent X') ==> (@equivalent X)) unprime_lst.
  Proof.
    unfold unprime_lst;intros A B I;apply antisymmetry;apply unprime_lst_incl;
      rewrite I;reflexivity.
  Qed.
  
End prime.

Notation " X ′ " := (@X' X) (at level 0).
Notation " A $ " := (prime_lst A) (at level 0).
Notation " A £ " := (unprime_lst A) (at level 0).
