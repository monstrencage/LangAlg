(** Toolbox of simple definitions, lemmas and tactics. *)

Require Export Eqdep Setoid Morphisms Psatz List Bool.
Export ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Infix " ∘ " := Basics.compose (at level 40).
Hint Unfold Basics.compose.

Notation " π{ x } " := (proj1_sig x).

(** Lifting of a binary function with arguments of type [A] and values
of type [B] to a binary function with arguments of type [option A] and
values of type [option B]. *)
Definition option_bimap (A B : Type) (f : A -> A -> B) x y :=
  match (x,y) with
  | (Some a,Some b) => Some (f a b)
  | _ => None
  end.

(** Typeclass and notation for axiomatic equivalence relations. *)
Class Equiv (A : Set) := equiv : relation A.
Notation " e ≡ f " := (equiv e f) (at level 80).

(** Typeclass and notation for semantic equivalence relations. *)
Class SemEquiv (A : Type) := sequiv : relation A.
Notation " e ≃ f " := (sequiv e f) (at level 80).

(** Typeclass and notation for axiomatic preorder relations. *)
Class Smaller (A : Set) := smaller : relation A.
Notation " e ≤ f " := (smaller e f) (at level 80).

(** Typeclass and notation for semantic preorder relations. *)
Class SemSmaller (A : Type) := ssmaller : relation A.
Notation " e ≲ f " := (ssmaller e f) (at level 80).

(** Typeclass and notation for support functions *)
Class Support (T : Set -> Set -> Set) (X Y : Set) :=
  support : T X Y -> list X.
Notation " ⌊ e ⌋ " := (support e).

(** Typeclass and notation for functions extracting sets of
variables. *)
Class Alphabet (T : Set -> Set) (X : Set) := 𝒱 : T X -> list X.

Reserved Notation " | e | " (at level 40).
(** Typeclass and notation for size functions *)
Class Size X := size : X -> nat.
Notation " | e | " := (size e).

(** Typeclass and notation for semantic maps. *)
Class semantics (T : Set -> Set) (D : Set -> Type) (X : Set) (A : Set)
  := interprete : (X -> D A) -> T X -> D A.
Notation " ⟦ e ⟧ σ " := (interprete σ e) (at level 75).

(** The following two definitions describe the standard way of
relating two terms through their semantics. *)
Definition semantic_equality
       (T : Set -> Set) (D : Set -> Type)  (X : Set)
       `{ forall A : Set, SemEquiv (D A) }
       `{ forall A : Set, semantics T D X A } : SemEquiv (T X) :=
  fun x y => forall A : Set,forall σ : X -> D A, ⟦x⟧σ ≃ ⟦y⟧σ. 
Definition semantic_containment
       (T : Set -> Set) (D : Set -> Type) (X : Set)
       `{ forall A : Set, SemSmaller (D A) }
       `{ forall A : Set, semantics T D X A} : SemSmaller (T X) :=
  fun x y => forall A : Set,forall σ : X -> D A, ⟦x⟧σ ≲ ⟦y⟧σ.

Hint Unfold semantic_containment semantic_equality ssmaller sequiv: semantics.
Global Instance semantic_equality_Equivalence
       (T : Set -> Set) (D : Set -> Type) (X : Set)
       `{eqA: forall A : Set, SemEquiv (D A)}
       `{S : forall A, semantics T D X A}
       `{forall A : Set, Equivalence (eqA A)} :
  Equivalence (@semantic_equality T D X eqA S).
Proof.
  split;intro;unfold semantic_equality;firstorder.
  - symmetry;auto.
  - etransitivity;auto.
Qed.

Global Instance semantic_containment_PreOrder
       (T : Set -> Set) (D : Set -> Type) (X : Set)
       `{inclA: forall A : Set, SemSmaller (D A)}
       `{S : forall A, semantics T D X A}
       `{forall A : Set, PreOrder (inclA A)} :
  PreOrder (@semantic_containment T D X inclA S).
Proof.
  split;intro;unfold semantic_containment;firstorder.
  etransitivity;auto.
Qed.

Global Instance semantic_containment_PartialOrder
       (T : Set -> Set) (D : Set -> Type) (X : Set)
       `{eqA: forall A : Set, SemEquiv (D A)}
       `{inclA: forall A : Set, SemSmaller (D A)}
       `{S : forall A, semantics T D X A}
       `{equivA : forall A : Set, Equivalence (eqA A)}
       `{preordA : forall A : Set, PreOrder (inclA A)}
       `{partordA : forall A : Set, PartialOrder (eqA A) (inclA A)} :
  @PartialOrder
    _ _ (@semantic_equality_Equivalence T D X eqA S equivA)
    _ (@semantic_containment_PreOrder T D X inclA S preordA).
Proof.
  split;unfold semantic_containment,semantic_equality,ssmaller,sequiv
    in *.
  - intros hyp;split;intros A σ;firstorder;apply partordA;eauto.
    apply equivA;auto.
  - intros (h1&h2);intros A σ;apply partordA;split;[apply h1|apply h2].
Qed.
  

(** * Decidable sets *)

(** The class of [decidable_set X] contains a binary function
associating to every pair of elements of type [X] a boolean and a
proof that this function encodes faithfully equality over [X]. *)
Class decidable_set X :=
  { eqX : X -> X -> bool;
    eqX_eq : forall x y, reflect (x = y) (eqX x y)}.

Section decidable.
  Context { X : Set }.
  Context { D : decidable_set X }.
 
  (** This lemma is the preferred way of translating back and forth
      between boolean and propositional equality. *)
  Lemma eqX_correct :
    forall x y : X, eqX x y = true <-> x = y.
  Proof. intros;symmetry;apply reflect_iff,eqX_eq. Qed.

  (** The next few lemmas are useful on occasion.  *)
  Lemma eqX_false :
    forall x y, eqX x y = false <-> x <> y.
  Proof. intros;rewrite<-(eqX_correct _),not_true_iff_false;tauto. Qed.

  Lemma X_dec (x y : X) : {x = y} + {x <> y}.
  Proof.
    case_eq (eqX x y).
    - now intro h;left;apply (eqX_correct _).
    - intro h;right;intro E;apply (eqX_correct _) in E.
      contradict E;rewrite h;auto.
  Qed.

  Lemma eqX_refl x : eqX x x = true.
  Proof. apply eqX_correct;reflexivity. Qed.

  (** Whenever we have a decidable set, we can define the following
  replacement function. *)
  Definition replace a b := (fun n => if eqX n a then b else n).

End decidable.

(* begin hide *)
Ltac destruct_eqX x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (@X_dec _ _ x o) as [Ei |Ni];
  [pose proof Ei as X;apply (@eqX_correct _ _) in X;
   try rewrite Ei in *
  |pose proof Ni as X;apply (@eqX_false _ _) in X];
  repeat rewrite X in *;repeat rewrite eqX_refl in *;clear X.

(* end hide *)

Notation " {| a \ b |} " := (replace a b).
  
(** The set of natural numbers is decidable. *)
Global Instance NatNum : decidable_set nat :=
  Build_decidable_set PeanoNat.Nat.eqb_spec.


(** The set of natural booleans is decidable. *)
Global Instance Boolean : decidable_set bool.
Proof.
  cut (forall x y, reflect (x = y) (eqb x y));
  [apply Build_decidable_set|].
  intros;apply iff_reflect;symmetry;apply eqb_true_iff.
Qed.

(** If [A] and [B] are decidable, then so is their Cartesian product. *)
Lemma dec_prod A B :
  decidable_set A -> decidable_set B -> decidable_set (A*B).
Proof.
  intros d1 d2.
  set (eqp := fun x y =>
                (@eqX _ d1 (fst x) (fst y))
                  && (@eqX _ d2 (snd x) (snd y))).
  assert (eqp_spec : forall x y, reflect (x=y) (eqp x y));
    [|apply (Build_decidable_set eqp_spec)].
  intros (x1,x2) (y1,y2);unfold eqp;simpl;
  destruct (@eqX_eq _ d1 x1 y1);destruct (@eqX_eq _ d2 x2 y2);
  apply ReflectT||apply ReflectF;
  (rewrite e,e0;reflexivity)||(intro h;inversion h;tauto).
Qed.

(** If [A] is decidable, then so is [option A]. *)
Lemma dec_option (A : Set) :
  decidable_set A -> decidable_set (option A).
Proof.
  intros d1.
  set (eqlbl :=
         fun l1 l2 : option A =>
           match (l1,l2) with
           | (None,None) => true
           | (Some x,Some y) => eqX x y
           | _ => false
           end).
  exists eqlbl;intros [|] [|];apply iff_reflect;unfold eqlbl;simpl;split;
    try discriminate || tauto.
  * intros E;inversion E; apply eqX_refl.
  * rewrite eqX_correct;intros ->;reflexivity.
Qed.


(** * Lists *)

Notation " # " := length. 
Open Scope list.
(** ** General lemmas *)
(** Strong induction on the length of a list. *)
Lemma len_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, (forall m, length m <= length l -> P m) -> P (a::l)) -> forall l, P l.
Proof.
  intros h0 hn l;remember (length l) as N.
  assert (len:length l <= N) by lia.
  clear HeqN;revert l len;induction N.
  - intros [|a l];simpl;try lia;auto.
  - intros [|a l];simpl;auto.
    intro len;apply hn;intros m;simpl;intros len'.
    apply IHN;lia.
Qed.

(** Induction principle for lists in the reverse order. *)
Lemma rev_induction {A} (P : list A -> Prop) :
  P [] -> (forall a l, P l -> P (l++[a])) -> forall l, P l.
Proof.
  intros;rewrite <- rev_involutive;induction (rev l);simpl;auto.
Qed.

(** Levi's lemma. *)
Lemma Levi {A:Set} (u v u' v' : list A) :
  u++v = u'++v' -> exists w, (u = u'++w /\ v' = w++v) \/ (u'=u++w /\ v = w++v').
Proof.
  revert v u' v';induction u as [|a u];intros v u' v' E.
  - exists u';right;simpl in *;tauto.
  - destruct u' as [|b u'].
    + exists (a::u);left;simpl in *;subst;tauto.
    + simpl in E;inversion E as [[e ih]];clear E;subst.
      apply IHu in ih as (w&[h|h]);destruct h as (->&->);exists w;simpl;tauto.
Qed.

(** If the list [l++a::l'] is duplicate free, so are [l] and [l']. *)
Lemma NoDup_remove_3 {A} (l l' : list A) (a : A) :
    NoDup (l ++ a :: l') -> NoDup l /\ NoDup l'.
Proof.
  revert l' a;induction l;intros l' b;simpl;
    repeat rewrite NoDup_cons_iff.
  - intros (_&h);split;auto;apply NoDup_nil.
  - rewrite in_app_iff;intros (N&hyp);apply IHl in hyp as (h1&h2);
      repeat split;auto.
Qed.

(** Filtering a concatenation is the same as concatenating filters. *)
Lemma filter_app {A} (f : A -> bool) (l m : list A) :
  filter f (l++m) = filter f l ++ filter f m.
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;auto.
  f_equal;auto.
Qed.

(** Filtering reduces the length of the list. *)
Lemma filter_length {A} (f : A -> bool) l :
  # (filter f l) <= # l .
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;lia.
Qed.

(** The following lemma give a more precise description. *)
Lemma filter_length_eq {A} (f : A -> bool) l :
  # (filter f l) + # (filter (fun x => negb (f x)) l) = # l.
Proof.
  induction l;simpl;auto.
  destruct (f a);simpl;lia.
Qed.

(** [filter] and [map] commute. *)
Lemma filter_map {A B} (f : A -> bool) (g : B -> A) l :
  filter f (map g l) = map g (filter (f∘g) l).
Proof.
  induction l;simpl;auto.
  unfold Basics.compose;destruct (f (g a));simpl;auto.
  f_equal;auto.
Qed.

(** [filter] only depends on the values of the filtering function, not
its implementation. *)
Lemma filter_ext_In {A} (f g : A -> bool) l :
  (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intro hyp;induction l as [|x l];simpl;auto.
  case_eq (f x);case_eq (g x).
  - intros _ _; f_equal;apply IHl;intros y I;apply hyp;now right.
  - intros h1 h2;exfalso.
    cut (true=false);[discriminate|].
    rewrite <-h1,<-h2;apply hyp;now left.
  - intros h1 h2;exfalso.
    cut (true=false);[discriminate|symmetry].
    rewrite <-h1,<-h2;apply hyp;now left.
  - intros _ _;apply IHl;intros y I;apply hyp;now right.
Qed.

Lemma filter_ext {A} (f g : A -> bool) l :
  (forall x, f x = g x) -> filter f l = filter g l.
Proof. intros hyp;apply filter_ext_In;intros x _;apply hyp. Qed.

(** Filtering with the predicate [true] does not modify the list. *)
Lemma filter_true {A} (l : list A) :
  filter (fun _ => true) l = l.
Proof. induction l;simpl;auto;congruence. Qed.

(** Filtering preserves the property [NoDup] (absence of duplicates). *)
Lemma filter_NoDup {A} (f : A -> bool) l :
  NoDup l -> NoDup (filter f l).
Proof.
  induction l;simpl;auto.
  destruct (f a);repeat rewrite NoDup_cons_iff;
    try rewrite filter_In;tauto.
Qed.

(** If two concatenations are equal, and if the two initial factors
have the same length, then the factors are equal. *)

Lemma length_app {A} (l1 l2 m1 m2 : list A) :
  # l1 = # m1 -> l1++l2 = m1++m2 -> l1 = m1 /\ l2 = m2.
Proof.
  intros El Ea.
  cut (l1 = m1).
  - intros ->;split;auto.
    eapply app_inv_head,Ea.
  - transitivity (firstn (length l1) (l1++l2)).
    + rewrite firstn_app,PeanoNat.Nat.sub_diag;simpl.
      rewrite app_nil_r,firstn_all;reflexivity.
    + rewrite Ea,El.
      rewrite firstn_app,PeanoNat.Nat.sub_diag;simpl.
      rewrite app_nil_r,firstn_all;reflexivity.
Qed.

(** ** Lists as finite sets *)

(** We associate the traditional containment symbol to list
inclusion. *)
Infix " ⊆ " := incl (at level 80).

(** We use the following symbol to denote the membership predicate. *)
Infix " ∈ " := In (at level 60).


(** We say that two lists are equivalent if they contain the same
elements. *)
Definition equivalent A l m := forall x : A , x ∈ l <-> x ∈ m.
Infix " ≈ " := equivalent (at level 80).

(** We now establish that [≈] is a congruence, and that [⊆] is a
partial order.*)
Global Instance equivalent_Equivalence T : Equivalence (@equivalent T).
Proof.
  split.
  - intros l x; firstorder.
  - intros l m h x; firstorder.
  - intros l m h n h' x; firstorder.
Qed.
Global Instance incl_PreOrder T : PreOrder (@incl T).
Proof.
  split.
  - intros l x ;firstorder.
  - intros l m h n h' x;eauto.
Qed.
Global Instance incl_PartialOrder T :
  PartialOrder (@equivalent T) (@incl T).
Proof.
  intros l m;split.
  - intros h;split;intro x; firstorder.
  - intros (h1 & h2);intro x; firstorder.
Qed.

(** Concatenation preserves both relations. *)
Global Instance incl_app_Proper T :
  Proper ((@incl T) ==> (@incl T) ==> (@incl T)) (@app T).
Proof. intros l m h1 n o h2 x;repeat rewrite in_app_iff;intuition. Qed.
Global Instance equivalent_app_Proper T :
  Proper ((@equivalent T) ==> (@equivalent T) ==> (@equivalent T))
         (@app T).
Proof. intros l m h1 n o h2 x;repeat rewrite in_app_iff;firstorder. Qed.

(** The operation of adding an element to a list preserves both
relations. *)
Global Instance incl_cons_Proper T a :
  Proper ((@incl T) ==> (@incl T)) (cons a).
Proof. intros l m h x;simpl in *;intuition. Qed.
Global Instance equivalent_cons_Proper T a :
  Proper ((@equivalent T) ==> (@equivalent T)) (cons a).
Proof. intros l m h x;simpl in *;firstorder. Qed.

(** For any function [f], the list morphism [map f] preserves both
relations. *)
Global Instance map_incl_Proper {A B} (f : A -> B) :
  Proper (@incl A ==> @incl B) (map f).
Proof.
  intros l m I x;rewrite in_map_iff,in_map_iff.
  intros (y&<-&J);exists y;split;auto.
Qed.
Global Instance map_equivalent_Proper {A B} (f : A -> B) :
  Proper (@equivalent A ==> @equivalent B) (map f).
Proof.
  intros l m I x;rewrite in_map_iff,in_map_iff.
  split;intros (y&<-&J);exists y;split;auto;apply I,J.
Qed.

(** For any boolean predicate [f], the filtering map [filter f]
preserves both relations. *)
Global Instance filter_incl_Proper {A} (f : A -> bool) :
  Proper (@incl A ==> @incl A) (filter f).
Proof.
  intros l m I x;repeat rewrite filter_In.
  intros (J&->);split;auto.
Qed.
Global Instance filter_equivalent_Proper {A} (f : A -> bool) :
  Proper (@equivalent A ==> @equivalent A) (filter f).
Proof.
  intros l m I x;repeat rewrite filter_In.
  split;intros (J&->);split;auto;apply I,J.
Qed.

(** The lemmas [In_incl_Proper] and [In_equivalent_Proper] are
completely tautological, but turn out to be useful for technical
reasons. *)
Global Instance In_incl_Proper {A} (x : A):
  Proper ((@incl A) ==> Basics.impl) (In x).
Proof. intros l m I;firstorder. Qed.
Global Instance In_equivalent_Proper {A} (x : A):
  Proper ((@equivalent A) ==> iff) (In x).
Proof. intros l m I;firstorder. Qed.


(** The following simple facts about inclusion are convenient to have
in our toolbox. *)
Lemma incl_nil T (A : list T) : [] ⊆ A.
Proof. intros x;firstorder. Qed.
Lemma incl_app_or T (A B C : list T) : A ⊆ B \/ A ⊆ C -> A⊆B++C.
Proof. intros [?|?];auto using incl_appl, incl_appr. Qed.
Create HintDb eq_list.
Lemma incl_app_split {A} (l m p : list A) :
  l++m ⊆ p <-> l⊆ p /\ m ⊆ p.
Proof. unfold incl;setoid_rewrite in_app_iff;firstorder. Qed.
Lemma rev_equivalent {A} (l : list A) : rev l ≈ l.
Proof. intro;rewrite <- in_rev;reflexivity. Qed.
Hint Resolve incl_appl incl_appr incl_nil app_assoc : eq_list.

Lemma in_concat {A : Set} (x : A) l : x ∈ concat l <-> exists y, x ∈ y /\ y ∈ l.
Proof.
  revert x;induction l;intro x;simpl.
  - firstorder.
  - rewrite in_app_iff,IHl.
    split.
    + intros [Ix|(y&Ix&Iy)].
      * exists a;tauto.
      * exists y;tauto.
    + intros (y&Ix&[<- | Iy]).
      * left;tauto.
      * right;exists y;tauto.
Qed.

(** If a boolean predicate [f] fails to be true for every element of a
list [l], then there must exists a witnessing element [y] falsifying
[f]. This is an instance of a classical principle holding
constructively when restricted to decidable properties over finite
domains. *)
Lemma forall_existsb {A} (f : A -> bool) l :
  ~ (forall x, x ∈ l -> f x = true) -> exists y, y ∈ l /\ f y = false.
Proof.
  induction l as [|a l].
  - intro h;exfalso;apply h.
    intros x;simpl;tauto.
  - intros h;case_eq (f a).
    + intro p;destruct IHl as (y&I&E).
      * intro h';apply h;intros x [<-|I];auto.
      * exists y;split;auto.
        now right.
    + intro E;exists a;split;auto.
      now left.
Qed.

(** ** Subsets of a list *)
Fixpoint subsets {A : Set} (l : list A) :=
  match l with
  | [] => [[]]
  | a::l => map (cons a) (subsets l)++subsets l
  end.

Lemma subsets_In {A : Set}(l : list A) :
  forall m, m ∈ subsets l -> m ⊆ l.
Proof.
  induction l as [|a l];intros m;simpl;try rewrite in_app_iff.
  - intros [<-|F];[reflexivity|tauto].
  - rewrite in_map_iff;intros [(m'&<-&I)|I];apply IHl in I as ->.
    + reflexivity.
    + intro;simpl;tauto.
Qed.

Lemma incl_cons_disj {A : Set} (a : A) m l :
  m ⊆ a :: l -> m ⊆ l \/ exists m', m ≈ a::m' /\ m' ⊆ l.
Proof.
  induction m as [|b m];simpl.
  - intro;left;apply incl_nil.
  - intros I.
    destruct IHm as [IH|(m'&E&IH)].
    + intros x Ix;apply I;now right.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m;split;[reflexivity|assumption].
      * left;intros c [<-|Ic];[assumption|].
        apply IH,Ic.
    + assert (I': b ∈ (b::m)) by now left.
      apply I in I' as [<-|Ib].
      * right;exists m';split;[|assumption].
        rewrite E;clear;intro;simpl;tauto.
      * right;exists (b::m');split.
        -- rewrite E;intro;simpl;tauto.
        -- intros c [<-|Ic];[assumption|].
           apply IH,Ic.
Qed.

Lemma subsets_spec {A : Set} (l : list A) :
  forall m, m ⊆ l <-> exists m', m' ∈ subsets l /\ m ≈ m'.
Proof.
  intro m;split.
  - revert m; induction l as [|a l];intros m L.
    + exists [];split;[simpl;tauto|].
      apply incl_PartialOrder;split;[assumption|apply incl_nil].
    + simpl;destruct (incl_cons_disj L) as [h|(m'&E&h)];apply IHl in h as (m''&I&E').
      * exists m'';split;[|assumption].
        rewrite in_app_iff;tauto.
      * exists (a::m'');split.
        -- apply in_app_iff;left;apply in_map_iff;exists m'';tauto.
        -- rewrite E,E';reflexivity.
  - intros (m'&I&->);apply subsets_In,I.
Qed.

Lemma subsets_NoDup {A : Set} (k l : list A) :
  NoDup l -> k ∈ subsets l -> NoDup k.
Proof.
  revert k;induction l as [|a l];intros k;simpl.
  - intros h [<-|F];tauto.
  - rewrite NoDup_cons_iff,in_app_iff,in_map_iff.
    intros (nI&nd) [(k'&<-&Ik')|Ik].
    + apply NoDup_cons.
      * intro h;apply nI,(subsets_In Ik'),h.
      * apply IHl;tauto.
    + apply IHl;tauto.
Qed.

(** ** Lists over a decidable set *)
Section dec_list.
  Context { A : Set }.
  Context { dec_A : decidable_set A }.

  (** Boolean equality for lists *)
  Fixpoint equal_list l m :=
    match (l,m) with
    | ([],[]) => true
    | (a::l,b::m) => eqX a b && equal_list l m
    | _ => false
    end.

  Lemma equal_list_spec l m : reflect (l = m) (equal_list l m).
  Proof.
    apply iff_reflect;revert m;induction l as [|a l];intros [|b m];
    simpl;split;try reflexivity||discriminate;
    rewrite andb_true_iff,<-IHl.
    - intro h;inversion h;split;auto;apply eqX_refl.
    - intros (h&->);apply eqX_correct in h as ->;reflexivity.
  Qed.
                                
  (** The set of lists of [A]s is decidable. *)
  Global Instance dec_list : decidable_set (list A).
  Proof. apply (Build_decidable_set equal_list_spec). Qed.

  (** Boolean predicate testing whether an element belongs to a list. *)
  Definition inb (n : A) l := existsb (eqX n) l.
  Lemma inb_spec n l : inb n l = true <-> n ∈ l.
  Proof.
    case_eq (inb n l);intro E;unfold inb in *.
    - apply existsb_exists in E as (y&I&E).
      apply eqX_correct in E as ->;tauto.
    - rewrite <- not_true_iff_false, existsb_exists in E;split.
      -- discriminate.
      -- intro I;exfalso;apply E;eexists;split;[eauto|];apply eqX_refl.
  Qed.

  Lemma inb_false n l : inb n l = false <-> ~ n ∈ l.
  Proof. rewrite <- inb_spec,not_true_iff_false;reflexivity. Qed.

  (** This boolean predicate allows us to use the excluded middle with
  the predicate [In]. *)
  Lemma inb_dec n l :
    { inb n l = true /\ n ∈ l } + { inb n l = false /\ ~ n ∈ l }.
  Proof.
    case_eq (inb n l);intro E;[left|right];rewrite <- inb_spec;auto.
    split;auto;rewrite E;discriminate.
  Qed.
  Lemma In_dec (n : A) l : { n ∈ l } + { ~ n ∈ l }.
  Proof.
    case_eq (inb n l);intro E;[left|right];rewrite <- inb_spec,E;auto.
  Qed.

  (** If [i] is in [l], then [l] can be decomposed as [m++i::n], where
  [n] doesn't contain [i]. *)
  Lemma in_split_strict (i : A) l :
   i ∈ l -> exists m n, l = m++(i::n) /\ ~ i ∈ n.
  Proof.
    induction l;simpl.
    - tauto.
    - intros [->|I].
      + destruct (In_dec i l);eauto.
        * destruct (IHl i0) as (m&n&->&N).
          exists (i::m);exists n; split;eauto.
        * exists [];exists l;split;auto.
      + destruct (IHl I) as (m&n&->&N).
        exists (a::m);exists n; split;eauto.
  Qed.
  
  (** Removing an element from a list. *)
  Definition rm (x : A) := filter (fun y => negb (eqX x y)).
  Hint Unfold rm.
  
  Lemma in_rm x y l : x ∈ (rm y l) <-> x <> y /\ x ∈ l .
  Proof.
    unfold rm;rewrite filter_In,negb_true_iff,<-not_true_iff_false.
    rewrite eqX_correct;firstorder.
  Qed.

  (** Removing from [m] an element that was not in [m] in the first
  place does not modify [m]. *)
  Lemma rm_notin a m : ~ a ∈ m -> rm a m = m.
  Proof.
    induction m;simpl;auto.
    intros N;rewrite IHm;[|intro I;apply N;tauto].
    set (e:=eqX a a0);assert (E:eqX a a0 = e) by auto;
    destruct e;simpl;auto.
    apply eqX_correct in E as ->;exfalso;apply N;tauto.
  Qed.

  (** [rm a] commutes with concatenation. *)
  Lemma rm_app a l m : rm a (l++m) = rm a l ++ rm a m.
  Proof. apply filter_app. Qed.

  (** [rm] reduces the length. *)
  Lemma rm_length x l :
    # (rm x l) <= # l.
  Proof.
    induction l;simpl;[lia|].
    destruct (eqX x a);simpl;lia.
  Qed.

  (** If [x] is in [l], then [rm x l] is strictly smaller than l. *)
  Lemma rm_length_in x l :
    x ∈ l -> # (rm x l) < # l.
  Proof.
    induction l;simpl;[tauto|].
    intros [->|I].
    - rewrite eqX_refl;simpl;pose proof (rm_length x l) as Hyp.
      lia.
    - apply IHl in I;destruct (eqX x a);simpl;lia.
  Qed.
  
  (** [rm a] preserves both [⊆] and [≈]. *)
  Global Instance rm_incl_Proper a :
    Proper (@incl A ==> @incl A) (rm a).
  Proof.
    intros l m I x;rewrite in_rm,in_rm.
    intros (N&J);split;auto.
  Qed.
  Global Instance rm_equivalent_Proper a :
    Proper (@equivalent A ==> @equivalent A) (rm a).
  Proof.
    intros l m I x;rewrite in_rm,in_rm.
    split;intros (N&J);split;auto;apply I,J.
  Qed.

  (** If [l] is contained in [m] and doesn't contain duplicates, 
      then it must be shorter than [m]. *)
 
  Lemma NoDup_length (l m : list A) :
    l ⊆ m -> NoDup l -> # l <= # m.
  Proof.
    revert m;induction l;simpl;intros m E ND.
    - lia.
    - cut (# l <= # (rm a m)).
      + assert (Ia : a ∈ m) by (apply E;now left).
        apply rm_length_in in Ia.
        lia.
      + apply NoDup_cons_iff in ND as (Ia&ND).
        apply IHl;auto.
        intros x I;apply in_rm;split.
        * intros ->;tauto.
        * apply E;now right.
  Qed.
  
  (** Boolean function implementing containment test. *)  
  Definition inclb (a b : list A) :=
    forallb (fun x => inb x b) a.
  
  Lemma inclb_correct a b : inclb a b = true <-> a ⊆ b.
  Proof.
    unfold incl,inclb;rewrite forallb_forall.
    setoid_rewrite inb_spec;intuition.
  Qed.

  (** [φ1 ⧼l⧽ φ2] is a function that combines [φ1] and [φ2] as
  illustrated by the following pair of lemmas. *)
  Definition seq_morph {B} (φ1 φ2 : A -> B) l :=
    fun x => if inb x l then φ1 x else φ2 x.

  Notation " f ⧼ l ⧽ g " := (seq_morph f g l) (at level 60).

  (** If [x] is in the list [l], then its image by [seq_morph φ1 φ2 l]
      is equal to its image by [φ1]. *)
  Lemma seq_morph_in {B} (φ1 φ2 : A -> B) l x :
    x ∈ l -> (φ1 ⧼l⧽ φ2) x = φ1 x.
  Proof.
    unfold seq_morph;intro I;apply inb_spec in I as ->;auto.
  Qed.
  (** Otherwise, [φ1 ⧼l⧽ φ2] sends [x] to [φ2 x]. *)
  Lemma seq_morph_not_in {B} (φ1 φ2 : A -> B) l x :
    ~ x ∈ l -> (φ1 ⧼l⧽ φ2) x = φ2 x.
  Proof.
    unfold seq_morph;intro I;apply inb_false in I as ->;auto.
  Qed.

  (** [seq_morph] uses its argument list as a set, so replacing a list
  with an equivalent list doesn't change the function. *)
  Lemma seq_morph_equivalent {B} l m
        (f g : A -> B) x :
    l ≈ m -> (f ⧼l⧽ g) x = (f ⧼m⧽ g) x.
  Proof.
    intros E;destruct (In_dec x l).
    - rewrite seq_morph_in;auto.
      rewrite seq_morph_in;auto;apply E,i.
    - rewrite seq_morph_not_in;auto.
      rewrite seq_morph_not_in;auto.
      rewrite <- E;auto.
  Qed.

End dec_list.  

(** ** Bimap *)

(** [bimap f l m] computes the list containing every element of the
    shape [f x y], with [x] in [l] and [y] in [m]. For instance, if we
    take [f] to be the pairing function that associate to [x] and [y]
    the pair [(x,y)], then [bimap f l m] is the Cartesian product of
    the lists [l] and [m]. *)
Definition bimap A B C (f : A -> B -> C) l m :=
  flat_map (fun a => map (f a) m) l.

Lemma in_bimap A B C (f : A -> B -> C) l m x :
  x ∈ (bimap f l m) <-> exists a b, f a b = x /\ a ∈ l /\ b ∈ m.
Proof.
  unfold bimap;rewrite in_flat_map;setoid_rewrite in_map_iff;firstorder.
Qed.

(** We can absorb a [map] inside a [bimap]. *)
Lemma map_bimap A B C D (g : C -> D) (f : A -> B -> C) l m :
  map g (bimap f l m) = bimap (fun x y => g (f x y)) l m.
Proof.
  unfold bimap;repeat rewrite flat_map_concat_map.
  rewrite concat_map,map_map;f_equal.
  apply map_ext;intro;apply map_map.
Qed.

(** [bimap f] is monotone. *)
Global Instance bimap_equiv {A B C} (f : A -> B -> C) :
  Proper ((@equivalent A) ==> (@equivalent B)==> (@equivalent C)) (bimap f).
Proof.
  intros l1 l2 El m1 m2 Em x.
  repeat rewrite in_bimap.
  setoid_rewrite El;setoid_rewrite Em;tauto.
Qed.
(** * Invertible functions *)

(** [ψ] is the inverse on [φ] in the list [A] if [ψ∘φ] is the
identity on the elements of [A]. *)
Definition inverse {X Y: Set} (φ : X -> Y) ψ A :=
  forall x, x ∈ A -> ψ (φ x) = x.

(** [φ] is injective on [A] if it admits an inverse on [A]. *)
Definition injective {X Y: Set} (φ : X -> Y) A :=
  exists ψ, inverse φ ψ A.

(** For we can compute an inverse of a composite function by composing
the inverses of its parts in reverse order. *)
Lemma inverse_composition {X Y Z : Set}
      (f : X -> Y) f' (g : Y -> Z) g' A :
  inverse f f' A  -> inverse g g' (List.map f A) ->
  inverse (g∘f) (f'∘g') A.
Proof.
  intros h1 h2 x I;unfold Basics.compose.
  rewrite h2,h1;auto.
  apply in_map_iff;eauto.
Qed.
Lemma injective_compose {X Y Z : Set}
      (f : X -> Y) (g : Y -> Z) A :
  injective f A -> injective g (List.map f A) -> injective (g∘f) A.
Proof.
  intros (f'&If) (g'&Ig);eexists;apply inverse_composition;eauto.
Qed.

(** The function [{|b\a|}] is the inverse of [{|a\b|}] on any
list that does not contain the element [b]. *)
Lemma inverse_replace {X : Set} `{decidable_set X} (a b : X) A :
  ~ b ∈ A -> inverse {| a \ b |} {| b \ a |} A.
Proof.
  intro N;intros x I.
  unfold replace;case_eq (eqX x a);[rewrite eqX_correct;intros ->
                                   |intros _].
  - unfold replace;case_eq (eqX b b);[auto|rewrite eqX_false;tauto].
  - unfold replace;case_eq (eqX x b);
    [rewrite eqX_correct;intros -> |intros _];tauto.
Qed.

Lemma injective_replace {X : Set} `{decidable_set X} (a b : X) A :
  ~ b ∈ A -> injective {| a \ b |} A.
Proof. intro N;eexists;apply inverse_replace,N. Qed.

(** The following trivial lemmas are used in many places in the
proof. *)
Definition incr a b := a + b.
Notation " ⨥ " := incr.
Definition decr a b := b - a.
Notation " ⨪ " := decr.
Hint Transparent incr decr.
Hint Unfold decr incr.

Lemma inverse_add_left n A :
  inverse (⨥ n) (⨪ n) A.
Proof. intro;autounfold;lia. Qed.

Lemma injective_add_left n A : injective (⨥ n) A.
Proof. eexists;apply inverse_add_left. Qed.


(* begin hide *)
Notation " f ⧼ l ⧽ g " := (seq_morph f g l) (at level 60).

(** Tactics *)
Lemma andb_prop_iff x y: Is_true (x && y) <-> Is_true x /\ Is_true y.
Proof.
  split; [apply andb_prop_elim | apply andb_prop_intro].
Qed.

Lemma orb_prop_iff x y: Is_true (x || y) <-> Is_true x \/ Is_true y.
Proof.
  split; [apply orb_prop_elim | apply orb_prop_intro].
Qed.

Hint Rewrite andb_prop_iff orb_prop_iff : quotebool.

Ltac case_equal a b :=
  let E := fresh "E" in
  destruct (X_dec a b) as [E|E];
    [try rewrite E in *|].
Goal (forall n, n = 0 \/ n <> 0).
Proof. intro n;case_equal n 0;tauto. Qed.

Ltac mega_simpl :=
  repeat (simpl in *;
           rewrite in_app_iff
           || match goal with
              | [ h : In _ (bimap _ _ _ ) |- _ ] => 
                let u1 := fresh "u" in
                let u2 := fresh "u" in
                let h1 := fresh "h" in
                apply in_bimap in h as (u1&u2&<-&h&h1)
              | [ h : In _ (map _ _ ) |- _ ] => 
                let u1 := fresh "u" in
                apply in_map_iff in h as (u1&<-&h)
              | [ h : _ \/ _ |- _ ] =>
                destruct h as [h|h]
              | [ h : In _ (_ ++ _ ) |- _ ] =>
                apply in_app_iff in h as [h|h]
              | [ _ : False |- _ ] => tauto
              | |- (forall _, _) => intro
              | |- (_ -> _) => intro
              | |- (In _ (map _ _)) => apply in_map_iff
              | |- (In _ (_ ++ _)) => apply in_app_iff
              | |- (In _ (bimap _ _ _)) => apply in_bimap
              | |- (_ /\ _) => split
              | |- (_ \/ False) => left
              | |- (exists _, _) => eexists
              | [ h : In _ ?l |- In _ ?l ] => apply h
              | [ h : In _ ?l |- In _ ?l \/ _ ] => left;apply h
              | [ h : In _ ?l |- _ \/ In _ ?l ] => right;apply h
              end).



Ltac destruct_eqb x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (PeanoNat.Nat.eq_dec x o) as [Ei |Ni];
    [pose proof Ei as X;apply PeanoNat.Nat.eqb_eq in X;
     try rewrite Ei in *
    |pose proof Ni as X;apply PeanoNat.Nat.eqb_neq in X];
    try rewrite X in *;clear X;
    repeat  (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).
Ltac destruct_eqX_D D x o :=
  let Ei := fresh "E" in
  let Ni := fresh "N" in
  let X := fresh "X" in
  destruct (@X_dec _ D x o) as [Ei |Ni];
    [pose proof Ei as X;apply (@eqX_correct _ D)in X;
     try rewrite Ei in *
    |pose proof Ni as X;apply  (@eqX_false _ D) in X];
    repeat rewrite X in *;repeat rewrite (eqX_refl D) in *;clear X.
Ltac destruct_ltb x o :=
  let Li := fresh "L" in
  let X := fresh "X" in
  destruct (Compare_dec.le_lt_dec o x) as [Li |Li];
    [pose proof Li as X;apply PeanoNat.Nat.ltb_ge in X
    |pose proof Li as X;apply PeanoNat.Nat.ltb_lt in X];
    try rewrite X in *;clear X;
    repeat (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).

Ltac destruct_leb o x :=
  let Li := fresh "L" in
  let X := fresh "X" in
  destruct (Compare_dec.le_lt_dec o x) as [Li |Li];
    [try rewrite (Compare_dec.leb_correct _ _ Li) in *
    |try rewrite (Compare_dec.leb_correct_conv _ _ Li) in *];
    repeat (rewrite <- plus_n_O || rewrite PeanoNat.Nat.eqb_refl).

Ltac simpl_nat :=
  repeat ((rewrite<-plus_n_O in * )
          ||(rewrite PeanoNat.Nat.add_sub in * )
          ||(rewrite Minus.minus_plus in * )).

Create HintDb simpl_typeclasses.
Ltac rsimpl := simpl;autorewrite with simpl_typeclasses;simpl.
Tactic Notation "rsimpl" "in" hyp(h) :=
  (simpl in h;autorewrite with simpl_typeclasses in h;simpl in h).
Tactic Notation "rsimpl" "in" "*" :=
  (simpl in *;autorewrite with simpl_typeclasses in *;simpl in *).
(* end hide *)

(*  LocalWords:  bimap
 *)
