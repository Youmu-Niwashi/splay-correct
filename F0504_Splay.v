Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.RTClosure.
Import ListNotations.
Local Open Scope Z.
Require Import PL.Imp.
Require Import FunctionalExtensionality.

(** Splay tree is a kind of self-balanced binary search tree. You may learn this
    data structure from online resources like:

    <<
       https://people.eecs.berkeley.edu/~jrs/61b/lec/36
    >>

    In this task, you should prove the functional correctness of the splay
    operation, the key operation of splay trees. We provide a step-wise
    description of splay. *)

Definition Key: Type := Z.
Definition Value: Type := Z.

Record Node  := {
   key_of_node : Key;
   value_of_node : Value
}.

Inductive tree : Type :=
| E : tree
| T : tree -> Node -> tree -> tree.

Definition optionZ_lt (ok1 ok2: option Key): Prop :=
  match ok1, ok2 with
  | Some k1, Some k2 => k1 < k2
  | _, _ => True
  end.
  
Definition optionZ_le (ok1 ok2: option Key): Prop :=
  match ok1, ok2 with
  | Some k1, Some k2 => k1 <= k2
  | _, _ => True
  end.

Inductive SearchTree : option Key -> tree -> option Key -> Prop :=
| ST_E : forall lo hi, optionZ_lt lo hi -> SearchTree lo E hi
| ST_T: forall lo l n r hi,
    SearchTree lo l (Some (key_of_node n)) ->
    SearchTree (Some (key_of_node n)) r hi ->
    SearchTree lo (T l n r) hi.

Definition relate_map := Key -> option Value .

Definition relate_default: relate_map := fun x => None.

Definition relate_single (k: Key) (v: Value): relate_map :=
  fun x =>
    if Z.eq_dec x k then Some v else None.

Definition combine (m1 m2: relate_map): relate_map :=
  fun x =>
    match m1 x, m2 x with 
    | None, Some v => Some v
    | Some v, None => Some v
    | _ ,_ => None
    end.

Inductive Abs : tree -> relate_map -> Prop :=
| Abs_E :  Abs E relate_default
| Abs_T: forall l n r lm rm,
    Abs l lm ->
    Abs r rm ->
    Abs
      (T l n r)
      (combine lm
         (combine (relate_single (key_of_node n) (value_of_node n)) rm)).

Inductive LeftOrRight :=
| L: LeftOrRight
| R: LeftOrRight.

Definition half_tree: Type := (LeftOrRight * Node * tree)%type.

Definition partial_tree: Type := list half_tree.

Inductive SearchTree_half_in: (*inner border of partial tree*)
  option Key -> partial_tree -> option Key -> Prop :=
| ST_in_nil:
    forall lo hi, optionZ_lt lo hi -> SearchTree_half_in lo nil hi
| ST_in_cons_L:
    forall lo hi h l n,
      SearchTree_half_in lo h hi ->
      SearchTree lo l (Some (key_of_node n)) ->
      SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) hi
| ST_in_cons_R:
    forall lo hi h r n,
      SearchTree_half_in lo h hi ->
      SearchTree (Some (key_of_node n)) r hi ->
      SearchTree_half_in lo ((R, n, r) :: h) (Some (key_of_node n)).

Fact example:
  forall n1 n2,
  key_of_node n1 = 11 ->
  value_of_node n1 = 11 ->
  key_of_node n2 = 9 ->
  value_of_node n2 = 9 ->
  SearchTree_half_in (Some (key_of_node n1)) [(L, n1,(T E n2 E))] (Some 10).
Proof.
  intros.
  assert (SearchTree_half_in (Some 8) [] (Some 10)).
  { constructor. simpl. lia. }
  assert (SearchTree (Some 8) (T E n2 E) (Some (key_of_node n1))).
  { constructor. constructor. rewrite H1. constructor.
    constructor. rewrite H, H1. constructor. }
  pose proof ST_in_cons_L _ _ _ _ _ H3 H4.
  exact H5.
Qed.

Inductive Abs_half : partial_tree -> relate_map -> Prop :=
| Abs_half_nil : Abs_half nil relate_default
| Abs_half_cons: forall LR n t h m1 m2,
    Abs t m1 ->
    Abs_half h m2 ->
    Abs_half
      ((LR, n, t) :: h)
      (combine m1
         (combine (relate_single (key_of_node n) (value_of_node n)) m2)).

Inductive SearchTree_half_out: (*outer border of partial tree*)
  option Key -> partial_tree -> option Key ->  Prop :=
| ST_out_nil:
    forall lo hi, optionZ_lt lo hi -> SearchTree_half_out lo nil hi 
| ST_out_cons_L:
    forall lo hi h l n,
      SearchTree_half_out lo h hi ->
      SearchTree lo l (Some (key_of_node n)) ->
      optionZ_lt (Some (key_of_node n)) hi ->
      SearchTree_half_out lo ((L, n, l) :: h) hi
| ST_out_cons_R:
    forall lo hi h r n,
      SearchTree_half_out lo h hi ->
      SearchTree (Some (key_of_node n)) r hi ->
      optionZ_lt lo (Some (key_of_node n)) ->
      SearchTree_half_out lo ((R, n, r) :: h) hi.

Inductive splay_step: partial_tree * tree -> partial_tree * tree -> Prop :=
| Splay_LL: forall h a b c d n1 n2 n3,
    splay_step
      ((R, n2, c) :: (R, n3, d) :: h, T a n1 b)
      (h, T a n1 (T b n2 (T c n3 d)))
| Splay_RR: forall h a b c d n1 n2 n3,
    splay_step
      ((L, n2, b) :: (L, n1, a) :: h, T c n3 d)
      (h, T (T (T a n1 b) n2 c) n3 d)
| Splay_RL: forall h a b c d n1 n2 n3, (* right child of left child *)
    splay_step
      ((L, n1, a) :: (R, n3, d) :: h, T b n2 c)
      (h, T (T a n1 b) n2 (T c n3 d))
| Splay_LR: forall h a b c d n1 n2 n3, (* left child of right child *)
    splay_step
      ((R, n3, d) :: (L, n1, a) :: h, T b n2 c)
      (h, T (T a n1 b) n2 (T c n3 d))
| Splay_L: forall x y z n1 n2,
    splay_step ((R, n2, z) :: nil, T x n1 y) (nil, T x n1 (T y n2 z))
| Splay_R: forall x y z n1 n2,
    splay_step ((L, n1, x) :: nil, T y n2 z) (nil, T (T x n1 y) n2 z)
.

Definition splay (h: partial_tree) (t t': tree): Prop :=
  clos_refl_trans splay_step (h, t) (nil, t').

Definition preserves: Prop :=
  forall HI LO hi lo h t t',
    optionZ_lt (Some LO) (Some lo) ->
    optionZ_lt (Some hi) (Some HI) ->
    SearchTree_half_in (Some lo) h (Some hi) ->
    SearchTree_half_out (Some LO) h (Some HI) ->
    SearchTree (Some lo) t (Some hi)->
    splay h t t' ->
    SearchTree (Some LO) t' (Some HI).

Definition correct: Prop :=
  forall h t t' m1 m2 lo hi LO HI,
    Abs_half h m1 ->
    Abs t m2 ->
    splay h t t' ->
    SearchTree (Some lo) t (Some hi)->(* new *)
    SearchTree_half_in (Some lo) h (Some hi)->(* new *)
    SearchTree_half_out (Some LO) h (Some HI)->(* new *)
    optionZ_lt (Some LO) (Some lo) ->
    optionZ_lt (Some hi) (Some HI) ->
    Abs t' (combine m1 m2).

Definition splay' :partial_tree * tree -> partial_tree * tree -> Prop :=
  clos_refl_trans splay_step .

Lemma splay'_splay :
  forall h t t',
  splay' (h,t) (nil,t') -> splay h t t'.
Proof.
  intros.
  unfold splay.
  unfold splay' in H.
  exact H.
Qed.

Lemma splay_splay':
  forall h t t',
  splay h t t' -> splay' (h,t) (nil,t').
Proof.
  intros. unfold splay'. unfold splay in H. exact H.
Qed.

(* =============================================================*)
(* =====================Proof of preserves =====================*)
(* =============================================================*)

Lemma lt_le:
  forall a b,
  optionZ_lt a b -> optionZ_le a b.
Proof.
  intros. destruct a;destruct b;simpl in *;try tauto. lia.
Qed.

Lemma lt_le':
  forall a b,
  optionZ_lt (Some a) (Some b) -> optionZ_le (Some a) (Some (b-1)).
Proof.
  intros. simpl in *. lia.
Qed.

Lemma lt_le'':
  forall a b,
  optionZ_lt (Some a) (Some b) -> optionZ_le (Some (a+1)) (Some b).
Proof.
  intros.
  simpl in *.
  lia.
Qed.

Lemma lt_le''':
  forall a b,
  optionZ_lt (Some a) (Some (b+1)) -> optionZ_le (Some a) (Some b).
Proof.
  intros. simpl in *. lia.
Qed.

Lemma optionZ_lt_cong: forall n lo hi,
optionZ_lt (Some (n)) hi->
optionZ_lt lo (Some (n))->
optionZ_lt lo hi.
Proof.
intros. induction hi; simpl in H;simpl; induction lo; simpl in H0; simpl; try exact I; unfold Key in *. lia. Qed. 

Lemma optionZ_le_cong: forall n lo hi,
optionZ_le (Some (n)) hi->
optionZ_le lo (Some (n))->
optionZ_le lo hi.
Proof.
intros. induction hi; simpl in H;simpl; induction lo; simpl in H0; simpl; try exact I; unfold Key in *. lia. Qed.

Lemma optionZ_let_cong: forall n lo hi,
optionZ_le (Some (n)) hi->
optionZ_lt lo (Some (n))->
optionZ_lt lo hi.
Proof.
intros. induction hi; simpl in H;simpl; induction lo; simpl in H0; simpl; try exact I; unfold Key in *. lia. Qed.

Lemma optionZ_lte_cong: forall n lo hi,
optionZ_lt (Some (n)) hi->
optionZ_le lo (Some (n))->
optionZ_lt lo hi.
Proof.
intros. induction hi; simpl in H;simpl; induction lo; simpl in H0; simpl; try exact I; unfold Key in *. lia. Qed.

Lemma optionZ_lt_SearchTree: forall l lo hi,
SearchTree lo l hi
-> optionZ_lt lo hi.
Proof.
intros. induction H. tauto. pose proof optionZ_lt_cong _ _ _ IHSearchTree2 IHSearchTree1. tauto. 
Qed.

Lemma looser_SearchTree_l: 
  forall lo' lo hi t,
    optionZ_lt lo (Some lo') -> 
    SearchTree (Some lo') t (Some hi) ->
    SearchTree lo t (Some hi).
Proof.
  intros. revert H. revert lo. revert H0. revert lo'. revert hi.
  induction t;subst.  
  2:{ intros. inversion H0; subst. constructor. 
      specialize (IHt1 (key_of_node n) lo' H6 lo H). 
      exact IHt1. exact H7. }
  intros. constructor. 
  pose proof optionZ_lt_SearchTree _ _ _ H0. 
  pose proof optionZ_lt_cong _ _ _ H1 H. 
  tauto. 
Qed.

Lemma looser_SearchTree_r: 
  forall hi' lo hi t,
    optionZ_lt (Some hi') hi -> 
    SearchTree (Some lo) t (Some hi') ->
    SearchTree (Some lo) t hi.
Proof.
  intros. revert H. revert hi. revert H0. revert lo. revert hi'. 
  induction t;subst.  
  2:{ intros. inversion H0; subst. 
      constructor. exact H6. 
      specialize (IHt2 hi' (key_of_node n) H7 hi H). 
      exact IHt2. }
  intros. constructor. 
  pose proof optionZ_lt_SearchTree _ _ _ H0. 
  pose proof optionZ_lt_cong _ _ _ H H1. 
  tauto. 
Qed.

Lemma looser_SearchTree: 
  forall lo' hi' lo hi t,
    optionZ_lt lo (Some lo') -> 
    optionZ_lt (Some hi') hi ->
    SearchTree (Some lo') t (Some hi') ->
    SearchTree lo t hi.
Proof.
intros. 
inversion H1. subst. constructor. pose proof optionZ_lt_cong _ _ _ H0 H2. pose proof optionZ_lt_cong _ _ _ H3 H. exact H4.  
subst. constructor. pose proof looser_SearchTree_l _ _ _ _ H H2. tauto. pose proof looser_SearchTree_r _ _ _ _ H0 H3. tauto. Qed.

Lemma looser_SearchTree_l_e: 
  forall lo' lo hi t,
    optionZ_le lo (Some lo') -> 
    SearchTree (Some lo') t (Some hi) ->
    SearchTree lo t (Some hi).
Proof.
  intros. revert H. revert lo. revert H0. revert lo'. revert hi.
  induction t;subst.  
  2:{ intros. inversion H0; subst. constructor. 
      specialize (IHt1 (key_of_node n) lo' H6 lo H). 
      exact IHt1. exact H7. }
  intros. constructor. 
  pose proof optionZ_lt_SearchTree _ _ _ H0. 
  pose proof optionZ_lte_cong _ _ _ H1 H. 
  tauto. 
Qed.

Lemma looser_SearchTree_r_e: 
  forall hi' lo hi t,
    optionZ_le (Some hi') hi -> 
    SearchTree (Some lo) t (Some hi') ->
    SearchTree (Some lo) t hi.
Proof.
  intros. revert H. revert hi. revert H0. revert lo. revert hi'. 
  induction t;subst.  
  2:{ intros. inversion H0; subst. 
      constructor. exact H6. 
      specialize (IHt2 hi' (key_of_node n) H7 hi H). 
      exact IHt2. }
  intros. constructor. 
  pose proof optionZ_lt_SearchTree _ _ _ H0. 
  pose proof optionZ_let_cong _ _ _ H H1. 
  tauto. 
Qed.

Lemma looser_SearchTree_le:
  forall lo' hi' lo hi t,
    optionZ_le lo (Some lo') -> 
    optionZ_le (Some hi') hi ->
    SearchTree (Some lo') t (Some hi') ->
    SearchTree lo t hi.
Proof.
intros. 
inversion H1; subst. constructor. pose proof optionZ_let_cong _ _ _ H0 H2. pose proof optionZ_lte_cong _ _ _ H3 H. exact H4.  
subst. constructor. pose proof looser_SearchTree_l_e _ _ _ _ H H2. tauto. pose proof looser_SearchTree_r_e _ _ _ _ H0 H3. tauto. Qed.


Fixpoint supremum (t: tree): option Key:= 
  match t with 
  | E => None
  | T _ n E => Some (key_of_node n)
  | T l n r => supremum r
  end.

Lemma sup_fact':
  forall t,
    t <> E ->
    exists v, supremum t = Some v.
Proof.
  intros.
  induction t.
  + tauto.
  + destruct t2.
    { exists (key_of_node n). simpl. reflexivity. }
    assert (T t2_1 n0 t2_2 <> E).
    { pose proof classic (T t2_1 n0 t2_2 = E).
      destruct H0;[inversion H0|tauto]. }
    specialize (IHt2 H0).
    destruct IHt2.
    exists x.
    simpl in *.
    exact H1.
Qed.

Lemma sup_fact :
  forall l n r, exists v, supremum (T l n r) = Some v.
Proof.
  intros.
  assert ((T l n r) <> E).
  { pose proof classic ((T l n r) = E). destruct H;[inversion H|tauto]. }
  apply sup_fact' in H. tauto.
Qed.

Lemma sup_property:
  forall lo hi t sup,
    SearchTree lo t hi ->
    supremum t = sup ->
    optionZ_lt sup hi.
Proof.
  intros.
  revert sup lo hi H H0.
  induction t;intros.
  + subst. simpl. tauto.
  + destruct t2.
    { simpl in H0. subst.
      inversion H;subst.
      inversion H6;subst.
      exact H0.
    }
    inversion H. subst lo0 l n1 r hi0.
    specialize (IHt2 sup _ _ H7).
    simpl in *.
    specialize (IHt2 H0).
    exact IHt2.
Qed.

Lemma SearchTree_sup:
  forall lo t hi sup,
    SearchTree lo t hi ->
    supremum t = (Some sup) ->
    SearchTree lo t (Some (sup+1)).
Proof.
  intros.
  revert lo hi sup H H0 .
  induction t;intros.
  + discriminate H0.
  + inversion H. subst lo0 l n0 r hi0.
    constructor;[tauto|].
    destruct t2.
    { simpl in H0. injection H0. intros. rewrite H1.
      constructor. simpl. lia. }
    specialize (IHt2 _ _ sup H7).
    simpl in *.
    specialize (IHt2 H0).
    exact IHt2.
Qed.

Fixpoint infimum (t: tree): option Key:= 
  match t with 
  | E => None
  | T E n _ => Some (key_of_node n)
  | T l n r => infimum l
  end.


Lemma inf_fact':
  forall t,
    t <> E ->
    exists v, infimum t = Some v.
Proof.
  intros.
  induction t.
  + tauto.
  + destruct t1.
    { exists (key_of_node n). simpl. reflexivity. }
    assert (T t1_1 n0 t1_2 <> E).
    { pose proof classic (T t1_1 n0 t1_2 = E).
      destruct H0;[inversion H0|tauto]. }
    specialize (IHt1 H0).
    destruct IHt1.
    exists x.
    simpl in *.
    exact H1.
Qed.

Lemma inf_fact :
  forall l n r, exists v, infimum (T l n r) = Some v.
Proof.
  intros.
  assert ((T l n r) <> E).
  { pose proof classic ((T l n r) = E). destruct H;[inversion H|tauto]. }
  apply inf_fact' in H. tauto.
Qed.

Lemma inf_property:
  forall lo hi t inf,
    SearchTree lo t hi ->
    infimum t = inf ->
    optionZ_lt lo inf.
Proof.
  intros.
  revert inf lo hi H H0.
  induction t;intros.
  + subst. destruct lo;simpl;tauto.
  + destruct t1.
    { simpl in H0. subst.
      inversion H;subst.
      inversion H5;subst.
      exact H0.
    }
    inversion H. subst lo0 l n1 r hi0.
    specialize (IHt1 inf _ _ H6).
    simpl in *.
    specialize (IHt1 H0).
    exact IHt1.
Qed.

Lemma SearchTree_inf:
  forall lo t hi inf,
    SearchTree lo t hi ->
    infimum t = (Some inf) ->
    SearchTree (Some (inf-1)) t hi.
Proof.
  intros.
  revert lo hi inf H H0 .
  induction t;intros.
  + discriminate H0.
  + inversion H. subst lo0 l n0 r hi0.
    constructor;[|tauto].
    destruct t1.
    { simpl in H0. injection H0. intros. rewrite H1.
      constructor. simpl. lia. }
    specialize (IHt1 _ _ inf H6).
    simpl in *.
    specialize (IHt1 H0).
    exact IHt1.
Qed.


Inductive R_in: partial_tree -> half_tree -> Prop :=
  | R_in_base: forall n r h, R_in ((R, n, r)::h) (R, n, r)
  | R_in_forward: forall n n' l r h, R_in h (R, n, r) -> R_in ((L, n', l)::h) (R, n, r).

Inductive all_L: partial_tree ->Prop :=
  | AL_nil: all_L nil
  | AL_forward: forall h n l, all_L h -> all_L ((L, n, l)::h).

Inductive L_in: partial_tree -> half_tree -> Prop :=
  | L_in_base: forall n l h, L_in ((L, n, l)::h) (L, n, l)
  | L_in_forward: forall n n' l r h, L_in h (L, n, l) -> L_in ((R, n', r)::h) (L, n, l).

Inductive all_R: partial_tree ->Prop :=
  | AR_nil: all_R nil
  | AR_forward: forall h n r, all_R h -> all_R ((R, n, r)::h).

Lemma all_L_or_R_in: forall h, 
  all_L h \/ exists n r, R_in h (R, n, r).
Proof.
  intros.
  induction h.
  + left. constructor.
  + destruct IHh.
    - destruct a. destruct p. destruct l.
      -- left. constructor. tauto.
      -- right. exists n,t. constructor.
    - right.
      destruct H as [n [r ?]].
      destruct a. destruct p. destruct l.
      -- exists n, r. constructor; tauto.
      -- exists n0, t. constructor.
Qed.

Lemma not_all_L_R_in: forall h,
  ~ all_L h <-> exists n r, R_in h (R, n, r) .
Proof.
  intros.
  unfold iff;split;intros.
  + pose proof all_L_or_R_in h.
    destruct H0;tauto.
  + pose proof classic (all_L h).
    destruct H0;[|tauto].
    destruct H as [n [r ?]].
    induction H;intros. 
    - inversion H0.
    - inversion H0;subst. tauto.
Qed.

Lemma all_R_or_L_in: forall h, 
  all_R h \/ exists n l, L_in h (L, n, l).
Proof.
  intros.
  induction h.
  + left. constructor.
  + destruct IHh.
    - destruct a. destruct p. destruct l.
      -- right. exists n,t. constructor.
      -- left. constructor. tauto.
    - right.
      destruct H as [n [l ?]].
      destruct a. destruct p. destruct l0.
      -- exists n0, t. constructor.
      -- exists n, l. constructor; tauto.
Qed.

Lemma not_all_R_L_in: forall h,
  ~ all_R h <-> exists n l, L_in h (L, n, l) .
Proof.
  intros.
  unfold iff;split;intros.
  + pose proof all_R_or_L_in h.
    destruct H0;tauto.
  + pose proof classic (all_R h).
    destruct H0;[|tauto].
    destruct H as [n [l ?]].
    induction H;intros. 
    - inversion H0.
    - inversion H0;subst. tauto.
Qed.


Lemma r_none_all_L: 
  forall n l h,
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) None ->
    all_L ((L, n, l) :: h).
Proof.
  intros.
  pose proof classic (all_L ((L, n, l) :: h)).
  pose proof not_all_L_R_in ((L, n, l) :: h).
  destruct H0;[tauto|].
  assert (exists (n0 : Node) (r : tree), R_in ((L, n, l) :: h) (R, n0, r)) by tauto.
  clear H0 H1.
  destruct H2 as [n0 [r ?]].
  inversion H0;subst.
  remember None as hi.
  remember (R, n0, r) as ht.
  revert n l H H0.
  induction H2;intros;subst.
  + inversion H;subst.
    inversion H6;subst.
  + inversion H;subst.
    inversion H0;subst.
    inversion H7;subst.
    specialize (IHR_in Heqht _ _ H7 H4).
    constructor. exact IHR_in.
Qed.

Lemma r_none_tighter: 
  forall n l h hi,
    optionZ_le (Some (key_of_node n)) hi ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) None ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) hi.
Proof.
  intros.
  pose proof r_none_all_L _ _ _ H0.
  inversion H1;subst.
  revert n l H H0 H1.
  induction H3;intros.
  + inversion H0;subst.
    clear H2.
    assert (SearchTree_half_in lo [] hi).
    { constructor. apply optionZ_lt_SearchTree in H8.
      pose proof optionZ_let_cong _ _ _ H H8. exact H2. }
    Print SearchTree_half_in.
    pose proof ST_in_cons_L _ _ _ _ _ H2 H8.
    exact H3.
  + inversion H0;subst.
    inversion H8;subst.
    inversion H1;subst.
    pose proof optionZ_lt_SearchTree _ _ _ H9.
    pose proof optionZ_let_cong _ _ _ H H4.
    apply lt_le in H6.
    specialize (IHall_L _ _ H6 H8 H5).
    Print SearchTree_half_in.
    pose proof ST_in_cons_L _ _ _ _ _ IHall_L H9.
    exact H7.
Qed.

Lemma l_none_all_R: 
  forall n r h,
    SearchTree_half_in None ((R, n, r) :: h) (Some (key_of_node n)) ->
    all_R ((R, n, r) :: h).
Proof.
  intros.
  pose proof classic (all_R ((R, n, r) :: h)).
  pose proof not_all_R_L_in ((R, n, r) :: h).
  destruct H0;[tauto|].
  assert (exists (n0 : Node) (l : tree), L_in ((R, n, r) :: h) (L, n0, l)) by tauto.
  clear H0 H1.
  destruct H2 as [n0 [l ?]].
  inversion H0;subst.
  remember None as lo.
  remember (L, n0, l) as ht.
  revert n r H H0.
  induction H2;intros;subst.
  + inversion H;subst.
    inversion H4;subst.
  + inversion H;subst.
    inversion H0;subst.
    inversion H5;subst.
    specialize (IHL_in Heqht _ _ H5 H3).
    constructor. exact IHL_in.
Qed.

Lemma l_none_tighter: 
  forall n r h lo,
    optionZ_le lo (Some (key_of_node n)) ->
    SearchTree_half_in None ((R, n, r) :: h) (Some (key_of_node n)) ->
    SearchTree_half_in lo ((R, n, r) :: h) (Some (key_of_node n)).
Proof.
  intros.
  pose proof l_none_all_R _ _ _ H0.
  inversion H1;subst.
  revert n r H H0 H1.
  induction H3;intros.
  + inversion H0;subst.
    assert (SearchTree_half_in lo [] hi).
    { constructor. apply optionZ_lt_SearchTree in H7.
      pose proof optionZ_lte_cong _ _ _ H7 H. exact H2. }
    Print SearchTree_half_in.
    pose proof ST_in_cons_R _ _ _ _ _ H2 H7.
    exact H3.
  + inversion H0;subst.
    inversion H6;subst.
    inversion H1;subst.
    pose proof optionZ_lt_SearchTree _ _ _ H8.
    pose proof optionZ_lte_cong _ _ _ H2 H.
    apply lt_le in H5.
    specialize (IHall_R _ _ H5 H6 H4).
    Print SearchTree_half_in.
    pose proof ST_in_cons_R _ _ _ _ _ IHall_R H8.
    exact H7.
Qed.

Lemma all_L_r_some_tighter:
  forall n l h hi k,
    all_L ((L, n, l) :: h) ->
    optionZ_le (Some (key_of_node n)) hi ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) (Some k) ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) hi.
Proof.
  intros.
  inversion H;subst.
  revert n l H0 H1 H.
  induction H3;intros.
  + inversion H1;subst.
    assert (SearchTree_half_in lo [] hi).
    { constructor. apply optionZ_lt_SearchTree in H8.
      pose proof optionZ_let_cong _ _ _ H0 H8. exact H3. }
    Print SearchTree_half_in.
    pose proof ST_in_cons_L _ _ _ _ _ H3 H8.
    exact H4.
  + inversion H1;subst.
    inversion H8;subst.
    inversion H;subst.
    pose proof optionZ_lt_SearchTree _ _ _ H9.
    pose proof optionZ_let_cong _ _ _ H0 H4.
    apply lt_le in H6.
    specialize (IHall_L _ _ H6 H8 H5).
    Print SearchTree_half_in.
    pose proof ST_in_cons_L _ _ _ _ _ IHall_L H9.
    exact H7.
Qed.

Lemma all_R_l_some_tighter:
  forall n r h lo k,
    all_R ((R, n, r) :: h) ->
    optionZ_le lo (Some (key_of_node n)) ->
    SearchTree_half_in (Some k) ((R, n, r) :: h) (Some (key_of_node n)) ->
    SearchTree_half_in lo ((R, n, r) :: h) (Some (key_of_node n)).
Proof.
  intros.
  inversion H;subst.
  revert n r H0 H1 H.
  induction H3;intros.
  + inversion H1;subst.
    assert (SearchTree_half_in lo [] hi).
    { constructor. apply optionZ_lt_SearchTree in H7.
      pose proof optionZ_lte_cong _ _ _ H7 H0. exact H2. }
    Print SearchTree_half_in.
    pose proof ST_in_cons_R _ _ _ _ _ H2 H7.
    exact H3.
  + inversion H1;subst.
    inversion H6;subst.
    inversion H;subst.
    pose proof optionZ_lt_SearchTree _ _ _ H8.
    pose proof optionZ_lte_cong _ _ _ H2 H0.
    apply lt_le in H5.
    specialize (IHall_R _ _ H5 H6 H4).
    Print SearchTree_half_in.
    pose proof ST_in_cons_R _ _ _ _ _ IHall_R H8.
    exact H7.
Qed.

Lemma R_in_r_bound: 
  forall n l n0 r0 h LO HI hi,
    R_in ((L, n, l)::h) (R, n0, r0) ->
    SearchTree_half_out (Some LO) ((L, n, l) :: h) (Some HI) ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) hi ->
    hi = (Some (key_of_node n0)) /\ optionZ_le hi (Some HI).
Proof.
  intros.
  inversion H;subst.
  clear H.
  remember (R, n0, r0) as h_t.
  revert n l H0 H1.
  induction H3;intros.
  + inversion H1;subst.
    inversion H6;subst.
    injection Heqh_t.
    intros;subst.
    inversion H0;subst.
    inversion H8;subst.
    apply optionZ_lt_SearchTree, lt_le in H15.
    split;[reflexivity|exact H15].
  + inversion H0;subst.
    inversion H1;subst.
    inversion H10;subst.
    specialize (IHR_in Heqh_t _ _ H6 H10).
    exact IHR_in.
Qed.

Lemma L_in_l_bound: 
  forall n r n0 l0 h LO HI lo,
    L_in ((R, n, r)::h) (L, n0, l0) ->
    SearchTree_half_out (Some LO) ((R, n, r) :: h) (Some HI) ->
    SearchTree_half_in lo ((R, n, r) :: h) (Some (key_of_node n)) ->
    lo = (Some (key_of_node n0)) /\ optionZ_le (Some LO) lo.
Proof.
  intros.
  inversion H;subst.
  clear H.
  remember (L, n0, l0) as h_t.
  revert n r H0 H1.
  induction H3;intros.
  + inversion H1;subst.
    inversion H4;subst.
    injection Heqh_t.
    intros;subst.
    inversion H0;subst.
    inversion H7;subst.
    apply optionZ_lt_SearchTree, lt_le in H14.
    split;[reflexivity|exact H14].
  + inversion H0;subst.
    inversion H1;subst.
    inversion H5;subst.
    specialize (IHL_in Heqh_t _ _ H6 H5).
    exact IHL_in.
Qed.

Lemma all_L_r_bound:
  forall lt nt rt LO HI n l h k,
    all_L ((L, n, l) :: h) ->
    SearchTree (Some (key_of_node n)) (T lt nt rt) (Some HI) ->
    SearchTree_half_out (Some LO) ((L, n, l) :: h) (Some HI) ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) (Some k) ->
    exists hi',
      SearchTree (Some (key_of_node n)) (T lt nt rt) (Some hi') /\
      SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) (Some hi') /\
      optionZ_le (Some hi') (Some HI).
Proof.
  intros.
  pose proof sup_fact lt nt rt. destruct H3 as [sup ?].
  exists (sup +1).
  pose proof SearchTree_sup _ _ _ _ H0 H3.
  split;[exact H4|split].
  { inversion H4;subst.
    apply optionZ_lt_SearchTree in H10. apply optionZ_lt_SearchTree in H11.
    pose proof optionZ_lt_cong _ _ _ H11 H10. apply lt_le in H5.
    pose proof all_L_r_some_tighter _ _ _ _ _ H H5 H2. exact H6. }
  pose proof sup_property _ _ _ _ H0 H3.
  apply lt_le'' in H5. exact H5.
Qed.

Lemma all_R_l_bound:
  forall lt nt rt LO HI n r h k,
    all_R ((R, n, r) :: h) ->
    SearchTree (Some LO) (T lt nt rt) (Some (key_of_node n)) ->
    SearchTree_half_out (Some LO) ((R, n, r) :: h) (Some HI) ->
    SearchTree_half_in (Some k) ((R, n, r) :: h) (Some (key_of_node n)) ->
    exists lo',
      SearchTree (Some lo') (T lt nt rt) (Some (key_of_node n)) /\
      SearchTree_half_in (Some lo') ((R, n, r) :: h) (Some (key_of_node n)) /\
      optionZ_le (Some LO) (Some lo').
Proof.
  intros.
  pose proof inf_fact lt nt rt. destruct H3 as [inf ?].
  exists (inf - 1).
  pose proof SearchTree_inf _ _ _ _ H0 H3.
  split;[exact H4|split].
  { inversion H4;subst.
    apply optionZ_lt_SearchTree in H10. apply optionZ_lt_SearchTree in H11.
    pose proof optionZ_lt_cong _ _ _ H11 H10. apply lt_le in H5.
    pose proof all_R_l_some_tighter _ _ _ _ _ H H5 H2. exact H6. }
  pose proof inf_property _ _ _ _ H0 H3.
  apply lt_le' in H5. exact H5.
Qed.

Lemma r_bound_None:
  forall lt nt rt LO HI n l h,
    SearchTree (Some (key_of_node n)) (T lt nt rt) (Some HI) ->
    SearchTree_half_out (Some LO) ((L, n, l) :: h) (Some HI) ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) None ->
    exists hi',
      SearchTree (Some (key_of_node n)) (T lt nt rt) (Some hi') /\
      SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) (Some hi') /\
      optionZ_le (Some hi') (Some HI).
Proof.
  intros.
  pose proof sup_fact lt nt rt. destruct H2 as [sup ?].
  exists (sup + 1).
  pose proof SearchTree_sup _ _ _ _ H H2.
  split;[exact H3|split].
  { inversion H3;subst.
    apply optionZ_lt_SearchTree in H9.
    apply optionZ_lt_SearchTree in H10.
    pose proof optionZ_lt_cong _ _ _ H10 H9.
    apply lt_le in H4. pose proof r_none_tighter _ _ _ _ H4 H1. exact H5. }
  Check sup_property.
  pose proof sup_property _ _ _ _ H H2.
  apply lt_le'' in H4. exact H4.
Qed.

Lemma l_bound_None:
  forall lt nt rt LO HI n r h,
    SearchTree (Some LO) (T lt nt rt) (Some (key_of_node n)) ->
    SearchTree_half_out (Some LO) ((R, n, r) :: h) (Some HI) ->
    SearchTree_half_in None ((R, n, r) :: h) (Some (key_of_node n)) ->
    exists lo',
      SearchTree (Some lo') (T lt nt rt) (Some (key_of_node n)) /\
      SearchTree_half_in (Some lo') ((R, n, r) :: h) (Some (key_of_node n)) /\
      optionZ_le (Some LO) (Some lo').
Proof.
  intros.
  pose proof inf_fact lt nt rt. destruct H2 as [inf ?].
  exists (inf - 1).
  pose proof SearchTree_inf _ _ _ _ H H2.
  split;[exact H3|split].
  { inversion H3;subst.
    apply optionZ_lt_SearchTree in H9.
    apply optionZ_lt_SearchTree in H10.
    pose proof optionZ_lt_cong _ _ _ H10 H9.
    apply lt_le in H4. pose proof l_none_tighter _ _ _ _ H4 H1. exact H5. }
  Check inf_property.
  pose proof inf_property _ _ _ _ H H2.
  apply lt_le' in H4. exact H4.
Qed. 


Lemma inner_border_tighter_L:
  forall n l h hi LO HI lt nt rt,
    SearchTree (Some (key_of_node n)) (T lt nt rt) hi ->
    SearchTree (Some (key_of_node n)) (T lt nt rt) (Some HI) ->
    SearchTree_half_out (Some LO) ((L, n, l) :: h) (Some HI) ->
    SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) hi ->
    exists hi',
      SearchTree (Some (key_of_node n)) (T lt nt rt) (Some hi') /\
      SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) (Some hi') /\
      optionZ_le (Some hi') (Some HI).
Proof.
  intros.
  destruct hi.
  2:{ pose proof r_bound_None _ _ _ _ _ _ _ _ H0 H1 H2. exact H3. }
  pose proof all_L_or_R_in ((L, n, l)::h).
  destruct H3;[|destruct H3 as [n0 [r ?]]].
  2:{ pose proof R_in_r_bound _ _ _ _ _ _ _ _ H3 H1 H2.
      destruct H4;injection H4;intros;subst.
      exists (key_of_node n0). tauto. }
  pose proof all_L_r_bound _ _ _ _ _ _ _ _ _ H3 H0 H1 H2. exact H4.
Qed.

Lemma inner_border_tighter_R:
  forall n r h lo LO HI lt nt rt,
    SearchTree lo (T lt nt rt) (Some (key_of_node n)) ->
    SearchTree (Some LO) (T lt nt rt) (Some (key_of_node n)) ->
    SearchTree_half_out (Some LO) ((R, n, r) :: h) (Some HI) ->
    SearchTree_half_in lo ((R, n, r) :: h) (Some (key_of_node n)) ->
    exists lo',
      SearchTree (Some lo') (T lt nt rt) (Some (key_of_node n)) /\
      SearchTree_half_in (Some lo') ((R, n, r) :: h) (Some (key_of_node n)) /\
      optionZ_le (Some LO) (Some lo').
Proof.
  intros.
  destruct lo.
  2:{ pose proof l_bound_None _ _ _ _ _ _ _ _ H0 H1 H2. exact H3. }
  pose proof all_R_or_L_in ((R, n, r)::h).
  destruct H3;[|destruct H3 as [n0 [l ?]]].
  2:{ pose proof L_in_l_bound _ _ _ _ _ _ _ _ H3 H1 H2.
      destruct H4;injection H4;intros;subst.
      exists (key_of_node n0). tauto. }
  pose proof all_R_l_bound _ _ _ _ _ _ _ _ _ H3 H0 H1 H2. exact H4.
Qed.

Lemma step_preserves: 
  forall h h' t t' lo hi LO HI,
    optionZ_le (Some LO) (Some lo) ->
    optionZ_le (Some hi) (Some HI) ->
    SearchTree_half_in (Some lo) h (Some hi) ->
    SearchTree_half_out (Some LO) h (Some HI) ->
    SearchTree (Some lo) t (Some hi) ->
    splay_step (h,t) (h',t') ->
    exists lo' hi',
      (optionZ_le (Some LO) (Some lo')) /\
      (optionZ_le (Some hi') (Some HI)) /\
      (SearchTree (Some lo') t' (Some hi')) /\ 
      (SearchTree_half_in (Some lo') h' (Some hi')) /\ 
      (SearchTree_half_out (Some LO) h' (Some HI)).
Proof.
  intros.
  inversion H4;subst.
  + inversion H1;subst.
    inversion H8;subst.
    rename H3 into H_Tn1, H11 into H_c, H13 into H_d.
    rename H12 into H_h'.
    inversion H2;subst.
    inversion H9;subst.
    exists lo.  
    inversion H_h';subst.
    3:{ exists (key_of_node n).
        inversion H10;subst.
        apply optionZ_lt_SearchTree , lt_le in H19.
        split;[exact H|split;[exact H19|split]].
        { inversion H_Tn1;subst.
        constructor;try tauto;constructor;try tauto;constructor;try tauto. }
        split;tauto. }
    - exists HI.
      split;[tauto|split;[simpl;lia|]].
      split;[|split;[|exact H10]].
      { inversion H_Tn1;subst.
        constructor;try tauto;constructor;try tauto;constructor;try tauto. }
      constructor.
      apply optionZ_lt_SearchTree in H_Tn1.
      apply optionZ_lt_SearchTree in H11.
      pose proof optionZ_lt_cong _ _ _ H11 H_Tn1.
      exact H5.
    - inversion H_Tn1;subst.
      assert (SearchTree (Some (key_of_node n)) (T a n1 (T b n2 (T c n3 d))) hi).
      { constructor;try tauto;constructor;try tauto;constructor;try tauto. }
      assert (SearchTree (Some (key_of_node n)) (T a n1 (T b n2 (T c n3 d))) (Some HI)).
      { constructor;try tauto;constructor;try tauto;constructor;try tauto. }
      pose proof inner_border_tighter_L _ _ _ _ _ _ _ _ _ H3 H7 H10 H_h'.
      destruct H13 as [hi' ?].
      exists hi'. tauto. 
  +  inversion H1;subst. inversion H10;subst.
     inversion H2;subst. inversion H9;subst.
     inversion H3;subst.
     inversion H12;subst.
     2:{ exists (key_of_node n), hi.
         inversion H14;subst. apply optionZ_lt_SearchTree, lt_le in H25.
         assert (SearchTree (Some (key_of_node n)) (T (T (T a n1 b) n2 c) n3 d) (Some hi)).
         { constructor;[constructor;[constructor;tauto|tauto]|tauto]. }
         tauto. }
     - exists LO, hi.
       assert (optionZ_le (Some LO) (Some LO)) by (simpl;lia).
       assert (SearchTree (Some LO) (T (T (T a n1 b) n2 c) n3 d) (Some hi)).
         { constructor;[constructor;[constructor;tauto|tauto]|tauto]. }
       apply optionZ_lt_SearchTree in H21. apply optionZ_lt_SearchTree in H20.
       apply optionZ_lt_SearchTree in H15.
       pose proof optionZ_lt_cong _ _ _ H21 H20.
       pose proof optionZ_lt_cong _ _ _ H8 H15.
       pose proof ST_in_nil _ _ H17.
       tauto.
    - assert (SearchTree lo (T (T (T a n1 b) n2 c) n3 d) (Some (key_of_node n))).
      { constructor;[constructor;[constructor;tauto|tauto]|tauto]. }
      assert (SearchTree (Some LO) (T (T (T a n1 b) n2 c) n3 d) (Some (key_of_node n))).
      { constructor;[constructor;[constructor;tauto|tauto]|tauto]. }
      pose proof inner_border_tighter_R _ _ _ _ _ _ _ _ _ H5 H7 H14 H12.
      destruct H8 as [lo' ?].
      exists lo' ,(key_of_node n). tauto. 
  + inversion H1;subst. inversion H10;subst.
    inversion H2;subst. inversion H12;subst.
    inversion H8;subst.
    - exists LO, HI.
      inversion H3;subst.
      assert (optionZ_le (Some LO) (Some LO)) by (simpl;lia).
      assert (optionZ_le (Some HI) (Some HI)) by (simpl;lia).
      assert (SearchTree (Some LO) (T (T a n1 b) n2 (T c n3 d)) (Some HI)).
      { constructor;constructor;tauto. }
      inversion H14;subst.
      assert (SearchTree_half_in (Some LO) [] (Some HI)) by (constructor;simpl;exact H17).
      tauto.
    - exists (key_of_node n).
      inversion H14;subst.
      apply optionZ_lt_SearchTree, lt_le in H23.
      inversion H3;subst.
      assert (SearchTree (Some (key_of_node n)) (T (T a n1 b) n2 (T c n3 d)) hi0).
      { constructor;constructor;tauto. }
      assert (SearchTree (Some (key_of_node n)) (T (T a n1 b) n2 (T c n3 d)) (Some HI)).
      { constructor;constructor;tauto. }
      pose proof inner_border_tighter_L _ _ _ _ _ _ _ _ _ H7 H9 H14 H8.
      destruct H17 as [hi' ?].
      exists hi'. tauto.
    - inversion H14;subst.
      apply optionZ_lt_SearchTree, lt_le in H23.
      inversion H3;subst.
      assert (SearchTree lo0 (T (T a n1 b) n2 (T c n3 d)) (Some (key_of_node n))).
      { constructor;constructor;tauto. }
      assert (SearchTree (Some LO) (T (T a n1 b) n2 (T c n3 d)) (Some (key_of_node n))).
      { constructor;constructor;tauto. }
      pose proof inner_border_tighter_R _ _ _ _ _ _ _ _ _ H7 H9 H14 H8.
      destruct H17 as [lo' ?].
      exists lo', (key_of_node n). tauto.
  + inversion H1;subst. inversion H8;subst.
    inversion H2;subst. inversion H10;subst.
    inversion H12;subst.
    - exists LO, HI.
      inversion H3;subst.
      assert (optionZ_le (Some LO) (Some LO)) by (simpl;lia).
      assert (optionZ_le (Some HI) (Some HI)) by (simpl;lia).
      assert (SearchTree (Some LO) (T (T a n1 b) n2 (T c n3 d)) (Some HI)).
      { constructor;constructor;tauto. }
      inversion H14;subst.
      assert (SearchTree_half_in (Some LO) [] (Some HI)) by (constructor;simpl;exact H17).
      tauto.
    - exists (key_of_node n).
      inversion H14;subst.
      apply optionZ_lt_SearchTree, lt_le in H23.
      inversion H3;subst.
      assert (SearchTree (Some (key_of_node n)) (T (T a n1 b) n2 (T c n3 d)) hi0).
      { constructor;constructor;tauto. }
      assert (SearchTree (Some (key_of_node n)) (T (T a n1 b) n2 (T c n3 d)) (Some HI)).
      { constructor;constructor;tauto. }
      pose proof inner_border_tighter_L _ _ _ _ _ _ _ _ _ H7 H9 H14 H12.
      destruct H17 as [hi' ?].
      exists hi'. tauto.
    - inversion H14;subst.
      apply optionZ_lt_SearchTree, lt_le in H23.
      inversion H3;subst.
      assert (SearchTree lo0 (T (T a n1 b) n2 (T c n3 d)) (Some (key_of_node n))).
      { constructor;constructor;tauto. }
      assert (SearchTree (Some LO) (T (T a n1 b) n2 (T c n3 d)) (Some (key_of_node n))).
      { constructor;constructor;tauto. }
      pose proof inner_border_tighter_R _ _ _ _ _ _ _ _ _ H7 H9 H14 H12.
      destruct H17 as [lo' ?].
      exists lo', (key_of_node n). tauto.
  +  inversion H1;subst.
     inversion H2;subst.
     inversion H3;subst.
     exists lo, HI.
     assert (optionZ_le (Some HI) (Some HI)) by (simpl;lia).
     assert (SearchTree (Some lo) (T x n1 (T y n2 z)) (Some HI)).
     { constructor;[tauto|constructor;tauto]. }
     pose proof optionZ_lt_SearchTree _ _ _ H6.
     assert (SearchTree_half_in (Some lo) [] (Some HI)) by (constructor;exact H7).
     tauto.
  +  inversion H1;subst.
     inversion H2;subst.
     inversion H3;subst.
     exists LO, hi.
     assert (optionZ_le (Some LO) (Some LO)) by (simpl;lia).
     assert (SearchTree (Some LO) (T (T x n1 y) n2 z) (Some hi)).
     { constructor;[constructor;tauto|tauto]. }
     pose proof optionZ_lt_SearchTree _ _ _ H6.
     assert (SearchTree_half_in (Some LO) [] (Some hi)) by (constructor;exact H7).
     tauto.
Qed.

Lemma preserves_le: 
  forall HI LO hi lo h t t',
    optionZ_le (Some LO) (Some lo) ->
    optionZ_le (Some hi) (Some HI) ->
    SearchTree_half_in (Some lo) h (Some hi) ->
    SearchTree_half_out (Some LO) h (Some HI) ->
    SearchTree (Some lo) t (Some hi)->
    splay h t t' ->
    SearchTree (Some LO) t' (Some HI).
Proof.
  intros.
  apply splay_splay' in H4.
  revert H H0 H1 H2 H3.
  revert lo hi LO HI.
  induction_1n H4; intros.
  2:{ rename p into h'.
      pose proof step_preserves _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H.
      clear H1 H2 H3 H4 H5 H.
      destruct H6 as [lo' [hi' [? [? [? [? ?]]]]]].
      specialize (IHrt _ _ _ _ H H1 H3 H4 H2).
      exact IHrt.
    }
  inversion H1. inversion H2. subst. clear H1 H2. 
  Check looser_SearchTree.
  pose proof looser_SearchTree_le _ _ _ _ _ H H0 H3. tauto. 
Qed.

Theorem preserve: preserves.
Proof.
  unfold preserves;intros.
  apply lt_le in H.
  apply lt_le in H0.
  pose proof preserves_le _ _ _ _ _ _ _ H H0 H1 H2 H3 H4.
  exact H5.
Qed.


(* ============================================================*)
(* ===================== Proof of correct =====================*)
(* ============================================================*)

Lemma map_eq: forall lm rm: relate_map,
(forall k , lm k = rm k)->
lm=rm.
Proof.
intros.
extensionality k. apply H. 
Qed.

Lemma combine_com: 
  forall m1 m2,
    forall k, combine m1 m2 k = combine m2 m1 k.
Proof.
  intros.
  unfold combine.
  destruct (m1 k);destruct (m2 k);reflexivity.
Qed.


Lemma Abs_in:
forall t lo hi m,
Abs t m->
SearchTree lo t hi->
forall k, (m k= None/\ optionZ_lt lo hi) \/ (exists v, m k =Some v /\  optionZ_lt lo (Some k) /\ optionZ_lt (Some k) hi).
Proof.
intros. revert H k. revert m. induction H0;subst.
intros.
inversion H0;subst. left. tauto. 
intros. inversion H;subst. specialize (IHSearchTree1 lm H4 k). specialize (IHSearchTree2 rm H5 k). destruct IHSearchTree1; destruct IHSearchTree2; pose proof combine_com (relate_single (key_of_node n) (value_of_node n)) rm;
pose proof map_eq _ _ H2; rewrite H3; unfold combine .
+ destruct H0;rewrite H0;destruct H1; rewrite H1;  unfold relate_single. destruct (Z.eq_dec k (key_of_node n)). right.  pose proof optionZ_lt_SearchTree _ _ _ H0_. pose proof optionZ_lt_SearchTree _ _ _ H0_0. pose proof lt_le _ _ H8. pose proof lt_le _ _ H9. rewrite e. exists (value_of_node n).  split;tauto. left. split. tauto. pose proof optionZ_lt_cong _ _ _ H7 H6. tauto.   
+ destruct H0; rewrite H0. destruct H1 as[v[?[? ?]]]. rewrite H1. assert ((key_of_node n)<> k). simpl in H7. lia.   unfold relate_single. destruct (Z.eq_dec k (key_of_node n)). rewrite e in H9. tauto.  right. exists v. split;[reflexivity| ]. split. pose proof optionZ_lt_SearchTree _ _ _ H0_. pose proof optionZ_lt_cong _ _ _ H7 H10. tauto. tauto.
+ destruct H0 as[v[?[? ?]]]. destruct H1. rewrite H0. rewrite H1. assert ((key_of_node n)<> k). simpl in H7. lia.   unfold relate_single. destruct (Z.eq_dec k (key_of_node n)). rewrite e in H9. tauto. right. exists v. split;[reflexivity| ]. split. tauto. pose proof optionZ_lt_SearchTree _ _ _ H0_0. pose proof optionZ_lt_cong _ _ _ H10 H7.  tauto.
+ destruct H0 as[vl[?[? ?]]]. destruct H1 as[vr[?[? ?]]]. simpl in H7. simpl in H8. lia.
  Qed.

Lemma l_none_le:
  forall n r h m k v,
  SearchTree_half_in None ((R, n, r) :: h) (Some (key_of_node n)) ->
  Abs_half ((R, n, r) :: h) m ->
  m k = Some v ->
  optionZ_le (Some (key_of_node n)) (Some k).
Proof.
  intros.
  pose proof l_none_all_R _ _ _ H.
  inversion H2;subst. clear H2.
  revert n r m v H H0 H1.
  induction H4;subst;intros.
  + inversion H0;subst.
    inversion H8;subst. clear H8.
    inversion H;subst. clear H5.
    inversion H8;subst.
    { inversion H7;subst. assert( relate_default k = None ) by (unfold relate_default;reflexivity). assert((relate_single (key_of_node n) (value_of_node n) k) = Some v). { destruct (relate_single (key_of_node n) (value_of_node n) k) eqn:?H. { unfold combine in H1;rewrite H3 in H1;rewrite H4 in H1. exact H1. } unfold combine in H1;rewrite H3 in H1;rewrite H4 in H1. discriminate H1. } unfold relate_single in H4. assert(k=(key_of_node n)).  { destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H4. } rewrite H5. simpl. simpl. lia. }
    pose proof Abs_in _ _ _ _ H7 H8. specialize (H4 k).
    destruct H4.
    { destruct H4.
      assert( relate_default k = None ) by (unfold relate_default;reflexivity). assert((relate_single (key_of_node n) (value_of_node n) k) = Some v). { destruct (relate_single (key_of_node n) (value_of_node n) k) eqn:?H. { unfold combine in H1;rewrite H4 in H1;rewrite H9 in H1;rewrite H6 in H1. exact H1. } unfold combine in H1;rewrite H4 in H1;rewrite H9 in H1;rewrite H6 in H1. discriminate H1. } unfold relate_single in H9. assert(k=(key_of_node n)).  { destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H9. } rewrite H10. simpl. simpl. lia. }
    destruct H4 as [? [? [? ?]]]. apply lt_le in H5. exact H5.
  
  + inversion H;subst. 
    inversion H0;subst.
    specialize (IHall_R n r m2).
    pose proof Abs_in _ _ _ _ H10 H8.
    specialize (H2 k). 
    destruct H2.
    2:{ destruct H2 as [? [? [? ?]]]. apply lt_le in H3. exact H3. }
    destruct H2.
    destruct ((relate_single (key_of_node n0) (value_of_node n0)) k) eqn:?H. 
    { unfold relate_single in H5. assert (k=(key_of_node n0)). { destruct (Z.eq_dec k (key_of_node n0)). tauto. discriminate H5. } rewrite H7. simpl. simpl. lia. }
    assert (m2 k = Some v). { unfold combine in H1; rewrite H2 in H1; rewrite H5 in H1. destruct (m2 k);[ exact H1| discriminate H1]. }
    clear H1.
    inversion H6;subst.
    specialize (IHall_R v H6 H11 H7).
    pose proof optionZ_let_cong _ _ _ IHall_R H3.
    apply lt_le in H1; exact H1.
Qed.

Lemma r_none_le:
  forall n l h m k v,
  SearchTree_half_in (Some (key_of_node n)) ((L, n, l) :: h) None ->
  Abs_half ((L, n, l) :: h) m ->
  m k = Some v ->
  optionZ_le (Some k) (Some (key_of_node n)).
Proof.
  intros.
  pose proof r_none_all_L _ _ _ H.
  inversion H2;subst. clear H2.
  revert n l m v H H0 H1.
  induction H4;subst;intros.
  + inversion H0;subst.
    inversion H8;subst. clear H8.
    inversion H;subst. clear H2. clear H8.
    inversion H9;subst.
    { inversion H7;subst. assert( relate_default k = None ) by (unfold relate_default;reflexivity). assert((relate_single (key_of_node n) (value_of_node n) k) = Some v). { destruct (relate_single (key_of_node n) (value_of_node n) k) eqn:?H. { unfold combine in H1;rewrite H3 in H1;rewrite H4 in H1. exact H1. } unfold combine in H1;rewrite H3 in H1;rewrite H4 in H1. discriminate H1. } unfold relate_single in H4. assert(k=(key_of_node n)).  { destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H4. } rewrite H5. simpl. simpl. lia. }
    pose proof Abs_in _ _ _ _ H7 H9. specialize (H4 k).
    destruct H4.
    { destruct H4.
      assert( relate_default k = None ) by (unfold relate_default;reflexivity). assert((relate_single (key_of_node n) (value_of_node n) k) = Some v). { destruct (relate_single (key_of_node n) (value_of_node n) k) eqn:?H. { unfold combine in H1;rewrite H4 in H1;rewrite H8 in H1;rewrite H6 in H1. exact H1. } unfold combine in H1;rewrite H4 in H1;rewrite H8 in H1;rewrite H6 in H1. discriminate H1. } unfold relate_single in H8. assert(k=(key_of_node n)).  { destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H8. } rewrite H10. simpl. simpl. lia. }
    destruct H4 as [? [? [? ?]]]. apply lt_le in H6. exact H6.
  
  + inversion H;subst. clear H2. 
    inversion H0;subst.
    specialize (IHall_L n l m2).
    pose proof Abs_in _ _ _ _ H10 H9.
    specialize (H2 k). 
    destruct H2.
    2:{ destruct H2 as [? [? [? ?]]]. apply lt_le in H5. exact H5. }
    destruct H2.
    destruct ((relate_single (key_of_node n0) (value_of_node n0)) k) eqn:?H. 
    { unfold relate_single in H5. assert (k=(key_of_node n0)). { destruct (Z.eq_dec k (key_of_node n0)). tauto. discriminate H5. } rewrite H6. simpl. simpl. lia. }
    assert (m2 k = Some v). { unfold combine in H1; rewrite H2 in H1; rewrite H5 in H1. destruct (m2 k);[ exact H1| discriminate H1]. }
    clear H1.
    inversion H8;subst.
    specialize (IHall_L v H8 H11 H6).
    pose proof optionZ_lte_cong _ _ _ H3 IHall_L.
    apply lt_le in H1; exact H1.
Qed.

Lemma Abs_in_half:
forall t lo hi m ,
Abs_half t m->
SearchTree_half_in (Some lo) t (Some hi)->
(* SearchTree_half_out LO t HI-> *)
forall k, m k= None \/ (exists v, m k =Some v /\  (optionZ_le (Some k) (Some lo) \/ optionZ_le (Some hi) (Some k))).
Proof.
  intros. revert H k. revert m. induction H0;subst;intros. 
  + inversion H0;subst.  left. tauto.
  + inversion H1;subst.
    specialize (IHSearchTree_half_in m2 H8 k).
    destruct IHSearchTree_half_in.
    { pose proof Abs_in _ _ _ _ H7 H.
      specialize (H3 k). 
      destruct H3.
      { destruct H3. destruct ((relate_single (key_of_node n) (value_of_node n)) k) eqn: ?H. 
        { right. exists v. split;[unfold combine;rewrite H2;rewrite H3;rewrite H5;reflexivity|]. unfold relate_single in H5. assert(k=(key_of_node n)). { destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H5. } rewrite H6 in *. left. simpl. lia. }
        left. unfold combine;rewrite H2;rewrite H3;rewrite H5;reflexivity. }
      destruct H3 as [v [? [? ?]]].
      destruct ((relate_single (key_of_node n) (value_of_node n)) k) eqn: ?H.
      { left. unfold combine;rewrite H2;rewrite H3;rewrite H6;reflexivity. }
      right. exists v. split;[unfold combine; rewrite H2;rewrite H3;rewrite H6;reflexivity|]. left. apply lt_le in H5;exact H5. }
    destruct H2 as [v [? ?]].
    destruct (m1 k) eqn: ?H;destruct ((relate_single (key_of_node n) (value_of_node n)) k) eqn: ?H.
    { left. assert(k=(key_of_node n)). {unfold relate_single in H5 . destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H5. } rewrite H6 in *. pose proof Abs_in _ _ _ _ H7 H. specialize (H9 (key_of_node n)). destruct H9. { destruct H9. rewrite H4 in H9. discriminate H9. } destruct H9 as [? [? [? ?]]]. simpl in H11. lia. }
    { left. unfold combine; rewrite H2;rewrite H4;rewrite H5;reflexivity. }
    { left. unfold combine; rewrite H2;rewrite H4;rewrite H5;reflexivity. }
    { right. exists v. split;[unfold combine; rewrite H2;rewrite H4;rewrite H5;reflexivity|]. 
      destruct H3;[|right;exact H3].
      destruct lo0 ;[rename k0 into lo0|].
      { left. apply optionZ_lt_SearchTree in H. pose proof optionZ_lte_cong _ _ _ H H3. apply lt_le in H6;exact H6. }
      inversion H0;subst.
      { inversion H8. rewrite <- H10 in H2. unfold relate_default in H2. discriminate H2. }
      pose proof l_none_le _ _ _ _ _ _ H0 H8 H2.
      right. exact H10. }
  + inversion H1;subst.
    specialize (IHSearchTree_half_in m2 H8 k).
    destruct IHSearchTree_half_in.
    { pose proof Abs_in _ _ _ _ H7 H.
      specialize (H3 k). 
      destruct H3.
      { destruct H3. destruct ((relate_single (key_of_node n) (value_of_node n)) k) eqn: ?H. 
        { right. exists v. split;[unfold combine;rewrite H2;rewrite H3;rewrite H5;reflexivity|]. unfold relate_single in H5. assert(k=(key_of_node n)). { destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H5. } rewrite H6 in *. right. simpl. lia. }
        left. unfold combine;rewrite H2;rewrite H3;rewrite H5;reflexivity. }
      destruct H3 as [v [? [? ?]]].
      destruct ((relate_single (key_of_node n) (value_of_node n)) k) eqn: ?H.
      { left. unfold combine;rewrite H2;rewrite H3;rewrite H6;reflexivity. }
      right. exists v. split;[unfold combine; rewrite H2;rewrite H3;rewrite H6;reflexivity|]. right. apply lt_le in H4;exact H4. }
    destruct H2 as [v [? ?]].
    destruct (m1 k) eqn: ?H;destruct ((relate_single (key_of_node n) (value_of_node n)) k) eqn: ?H.
    { left. assert(k=(key_of_node n)). {unfold relate_single in H5 . destruct(Z.eq_dec k (key_of_node n)). tauto. discriminate H5. } rewrite H6 in *. pose proof Abs_in _ _ _ _ H7 H. specialize (H9 (key_of_node n)). destruct H9. { destruct H9. rewrite H4 in H9. discriminate H9. } destruct H9 as [? [? [? ?]]]. simpl in H10. lia. }
    { left. unfold combine; rewrite H2;rewrite H4;rewrite H5;reflexivity. }
    { left. unfold combine; rewrite H2;rewrite H4;rewrite H5;reflexivity. }
    { right. exists v. split;[unfold combine; rewrite H2;rewrite H4;rewrite H5;reflexivity|]. 
      destruct H3;[left;exact H3|].
      destruct hi0 ;[rename k0 into hi0|].
      { right. apply optionZ_lt_SearchTree in H. pose proof optionZ_let_cong _ _ _ H3 H. apply lt_le in H6;exact H6. }
      inversion H0;subst.
      { inversion H8. rewrite <- H10 in H2. unfold relate_default in H2. discriminate H2. }
      pose proof r_none_le _ _ _ _ _ _ H0 H8 H2.
      left. exact H10. }
Qed.

Lemma step_correct_le: 
  forall h t h' t' m1 m2 lo hi LO HI,
    splay_step (h,t) (h',t') ->
    Abs_half h m1 ->
    Abs t m2 ->
    SearchTree (Some lo) t (Some hi)->
    (SearchTree_half_in (Some lo) h (Some hi))->
    (SearchTree_half_out (Some LO) h (Some HI))->
    optionZ_le (Some LO) (Some lo)->
    optionZ_le (Some hi) (Some HI)->
    (exists  lo' hi' LO' HI' m1' m2',
      (SearchTree (Some lo') t' (Some hi') )/\
      (SearchTree_half_in (Some lo') h' (Some hi')) /\ (SearchTree_half_out (Some LO') h' (Some HI')) /\  optionZ_le (Some LO') (Some lo') /\
    optionZ_le (Some hi') (Some HI') /\ (Abs_half h' m1') /\ (Abs t' m2') /\ 
      (forall k, combine m1' m2' k = combine m1 m2 k)).
Proof.
  intros.
  pose proof step_preserves _ _ _ _ _ _ _ _ H5 H6 H3 H4 H2 H.
  destruct H7 as [lo' [hi' [? [? [? [? ?]]]]]].
  exists lo',hi', LO ,HI. 
  inversion H;subst.
  + inversion H0;subst. inversion H1;subst. inversion H18;subst. exists m2.  exists (combine lm (combine (relate_single (key_of_node n1) (value_of_node n1)) 
     (combine rm (combine (relate_single (key_of_node n2) (value_of_node n2)) 
     (combine m0 (combine (relate_single (key_of_node n3) (value_of_node n3))
      m1)))))). split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split. constructor;try tauto. constructor;try tauto.  constructor;try tauto. intros.  clear H7 H8 H11 H5 H6 H3 H4 H H0 H18 H1. inversion H9;subst;clear H9. inversion H6;subst;clear H6. inversion H8;subst;clear H8. pose proof Abs_in _ _ _ _ H16 H5 k; pose proof optionZ_lt_SearchTree _ _ _ H5; clear H16 H5. pose proof Abs_in _ _ _ _ H19 H7 k; pose proof optionZ_lt_SearchTree _ _ _ H7; clear H19 H7. pose proof Abs_in _ _ _ _ H17 H6 k; pose proof optionZ_lt_SearchTree _ _ _ H6; clear H17 H6. clear H2. pose proof Abs_in _ _ _ _ H21 H9 k. clear H21 H9.
pose proof Abs_in_half _ _ _ _ H22 H10 k; clear H22 H10. destruct H. 
2:{ destruct H1.
    2:{ destruct H as [v[?[? ? ]]]. destruct H1 as [v1[?[? ? ]]]. simpl in H9. simpl in H8. 
lia. }
    destruct H4.
    2:{ destruct H as [v[?[? ? ]]]. destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{ destruct H as [v[?[? ? ]]]. destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H6; destruct H1;destruct H4;destruct H2.  
    2:{ destruct H as [v[?[? ? ]]]. destruct H6 as [v1[? ?]]. simpl in *. lia. }
    destruct H as[v[?[? ?]]]. unfold combine.  rewrite H1, H4,H2,H6,H. clear H1 H2 H4 H6 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
          destruct H. clear H7. 
      destruct H1.
  2:{ destruct H1 as [v[?[? ? ]]]. destruct H4.
    2:{ destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H6.
    2:{ destruct H6 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4;destruct H2. unfold combine. rewrite H1, H4,H2,H6,H. clear H1 H2 H4 H6 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H1. 
      destruct H4.
    2:{ destruct H4 as [v[?[? ? ]]].  destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H6.
    2:{ destruct H6 as [v1[? ? ]]. simpl in *. lia. }
      destruct H2. unfold combine. rewrite H1,H2,H6, H4,H. clear H1 H2 H6 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H2.   
      2:{destruct H2 as [v[?[? ?] ]]. destruct H6.
    2:{ destruct H6 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4. unfold combine. rewrite H1,H2,H6, H4,H. clear H1 H2 H6 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H6;destruct H4;destruct H2.
      1:{unfold combine. rewrite H1,H2,H6, H4,H. clear H1 H2 H6 H4 H. simpl in *. unfold relate_single. destruct (Z.eq_dec k (key_of_node n1)).
      1:{ destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. }
    destruct (Z.eq_dec k (key_of_node n2)). 1:{ destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. } destruct (Z.eq_dec k (key_of_node n3));try tauto. }
    destruct H6 as [v[? ?]]. destruct H10;simpl in *;
   unfold combine; rewrite H1,H2,H6, H4,H; clear H1 H2 H6 H4 H; simpl in *; unfold relate_single;  destruct (Z.eq_dec k (key_of_node n1));try lia; destruct (Z.eq_dec k (key_of_node n2));try lia; destruct (Z.eq_dec k (key_of_node n3));try lia; tauto. 
 + inversion H0;subst. inversion H1;subst. inversion H18;subst. exists m2.  exists (combine(combine(combine m1(combine (relate_single(key_of_node n1)(value_of_node n1)) m0))(combine(relate_single(key_of_node n2)(value_of_node n2)) lm)) (combine (relate_single(key_of_node n3)(value_of_node n3)) rm)).  split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split. constructor;try tauto. constructor;try tauto.  constructor;try tauto. intros.  clear H7 H8 H11 H5 H6 H3 H4 H H0 H18 H1. inversion H9;subst;clear H9. inversion H5;subst;clear H5. inversion H7;subst;clear H7. pose proof Abs_in _ _ _ _ H21 H5 k; pose proof optionZ_lt_SearchTree _ _ _ H5; clear H21 H5.  pose proof Abs_in _ _ _ _ H17 H9 k; pose proof optionZ_lt_SearchTree _ _ _ H9; clear H17 H9. pose proof Abs_in _ _ _ _ H16 H8 k; pose proof optionZ_lt_SearchTree _ _ _ H8; clear H16 H8. clear H2. pose proof Abs_in _ _ _ _ H19 H6 k; clear H19 H6.
pose proof Abs_in_half _ _ _ _ H22 H10 k; clear H22 H10.  destruct H. 
2:{ destruct H1. 
    2:{ destruct H as [v[?[? ? ]]]. destruct H1 as [v1[?[? ? ]]]. simpl in H9. simpl in H8. 
lia. }
    destruct H4.
    2:{ destruct H as [v[?[? ? ]]]. destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{ destruct H as [v[?[? ? ]]]. destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H6; destruct H1;destruct H4;destruct H2.  
    2:{ destruct H as [v[?[? ? ]]]. destruct H6 as [v1[? ?]]. simpl in *. lia. }
    destruct H as[v[?[? ?]]]. unfold combine.  rewrite H1, H4,H2,H6,H. clear H1 H2 H4 H6 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
          destruct H. clear H7. 
      destruct H1.
  2:{ destruct H1 as [v[?[? ? ]]]. destruct H4.
    2:{ destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H6.
    2:{ destruct H6 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4;destruct H2. unfold combine. rewrite H1, H4,H2,H6,H. clear H1 H2 H4 H6 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H1. 
      destruct H4.
    2:{ destruct H4 as [v[?[? ? ]]].  destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H6.
    2:{ destruct H6 as [v1[? ? ]]. simpl in *. lia. }
      destruct H2. unfold combine. rewrite H1,H2,H6, H4,H. clear H1 H2 H6 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H2.  
      2:{destruct H2 as [v[?[? ?] ]]. destruct H6.
    2:{ destruct H6 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4. unfold combine. rewrite H1,H2,H6, H4,H. clear H1 H2 H6 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H6;destruct H4;destruct H2.
      1:{unfold combine. rewrite H1,H2,H6, H4,H. clear H1 H2 H6 H4 H. simpl in *. unfold relate_single. destruct (Z.eq_dec k (key_of_node n1)).
      1:{ destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. }
    destruct (Z.eq_dec k (key_of_node n2)). 1:{ destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. } destruct (Z.eq_dec k (key_of_node n3));try tauto. }
    destruct H6 as [v[? ?]]. destruct H10;simpl in *;
   unfold combine; rewrite H1,H2,H6, H4,H; clear H1 H2 H6 H4 H; simpl in *; unfold relate_single;  destruct (Z.eq_dec k (key_of_node n1));try lia; destruct (Z.eq_dec k (key_of_node n2));try lia; destruct (Z.eq_dec k (key_of_node n3));try lia; tauto. 
+  inversion H0;subst. inversion H1;subst. inversion H18;subst. exists m2.  exists (combine(combine m0 (combine (relate_single(key_of_node n1)(value_of_node n1)) lm))(combine(relate_single(key_of_node n2)(value_of_node n2))(combine rm (combine(relate_single(key_of_node n3)(value_of_node n3)) m1)))). split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split. constructor;try tauto. constructor;try tauto.  constructor;try tauto. intros.  clear H7 H8 H11 H5 H6 H3 H4 H H0 H18 H1. inversion H9;subst;clear H9. inversion H5;subst;clear H5. inversion H6;subst;clear H6. pose proof Abs_in _ _ _ _ H21 H9 k; pose proof optionZ_lt_SearchTree _ _ _ H9; clear H21 H9.  pose proof Abs_in _ _ _ _ H17 H7 k; pose proof optionZ_lt_SearchTree _ _ _ H7; clear H17 H7. pose proof Abs_in _ _ _ _ H16 H8 k; pose proof optionZ_lt_SearchTree _ _ _ H8; clear H16 H8. clear H2. pose proof Abs_in _ _ _ _ H19 H5 k; pose proof optionZ_lt_SearchTree _ _ _ H5; clear H19 H5.
pose proof Abs_in_half _ _ _ _ H22 H10 k; clear H22 H10.  destruct H. 
2:{ destruct H1. 
    2:{ destruct H as [v[?[? ? ]]]. destruct H1 as [v1[?[? ? ]]]. simpl in *. lia. }
    destruct H4.
    2:{ destruct H as [v[?[? ? ]]]. destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{ destruct H as [v[?[? ? ]]]. destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H5; destruct H1;destruct H4;destruct H2.  
    2:{ destruct H as [v[?[? ? ]]]. destruct H5 as [v1[? ?]]. simpl in *. lia. }
    destruct H as[v[?[? ?]]]. unfold combine.  rewrite H1, H4,H2,H5,H. clear H1 H2 H4 H5 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
          destruct H. clear H8. 
      destruct H1.
  2:{ destruct H1 as [v[?[? ? ]]]. destruct H4.
    2:{ destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H5.
    2:{ destruct H5 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4;destruct H2. unfold combine. rewrite H1, H4,H2,H5,H. clear H1 H2 H4 H5 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H1. 
      destruct H4.
    2:{ destruct H4 as [v[?[? ? ]]].  destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H5.
    2:{ destruct H5 as [v1[? ? ]]. simpl in *. lia. }
      destruct H2. unfold combine. rewrite H1,H2,H5, H4,H. clear H1 H2 H5 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H2.  
      2:{destruct H2 as [v[?[? ?] ]]. destruct H5.
    2:{ destruct H5 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4. unfold combine. rewrite H1,H2,H5, H4,H. clear H1 H2 H5 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H5;destruct H4;destruct H2.
      1:{unfold combine. rewrite H1,H2,H5, H4,H. clear H1 H2 H5 H4 H. simpl in *. unfold relate_single. destruct (Z.eq_dec k (key_of_node n1)).
      1:{ destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. }
    destruct (Z.eq_dec k (key_of_node n2)). 1:{ destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. } destruct (Z.eq_dec k (key_of_node n3));try tauto. }
    destruct H5 as [v[? ?]]. destruct H10;simpl in *;
   unfold combine; rewrite H1,H2,H5, H4,H; clear H1 H2 H5 H4 H; simpl in *; unfold relate_single;  destruct (Z.eq_dec k (key_of_node n1));try lia; destruct (Z.eq_dec k (key_of_node n2));try lia; destruct (Z.eq_dec k (key_of_node n3));try lia; tauto. 
+ inversion H0;subst. inversion H1;subst. inversion H18;subst. exists m2.  exists (combine (combine m1 (combine(relate_single(key_of_node n1)(value_of_node n1)) lm))(combine (relate_single(key_of_node n2)(value_of_node n2))(combine rm (combine(relate_single(key_of_node n3)(value_of_node n3)) m0)))). split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split. constructor;try tauto. constructor;try tauto.  constructor;try tauto. intros.  clear H7 H8 H11 H5 H6 H3 H4 H H0 H18 H1. inversion H9;subst;clear H9. inversion H5;subst;clear H5. inversion H6;subst;clear H6. pose proof Abs_in _ _ _ _ H17 H9 k; pose proof optionZ_lt_SearchTree _ _ _ H9; clear H17 H9.  pose proof Abs_in _ _ _ _ H21 H7 k; pose proof optionZ_lt_SearchTree _ _ _ H7; clear H21 H7. pose proof Abs_in _ _ _ _ H16 H8 k; pose proof optionZ_lt_SearchTree _ _ _ H8; clear H16 H8. clear H2. pose proof Abs_in _ _ _ _ H19 H5 k; pose proof optionZ_lt_SearchTree _ _ _ H5; clear H19 H5.
pose proof Abs_in_half _ _ _ _ H22 H10 k; clear H22 H10.  destruct H. 
2:{ destruct H1. 
    2:{ destruct H as [v[?[? ? ]]]. destruct H1 as [v1[?[? ? ]]]. simpl in *. lia. }
    destruct H4.
    2:{ destruct H as [v[?[? ? ]]]. destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{ destruct H as [v[?[? ? ]]]. destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H5; destruct H1;destruct H4;destruct H2.  
    2:{ destruct H as [v[?[? ? ]]]. destruct H5 as [v1[? ?]]. simpl in *. lia. }
    destruct H as[v[?[? ?]]]. unfold combine.  rewrite H1, H4,H2,H5,H. clear H1 H2 H4 H5 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
          destruct H. clear H8. 
      destruct H1.
  2:{ destruct H1 as [v[?[? ? ]]]. destruct H4.
    2:{ destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H5.
    2:{ destruct H5 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4;destruct H2. unfold combine. rewrite H1, H4,H2,H5,H. clear H1 H2 H4 H5 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H1. 
      destruct H4.
    2:{ destruct H4 as [v[?[? ? ]]].  destruct H2.
    2:{destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H5.
    2:{ destruct H5 as [v1[? ? ]]. simpl in *. lia. }
      destruct H2. unfold combine. rewrite H1,H2,H5, H4,H. clear H1 H2 H5 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H2.  
      2:{destruct H2 as [v[?[? ?] ]]. destruct H5.
    2:{ destruct H5 as [v1[? ? ]]. simpl in *. lia. }
      destruct H4. unfold combine. rewrite H1,H2,H5, H4,H. clear H1 H2 H5 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto.  }
      destruct H5;destruct H4;destruct H2.
      1:{unfold combine. rewrite H1,H2,H5, H4,H. clear H1 H2 H5 H4 H. simpl in *. unfold relate_single. destruct (Z.eq_dec k (key_of_node n1)).
      1:{ destruct (Z.eq_dec k (key_of_node n2));try lia. destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. }
    destruct (Z.eq_dec k (key_of_node n2)). 1:{ destruct (Z.eq_dec k (key_of_node n3));try lia. tauto. } destruct (Z.eq_dec k (key_of_node n3));try tauto. }
    destruct H5 as [v[? ?]]. destruct H10;simpl in *;
   unfold combine; rewrite H1,H2,H5, H4,H; clear H1 H2 H5 H4 H; simpl in *; unfold relate_single;  destruct (Z.eq_dec k (key_of_node n1));try lia; destruct (Z.eq_dec k (key_of_node n2));try lia; destruct (Z.eq_dec k (key_of_node n3));try lia; tauto. 
+ inversion H1;subst;clear H1. inversion H0;subst;clear H0. inversion H19;subst;clear H19. exists relate_default. exists (combine lm (combine (relate_single (key_of_node n1)(value_of_node n1)) (combine rm (combine (relate_single(key_of_node n2)(value_of_node n2)) m0)))).  split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. constructor. split. constructor;try tauto. constructor;try tauto. inversion H9;subst;clear H9. inversion H19;subst;clear H19. intros. clear H H4 H3 H5 H6 H7 H8 H11 H10. pose proof Abs_in _ _ _ _ H16 H15 k; pose proof optionZ_lt_SearchTree _ _ _ H15; clear H16 H15.  pose proof Abs_in _ _ _ _ H17 H14 k; pose proof optionZ_lt_SearchTree _ _ _ H14; clear H17 H14. pose proof Abs_in _ _ _ _ H18 H20 k; pose proof optionZ_lt_SearchTree _ _ _ H20; clear H18 H20. clear H2. destruct H. 
2:{ destruct H1. 
    2:{ destruct H as [v[?[? ? ]]]. destruct H1 as [v1[?[? ? ]]]. simpl in *. lia. }
    destruct H4.
    2:{ destruct H as [v[?[? ? ]]]. destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H as[v[?[? ?]]]. unfold combine. destruct H1;destruct H2;clear H8.  rewrite H1, H2,H. clear H1 H2 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia.  tauto.  }
          destruct H. clear H2. 
      destruct H1.
  2:{ destruct H1 as [v[?[? ? ]]]. destruct H4.
    2:{ destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }     
      destruct H4. unfold combine. clear H7. rewrite H1, H4,H. clear H1 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. tauto.  }
      destruct H1. 
      destruct H4.
    2:{ destruct H4 as [v[?[? ? ]]]. unfold combine,relate_single.  rewrite H1,H4,H. clear H1 H4 H.  simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia.  tauto.  }
      destruct H4. unfold combine. clear H6. rewrite H1, H4,H. clear H1 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1)). 
      1:{  destruct (Z.eq_dec k (key_of_node n2));try lia. tauto.  }
      destruct (Z.eq_dec k (key_of_node n2));try tauto. 
+ inversion H1;subst;clear H1. inversion H0;subst;clear H0. inversion H19;subst;clear H19. exists relate_default. exists (combine (combine m0 (combine (relate_single(key_of_node n1)(value_of_node n1)) lm))(combine(relate_single (key_of_node n2)(value_of_node n2)) rm)).  split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. split ;try tauto. constructor. split. constructor;try tauto. constructor;try tauto. inversion H9;subst;clear H9. inversion H15;subst;clear H15. intros. clear H H4 H3 H5 H6 H7 H8 H11 H10. pose proof Abs_in _ _ _ _ H16 H20 k; pose proof optionZ_lt_SearchTree _ _ _ H20; clear H16 H20.  pose proof Abs_in _ _ _ _ H17 H19 k; pose proof optionZ_lt_SearchTree _ _ _ H19; clear H17 H19. pose proof Abs_in _ _ _ _ H18 H14 k; pose proof optionZ_lt_SearchTree _ _ _ H14; clear H18 H14. clear H2. destruct H. 
2:{ destruct H1. 
    2:{ destruct H as [v[?[? ? ]]]. destruct H1 as [v1[?[? ? ]]]. simpl in *. lia. }
    destruct H4.
    2:{ destruct H as [v[?[? ? ]]]. destruct H2 as [v1[?[? ? ]]]. simpl in *.  lia. }
    destruct H as[v[?[? ?]]]. unfold combine. destruct H1;destruct H2;clear H8.  rewrite H1, H2,H. clear H1 H2 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia.  tauto.  }
          destruct H. clear H2. 
      destruct H1.
  2:{ destruct H1 as [v[?[? ? ]]]. destruct H4.
    2:{ destruct H4 as [v1[?[? ? ]]]. simpl in *.  lia. }     
      destruct H4. unfold combine. clear H7. rewrite H1, H4,H. clear H1 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia. tauto.  }
      destruct H1. 
      destruct H4.
    2:{ destruct H4 as [v[?[? ? ]]]. unfold combine,relate_single.  rewrite H1,H4,H. clear H1 H4 H.  simpl in *. destruct (Z.eq_dec k (key_of_node n1));try lia. destruct (Z.eq_dec k (key_of_node n2));try lia.  tauto.  }
      destruct H4. unfold combine. clear H6. rewrite H1, H4,H. clear H1 H4 H. unfold relate_single. simpl in *. destruct (Z.eq_dec k (key_of_node n1)). 
      1:{  destruct (Z.eq_dec k (key_of_node n2));try lia. tauto.  }
      destruct (Z.eq_dec k (key_of_node n2));try tauto. 
      Qed.

 
Lemma combine_default:
  forall m ,
  forall k, m k= combine relate_default m k.
Proof.
intros. unfold combine, relate_default. induction m;tauto. 
Qed.

Lemma correct_le:
   forall h t t' m1 m2 lo hi LO HI,
    Abs_half h m1 ->
    Abs t m2 ->
    splay h t t' ->
    SearchTree (Some lo) t (Some hi)->(* new *)
    SearchTree_half_in (Some lo) h (Some hi)->(* new *)
    SearchTree_half_out (Some LO) h (Some HI)->(* new *)
    optionZ_le (Some LO) (Some lo) ->
    optionZ_le (Some hi) (Some HI) ->
    Abs t' (combine m1 m2).
Proof.
  intros.
  apply splay_splay' in H1.
  revert H H0 H2 H3 H4 H5 H6 .
  revert m1 m2 lo hi LO HI.
  induction_1n H1;intros.
  + inversion H;subst.
    pose proof combine_default m2 . pose proof map_eq _ _ H1. rewrite <-H7. tauto.
  + 
  pose proof step_correct_le _ _ _ _ _ _ _ _ _ _ H H1 H2 H3 H4 H5 H6 H7.
  destruct H8 as [lo' [hi'[LO'[HI'[m1'[m2'[?[?[?[?[?[?[? ?]]]]]]]]]]]]].
  specialize (IHrt _ _ _ _ _ _  H13 H14 H8 H9 H10 H11 H12). pose proof map_eq _ _ H15. rewrite<- H16 . tauto.
   Qed.
   
Theorem correctness: correct.
Proof.
unfold correct;intros.
pose proof lt_le _ _ H6. pose proof lt_le _ _ H5.
pose proof correct_le _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H8 H7. tauto. 
Qed.

(* Long may the sun shine! *)
(* 2021-06-08 22:13 *)
