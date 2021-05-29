Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.RTClosure.
Import ListNotations.
Local Open Scope Z.
Require Import PL.Imp.

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
| Abs_E : forall m, (forall k, m k = relate_default k) -> Abs E m
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
| Abs_half_nil : forall m, (forall k, m k = relate_default k) -> Abs_half nil m
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
  forall h t t' m1 m2,
    Abs_half h m1 ->
    Abs t m2 ->
    splay h t t' ->
    Abs t' (combine m1 m2).

Print clos_refl_trans.

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
  + 
    inversion H1;subst.
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
  +


    (* pose proof inner_border_expansion_R _ _ _ _ _ _ _ H0 H1 H2.
    destruct H5 as [hi0 [? [? ?]]].
    inversion H2;subst.
    pose proof inner_border_expansion_R _ _ _ _ _ _ _ H7 H5 H12.
    destruct H8 as [hi1 [? [? ?]]].
    inversion H12;subst.
    exists lo, hi1.
    split;[exact H|].
    split;[exact H10|].
    split;[|split;[exact H8|exact H18]].
    clear H5 H7 H12 H14 H15 H8 H10 H18 H20 H21.
    inversion H3;subst;clear H3.
    inversion H1;subst.
    inversion H8;subst.
    constructor;[tauto|].
    constructor;[tauto|].
    constructor;tauto. *) 
  
Admitted.


Lemma looser_SearchTree_le:
  forall lo' hi' lo hi t,
    optionZ_le lo (Some lo') -> 
    optionZ_le (Some hi') hi ->
    SearchTree (Some lo') t (Some hi') ->
    SearchTree lo t hi.
Proof.
Admitted.

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


Lemma combine_com: 
  forall m1 m2,
    forall k, combine m1 m2 k = combine m2 m1 k.
Proof.
  intros.
  unfold combine.
  destruct (m1 k);destruct (m2 k);reflexivity.
Qed.

Lemma combine_asso:
  forall m1 m2 m3, 
    forall k, combine m1 (combine m2 m3) k = combine (combine m1 m2) m3 k.
Proof.
  intros.
  unfold combine.
  destruct (m1 k) eqn:H1;destruct (m2 k) eqn:H2;destruct (m3 k) eqn:H3. try reflexivity.
Admitted.
  
Lemma step_correct: 
  forall h t h' t' m1 m2 ,
    splay_step (h,t) (h',t') ->
    Abs_half h m1 ->
    Abs t m2 ->
    exists m1' m2',
      (Abs_half h' m1') /\ (Abs t' m2') /\ 
      (forall k, combine m1' m2' k = combine m1 m2 k).
Proof.
  intros.
  inversion H;subst.
  + inversion H0;subst.
    inversion H8;subst.
    inversion H1;subst.
    exists m4. 
    exists (combine lm (combine (relate_single (key_of_node n1) (value_of_node n1)) 
     (combine rm (combine (relate_single (key_of_node n2) (value_of_node n2)) 
     (combine m0 (combine (relate_single (key_of_node n3) (value_of_node n3))
      m1)))))).
    split; try split.
    { exact H10. }
    { constructor;try tauto; try constructor;try tauto;try constructor;tauto . }
    intros.
    simpl.
    
Admitted.

Lemma combine_default:
  forall m0,
  (forall k, m0 k = relate_default k)->
  (forall m,
    forall k, m k = combine m0 m k ).
Proof.
intros. unfold combine, relate_default. induction m. specialize (H k). rewrite H. simpl. reflexivity. specialize (H k). rewrite H. simpl. reflexivity. 
Qed.


Lemma Abs_congr: 
  forall t m1 m2, 
    (forall k, m1 k = m2 k) ->
    Abs t m1 -> 
    Abs t m2.
Proof.
  intros.
  revert m2 H.
  induction H0;intros.
  + apply Abs_E.
    intros.
    specialize (H k).
    specialize (H0 k).
    rewrite <- H0.
    exact H.
  + (* set (m2l := fun k => if (lm k) then m2 k else None).
    set (m2r := fun k => if (rm k) then m2 k else None).
    specialize (IHAbs1 m2l).
    specialize (IHAbs2 m2r).
    assert (forall k : Key, lm k = m2l k).
    { intros. destruct (lm k).  *)
    
    set(ml := fun k => if Some (lm k) then m2 k else None).
    specialize (IHAbs1 ml).
    assert (forall k : Key, lm k = ml k). 
    intros.
    - unfold ml. destruct (lm k) eqn:?H.
      unfold ml in IHAbs1.
    set(m4 := fun k => if rm k then m2 k else None).
Admitted.

Admitted.



Theorem correctness: correct.
Proof.
  unfold correct;intros.
  apply splay_splay' in H1.
  revert H H0.
  revert m1 m2.
  induction_1n H1;intros.
  + inversion H;subst.
    pose proof combine_default m1 H1 m2. 
    pose proof Abs_congr t' m2 (combine m1 m2) H2 H0. 
    exact H3.
  + pose proof step_correct _ _ _ _ _ _ H H1 H2.
    destruct H3 as [m1' [m2' [? [? ?]]]].
    clear H H1 H2.
    specialize (IHrt _ _ H3 H4).
    clear H3 H4.
    pose proof Abs_congr t' (combine m1' m2') (combine m1 m2) H5 IHrt.
    exact H.
Qed.



(* 2021-05-07 20:39 *)
