Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.RTClosure.
Import ListNotations.
Local Open Scope Z.

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
| Abs_E : Abs E relate_default
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
    optionZ_lt LO lo ->
    optionZ_lt hi HI ->
    SearchTree_half_in lo h hi ->
    SearchTree_half_out LO h HI ->
    SearchTree lo t hi ->
    splay h t t' ->
    SearchTree LO t' HI.

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
  intros.
  unfold splay'.
  unfold splay in H.
  exact H.
Qed.

Lemma step_preserves: 
  forall h h' t t' lo hi LO HI,
    optionZ_lt LO lo ->
    optionZ_lt hi HI ->
    SearchTree_half_in lo h hi ->
    SearchTree_half_out LO h HI ->
    SearchTree lo t hi ->
    splay_step (h,t) (h',t') ->
    exists lo' hi',
      (optionZ_lt LO lo') /\
      (optionZ_lt hi' HI) /\
      (SearchTree lo' t' hi') /\ 
      (SearchTree_half_in lo' h' hi') /\ 
      (SearchTree_half_out LO h' HI).
Proof.
  intros.
  inversion H2;subst.
  +
Admitted.

Lemma in_bounded_by_out: 
  forall lo hi LO HI h,
    h <> nil ->
    SearchTree_half_in lo h hi ->
    SearchTree_half_out LO h HI ->
    (optionZ_lt LO lo) /\ (optionZ_lt hi HI).
Proof.
Admitted.

Lemma looser_SearchTree: 
  forall lo' hi' lo hi t,
    optionZ_lt lo lo' -> 
    optionZ_lt hi' hi ->
    SearchTree lo' t hi' ->
    SearchTree lo t hi.
Proof.
Admitted.

Print SearchTree.

Lemma subtree_SearchTree:
  forall lo hi l n r,
    SearchTree lo (T l n r) hi ->
    (SearchTree lo l hi) /\ (SearchTree lo r hi).
Proof.
Admitted.


Theorem preserve: preserves.
Proof.
  unfold preserves;intros.
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
  pose proof looser_SearchTree _ _ _ _ _ H H0 H3.
  exact H4.
Qed.


Lemma step_correct: 
  forall h t h' t' m1 m2 ,
    splay_step (h,t) (h',t') ->
    Abs_half h m1 ->
    Abs t m2 ->
    exists m1' m2',
      (Abs_half h' m1') /\ (Abs t' m2') /\ 
      (forall k, combine m1' m2' k = combine m1 m2 k).
Proof.
Admitted.

Lemma combine_default:
  forall m ,
    forall k, m k = combine relate_default m k .
Proof.
Admitted.

Lemma Abs_congr: 
  forall t m1 m2, 
    (forall k, m1 k = m2 k) ->
    Abs t m1 -> 
    Abs t m2.
Proof.
Admitted.

Theorem correctness: correct.
Proof.
  unfold correct;intros.
  apply splay_splay' in H1.
  revert H H0.
  revert m1 m2.
  induction_1n H1;intros.
  + inversion H;subst.
    pose proof combine_default m2.
    pose proof Abs_congr t' m2 (combine relate_default m2) H1 H0.
    exact H2.
  + pose proof step_correct _ _ _ _ _ _ H H1 H2.
    destruct H3 as [m1' [m2' [? [? ?]]]].
    clear H H1 H2.
    specialize (IHrt _ _ H3 H4).
    clear H3 H4.
    pose proof Abs_congr t' (combine m1' m2') (combine m1 m2) H5 IHrt.
    exact H.
Admitted.



(* 2021-05-07 20:39 *)
