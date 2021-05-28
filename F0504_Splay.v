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
  intros.
  unfold splay'.
  unfold splay in H.
  exact H.
Qed.


Lemma inner_border_expansion_L: 
  forall lo hi LO HI n l (h:partial_tree),
    optionZ_lt (Some LO) (Some lo) ->
    SearchTree_half_in (Some lo) ((L, n, l)::h) (Some hi) ->
    SearchTree_half_out (Some LO) ((L, n, l)::h) (Some HI) ->
    exists lo' ,
      SearchTree_half_in (Some lo') h (Some hi) /\
      SearchTree (Some lo') l (Some (key_of_node n)) /\
      optionZ_lt (Some LO) (Some lo').
Proof.
  intros.
  inversion H0;subst.
  inversion H1;subst.
  inversion H7;subst.
  + unfold Key in *.
    
    
    
Admitted.

Lemma inner_border_expansion_R: 
  forall lo hi LO HI n r (h:partial_tree),
    optionZ_lt (Some hi) (Some HI) ->
    SearchTree_half_in (Some lo) ((R, n, r)::h) (Some hi) ->
    SearchTree_half_out (Some LO) ((R, n, r)::h) (Some HI) ->
    exists hi',
      SearchTree_half_in (Some lo) h (Some hi') /\
      SearchTree (Some (key_of_node n)) r (Some hi') /\
      optionZ_lt (Some hi') (Some HI).
Proof.
  intros.
  inversion H0;subst.
  { inversion H5;subst.
    +
Admitted.

Lemma step_preserves: 
  forall h h' t t' lo hi LO HI,
    optionZ_lt (Some LO) (Some lo) ->
    optionZ_lt (Some hi) (Some HI) ->
    SearchTree_half_in (Some lo) h (Some hi) ->
    SearchTree_half_out (Some LO) h (Some HI) ->
    SearchTree (Some lo) t (Some hi) ->
    splay_step (h,t) (h',t') ->
    exists lo' hi',
      (optionZ_lt (Some LO) (Some lo')) /\
      (optionZ_lt (Some hi') (Some HI)) /\
      (SearchTree (Some lo') t' (Some hi')) /\ 
      (SearchTree_half_in (Some lo') h' (Some hi')) /\ 
      (SearchTree_half_out (Some LO) h' (Some HI)).
Proof.
  intros.
  inversion H4;subst.
  + pose proof inner_border_expansion_R _ _ _ _ _ _ _ H0 H1 H2.
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
    constructor;tauto.
  +
Admitted.


Lemma optionZ_lt_cong: forall n lo hi,
optionZ_lt (Some (n)) hi->
optionZ_lt lo (Some (n))->
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

Print SearchTree.


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
  inversion H1. inversion H2. subst. clear H1 H2. 
  pose proof looser_SearchTree _ _ _ _ _ H H0 H3. tauto. 
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
  + 

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
