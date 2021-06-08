This is the final project for the course SJTU_CS263_Programming_Languages.
We proved the functional correctness('preserves' and 'correct') of splay tree.

1. preserves
  Key intermediate lemma is 'step_preserves', and to prove this lemma, we proved two auxiliary lemmas,  'inner_border_tighter_L' and 'inner_border_tighter_R' , using definitions of 'all_L', 'R_in', 'all_R' and 'L_in'.

2. correct 
  Key intermediate lemma is 'step_correct_le'. To prove 'step_correct_le', we proved two auxiliary lemmas, 'Abs_in' and 'Abs_in_half'. In addition, the conclusion of 'step_preserves' is useful in the proof of 'step_correct_le'.
