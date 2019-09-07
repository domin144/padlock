Require Import Coq.Bool.Bool.

Inductive digit : Type :=
  | digit_0 : digit
  | digit_1 : digit
  | digit_2 : digit
  | digit_3 : digit
  | digit_4 : digit
  | digit_5 : digit
  | digit_6 : digit
  | digit_7 : digit
  | digit_8 : digit
  | digit_9 : digit.

Example sample_digit : digit.
  apply digit_0.
Qed.

Inductive code : Type :=
  | code_intro : digit -> digit -> digit -> code.

Inductive position : Type :=
  | position_0 : position
  | position_1 : position
  | position_2 : position.

Inductive has_digit : code -> digit -> position -> Prop :=
  | has_digit_0 :
    forall d0 d1 d2,
      has_digit (code_intro d0 d1 d2) d0 position_0
  | has_digit_1 :
    forall d0 d1 d2,
      has_digit (code_intro d0 d1 d2) d1 position_1
  | has_digit_2 :
    forall d0 d1 d2,
      has_digit (code_intro d0 d1 d2) d2 position_2.

Inductive match_at_position : code -> code -> position -> Prop :=
  | match_at_position_intro :
    forall d pos c0 c1,
      has_digit c0 d pos -> has_digit c1 d pos -> match_at_position c0 c1 pos.

Inductive wrong_position : code -> code -> position -> Prop :=
  | wrong_position_intro :
    forall d pos0 pos1 c0 c1,
      has_digit c0 d pos0 ->
        has_digit c1 d pos1 ->
          ~(has_digit c1 d pos0) -> wrong_position c0 c1 pos0.

Inductive invalid_digit_at_position : code -> code -> position -> Prop :=
  | invalid_digit_at_position_intro :
    forall d pos0 c0 c1,
      has_digit c0 d pos0 ->
        (forall pos1, ~(has_digit c1 d pos1)) ->
          invalid_digit_at_position c0 c1 pos0.

Inductive three_different_positions : position -> position -> position -> Prop :=
  | three_different_positions_intro :
    forall p0 p1 p2,
      p0 <> p1 -> p0 <> p2 -> p1 <> p2 -> three_different_positions p0 p1 p2.

Definition code_682 :=
  code_intro digit_6 digit_8 digit_2.

Definition code_614 :=
  code_intro digit_6 digit_1 digit_4.

Definition code_206 :=
  code_intro digit_2 digit_0 digit_6.

Definition code_738 :=
  code_intro digit_7 digit_3 digit_8.

Definition code_870 :=
  code_intro digit_8 digit_7 digit_0.

Inductive condition_0 : code -> Prop :=
  | condition_0_intro :
    forall c p0 p1 p2,
      three_different_positions p0 p1 p2 ->
        match_at_position code_682 c p0 ->
          invalid_digit_at_position code_682 c p1 ->
            invalid_digit_at_position code_682 c p2 ->
              condition_0 c.

Inductive condition_1 : code -> Prop :=
  | condition_1_intro :
    forall c p0 p1 p2,
      three_different_positions p0 p1 p2 ->
        wrong_position code_614 c p0 ->
          invalid_digit_at_position code_614 c p1 ->
            invalid_digit_at_position code_614 c p2 ->
              condition_1 c.

Inductive condition_2 : code -> Prop :=
  | condition_2_intro :
    forall c p0 p1 p2,
      three_different_positions p0 p1 p2 ->
        wrong_position code_206 c p0 ->
          wrong_position code_206 c p1 ->
            invalid_digit_at_position code_206 c p2 ->
              condition_2 c.

Inductive condition_3 : code -> Prop :=
  | condition_3_intro :
    forall c,
      (forall pos, invalid_digit_at_position code_738 c pos) ->
        condition_3 c.

Inductive condition_4 : code -> Prop :=
  | condition_4_intro :
    forall c p0 p1 p2,
      three_different_positions p0 p1 p2 ->
        wrong_position code_870 c p0 ->
          invalid_digit_at_position code_870 c p1 ->
            invalid_digit_at_position code_870 c p2 ->
              condition_4 c.

Inductive valid_code (c : code) : Prop :=
  | valid_code_intro :
    condition_0 c ->
      condition_1 c ->
        condition_2 c ->
          condition_3 c ->
            condition_4 c ->
              valid_code c.







Theorem same_digit_at_pos :
  forall c d0 d1 p,
    has_digit c d0 p ->
      has_digit c d1 p ->
        d0 = d1.
Proof.
  intros.
  destruct c.
  destruct p;
    inversion H; subst;
    inversion H0; subst;
    reflexivity.
Qed.

Definition get_digit_at_pos (c : code) (p : position) :=
  match c with
  | code_intro d0 d1 d2 => match p with
    | position_0 => d0
    | position_1 => d1
    | position_2 => d2
    end
  end.

Theorem get_digit_at_pos_correct :
  forall c d p,
    get_digit_at_pos c p = d <-> has_digit c d p.
Proof.
  intros.
  destruct c.
  split.
  + intro H.
    destruct p; simpl in H; subst.
    - apply has_digit_0.
    - apply has_digit_1.
    - apply has_digit_2.
  + intro H.
    destruct p;
      simpl;
      inversion H;
      reflexivity.
Qed.

Definition next_position (p : position) : position :=
  match p with
  | position_0 => position_1
  | position_1 => position_2
  | position_2 => position_0
  end.

Theorem next_next_position_different :
  forall p,
    three_different_positions p (next_position p) (next_position (next_position p)).
Proof.
  intros p.
  apply three_different_positions_intro;
    destruct p;
    simpl;
    intros H;
    inversion H.
Qed.

Definition digit_eq_bool (d0 d1 : digit) : bool :=
  match d0, d1 with
  | digit_0, digit_0 => true
  | digit_1, digit_1 => true
  | digit_2, digit_2 => true
  | digit_3, digit_3 => true
  | digit_4, digit_4 => true
  | digit_5, digit_5 => true
  | digit_6, digit_6 => true
  | digit_7, digit_7 => true
  | digit_8, digit_8 => true
  | digit_9, digit_9 => true
  | _, _ => false
  end.

Theorem digit_eq_bool_correct :
  forall d0 d1,
    d0 = d1 <-> digit_eq_bool d0 d1 = true.
Proof.
  split.
  - intro H.
    subst.
    destruct d1;
      reflexivity.
  - intro H.
    destruct d0, d1;
      try reflexivity;
      try inversion H.
Qed.

Theorem digit_eq_bool_reflexive :
  forall d, digit_eq_bool d d = true.
Proof.
  intro d.
  apply digit_eq_bool_correct.
  reflexivity.
Qed.

Definition match_at_position_bool (c0 c1 : code) (p : position) : bool :=
  digit_eq_bool (get_digit_at_pos c0 p) (get_digit_at_pos c1 p).

Theorem match_at_position_bool_correct :
  forall c0 c1 p,
    match_at_position c0 c1 p <-> match_at_position_bool c0 c1 p = true.
Proof.
  intros c0 c1 p.
  unfold match_at_position_bool.
  split.
  - intro H.
    apply digit_eq_bool_correct.
    inversion H; subst.
    apply get_digit_at_pos_correct in H0.
    apply get_digit_at_pos_correct in H1.
    rewrite H0.
    rewrite H1.
    reflexivity.
  - intro H.
    apply digit_eq_bool_correct in H.
    apply match_at_position_intro with (get_digit_at_pos c0 p).
    + apply get_digit_at_pos_correct.
      reflexivity.
    + apply get_digit_at_pos_correct.
      rewrite H.
      reflexivity.
Qed.

Theorem three_different_as_all_pos (pr : position -> Prop) :
  forall p0 p1 p2,
    three_different_positions p0 p1 p2 ->
      pr p0 -> pr p1 -> pr p2 ->
        forall p, pr p.
Proof.
  intros.
  destruct p;
    destruct p0;
    destruct p1;
    destruct p2;
    try auto;
    try (
      inversion H;
      exfalso;
      auto).
Defined.

Theorem always_one_of_three :
  forall p p0 p1 p2,
    three_different_positions p0 p1 p2 ->
      p = p0 \/ p = p1 \/ p = p2.
Proof.
  intros.
  inversion H; subst.
  destruct p, p0;
    try (left; reflexivity);
    right;
    destruct p1;
    try (left; reflexivity);
    right;
    destruct p2;
    try reflexivity;
    try (exfalso; auto).
Qed.

Definition invalid_digit_at_position_bool (c0 c1 : code) (p : position) : bool :=
  negb (digit_eq_bool (get_digit_at_pos c0 p) (get_digit_at_pos c1 p))
  && negb (digit_eq_bool (get_digit_at_pos c0 p) (get_digit_at_pos c1 (next_position p)))
  && negb (digit_eq_bool (get_digit_at_pos c0 p) (get_digit_at_pos c1 (next_position (next_position p)))).

Theorem invalid_digit_at_position_bool_correct :
  forall c0 c1 p,
    invalid_digit_at_position c0 c1 p <-> invalid_digit_at_position_bool c0 c1 p = true.
Proof.
  intros.
  split.
  - intro H.
    unfold invalid_digit_at_position_bool.
    inversion H; subst.
    apply get_digit_at_pos_correct in H0.
    rewrite H0.
    assert (forall pp, digit_eq_bool d (get_digit_at_pos c1 pp) = false) as Hpb.
    { intro pp.
      apply not_true_is_false.
      intro Hinv.
      apply H1 with pp.
      apply digit_eq_bool_correct in Hinv.
      apply get_digit_at_pos_correct.
      rewrite <- Hinv.
      reflexivity. }
    rewrite (Hpb p).
    rewrite (Hpb (next_position p)).
    rewrite (Hpb (next_position (next_position p))).
    reflexivity.
  - intro.
    apply invalid_digit_at_position_intro with (get_digit_at_pos c0 p).
    + apply get_digit_at_pos_correct.
      reflexivity.
    + apply three_different_as_all_pos with p (next_position p) (next_position (next_position p));
        try (
          unfold invalid_digit_at_position_bool in H;
          intro Hinv;
          apply get_digit_at_pos_correct in Hinv;
          rewrite Hinv in H;
          rewrite digit_eq_bool_reflexive in H;
          simpl in H;
          repeat rewrite andb_false_r in H;
          inversion H).
      * apply next_next_position_different.
Qed.

Definition wrong_position_bool (c0 c1 : code) (p : position) : bool :=
  negb (match_at_position_bool c0 c1 p)
  && (
    (digit_eq_bool (get_digit_at_pos c0 p) (get_digit_at_pos c1 (next_position p)))
    || (digit_eq_bool (get_digit_at_pos c0 p) (get_digit_at_pos c1 (next_position (next_position p))))).

Theorem wrong_position_bool_correct :
  forall c0 c1 p,
    wrong_position c0 c1 p <-> wrong_position_bool c0 c1 p = true.
Proof.
  intros.
  split.
  - intro H.
    inversion H; subst.
    apply get_digit_at_pos_correct in H0.
    apply get_digit_at_pos_correct in H1.
    unfold wrong_position_bool.
    unfold match_at_position_bool.
    rewrite H0.
    assert (digit_eq_bool d (get_digit_at_pos c1 p) = false) as Hnotmatch.
    { apply not_true_is_false.
      intro Hinv.
      apply digit_eq_bool_correct in Hinv.
      apply H2.
      apply get_digit_at_pos_correct.
      auto. }
    rewrite Hnotmatch.
    simpl.
    assert (pos1 = p \/ pos1 = (next_position p) \/ pos1 = (next_position (next_position p))) as Hpnnp.
    { apply always_one_of_three.
      apply next_next_position_different. }
    destruct Hpnnp; subst.
    + exfalso.
      apply H2.
      apply get_digit_at_pos_correct.
      apply H1.
    + destruct H3; subst.
      * rewrite H1.
        rewrite digit_eq_bool_reflexive.
        reflexivity.
      * rewrite H1.
        rewrite digit_eq_bool_reflexive.
        apply orb_true_r.
  - intro H.
    unfold wrong_position_bool in H.
    apply andb_prop in H.
    destruct H.
    apply orb_prop in H0.
    destruct H0.
    + apply wrong_position_intro with (get_digit_at_pos c0 p) (next_position p).
      * apply get_digit_at_pos_correct.
        reflexivity.
      * apply get_digit_at_pos_correct.
        apply digit_eq_bool_correct in H0.
        auto.
      * intro Hinv.
        apply get_digit_at_pos_correct in Hinv.
        unfold match_at_position_bool in H.
        rewrite Hinv in H.
        rewrite digit_eq_bool_reflexive in H.
        inversion H.
    + apply wrong_position_intro with (get_digit_at_pos c0 p) (next_position (next_position p)).
      * apply get_digit_at_pos_correct.
        reflexivity.
      * apply get_digit_at_pos_correct.
        apply digit_eq_bool_correct in H0.
        auto.
      * intro Hinv.
        apply get_digit_at_pos_correct in Hinv.
        unfold match_at_position_bool in H.
        rewrite Hinv in H.
        rewrite digit_eq_bool_reflexive in H.
        inversion H.
Qed.

Theorem code_012_condition_0 :
  condition_0 (code_intro digit_0 digit_1 digit_2).
Proof.
  apply condition_0_intro with position_2 position_0 position_1.
  - apply three_different_positions_intro;
    intro H;
    inversion H.
  - apply match_at_position_bool_correct.
    reflexivity.
  - apply invalid_digit_at_position_bool_correct.
    reflexivity.
  - apply invalid_digit_at_position_bool_correct.
    reflexivity.
Qed.

Theorem code_012_condition_1 :
  ~(condition_1 (code_intro digit_0 digit_1 digit_2)).
Proof.
  intro H.
  inversion H; subst.
  apply wrong_position_bool_correct in H1.
  destruct p0;
    simpl in H1;
    inversion H1.
Qed.

Theorem code_012_is_not_valid :
  ~(valid_code (code_intro digit_0 digit_1 digit_2)).
Proof.
  intro.
  destruct H as [H0 H1 H2 H3 H4].
  apply code_012_condition_1.
  auto.
Qed.

Theorem invalid_8 :
  forall c,
    valid_code c ->
      forall pos, ~(has_digit c digit_8 pos).
Proof.
  intros c H.
  inversion H.
  inversion H3; subst.
  intros pos.
  pose (H5 position_2) as H6.
  inversion H6; subst.
  inversion H7; subst.
  apply H8.
Qed.

Theorem wrong_position_0_at_2 :
  forall c,
    valid_code c ->
      has_digit c digit_0 position_0 \/ has_digit c digit_0 position_1.
Proof.
  intros.
  inversion H.
  inversion H3; subst.
  inversion H4; subst.
  assert (p0 <> position_0).
  { intros Hinv.
    subst.
    inversion H7; subst.
    inversion H10; subst.
    apply (invalid_8 c H pos1).
    apply H11. }
  assert (p0 <> position_1).
  { intros Hinv.
    subst.
    inversion H7; subst.
    inversion H11; subst.
    pose (H5 position_0) as H5_position_0.
    inversion H5_position_0; subst.
    inversion H14; subst.
    apply (H15 pos1).
    auto. }
  assert (p0 = position_2).
  { destruct p0.
    - exfalso.
      apply H10.
      reflexivity.
    - exfalso.
      apply H11.
      reflexivity.
    - reflexivity. }
  subst.
  inversion H7; subst.
  inversion H12; subst.
  destruct pos1.
  - left.
    auto.
  - right.
    auto.
  - exfalso.
    apply H14.
    auto.
Qed.

Theorem not_0_at_1 :
  forall c,
    valid_code c ->
      ~(has_digit c digit_0 position_1).
Proof.
  intros c H Hinv.
  inversion H.
  inversion H2; subst.
  assert (position_1 = p0 \/ position_1 = p1 \/ position_1 = p2) as Hchoice.
  { apply always_one_of_three.
    auto. }
  destruct Hchoice as [Hc | [Hc | Hc]].
  - subst.
    inversion H6; subst.
    inversion H9; subst.
    auto.
  - subst.
    inversion H7; subst.
    inversion H9; subst.
    auto.
  - subst.
    inversion H8; subst.
    inversion H9; subst.
    apply (H10 position_1).
    auto.
Qed.

Theorem correct_position_0_at_0 :
  forall c,
    valid_code c ->
      has_digit c digit_0 position_0.
Proof.
  intros c H.
  pose (wrong_position_0_at_2 c H) as H1.
  destruct H1.
  - auto.
  - exfalso.
    apply (not_0_at_1 c); auto.
Qed.

Theorem correct_position_2_at_2 :
  forall c,
    valid_code c ->
      has_digit c digit_2 position_2.
Proof.
  intros c H.
  inversion H.
  inversion H0; subst.
  destruct p0.
  - inversion H6; subst.
    inversion H9; subst.
    assert (digit_6 = digit_0).
    { apply same_digit_at_pos with c position_0; auto.
      apply correct_position_0_at_0; auto. }
    inversion H11.
  - inversion H6; subst.
    inversion H9; subst.
    exfalso.
    apply invalid_8 with c position_1; auto.
  - inversion H6; subst.
    inversion H9; subst.
    auto.
Qed.

Theorem invalid_6 :
  forall c,
    valid_code c ->
      forall pos, ~(has_digit c digit_6 pos).
Proof.
  intros c H.
  inversion H.
  inversion H2; subst.
  destruct p2.
  - inversion H8; subst.
    inversion H9; subst.
    exfalso.
    apply (H10 position_2).
    apply correct_position_2_at_2.
    auto.
  - inversion H8; subst.
    inversion H9; subst.
    exfalso.
    apply (H10 position_0).
    apply correct_position_0_at_0.
    auto.
  - inversion H8; subst.
    inversion H9; subst.
    apply H10.
Qed.

Theorem correct_position_4_at_1 :
  forall c,
    valid_code c ->
      has_digit c digit_4 position_1.
Proof.
  intros c H.
  inversion H.
  inversion H1; subst.
  destruct p0.
  - exfalso.
    inversion H6; subst.
    inversion H9; subst.
    apply invalid_6 with c pos1; auto.
  - inversion H6; subst.
    inversion H9; subst.
    destruct pos1.
    * assert (digit_1 = digit_0).
      { apply same_digit_at_pos with c position_0.
        - auto.
        - apply correct_position_0_at_0.
          auto. }
      inversion H12.
    * exfalso.
      auto.
    * assert (digit_1 = digit_2).
      { apply same_digit_at_pos with c position_2.
        - auto.
        - apply correct_position_2_at_2.
          auto. }
      inversion H12.
  - inversion H6; subst.
    inversion H9; subst.
    destruct pos1.
    * assert (digit_4 = digit_0).
      { apply same_digit_at_pos with c position_0.
        - auto.
        - apply correct_position_0_at_0.
          auto. }
      inversion H12.
    * auto.
    * assert (digit_4 = digit_2).
      { apply same_digit_at_pos with c position_2.
        - auto.
        - apply correct_position_2_at_2.
          auto. }
      inversion H12.
Qed.

Definition code_042 :=
  code_intro digit_0 digit_4 digit_2.

Theorem only_valid_code_is_042 :
  forall c,
    valid_code c -> c = code_042.
Proof.
  intros c H.
  assert (has_digit c digit_0 position_0) as Hd0.
  { apply correct_position_0_at_0; auto. }
  assert (has_digit c digit_4 position_1) as Hd1.
  { apply correct_position_4_at_1; auto. }
  assert (has_digit c digit_2 position_2) as Hd2.
  { apply correct_position_2_at_2; auto. }
  destruct c.
  inversion Hd0; subst.
  inversion Hd1; subst.
  inversion Hd2; subst.
  reflexivity.
Qed.
