-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .linear

variables {a: Type} [ordered_add_comm_group a].

def positive (s: stream a) := 0 <= s.
def stream_monotone (s: stream a) := ∀ t, s t ≤ s (t+1).
def is_positive {b: Type} [ordered_add_comm_group b]
  (f: stream a → stream b) := ∀ s, positive s → positive (f s).

-- TODO: could not get library monotone definition to work, possibly due to
-- partial_order.to_preorder?

-- set_option pp.notation false.
-- set_option pp.implicit true.

-- prove that [stream_monotone] can be rephrased in terms of order preservation
theorem stream_monotone_order (s: stream a) :
  stream_monotone s ↔ (∀ t1 t2, t1 ≤ t2 → s t1 ≤ s t2) :=
begin
  unfold stream_monotone, split; intro h; introv,
  { intros hle, have heq : t2 = t1 + (t2 - t1) := by omega,
    rw heq at *,
    generalize : (t2 - t1) = d,
    clear_dependent t2,
    induction d,
    { simp, },
    { transitivity s (t1 + d_n), assumption,
      apply h, }
   },
  { apply h, linarith, },
end

lemma integral_monotone (s: stream a) :
  positive s → stream_monotone (I s) :=
begin
  intros hp,
  intros t,
  repeat { rw integral_sum_vals },
  repeat { simp [sum_vals] },
  have h := hp (t + 1), simp at h,
  assumption,
end

lemma derivative_pos (s: stream a) :
  -- NOTE: paper is missing this, but it is also necessary (maybe they
  -- intend `s[-1] =0` in the definition of monotone)
  0 ≤ s 0 →
  stream_monotone s → positive (D s) :=
begin
  intros h0 hp, intros t; simp,
  unfold D delay; simp,
  split_ifs,
  { subst t, assumption },
  { have hle := hp (t - 1),
    have heq : t - 1 + 1 = t := by omega, rw heq at hle,
    assumption,
   },
end

lemma derivative_pos_counter_example :
  (∃ (x:a), x < 0) →
  ¬(∀ (s: stream a), stream_monotone s → positive (D s)) :=
begin
  intros h, cases h with x hneg,
  simp,
  -- pushing the negation through, we're going to prove
  -- ∃ (x : stream a), stream_monotone x ∧ ¬positive (D x)
  use (λ _n, x),
  split,
  { intros t, simp, },
  { unfold positive,
    rw stream_le_ext, simp,
    use 0, simp [D],
    apply not_le_of_gt, assumption,
   },
end
