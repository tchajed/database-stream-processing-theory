-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .stream
import .linear
import .incremental
import tactic.abel
import init.classical

section zero.
variables {a: Type} [has_zero a].

def δ0 (x:a) : stream a :=
  λ t, if t = 0 then x else 0.

@[simp]
lemma δ0_apply (x: a) (n: ℕ) :
  δ0 x n = if n = 0 then x else 0
  := rfl.

@[simp]
lemma δ0_0 : δ0 (0: a) = 0 :=
begin
  ext n, simp,
end

def zero_after (s: stream a) (n: ℕ) := ∀ t ≥ n, s t = 0.

lemma zero_after_ge {s: stream a} {n1: ℕ} (pf1: zero_after s n1) :
  ∀ n2 ≥ n1, zero_after s n2 :=
begin
  intros n2 hge,
  intros m hge2,
  apply pf1, omega,
end

def δ0_zero_after (x:a) : zero_after (δ0 x) 1 :=
begin
  intros t hge, unfold δ0, rw if_neg, omega
end
end zero.

variables {a: Type} [add_comm_group a].

def drop (k: ℕ) (s: stream a) : stream a :=
  λ n, s (k + n).

lemma sum_vals_split (s: stream a) (n k: ℕ) :
  sum_vals s (n + k) = sum_vals s n + sum_vals (drop n s) k :=
begin
  revert n,
  induction k; introv,
  { simp, },
  { change (n + k_n.succ) with (n + k_n).succ,
    unfold sum_vals,
    rw k_ih,
    abel, }
end

lemma sum_vals_zero_ge (s: stream a) (n m:ℕ) (hz: zero_after s n) (hge: m ≥ n) :
  sum_vals s n = sum_vals s m :=
begin
  have h := sum_vals_split s n (m - n),
  have hdiff : m = n + (m - n) := by omega,
  rw [hdiff, h],
  rw sum_vals_zero (drop _ _), abel,
  intros t, unfold drop, apply hz, omega,
end

lemma sum_vals_eq_helper (s: stream a) (n1 n2: ℕ) (hz1: zero_after s n1) (hz2: zero_after s n2) :
  n1 ≤ n2 →
  sum_vals s n1 = sum_vals s n2 :=
begin
  intros hle,
  rw sum_vals_zero_ge,
  assumption,
  omega,
end

lemma sum_vals_eq (s: stream a) (n1 n2: ℕ) (hz1: zero_after s n1) (hz2: zero_after s n2) :
  sum_vals s n1 = sum_vals s n2 :=
begin
  by_cases (n1 ≤ n2),
  { rw sum_vals_eq_helper; assumption, },
  { symmetry, rw sum_vals_eq_helper; try { assumption }, omega, },
end

noncomputable def stream_elim (s: stream a) : a :=
  match classical.prop_decidable (∃ n, zero_after s n) with
  | decidable.is_true h := sum_vals s (classical.some h)
  | decidable.is_false _ := 0
  end.

lemma stream_elim_zero_after (s: stream a) (n:ℕ) (pf:zero_after s n) :
  stream_elim s = sum_vals s n :=
begin
  unfold stream_elim,
  cases (classical.prop_decidable _),
  { exfalso,
    apply h, use n, assumption,
  },
  { unfold stream_elim._match_1,
    apply sum_vals_eq,
    {  apply classical.some_spec h, },
    { assumption, },
  }
end

notation `∫ ` := stream_elim.

@[simp]
lemma stream_elim_0 : ∫ (0: stream a) = 0 :=
begin
  rw stream_elim_zero_after _ 0,
  { simp, },
  { intros t heq, simp, },
end

theorem stream_elim_delta (x: a) :
  ∫ (δ0 x) = x :=
begin
  rw stream_elim_zero_after _ 1,
  simp,
  apply δ0_zero_after,
end

theorem delta_linear :
  ∀ (x y: a), δ0 (x + y) = δ0 x + δ0 y :=
begin
  introv,
  ext t, simp,
  split_ifs; simp,
end

@[simp]
lemma delta_incremental :
  ↑↑(@δ0 a _)^Δ = ↑↑δ0 :=
begin
  apply lti_incremental,
  apply lifting_lti,
  apply delta_linear,
end

lemma sum_vals_linear (s1 s2: stream a) (n: ℕ) :
  sum_vals (s1 + s2) n = sum_vals s1 n + sum_vals s2 n :=
begin
  induction n; simp,
  rw n_ih, abel,
end

lemma sum_zero_after {s1 s2: stream a}
  {n1: ℕ} (pf1: zero_after s1 n1) {n2: ℕ} (pf2: zero_after s2 n2) :
  zero_after (s1 + s2) (if n1 ≥ n2 then n1 else n2) :=
begin
  split_ifs,
  { intros m hge, simp,
    rw pf1, swap, omega,
    rw pf2, swap, omega,
    simp,
  },
  { intros m hge, simp,
    rw pf1, swap, omega,
    rw pf2, swap, omega,
    simp,
  },
end

lemma sub_zero_after {s1 s2: stream a}
  {n1: ℕ} (pf1: zero_after s1 n1) {n2: ℕ} (pf2: zero_after s2 n2) :
  zero_after (s1 - s2) (if n1 ≥ n2 then n1 else n2) :=
begin
  split_ifs,
  { intros m hge, simp,
    rw pf1, swap, omega,
    rw pf2, swap, omega,
    simp,
  },
  { intros m hge, simp,
    rw pf1, swap, omega,
    rw pf2, swap, omega,
    simp,
  },
end

theorem stream_elim_linear (s1 s2: stream a)
  (n1: ℕ) (pf1: zero_after s1 n1) (n2: ℕ) (pf2: zero_after s2 n2) :
  ∫ (s1 + s2) = ∫ s1 + ∫ s2 :=
begin
  rw (stream_elim_zero_after s1 _ pf1),
  rw (stream_elim_zero_after s2 _ pf2),
  rw (stream_elim_zero_after _ _ (sum_zero_after pf1 pf2)),
  simp,

  generalize hmax : (if n2 ≤ n1 then n1 else n2) = max,

  have hmax1 : max ≥ n1 := by { subst hmax, split_ifs; omega },
  have hmax2 : max ≥ n2 := by { subst hmax, split_ifs; omega },
  rw (sum_vals_zero_ge s1 _ max pf1), swap, omega,
  rw (sum_vals_zero_ge s2 _ max pf2), swap, omega,

  apply sum_vals_linear,
end

lemma stream_elim_time_invariant :
  time_invariant ↑↑(@stream_elim a _) :=
begin
  apply lifting_time_invariant, simp,
end

lemma integral_zero (s: stream a) (n: ℕ) :
  zero_after (I s) n → zero_after s n.succ :=
begin
  intros hz,
  intros m hge,
  have hm := hz m (by omega),
  rw integral_unfold at hm, simp at hm,
  have hm' : z⁻¹ (I s) m = I s (m - 1) := by {
    unfold delay, rw if_neg, omega,
  },
  rw hm' at hm,
  rw (hz (m - 1)) at hm,
  abel at hm, assumption,
  omega,
end

lemma integral_nested_unfold (s: stream (stream a)) (t: ℕ) :
  0 < t →
  I s t = s t + I s (t-1) :=
begin
  intros hnz,
  conv_lhs {
    rw integral_unfold, simp,
  },
  simp,
  rw delay_sub_1, omega,
end

lemma integral_zero' (s: stream (stream a)) (t n: ℕ) :
  zero_after (I s t) n →
  zero_after (I s (t-1)) n →
  zero_after (s t) n.succ :=
begin
  by_cases (t = 0),
  { subst t, simp, intros hz _hz',
    apply (zero_after_ge hz), omega, },
  intros hz hz',
  intros m hge,
  transitivity (D (I s) t m),
  { simp, },
  unfold D, simp,
  rw (hz m), swap, omega,
  rw delay_sub_1, swap, omega,
  rw (hz' m), swap, omega,
  abel,
end

-- stream_elim_incremental is not provable
example {a: Type} [add_comm_group a] : true :=
begin
  have h : ↑↑(@stream_elim a _)^Δ = ↑↑stream_elim := by {
    unfold incremental,
    funext s,
    unfold D,
    funext t, simp,
    by_cases ht : (t = 0),
    { subst t, simp, },
    rw delay_sub_1, swap, omega, simp,
    -- this is not true: ∫ (I s t) might converge while ∫ (I s (t-1)) diverges and
    -- ∫ (s t) converges for example. What does seem true is that if both
    -- integrals on the left hand side converge, then the right-hand side
    -- converges and the equality holds.
    by_cases (∃ n, zero_after (I s t) n),
    { cases h with n hz,
      sorry,
    },
    -- this doesn't seem true
    sorry,
  },
  trivial,
end

lemma integral_delta (x:a) :
  I (δ0 x) = λ _n, x :=
begin
  ext t,
  induction t,
  { simp, },
  { rw integral_unfold, simp, assumption, }
end

@[simp]
lemma integral_delta_apply (x:a) (n:ℕ) :
  I (δ0 x) n = x :=
begin
  rw integral_delta,
end

variables {b: Type} [add_comm_group b].

lemma nested_zpp (Q: operator a b) :
  time_invariant Q → ∫ (Q (δ0 0)) = 0 :=
begin
  intros hti,
  rw δ0_0,
  rw time_invariant_zpp _ hti,
  rw stream_elim_0,
end
