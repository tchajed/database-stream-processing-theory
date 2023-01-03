-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .relational
import .relational_incremental
import .stream_elim
import logic.function.iterate

open zset

section recursion.

variables {a: Type}.
variables [decidable_eq a].

-- idea is that we're supposed to compute O such that R(O) = O
variables (R: Z[a] → Z[a]).

private def approxs : stream Z[a] :=
  fix (λ (o: stream Z[a]), ↑↑R (z⁻¹ o)).

lemma approxs_unfold :
  approxs R = ↑↑R (z⁻¹ (approxs R)) :=
begin
  unfold approxs,
  apply fix_eq,
  apply causal_strict_strict, swap, simp,
  apply delay_strict,
end

noncomputable def recursive_fixpoint : Z[a] :=
  ∫ (D (approxs R)).

lemma approxs_apply
  (n: ℕ) :
  approxs R n = (R^[n.succ]) 0 :=
begin
  induction n, simp,
  { unfold approxs,
    rw fix_0, simp, },
  { rw approxs_unfold, simp,
    rw n_ih, simp,
    repeat { rw (function.commute.iterate_self R) }, },
end

lemma approxs_unfold_succ
  (n: ℕ) :
  approxs R n.succ = R (approxs R n) :=
begin
  rw approxs_apply,
  rw approxs_apply,
  simp,
  rw function.commute.iterate_self R,
end

private lemma eq_succ_is_fixpoint
  (n: ℕ) (heqn: R^[n.succ] 0 = (R^[n]) 0) :
  ∀ m ≥ n,
  R^[m] 0 = (R^[n]) 0 :=
begin
  intros m hge,
  by_cases (m = n), cc,
  generalize hdiff : m - n - 1 = d,
  have hm : m = (n + d).succ := by omega,
  rw hm, rw hm at *, clear_dependent m, clear hdiff,
  clear hge h,
  induction d,
  { simp, assumption, },
  { have hnsucc : (n + d_n.succ) = (n + d_n).succ := by omega,
    simp, rw function.commute.iterate_self,
    rw [hnsucc, d_ih],
    simp at heqn, rw function.commute.iterate_self at heqn,
    exact heqn,
  },
end

lemma derivative_approx_almost_zero
  (n: ℕ) (heqn: (R^[n.succ]) 0 = (R^[n]) 0) :
  zero_after (D (approxs R)) n.succ :=
begin
  intros m hge,
  rw derivative_difference_t, swap, omega,
  repeat { rw approxs_apply },
  have heq : (m - 1).succ = m := by omega, rw heq, clear heq,
  rw (eq_succ_is_fixpoint _ n heqn m.succ), swap, omega,
  rw (eq_succ_is_fixpoint _ n heqn m), swap, omega,
  simp,
end

theorem recursive_fixpoint_ok
  (n: ℕ) (heqn: (R^[n.succ]) 0 = (R^[n]) 0) :
  recursive_fixpoint R = (R^[n]) 0 :=
begin
  unfold recursive_fixpoint,
  rw (stream_elim_zero_after (D (approxs R)) n.succ),
  { rw <- integral_sum_vals,
    simp,
    rw approxs_apply, dsimp,
    exact heqn, },
  apply (derivative_approx_almost_zero _ n heqn),
end

end recursion.

section seminaive.


variables {a b: Type}.
variables [decidable_eq a] [decidable_eq b].

variables (R: Z[b] → Z[a] → Z[a]).

noncomputable def naive : Z[b] → Z[a] :=
  λ i, ∫ (D (fix (λ (o: stream Z[a]), ↑²R (I (δ0 i)) (z⁻¹ o)))).

noncomputable def seminaive : Z[b] → Z[a] :=
  λ i, ∫ (fix (λ (o: stream Z[a]), ↑²R^Δ2 (δ0 i) (z⁻¹ o))).

-- hack to make the change work (need a better way to introduce incremental)
local attribute [reducible] incremental.

theorem seminaive_equiv :
  seminaive R = naive R :=
begin
  ext x,
  unfold naive seminaive,
  congr' 1,
  congr' 1,
  change (D (fix (λ (o : stream Z[a]), ↑²R (I (δ0 x)) (z⁻¹ o)))) with
    (λ i, (fix (λ (o : stream Z[a]), ↑²R i (z⁻¹ o))))^Δ (δ0 x),
  rw cycle_incremental (λ i o, ↑²R i o),
  dsimp,
  rw uncurry_op_lifting2,
  apply lifting_causal,
end

theorem naive_ok (i: Z[b])
  (n: ℕ) (heqn: (R i)^[n.succ] 0 = ((R i)^[n]) 0) :
  naive R i = ((R i)^[n]) 0 :=
begin
  unfold naive,
  have  heq := (recursive_fixpoint_ok (R i)) _ heqn,
  unfold recursive_fixpoint approxs at heq,
  rw<- heq,
  congr' 3,
  funext o,
  congr' 1,
  funext t, simp,
end

theorem seminaive_ok (i: Z[b])
  (n: ℕ) (heqn: (R i)^[n.succ] 0 = ((R i)^[n]) 0) :
  seminaive R i = ((R i)^[n]) 0 :=
begin
  rw seminaive_equiv,
  apply naive_ok, assumption,
end

end seminaive.
