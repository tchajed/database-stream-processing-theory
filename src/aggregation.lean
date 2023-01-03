-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .relational

open zset

section count.
variables {a: Type} [decidable_eq a].

def count (m: Z[a]) : ℤ :=
  m.support.sum (λ a, m a).

def count' : Z[a] → Z[ℤ] := λ m, {count m}.

theorem count_ok (s: finset a) :
  count (zset.from_set s) = s.card :=
begin
  unfold count zset.from_set,
  simp,
  congr' 1,
  ext a, simp,
end

theorem count_linear (m1 m2: Z[a]) :
  count (m1 + m2) = count m1 + count m2 :=
begin
  unfold count,
  rw add_support,
  simp only [ne.def],
  rw finset.sum_filter_of_ne, swap,
  { intros x, simp, },
  conv_lhs {
    congr, skip,
    funext,
    simp, skip,
  },
  rw finset.sum_add_distrib,
  congr' 1,
  { rw sum_union_zero_l, simp, },
  { rw finset.union_comm,
    rw sum_union_zero_l, simp, }
end

theorem count'_ok (s: finset a) :
  zset.to_set (count' (zset.from_set s)) = {s.card} :=
begin
  unfold count' zset.to_set,
  rw count_ok,
  simp,
end
end count.

namespace zset.

-- NOTE: this could be generalized to any vector space with ℤ as its constants
protected def sum (m: Z[ℚ]) : ℚ :=
  m.support.sum (λ a, a * m a).

def sum' : Z[ℚ] → Z[ℚ] := λ m, {zset.sum m}.

theorem sum_ok (s: finset ℚ) :
  zset.sum (zset.from_set s) = finset.sum s (λ a, a) :=
begin
  unfold zset.sum zset.from_set,
  simp,
  apply finset.sum_congr,
  { ext a, simp, },
  { intros, refl, },
end

theorem sum_linear (m1 m2: Z[ℚ]) :
  zset.sum (m1 + m2) = zset.sum m1 + zset.sum m2 :=
begin
  unfold zset.sum,
  apply general_sum_linear (λ a m, a * (↑m : ℚ)),
  { intros, simp, },
  { intros, simp, rw mul_add, },
end

theorem sum'_ok (s: finset ℚ) :
  zset.to_set (sum' (zset.from_set s)) = {finset.sum s (λ a, a)} :=
begin
  unfold sum' zset.to_set,
  rw sum_ok,
  simp,
end

end zset.
