-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .relational
import .incremental

open zset

variables {A B C: Type}.
variables [decidable_eq A] [decidable_eq B] [decidable_eq C].

def distinct_H_at (i d: Z[A]) : A → ℤ :=
  λ x, if 0 < i x ∧ (i + d) x ≤ 0
       then -1 else
        if i x ≤ 0 ∧ 0 < (i + d) x
        then 1 else 0.

def distinct_H (i d: Z[A]) : Z[A] :=
  dfinsupp.mk (i.support ∪ d.support)
    (λ x, distinct_H_at i d x).

@[simp]
lemma distinct_H_apply (i d: Z[A]) (x: A) :
  distinct_H i d x = distinct_H_at i d x :=
begin
  unfold distinct_H, simp,
  push_neg,
  intros h, cases h with h1 h2,
  simp [distinct_H_at], rw [h1, h2],
  rw [if_neg, if_neg]; simp,
end

def distinct_incremental : stream Z[A] → stream Z[A] :=
  λ d, (↑² distinct_H) (z⁻¹ (I d)) d.

theorem distinct_incremental_ok :
  (↑↑ distinct)^Δ = @distinct_incremental A _ :=
begin
  funext d,
  unfold incremental distinct_incremental,
  unfold D,
  conv_lhs {
    congr, { rw integral_unfold, skip}, { skip }
  },
  rw<- lifting_time_invariant, swap, simp,
  repeat { rw<- integral_time_invariant },
  ext t a, unfold lifting2, simp,
  generalize hi : I (z⁻¹ d) t = i,
  generalize hd : d t = d_t,
  clear hi hd d t,
  unfold distinct_H_at,
  simp,
  -- canonicalize the tests a little bit so splitting produces fewer cases
  rw (add_comm (i a) (d_t a)),
  repeat { rw <- ite_ite },
  split_ifs; refl <|> { exfalso, omega },
end

@[simp]
lemma flatmap_incremental (f: A → Z[B]) :
  ↑↑(zset.flatmap f)^Δ = ↑↑(zset.flatmap f) :=
begin
  apply lti_incremental,
  apply lifting_lti,
  apply flatmap_linear,
end

@[simp]
lemma map_incremental (f: A → B) :
  ↑↑(zset.map f)^Δ = ↑↑(zset.map f) :=
  flatmap_incremental _.

@[simp]
lemma lifting_map_incremental {A B} [decidable_eq A] [decidable_eq B] (f: A → B) :
  ↑↑(↑↑(zset.map f))^Δ = ↑↑(↑↑(zset.map f)) :=
begin
  rw lti_incremental,
  apply lifting_lti,
  intros x y, rw lifting_linear, apply map_linear,
end


@[simp]
lemma map_incremental_unfolded (f: A → B) (s: stream Z[A]) :
  D (↑↑(zset.map f) (I s)) = ↑↑(zset.map f) s :=
begin
  conv_rhs {
    rw<- map_incremental,
  },
  rw incremental_unfold,
end

theorem equi_join_incremental (π1: A → C) (π2: B → C) :
  ↑²(equi_join π1 π2)^Δ2 =
    times_incremental ↑²(equi_join π1 π2) :=
begin
  rw (bilinear_incremental (↑²(equi_join π1 π2))),
  { rw lifting2_time_invariant,
    refl, },
  { apply lifting_bilinear,
    apply equi_join_bilinear,
  },
end

@[simp]
lemma filter_incremental (p: A → Prop) [decidable_pred p] :
  ↑↑(filter p)^Δ = ↑↑(filter p) :=
begin
  apply lti_incremental,
  apply lifting_lti,
  apply filter_linear,
end
