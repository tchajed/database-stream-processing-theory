-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .incremental
import .relational
import .relational_incremental

open zset

class schema :=
  -- the schemas for the two tables, T and R
  (T R : Type)
  -- t.a > 2
  -- r.s > 5
  (σT : T → Prop) (σR : R → Prop)
  -- the type of t1.x, t2.y, and the common id field
  (T1X T2Y Id : Type)
  (π1 : T → T1X × Id) (π2 : R → Id × T2Y).

def πxy (S: schema) (t : (S.T1X × S.Id) × (S.Id × S.T2Y)) : S.T1X × S.T2Y :=
  (t.1.1, t.2.2).

class schema_ok (S: schema) :=
  (i1 : decidable_eq S.T)
  (i2 : decidable_eq S.R)
  (i3 : decidable_pred S.σT)
  (i4 : decidable_pred S.σR)
  (i5 : decidable_eq S.T1X)
  (i6 : decidable_eq S.T2Y)
  (i7 : decidable_eq S.Id).

section instances.
open schema_ok.
attribute [instance] i1 i2 i3 i4 i5 i6 i7.
end instances.

variables (S: schema) [schema_ok S].

def t1 : Z[S.T] → Z[S.T1X × S.Id] :=
  λ t, zset.distinct (zset.map S.π1 (zset.distinct (filter S.σT (zset.distinct t)))).

def t2 : Z[S.R] → Z[S.Id × S.T2Y] :=
  λ r, zset.distinct (zset.map S.π2 (zset.distinct (filter S.σR (zset.distinct r)))).

def V : Z[S.T] → Z[S.R] → Z[S.T1X × S.T2Y] :=
  λ t r, zset.distinct
    (zset.map (πxy S)
      (equi_join prod.snd prod.fst (t1 S t) (t2 S r))).

-- set up optimizations

/- pos_equiv says f1 and f2 are equivalent on positive inputs -/
def pos_equiv {A B: Type} [decidable_eq A] [decidable_eq B]
  (f1 f2: Z[A] → Z[B]) :=
  ∀ i, is_bag i → f1 i = f2 i.

def pos_equiv2 {A B C: Type} [decidable_eq A] [decidable_eq B] [decidable_eq C]
  (f1 f2: Z[A] → Z[B] → Z[C]) :=
  ∀ i1 i2, is_bag i1 → is_bag i2 → f1 i1 i2 = f2 i1 i2.

infix ` =≤= `:50 := pos_equiv.
infix ` =≤2= `:50 := pos_equiv2.

/-- `same` is a technical device for automation purposes. It is just equality,
  but marked irreducible.

  The way this is used is that we can work on a goal `same x ?y` (where `?y` is
  an existential variable), gradually rewriting x to simplify it. If we tried to
  prove `x = ?y`, then `rw` an `simp` would always try to instantiate ?y with x,
  even if we want to continue rewriting.

  To make intermediate goals readable we provide `x === y` as notation for `same
  x y`.
   -/
def same {A : Type} (x y: A) := x = y.
lemma same_def {A} (x y: A) : same x y = (x = y) := rfl.
local attribute [irreducible] same.

lemma same_intro {A: Type} (x y: A) : same x y → x = y :=
  by { rw same_def, finish, }.

lemma same_elim {A: Type} (x: A) : same x x :=
  by { rw same_def, }.

infix ` === `:50 := same.

structure sig (A: Type) (p: A → Prop) :=
  (witness: A)
  (pf: p witness).

def t1_opt_goal : sig (Z[S.T] → Z[S.T1X × S.Id])
                  (λ opt, t1 S =≤= opt) :=
begin
  econstructor,
  intros t hpos,
  apply same_intro,
  simp [t1],
  rw filter_distinct_dedup,
  rw map_distinct_dedup,
  swap, { apply filter_pos, assumption, },
  apply same_elim,
end

-- TODO: reduce this first
def t1_opt := (t1_opt_goal S).witness.
def t1_opt_ok : t1 S =≤= t1_opt S := (t1_opt_goal S).pf.

def t2_opt_goal : sig (Z[S.R] → Z[S.Id × S.T2Y])
                  (λ opt, t2 S =≤= opt) :=
begin
  econstructor,
  intros t hpos,
  apply same_intro,
  simp [t2],
  rw filter_distinct_dedup,
  rw map_distinct_dedup,
  swap, { apply filter_pos, assumption, },
  apply same_elim,
end

def v_opt_goal : sig (Z[S.T] → Z[S.R] → Z[S.T1X × S.T2Y])
                  (λ opt, V S =≤2= opt) :=
begin
  econstructor, intros i1 i2 hpos1 hpos2,
  apply same_intro,
  simp [V],
  rw (t1_opt_goal S).pf _ (by assumption),
  rw (t2_opt_goal S).pf _ (by assumption),
  simp [t1_opt_goal, t2_opt_goal],
  rw join_distinct_comm, rotate,
  { apply map_pos, apply filter_pos, assumption, },
  { apply map_pos, apply filter_pos, assumption, },
  rw map_distinct_dedup, rotate,
  { apply equi_join_pos; apply map_pos; apply filter_pos; assumption },
  apply same_elim,
end

/- The optimized ℤ-set query from the paper -/
def Vopt (t1: Z[S.T]) (t2: Z[S.R]) :=
  distinct $ zset.map (πxy S)
    (equi_join prod.snd prod.fst
      (zset.map schema.π1 (filter schema.σT t1))
      (zset.map schema.π2 (filter schema.σR t2))).

-- the simplifications above produce exactly what's in the paper
lemma v_opt_ok : V S =≤2= Vopt S :=
  (v_opt_goal S).pf.

lemma v_lifted : ↑²(Vopt S) =
  λ t1 t2, ↑↑distinct (↑↑(zset.map (πxy S)) (↑²(equi_join prod.snd prod.fst)
      (↑↑(zset.map schema.π1) (↑↑(filter schema.σT) t1))
      (↑↑(zset.map schema.π2) (↑↑(filter schema.σR) t2)))) :=
begin
  refl,
end

/- This is the intermediate incremental circuit -/
def VΔ1 (t1: stream Z[S.T]) (t2: stream Z[S.R]) :=
  (↑↑distinct)^Δ $ ↑↑(zset.map (πxy S)) $ ↑²(equi_join prod.snd prod.fst)^Δ2
      (↑↑(zset.map schema.π1) (↑↑(filter schema.σT) t1))
      (↑↑(zset.map schema.π2) (↑↑(filter schema.σR) t2)).

lemma VΔ1_ok :
  ↑²(Vopt S)^Δ2 = VΔ1 S :=
begin
  funext t1 t2,
  -- hide the right-hand side
  transitivity,
  { apply same_intro,
    rw v_lifted, dsimp,
    dsimp only [incremental2],
    repeat { rw D_push2 <|> rw D_push }, simp,
    -- TODO: why does this have to be done explicitly?
    rw (map_incremental (πxy S)),
    rw (map_incremental schema.π1), simp,
    rw (map_incremental schema.π2), simp,
    apply same_elim, },
  { refl },
end

def VΔ (t1: stream Z[S.T]) (t2: stream Z[S.R]) :=
  distinct_incremental $ ↑↑(zset.map $ πxy S) $ times_incremental ↑²(equi_join prod.snd prod.fst)
      (↑↑(zset.map schema.π1) (↑↑(filter schema.σT) t1))
      (↑↑(zset.map schema.π2) (↑↑(filter schema.σR) t2)).

theorem VΔ_ok :
  ↑²(Vopt S)^Δ2 = VΔ S :=
begin
  rw VΔ1_ok, funext t1 t2, unfold VΔ1,
  rw distinct_incremental_ok,
  rw equi_join_incremental,
  refl,
end
