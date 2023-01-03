-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import init.algebra.order

import algebra.big_operators.basic
import data.dfinsupp.basic
import data.finset
import data.multiset.sort
import data.prod.lex

import tactic.omega
import tactic.linarith

/-!

# Z-sets

The type `Z[A]` is called a Z-set over elements of type A, which we can think of
as a collection of rows of type A. However, Z-sets are more general in that they
allow *integer multiplicities*; multiplicities greater than 1 correspond to
duplicates, while negative multiplicities correspond to retractions or
deletions. Hence `Z[A]` can be used not only to represent a table with rows of
type A but also changes to such a table.

Formally `Z[A]` is modeled as a function `A → ℤ` with finite support; that is,
only finitely many elements have non-zero multiplicity. This is necessary to
support well-defined summations over Z-sets.

`Z[A]` has a group structure that is essentially inherited from ℤ (the
operations are all pointwise). Similarly, it has a partial ordering where `m1 ≤
m2 := ∀ x, m1 x ≤ m2 x`.

Note that `Z[A]` is isomorphic to the free abelian group over `A`, so it is in a
formal sense the minimum needed to give `A` a group structure.

-/

variables {A B C: Type}.
variables [decidable_eq A] [decidable_eq B] [decidable_eq C].

/--
A Z-set is a function from A to ℤ with finite support.

This is implemented using dfinsupp; we use dfinsupp rather than finsupp since
its implementation is computable.
-/
def zset (A: Type) := Π₀ (_:A), ℤ.

notation `Z[` T `]` := zset T.

namespace zset.

instance zset_group : add_comm_group Z[A] :=
  by { unfold zset, apply (@dfinsupp.add_comm_group A (λ _, ℤ) _), }.

instance zset_fun_like : fun_like Z[A] A (λ (_:A), ℤ) :=
  by { unfold zset, apply_instance }.

-- this next few definitions do some work to implement printing of Z-sets, which
-- is unused so far.

def graph (m: Z[A]) : multiset (A × ℤ) :=
  m.support.val.map (λ a, (a, m a)).

def graph_list [linear_order A] (m: Z[A]) : list (A ×ₗ ℤ) :=
  multiset.sort (≤) (graph m).

def elements [linear_order A] (m: Z[A]) : list A :=
  multiset.sort (≤) (m.sum (λ a _, {a})).

@[protected, instance]
meta def has_to_format [has_to_format A] [linear_order A] : has_to_format Z[A] :=
  {to_format := λ m, (graph_list m).to_format}.

@[protected]
instance has_to_string [has_to_string A] [linear_order A] : has_to_string Z[A] :=
  {to_string := λ m, (list.map (λ (xz: A × ℤ), xz) (graph_list m)).to_string}.

@[simp]
lemma add_apply (m1 m2: Z[A]) (a: A) : (m1 + m2) a = m1 a + m2 a := rfl.

@[simp]
lemma sub_apply (m1 m2: Z[A]) (a: A) : (m1 - m2) a = m1 a - m2 a := rfl.

@[simp]
lemma neg_apply (m: Z[A]) (a: A) : (-m) a = -(m a) := rfl.

lemma add_support (m1 m2: Z[A]) :
  (m1 + m2).support =
  (m1.support ∪ m2.support).filter (λ a, m1 a + m2 a ≠ 0) :=
begin
  ext a, simp,
  contrapose!,
  intros h, cases h with h1 h2, rw [h1, h2], simp,
end

-- now we do some work so that `{a, b, c}` can be used to construct a Z-set

protected def empty : Z[A] := dfinsupp.mk ∅ (λ _, 0).
instance : has_emptyc Z[A] := {emptyc := zset.empty}.

protected def single (a:A) : Z[A] :=
  dfinsupp.single a 1.
instance : has_singleton A Z[A] := {singleton := zset.single}.

protected def insert (a:A) (m: Z[A])  : Z[A] := m + {a}.
instance : has_insert A Z[A] := {insert := zset.insert}.

@[simp]
lemma emptyc_apply (a:A) : (∅ : Z[A]) a = 0 := rfl.

@[simp]
lemma single_apply (a:A) (a': A) :
  ({a} : Z[A]) a' = if a = a' then 1 else 0 :=
begin
  change ({a} : Z[A]) with (zset.single a),
  unfold zset.single, simp,
end

@[simp]
lemma insert_apply (a: A) (m: Z[A]) (a': A) :
  has_insert.insert a m a' = m a' + if a = a' then 1 else 0 :=
begin
  change (has_insert.insert a m) with (zset.insert a m),
  unfold zset.insert, simp,
end

instance : is_lawful_singleton A Z[A] :=
begin
  split,
  intros x, ext a, simp,
end

#eval graph ({"alice", "bob"} : Z[string]).
#eval graph ({"alice"} - {"bob"} : Z[string]).

-- TODO: data.dfinsupp.order does contain a partial_order, but it had some weird
-- behavior
@[protected]
instance po : partial_order Z[A] :=
  { le := λ m1 m2, ∀ a, m1 a ≤ m2 a,
    le_refl := by { intros m a, simp, },
    le_trans := begin
      intros m1 m2 m3 h12 h23, intros a,
      apply le_trans, apply h12, apply h23,
    end,
    le_antisymm := begin
      intros m1 m2 hle1 hle2,
      ext a,
      apply le_antisymm, apply hle1, apply hle2,
    end,
  }.

-- TODO: how do I define `ordered_add_comm_group Z[A]` by just extending the existing
-- instances?

@[ext]
lemma zset_le_ext (m1 m2: Z[A]) : m1 ≤ m2 = (∀ a, m1 a ≤ m2 a) := rfl.

instance zset_mem : has_mem A Z[A] := ⟨λ a m, a ∈ m.support⟩.
lemma elem_eq (a: A) (m: zset A) : (a ∈ m) = (a ∈ m.support) := rfl.

protected def from_set (s: finset A) : Z[A] := dfinsupp.mk s (λ a, 1).

@[simp]
lemma from_set_0 : zset.from_set (∅ : finset A) = dfinsupp.mk ∅ (λ a, 1)
  := rfl.

@[simp]
lemma from_set_apply (s: finset A) (a: A) :
  zset.from_set s a = if (a ∈ s) then 1 else 0
  := rfl.

@[simp]
lemma from_set_support (s: finset A) :
  (zset.from_set s).support = s := by { ext a, simp }.

protected def to_set (s: Z[A]) : finset A := s.support.

@[simp]
lemma elem_to_set (a: A) (m: Z[A]) : a ∈ m.to_set ↔ a ∈ m := by refl.

@[simp]
lemma elem_from_set (a: A) (s: finset A) : a ∈ zset.from_set s ↔ a ∈ s :=
begin
  rw elem_eq, simp,
end

lemma to_from_set (s: finset A) [∀ a, decidable (a ∈ s)] :
  (zset.from_set s).to_set = s :=
begin
  ext a, simp,
end

/-
  Unlike the paper, we use [is_bag] for the property on ℤ-sets, [fun_positive]
  for the property on functions, [positive] for streams, and [is_positive] for
  the property on operators.
-/
def is_set (m: Z[A]) := ∀ a, a ∈ m → m a = 1.
def is_bag (m: Z[A]) := 0 ≤ m.
def fun_positive (f: Z[A] → Z[B]) := ∀ m, is_bag m → is_bag (f m).
def fun_positive2 (f: Z[A] → Z[B] → Z[C]) :=
  ∀ m1 m2, is_bag m1 → is_bag m2 → is_bag (f m1 m2).

-- mp stands for multiplicity, the result of applying a zset to an element
lemma elem_mp (m: Z[A]) (a: A) : a ∈ m ↔ m a ≠ 0 :=
  by { rw elem_eq, simp }.
lemma not_elem_mp (a: A) (m: Z[A]) : a ∉ m ↔ m a = 0 :=
  by { rw elem_eq, simp }.

lemma is_set_or (s: Z[A]) :
  is_set s ↔ ∀ a, s a = 0 ∨ s a = 1 :=
begin
  unfold is_set,
  split; intros h a,
  { rw<- not_elem_mp,
    by_cases (a ∈ s); tauto, },
  { have h' := h a,
    rw elem_mp, tauto, }
end

@[simp]
lemma is_set_0 : is_set (0: Z[A]) :=
begin
  rw is_set_or, tauto,
end

lemma set_is_bag (s: Z[A]) :
  is_set s -> is_bag s :=
begin
  intros hset a,
  cases ((is_set_or _).mp hset a) with h_a h_a; rw h_a;
  simp,
end

@[simp]
lemma elem_single (a x:A) :
  x ∈ ({a} : Z[A]) ↔ a = x :=
begin
  rw elem_mp, simp,
end

@[simp]
lemma support_single (a: A) :
  ({a} : Z[A]).support = {a} :=
begin
  ext x, simp, tauto,
end

def distinct (m: Z[A]) : Z[A] :=
  dfinsupp.mk (m.support.filter (λ a, m a > 0)) (λ _, 1).

@[simp]
lemma distinct_apply (m: Z[A]) (a: A) :
  distinct m a = if m a > 0 then 1 else 0 :=
begin
  unfold distinct, simp,
  congr' 1, ext, simp,
  intros, linarith,
end

section sum_linear.

namespace finset.
  lemma union_disjoint_l (s1 s2: finset A) :
    s1 ∪ s2 = s1.disj_union (s2 \ s1) finset.disjoint_sdiff :=
  begin
    ext a, simp,
  end

  lemma filter_filter_comm (p q : A → Prop) [decidable_pred p] [decidable_pred q] (s: finset A) :
    finset.filter p (finset.filter q s) = finset.filter q (finset.filter p s) :=
  begin
    repeat { rw finset.filter_filter },
    congr' 1, finish,
  end
end finset.

lemma sum_union_zero_l {α: Type} [add_comm_monoid α] (f: A → α) (s s': finset A) :
  (∀ x, x ∈ s' → x ∉ s → f x = 0) →
  finset.sum (s ∪ s') f =
  finset.sum s f :=
begin
  intros hz,
  rw finset.union_disjoint_l,
  rw finset.sum_disj_union,
  repeat { rw finset.sum_ite <|> rw finset.sum_add_distrib },
  simp,
  rw (@finset.sum_eq_zero _ _ _ _ (s' \ s)), simp,
  introv hel, simp at hel, apply hz; finish,
end

variables {G: Type} [add_comm_group G] (f: A → ℤ → G).

theorem general_sum_linear (m1 m2: Z[A]) :
  (∀ a, f a 0 = 0) →
  (∀ a m1 m2, f a (m1 + m2) = f a m1 + f a m2) →
  (m1 + m2).support.sum (λ a, f a ((m1 + m2) a)) =
  m1.support.sum (λ a, f a (m1 a)) +
  m2.support.sum (λ a, f a (m2 a)) :=
begin
  intros hf0 hflin,
  rw add_support,
  simp only [ne.def],
  rw finset.sum_filter_of_ne, swap,
  { intros x, simp, intros h1, contrapose!,
    intro hz, rw hz,
    apply hf0,
  },
  conv_lhs {
    congr, skip,
    funext,
    simp, rw hflin, skip,
  },
  rw finset.sum_add_distrib,
  congr' 1,
  { rw sum_union_zero_l, simp,
    introv hnz hz,
    rw hz,
    apply hf0, },
  { rw finset.union_comm,
    rw sum_union_zero_l, simp,
    introv hnz hz,
    rw hz,
    apply hf0, }
end

end sum_linear.

-- map is sufficiently complex and specific to the zset representation that we
-- define it here and prove some basic properties, from which it is much easier
-- to reason about it as a relational operator
section flatmap.

variables (f: A → Z[B]).

-- the core of flatmap (without the finite support of a real `Z[B]`)
def flatmap_at (m: Z[A]) : B → ℤ :=
  λ b, (m.support.sum (λ a, f a b * m a)).

def flatmap (m: Z[A]) : Z[B] :=
  dfinsupp.mk (m.support.bUnion (λ a, (f a).support)) (λ b, flatmap_at f m b).

-- This is the function used in the definition of flatmap; the theorem shows that
-- the support chosen is correct; that is, it is an over-approximation (the
-- actual support excludes elements where the sum cancels out and
-- reaches 0)
lemma flatmap_apply (m: Z[A]) :
  ∀ b, m.flatmap f b = flatmap_at f m b :=
begin
  intros,
  unfold zset.flatmap flatmap_at,
  simp,
  intros h,
  rw finset.sum_eq_zero,
  intros x h'; simp at h',
  rw h, simp, assumption,
end

theorem flatmap_0 : zset.flatmap f 0 = 0 := rfl.

private lemma ite_cases {c: Prop} [decidable c] (x z: A) (p: A → Prop) :
  p z →
  p x →
  p (ite c x z) :=
begin
  intros, split_ifs; finish,
end

theorem flatmap_linear (m1 m2: Z[A]) :
  zset.flatmap f (m1 + m2) = zset.flatmap f m1 + zset.flatmap f m2 :=
begin
  ext b, simp,
  repeat { rw flatmap_apply }, unfold flatmap_at,
  apply general_sum_linear (λ a m, f a b * m),
  { intros, simp, },
  { intros, simp, rw mul_add, },
end

lemma flatmap_from_set_card (s: finset A) (b:B) :
  (∀ a, (f a).is_set) →
  zset.flatmap_at f (zset.from_set s) b =
  finset.card (s.filter (λ (x : A), b ∈ f x)) :=
begin
  intros hset,
  unfold flatmap_at, simp,
  have hsum_1 : s.sum (λ a, f a b) = s.sum (λ a, if b ∈ f a then 1 else 0) := by {
    apply finset.sum_congr, refl,
    intros, split_ifs,
    { apply hset, assumption, },
    { rw not_elem_mp at h, assumption, },
  },
  rw hsum_1, simp,
end

lemma map_from_set_card (f: A → B) (s: finset A) (b:B) :
  zset.flatmap_at (λ a, {f a}) (zset.from_set s) b =
  finset.card (s.filter (λ (x : A), f x = b)) :=
begin
  rw flatmap_from_set_card,
  { simp },
  intros a,
  unfold is_set, simp,
end
end flatmap.

section map.

variables (f: A → B).

protected def map (m: Z[A]) : Z[B] := flatmap (λ a, {f a}) m.

lemma flatmap_map_at (m: Z[A]) (b: B) :
  flatmap_at (λ a, {f a}) m b = m.support.sum (λ a, if f a = b then m a else 0) :=
begin
  unfold flatmap_at, simp,
end

lemma map_apply (m: Z[A]) (b: B) :
  zset.map f m b = m.support.sum (λ a, if f a = b then m a else 0) :=
begin
  unfold zset.map, rw flatmap_apply,
  rw flatmap_map_at,
end

theorem map_linear (f: A → B) (m1 m2: Z[A]) :
  zset.map f (m1 + m2) = zset.map f m1 + zset.map f m2 :=
begin
  apply flatmap_linear,
end

lemma map_is_card (s: finset A) :
  ∀ b, zset.map f (zset.from_set s) b =
       (s.val.map f).count b :=
begin
  intros, unfold zset.map,
  rw flatmap_apply,
  rw flatmap_from_set_card,
  unfold multiset.count,
  rw multiset.countp_map,
  simp,
  rw finset.card_def,
  simp,
  congr' 1,
  apply multiset.filter_congr,
  { finish, },
  { intros a, unfold is_set, simp, },
end

namespace finset.
lemma sum_nonneg (s: finset A) (f: A → ℤ) :
  (∀ x, x ∈ s → 0 ≤ f x) →
  0 ≤ s.sum f :=
begin
  intros hnn,
  apply finset.sum_induction,
  { intros, linarith, },
  { linarith, },
  { assumption, },
end

lemma sum_pos (s: finset A) (f: A → ℤ) :
  (∃ a, a ∈ s ∧ 0 < f a) →
  (∀ x, x ∈ s → 0 ≤ f x) →
  0 < s.sum f :=
begin
  intros hpos hnn,
    cases hpos with a hpos, cases hpos with hel hpos,
  rw<- (finset.add_sum_erase s _ hel),
  suffices h : 0 ≤ (s.erase a).sum f,
  linarith,
  apply sum_nonneg,
  safe,
end
end finset.

lemma map_at_nonneg (f: A → B) (m: Z[A]) (b: B) :
  is_bag m →
  0 ≤ flatmap_at (λ a, {f a}) m b :=
begin
  intros hpos,
  unfold flatmap_at,
  apply finset.sum_nonneg,
  intros x, simp, intros,
  apply ite_cases, omega,
  apply hpos,
end

lemma map_at_pos (f: A → B) (m: Z[A]) (b: B) :
  is_bag m →
  (0 < flatmap_at (λ a, {f a}) m b ↔ ∃ a, a ∈ m ∧ f a = b) :=
begin
  intros hpos,
  split,
  { unfold flatmap_at,
    intros hmap,
    by_contra,
    rw finset.sum_eq_zero at hmap,
    { linarith, },
    { intros x, simp, intros h1 h2,
      push_neg at h,
      rw<- not_elem_mp at h1,
      tauto,
    }
  },
  { intros hex,
    unfold flatmap_at,
    apply finset.sum_pos,
    { cases hex with a h, cases h with hel hf,
      use a, simp,
      rw (if_pos hf),
      have ha := hpos a, simp at ha,
      rw elem_mp at hel, simp at hel,
      split,
      { tauto },
      { omega, }
    },
    { simp, intros,
      apply ite_cases, omega,
      apply hpos, },
  }
end

end map.

end zset.
