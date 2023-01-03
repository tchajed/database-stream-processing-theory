-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .zset
import .linear

open zset

variables {A B C: Type}.
variables [decidable_eq A] [decidable_eq B] [decidable_eq C].

lemma distinct_is_set (m: Z[A]) : is_set (distinct m) :=
begin
  intros a, rw elem_mp, simp,
  intros, linarith,
end

lemma distinct_is_bag (m: Z[A]) : is_bag (distinct m) :=
begin
  apply set_is_bag, apply distinct_is_set,
end

lemma distinct_set_id (m: Z[A]) : is_set m → m.distinct = m :=
begin
  intros h,
  ext a, simp,
  cases (is_set_or _).mp h a with hma hma; rw hma,
  { rw if_neg, omega, },
  { rw if_pos, omega, },
end

@[simp]
lemma distinct_set_simp (m: Z[A]) : is_set (distinct m) ↔ true :=
  by { simp, apply distinct_is_set }.

@[simp]
lemma distinct_bag_simp (m: Z[A]) : is_bag (distinct m) ↔ true :=
  by { simp, apply distinct_is_bag }.

lemma distinct_elem {m: Z[A]} {a: A} :
  is_bag m →
  (a ∈ m.distinct ↔ a ∈ m) :=
begin
  intros hpos,
  rw [elem_mp, elem_mp],
  rw distinct_apply,
  have h := hpos a, simp at h,
  split_ifs; simp,
  omega, omega,
end

lemma distinct_pos : fun_positive (@distinct A _) :=
begin
  intros f hp, simp,
end

@[simp]
lemma distinct_0 : distinct (0 : Z[A]) = 0 := rfl.

def query (A B: Type) := operator Z[A] Z[B].

def union (m1 m2: Z[A]) := distinct (m1 + m2).
instance zset_union : has_union Z[A] := ⟨union⟩.
lemma union_eq (m1 m2: Z[A]) : m1 ∪ m2 = union m1 m2 := rfl.

lemma union_apply (m1 m2: Z[A]) (a: A) :
  union m1 m2 a = if 0 < m1 a + m2 a then 1 else 0 :=
begin
  unfold union distinct; simp,
  apply if_congr; try { refl },
  simp, omega,
end

theorem union_ok (s1 s2: finset A) :
  zset.to_set (zset.from_set s1 ∪ zset.from_set s2) = s1 ∪ s2 :=
begin
  ext a,
  rw finset.mem_union,
  rw union_eq, unfold union,
  unfold distinct zset.from_set zset.to_set; simp,
  split_ifs; ring_nf; simp; tauto,
end

theorem union_pos : fun_positive2 (@union A _) :=
begin
  intros m1 m2 h1 h2,
  intros a, simp,
  rw union_apply,
  split_ifs; omega,
end

theorem map_ok (f: A → B) (s: finset A) :
  (zset.map f (zset.from_set s)).support = s.image f :=
begin
  ext b, simp, rw map_is_card,
  simp,
  tauto,
end

theorem map_pos (f: A → B) : fun_positive (zset.map f) :=
begin
  intros m h,
  intros a, simp,
  unfold zset.map, rw flatmap_apply,
  apply map_at_nonneg, assumption,
end

section filter.
  variables (p: A → Prop) [decidable_pred p].

  def filter (m: Z[A]) : Z[A] :=
    dfinsupp.mk (m.support.filter p) (λ a, m a).

  lemma filter_support (m: Z[A]) :
    dfinsupp.support (filter p m) = m.support.filter p :=
  begin
    unfold filter, ext a, simp,
    tauto,
  end

  @[simp]
  lemma filter_apply (m: Z[A]) (a: A) :
    filter p m a = if p a then m a else 0 :=
  begin
    unfold filter, simp,
    split_ifs; tauto,
  end

  theorem filter_ok (s: finset A) :
    zset.to_set (filter p (zset.from_set s)) = s.filter p :=
  begin
    ext a, simp,
    rw [elem_mp, filter_apply],
    simp, tauto,
  end

  lemma filter_linear :
    ∀ (m1 m2: Z[A]), filter p (m1 + m2) = filter p m1 + filter p m2 :=
  begin
    intros,
    ext a, simp,
    split_ifs,
    { simp },
    { finish },
  end

  theorem filter_pos : fun_positive (filter p) :=
  begin
    intros m h, intros a, simp,
    split_ifs,
    { apply h, },
    { linarith, }
  end

  lemma filter_0 : filter p 0 = 0 := rfl.

end filter.

section product.
  def product (m1: Z[A]) (m2: Z[B]) : Z[A × B] :=
    -- the unusual binder is because dfinupp.mk actually supplies a proof that
    -- the input is in the support, which is being ignored here
    dfinsupp.mk
      (finset.product m1.support m2.support)
      (λ ⟨(a, b), _⟩, m1 a * m2 b).

  @[simp]
  lemma product_apply (m1: Z[A]) (m2: Z[B]) (ab: A × B) :
    product m1 m2 ab = m1 ab.1 * m2 ab.2 :=
  begin
    unfold product, cases ab with a b, simp,
    split_ifs,
    { refl },
    { finish },
  end

  theorem product_ok (s1: finset A) (s2: finset B) :
    zset.to_set (product (zset.from_set s1) (zset.from_set s2)) = finset.product s1 s2 :=
  begin
    ext ab, cases ab with a b, simp,
    rw elem_eq, simp,
  end

  theorem product_bilinear : bilinear (@product A B _ _) :=
  begin
    split,
    { intros x1 x2 y,
      ext ab, cases ab with a b, simp,
      omega, },
    { intros x y1 y2,
      ext ab, cases ab with a b, simp,
      omega, }
  end

  theorem product_pos : fun_positive2 (@product A B _ _) :=
  begin
    intros m1 m2 h1 h2,
    intros ab, cases ab with a b, simp,
    have h1a := h1 a,
    have h2a := h2 b,
    simp at h1a h2a,
    nlinarith,
  end

  @[simp]
  lemma product_0 : @product A B _ _ 0 0 = 0 := rfl.

  section equi_join.

  variables (π1: A → C) (π2: B → C).

  def equi_join (m1: Z[A]) (m2: Z[B]) : Z[A × B]
    := filter (λ t, π1 t.1 = π2 t.2) (product m1 m2).

  @[simp]
  lemma equi_join_apply (m1: Z[A]) (m2: Z[B]) (t: A × B) :
    equi_join π1 π2 m1 m2 t = if π1 t.1 = π2 t.2 then m1 t.1 * m2 t.2 else 0 :=
    by { unfold equi_join, simp, }.

  theorem equi_join_bilinear : bilinear (equi_join π1 π2) :=
  begin
    split; intros,
    { unfold equi_join, rw [product_bilinear.1, filter_linear], },
    { unfold equi_join, rw [product_bilinear.2, filter_linear], },
  end

  theorem equi_join_pos : fun_positive2 (equi_join π1 π2) :=
  begin
    intros m1 m2 h1 h2,
    apply filter_pos, apply product_pos; assumption,
  end

  @[simp]
  lemma equi_join_0_l (b: Z[B]) : equi_join π1 π2 0 b = 0 := rfl.

  @[simp]
  lemma equi_join_0_r (a: Z[A]) : equi_join π1 π2 a 0 = 0 :=
  begin
    ext a, simp,
  end


  end equi_join.

end product.

-- TODO: paper says intersection can be defined as a special case of an
-- equijoin, but this construction required projecting A × A → A (where both are
-- equal due to the filter), and it's not obvious that project preserves
-- bilinearity. In any case the direct definition is straightforward.

def intersect (m1 m2: Z[A]) : Z[A] :=
  dfinsupp.mk (m1.support ∩ m2.support) (λ a, m1 a * m2 a).
instance : has_inter (Z[A]) := ⟨intersect⟩.

@[simp]
lemma intersect_apply (m1 m2: Z[A]) (a: A) :
  (m1 ∩ m2) a = m1 a * m2 a :=
begin
  change (m1 ∩ m2) with (intersect m1 m2),
  unfold intersect, simp,
  tauto,
end

@[simp]
lemma intersect_0 : (0: Z[A]) ∩ 0 = 0 := rfl.

@[simp]
lemma intersect_support (m1 m2: Z[A]) :
  (m1 ∩ m2).support = m1.support ∩ m2.support :=
begin
  ext a,
  change (m1 ∩ m2) with (intersect m1 m2),
  unfold intersect, simp,
  tauto,
end

theorem intersect_ok (s1 s2: finset A) :
  zset.to_set (zset.from_set s1 ∩ zset.from_set s2) = s1 ∩ s2 :=
begin
  ext a, simp,
   rw elem_mp, simp,
end

theorem intersect_pos : fun_positive2 ((∩) : Z[A] → Z[A] → Z[A]) :=
begin
  intros m1 m2 hpos1 hpos2,
  intros a, simp,
  have h1 := hpos1 a, have h2 := hpos2 a, simp at h1 h2,
  nlinarith,
end

theorem intersect_bilinear : bilinear ((∩) : Z[A] → Z[A] → Z[A]) :=
begin
  split; introv; ext a; simp; nlinarith,
end


def difference (m1 m2: Z[A]) : Z[A] := distinct (m1 - m2).

theorem difference_ok (s1 s2: finset A) :
  zset.to_set (difference (zset.from_set s1) (zset.from_set s2)) = s1 \ s2 :=
begin
  ext a, simp,
  rw elem_mp, unfold difference, simp,
  split_ifs; try { simp }; clarify,
end

section group_by.

variables {K: Type} [decidable_eq K] (p: A → K).

def group_by : Z[A] → Π₀ (_: K), Z[A] :=
  λ m, dfinsupp.mk (m.support.image p)
    (λ k, dfinsupp.mk (m.support.filter (λ a, p a = k))
      (λ a, if p a = k then m a else 0)).

@[simp]
lemma group_by_apply (m: Z[A]) (k: K) (a: A) :
  group_by p m k a = if p a = k then m a else 0 :=
begin
  unfold group_by, simp,
  split_ifs with hk hp; simp at hk |-,
  { split_ifs; try { tauto }, },
  { tauto, },
  { by_contra, apply (hk a); tauto, },
end

lemma group_by_support (m: Z[A]) (k: K) :
  (group_by p m k).support = m.support.filter (λ a, p a = k) :=
begin
  ext a, simp, tauto,
end

lemma elem_group_by (m: Z[A]) (k: K) (a: A) :
  a ∈ group_by p m k ↔ p a = k ∧ a ∈ m :=
begin
  rw [elem_mp, elem_mp], simp,
end

lemma group_by_linear (m1 m2: Z[A]) :
  group_by p (m1 + m2) = group_by p m1 + group_by p m2 :=
begin
  ext k a, simp,
  split_ifs; refl
end

end group_by.

/- A few properties about [distinct] -/

@[simp]
lemma ite_ite {A: Type} {c1: Prop} [decidable c1] {c2: Prop} [decidable c2] (x z: A) :
  ite c1 (ite c2 x z) z = ite (c1 ∧ c2) x z :=
begin
  split_ifs; clarify,
end

-- this doesn't require is_bag i
lemma filter_distinct_comm (p: A → Prop) [decidable_pred p] (i: Z[A]) :
  filter p (distinct i) = distinct (filter p i) :=
begin
  ext a, simp,
  apply if_congr; try { refl },
  split_ifs; clarify,
end

theorem product_distinct_comm (i1: Z[A]) (i2: Z[B]) :
  is_bag i1 → is_bag i2 →
  product (distinct i1) (distinct i2) = distinct (product i1 i2) :=
begin
  intros hpos1 hpos2,
  ext ab, cases ab with a b, simp,
  have h1 := hpos1 a, have h2 := hpos2 b,
  simp at h1 h2,
  apply if_congr; try { refl },
  tauto { closer := `[nlinarith] },
end

theorem join_distinct_comm (π1: A → C) (π2: B → C) (i1: Z[A]) (i2: Z[B]) :
  is_bag i1 → is_bag i2 →
  equi_join π1 π2 (distinct i1) (distinct i2) = distinct (equi_join π1 π2 i1 i2) :=
begin
  intros hpos1 hpos2,
  unfold equi_join,
  rw <- filter_distinct_comm,
  { rw<- product_distinct_comm; assumption },
end

theorem intersect_distinct_comm (i1 i2: Z[A]) :
  is_bag i1 → is_bag i2 →
  distinct i1 ∩ distinct i2 = distinct (i1 ∩ i2) :=
begin
  intros hpos1 hpos2,
  ext a, simp,
  apply if_congr; try { refl },
  have h1 := hpos1 a, have h2 := hpos2 a, simp at h1 h2,
  tauto { closer := `[nlinarith] },
end

private lemma map_at_distinct_none (f: A → B) (i: Z[A]) (b: B) :
  is_bag i →
  (∀ a, a ∈ i → f a ≠ b) →
  flatmap_at (λ a, {f a}) i.distinct b = 0 :=
begin
  intros hpos h,
  unfold flatmap_at,
  rw finset.sum_eq_zero,
  intros x ix_pos, simp at ix_pos,
  simp, intros hfx,
  suffices hne : f x ≠ b, { tauto },
  apply h, rw elem_mp, linarith,
end

theorem map_inj_distinct_comm (f: A → B) [f_inj: function.injective f] (i: Z[A]) :
  is_bag i →
  distinct (zset.map f i) = zset.map f (distinct i) :=
begin
  intros hpos,
  ext b, simp,
  unfold zset.map,
  rw [flatmap_apply, flatmap_apply],
  split_ifs with h h; rw (map_at_pos _ _ _ hpos) at h,
  { cases h with a h, cases h with hel hf,
    have ha := hpos a, simp at ha,
    rw flatmap_map_at,
    -- split sum into a and everything else; intuition is that "everything else"
    -- can't include any matching elements because f is injective
    rw<- (@finset.sum_erase_add _ _ _ _ _ _ a),
    { rw finset.sum_eq_zero,
      { rw distinct_apply,
        rw elem_mp at hel,
        rw if_pos, swap, assumption,
        rw if_pos, swap, omega,
        refl, },
      introv hel_erase,
      split_ifs, swap, refl,
      simp at hel_erase |-,
      suffices hxa : (x = a), { exfalso, tauto, },
      apply f_inj, cc,
    },
    simp, { rw elem_mp at hel, omega },
  },
  { push_neg at h,
    rw map_at_distinct_none,
    assumption,
    assumption,
  }
end

@[simp]
lemma distinct_idem (i: Z[A]) :
  distinct (distinct i) = distinct i :=
begin
  ext a, simp,
  split_ifs; refl <|> linarith,
end

theorem filter_distinct_dedup (p: A → Prop) [decidable_pred p] (i: Z[A]) :
  distinct (filter p (distinct i)) = distinct (filter p i) :=
begin
  rw [filter_distinct_comm, distinct_idem],
end

theorem map_distinct_dedup (f: A → B) (i: Z[A]) :
  is_bag i →
  distinct (zset.map f (distinct i)) = distinct (zset.map f i) :=
begin
  intros hpos,
  ext b, simp,
  apply if_congr; try { refl },
  unfold zset.map,
  rw [flatmap_apply, flatmap_apply],
  rw [map_at_pos, map_at_pos],
  { conv_lhs {
      congr,
      funext,
      rw (distinct_elem hpos),
      skip,
    },
   },
  { assumption, },
  { simp, },
end

theorem add_distinct_dedup (i1 i2: Z[A]) :
  is_bag i1 → is_bag i2 →
  distinct (i1.distinct + i2.distinct) = distinct (i1 + i2) :=
begin
  intros hpos1 hpos2,
  ext a, simp,
  have h1 := hpos1 a, have h2 := hpos2 a, simp at h1 h2,
  split_ifs; refl <|> linarith,
end

theorem product_distinct_dedup (i1: Z[A]) (i2: Z[B]) :
  is_bag i1 → is_bag i2 →
  distinct (product (distinct i1) (distinct i2)) = distinct (product i1 i2) :=
begin
  intros hpos1 hpos2,
  rw [product_distinct_comm, distinct_idem];
  assumption
end

theorem join_distinct_dedup (π1: A → C) (π2: B → C) (i1: Z[A]) (i2: Z[B]) :
  is_bag i1 → is_bag i2 →
  distinct (equi_join π1 π2 (distinct i1) (distinct i2)) = distinct (equi_join π1 π2 i1 i2) :=
begin
  intros hpos1 hpos2,
  rw [join_distinct_comm, distinct_idem];
  assumption,
end

theorem intersect_distinct_dedup (i1 i2: Z[A]) :
  is_bag i1 → is_bag i2 →
  distinct (distinct i1 ∩ distinct i2) = distinct (i1 ∩ i2) :=
begin
  intros hpos1 hpos2,
  rw [intersect_distinct_comm, distinct_idem];
  assumption,
end
