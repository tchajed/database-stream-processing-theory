-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .relational
import .relational_incremental
import .recursive

open zset.

variables {Node: Type} [decidable_eq Node].

def Edge (Node: Type) := Node × Node.

instance : decidable_eq (Edge Node) := by apply_instance.

-- get a self-edge for the head
def πh (input: Edge Node) : Edge Node := (input.1, input.1).
-- get a self-edge for the tail
def πt (input: Edge Node) : Edge Node := (input.2, input.2).

def πht (x: Edge Node × Edge Node) : Edge Node :=
  let r1 := x.1 in
  let e := x.2 in
  (r1.1, e.2).

local prefix (name := lifting) `↑`:std.prec.max := lifting.

def closure1 (E R1: Z[Edge Node]) : Z[Edge Node] :=
  distinct $
    zset.map πht (equi_join prod.snd prod.fst R1 E) +
    E +
    zset.map πh E +
    zset.map πt E.

lemma lifting_closure1_eq (E R1: stream Z[Edge Node]) :
  ↑²closure1 E R1 =
  ↑distinct (
    ↑(zset.map πht) (↑²(equi_join prod.snd prod.fst) R1 E) +
    E +
    ↑(zset.map πh) E +
    ↑(zset.map πt) E) := rfl.

noncomputable def closure : Z[Edge Node] → Z[Edge Node] := naive closure1.

noncomputable def closure_seminaive : Z[Edge Node] → Z[Edge Node] :=
  λ E, let E := δ0 E in
  ∫ $ fix (λ R, ↑distinct^Δ
                (↑(zset.map πht) (↑²(equi_join prod.snd prod.fst)^Δ2 (z⁻¹ R) E) +
                E +
                ↑(zset.map πh) E +
                ↑(zset.map πt) E)).

theorem closure_efficient_ok :
  @closure_seminaive Node _ = closure :=
begin
  unfold closure,
  symmetry,
  rw<- seminaive_equiv,
  funext E,
  unfold closure_seminaive seminaive,
  dsimp,
  congr' 2,
  funext R1,
  conv_lhs {
    simp [incremental2], rw lifting_closure1_eq, skip,
  },
  simp,
  rw D_push, congr' 1,
  repeat { rw derivative_linear }, simp,
  rw D_push, simp,
  rw incremental2_unfold,
end

noncomputable def incremental_closure : operator (Z[Edge Node]) (Z[Edge Node]) :=
  incremental (λ dE,
    let E := ↑δ0 dE in
    ↑∫ $ fix2 (λ R, ↑((↑distinct)^Δ)
                  (↑(↑(zset.map πht))
                    (↑²(↑²(equi_join prod.snd prod.fst)^Δ2) (↑z⁻¹ R) E) +
                  E +
                  ↑(↑(zset.map πh)) E +
                  ↑(↑(zset.map πt)) E))).

local attribute [simp] sum_causal causal_comp_causal.

theorem incremental_closure_ok :
  @incremental_closure Node _ = (↑closure)^Δ :=
begin
  funext EΔ,
  unfold incremental_closure, unfold incremental, dsimp,
  rw<- closure_efficient_ok,
  generalize heq : I EΔ = E, clear_dependent EΔ,
  congr' 1,
  change (↑closure_seminaive E) with
    (↑∫ $ ↑(λ E, fix (λ R, ↑distinct^Δ
                    (↑(zset.map πht) (↑²(equi_join prod.snd prod.fst)^Δ2 (z⁻¹ R) E) +
                    E +
                    ↑(zset.map πh) E +
                    ↑(zset.map πt) E))) $ ↑δ0 $ E),
  rw lifting_cycle (λ (E R: stream Z[Edge Node]), ↑distinct^Δ (↑(zset.map πht)
          (↑²(equi_join prod.snd prod.fst)^Δ2 R E) +
          E +
          ↑(zset.map πh) E +
          ↑(zset.map πt) E)),
  { simp,
    congr' 2, },
  unfold uncurry_op,
  simp,
end

noncomputable def incremental_closure2 : operator Z[Edge Node] Z[Edge Node] :=
  λ dE,
    let E := ↑δ0 dE in
    (↑∫)^Δ $ fix2 (λ R, ↑((↑distinct)^Δ)^Δ
                  (↑(↑(zset.map πht))
                    (↑²(↑²(equi_join prod.snd prod.fst)^Δ2)^Δ2 (↑z⁻¹ R) E) +
                  E +
                  ↑(↑(zset.map πh)) E +
                  ↑(↑(zset.map πt)) E)).

lemma fix2_congr {a: Type} [add_comm_group a] (F1 F2: operator (stream a) (stream a)) :
  F1 = F2 →
  fix2 F1 = fix2 F2 := by cc.

@[simp]
lemma lifting_map_πht_incremental :
  ↑(↑(zset.map (@πht Node _)))^Δ = ↑(↑(zset.map πht)) :=
begin
  apply lifting_map_incremental,
end

theorem incremental_closure2_ok :
  @incremental_closure2 Node _ = (↑closure)^Δ :=
begin
  rw<- incremental_closure_ok,
  funext dE, simp [incremental_closure, incremental_closure2],
  symmetry,
  rw (incremental_comp (↑∫) _ dE),
  congr' 1,
  rw (cycle2_incremental
    (λ s (R : stream (stream Z[Edge Node])),
              ↑(↑distinct^Δ)
                (↑ ↑(zset.map πht) (↑²(↑²(equi_join prod.snd prod.fst)^Δ2) R (↑δ0 s)) +
                       ↑δ0 s +
                     ↑ ↑(zset.map πh) (↑δ0 s) +
                   ↑ ↑(zset.map πt) (↑δ0 s)))
  ), dsimp,
  apply fix2_congr, funext R,
  rw (incremental2_unfold _ dE),
  rw D_push,
  congr' 1,
  rw derivative_linear,
  rw derivative_linear,
  rw derivative_linear,
  rw D_push, simp,
  rw D_push2, simp,
  rw D_push, simp,
  rw D_push, simp,
  rw D_push, simp,
  rw D_push, simp,
  rw D_push, simp,

  -- need to prove causal_nested
  intros s, dsimp,
  apply causal_nested_comp; simp,
  apply sum_causal_nested; simp,
  apply sum_causal_nested; simp,
  apply sum_causal_nested; simp,
  apply causal_nested_comp, simp,
  apply causal_nested_lifting2; simp,
  { unfold uncurry_op,
    apply causal_lifting2_incremental; simp, },
  { apply causal_nested_id, },
end

def distinct_double_incremental {A: Type} [decidable_eq A] : operator (stream Z[A]) (stream Z[A]) :=
  λ i, D $ ↑²(↑² (@distinct_H A _)) (↑z⁻¹ (↑I (I i))) (I i).

theorem distinct_double_incremental_ok {A: Type} [decidable_eq A] :
  (↑(↑(@distinct A _)^Δ))^Δ =
  distinct_double_incremental :=
begin
  funext s,
  unfold distinct_double_incremental,
  rw distinct_incremental_ok,
  unfold distinct_incremental,
  rw incremental_unfold,
  refl,
end

section equi_join.
variables {A B C: Type}.
variables [decidable_eq A] [decidable_eq B] [decidable_eq C].

variables (π1: A → C) (π2: B → C).

local notation x `▹◃`:40 y := (lifting2 (lifting2 (equi_join x y))).

local attribute [irreducible] lifting2 equi_join.

def join_double_incremental1 : operator2 (stream (Z[A])) (stream Z[B]) (stream Z[A × B]) :=
  λ a b,
      ↑²(↑²(equi_join π1 π2))^Δ2 a b +
      ↑²(↑²(equi_join π1 π2))^Δ2 (↑z⁻¹ $ ↑I $ a) b +
      ↑²(↑²(equi_join π1 π2))^Δ2 a (↑z⁻¹ $ ↑I $ b).

@[simp]
lemma lifting_I_delay_incremental {a: Type} [add_comm_group a] :
  incremental ↑(λ (x: stream a), I (z⁻¹ x)) = ↑(λ x, I (z⁻¹ x)) :=
begin
  apply lti_incremental,
  apply lifting_lti,
  intros s1 s2,
  rw [delay_linear, integral_linear],
end

lemma lifting_I_delay_simplify (s: stream (stream Z[A])) :
  ↑(λ x, I (z⁻¹ x)) s = ↑z⁻¹ (↑I s) :=
begin
  rw<- lifting_comp,
  funext t, simp,
  rw integral_time_invariant,
end

theorem join_double_incremental1_ok :
  ↑²(↑²(equi_join π1 π2)^Δ2)^Δ2 = join_double_incremental1 π1 π2 :=
begin
  unfold join_double_incremental1,
  rw equi_join_incremental, unfold times_incremental,
  funext a b,
  rw lifting2_incremental_sum,
  rw lifting2_incremental_sum,
  simp,
  rw (lifting2_incremental_comp_1 _ (λ (x: stream Z[A]), I (z⁻¹ x))),
  rw (lifting2_incremental_comp_2 _ (λ (y: stream Z[B]), I (z⁻¹ y))),
  simp,
  rw lifting_I_delay_simplify,
  rw lifting_I_delay_simplify,
end

-- this is the fully optimized circuit
def join_double_incremental : operator2 (stream Z[A]) (stream Z[B]) (stream Z[A × B]) :=
  λ a b,
    let join := ↑²(↑²(equi_join π1 π2)) in
    join (z⁻¹ (I a)) (↑z⁻¹ $ ↑I b) +
    join (I $ ↑I $ a) b +
    join (↑I a) (z⁻¹ $ I b) +
    join a (↑z⁻¹ $ I $ ↑I b).

lemma equi_join_lifting2_time_invariant :
  ∀ s1 s2, z⁻¹ (↑²(↑² (equi_join π1 π2)) s1 s2) =
           ↑²(↑² (equi_join π1 π2)) (z⁻¹ s1) (z⁻¹ s2) :=
begin
  intros s1 s2,
  funext n t, simp,
  unfold delay, split_ifs; simp,
end

lemma equi_join_double_lift_bilinear :
  bilinear (↑²(↑² (equi_join π1 π2))) :=
begin
  split; intros,
  { funext n t, simp, rw (equi_join_bilinear _ _).1, },
  { funext n t, simp, rw (equi_join_bilinear _ _).2, },
end

lemma equi_join_I_1 :
  ∀ a b, ↑²(↑² (equi_join π1 π2)) (I a) b =
  ↑²(↑² (equi_join π1 π2)) a b +
  ↑²(↑² (equi_join π1 π2)) (z⁻¹ (I a)) b :=
begin
  intros,
  conv_lhs {
    rw [integral_unfold a],
  },
  rw (equi_join_double_lift_bilinear _ _).1,
end

lemma equi_join_lift_I_1 :
  ∀ a b,
    ↑²(↑² (equi_join π1 π2)) (↑I a) b =
    ↑²(↑² (equi_join π1 π2)) a b +
    ↑²(↑² (equi_join π1 π2)) (↑I (↑z⁻¹ a)) b :=
begin
  intros,
  funext n t, simp,
  conv_lhs {
    rw integral_unfold,
  },
  simp,
  rw (equi_join_bilinear _ _).1,
  rw integral_time_invariant,
end

lemma equi_join_lift_I_2 :
  ∀ a b,
    ↑²(↑² (equi_join π1 π2)) a (↑I b) =
    ↑²(↑² (equi_join π1 π2)) a b +
    ↑²(↑² (equi_join π1 π2)) a (↑I (↑z⁻¹ b)) :=
begin
  intros,
  funext n t, simp,
  conv_lhs {
    rw integral_unfold,
  },
  simp,
  rw (equi_join_bilinear _ _).2,
  rw integral_time_invariant,
end

lemma equi_join_I_2 :
  ∀ a b, ↑²(↑² (equi_join π1 π2)) a (I b) =
  ↑²(↑² (equi_join π1 π2)) a b +
  ↑²(↑² (equi_join π1 π2)) a (z⁻¹ (I b)) :=
begin
  intros,
  conv_lhs {
    rw [integral_unfold b],
  },
  rw (equi_join_double_lift_bilinear _ _).2,
end

lemma equi_join_I_unfold :
  ∀ a b, ↑²(↑² (equi_join π1 π2)) (I a) (I b) =
  ↑²(↑² (equi_join π1 π2)) a b +
  ↑²(↑² (equi_join π1 π2)) a (z⁻¹ (I b)) +
  ↑²(↑² (equi_join π1 π2)) (z⁻¹ (I a)) b +
  ↑²(↑² (equi_join π1 π2)) (z⁻¹ (I a)) (z⁻¹ (I b)) :=
begin
  intros,
  repeat { rw equi_join_I_1 <|> rw equi_join_I_2 },
  abel,
end

private lemma neg_add_sub {α: Type} [add_comm_group α] (x y: α) :
  (-1 : ℤ) • x + y = y - x :=
begin
  abel,
end

private lemma add_both_sides {G} [has_add G] [is_right_cancel_add G] (x: G) {a b: G} :
  a + x = b + x -> a = b :=
begin
  apply add_right_cancel,
end

private lemma fold_join_helper :
  ∀ a b, ((-1 : ℤ) • (π1▹◃π2) (I (z⁻¹ (↑I a))) b + (π1▹◃π2) (I (z⁻¹ (↑I (↑z⁻¹ a)))) b) =
   (-1 : ℤ) • (π1▹◃π2) (I (z⁻¹ a)) b  :=
begin
  intros,
  apply (add_both_sides ((π1▹◃π2) (I (z⁻¹ a)) b)),
  abel,
  rw neg_add_sub,
  rw<- add_sub_assoc,
  rw<- (equi_join_double_lift_bilinear π1 π2).1,
  rw<- integral_linear,
  rw<- delay_linear,
  rw<- (bilinear_sub_1 (equi_join_double_lift_bilinear π1 π2)),
  rw<- (linear_sub integral_linear),
  rw<- (linear_sub delay_linear),
  have hz: a + ↑I (↑z⁻¹ a) - ↑I a = 0 := by {
    have h: ↑I a = a + ↑I (↑z⁻¹ a) := by {
      funext n, simp,
      conv_lhs {
        rw integral_unfold,
      },
      rw integral_time_invariant,
    },
    rw h, abel,
  },
  rw hz, simp,
  funext n t, simp,
end

theorem join_double_incremental_ok :
  ↑²(↑²(equi_join π1 π2)^Δ2)^Δ2 = join_double_incremental π1 π2 :=
  begin
  rw join_double_incremental1_ok,
  unfold join_double_incremental1 join_double_incremental,
  funext a b, simp,
  unfold incremental2,
  unfold D,
  repeat { rw equi_join_lifting2_time_invariant },
  rw equi_join_I_unfold,
  rw equi_join_I_unfold,
  rw equi_join_I_unfold,
  abel,
  repeat { rw<- integral_lift_time_invariant <|>
           rw<- lift_integral_lift_time_invariant <|>
           rw<- integral_time_invariant },
  conv_rhs {
    rw equi_join_I_1 π1 π2 (↑I a) b,
    rw equi_join_I_2 π1 π2 a _,
    rw (equi_join_lift_I_1 π1 π2 a),
    rw (equi_join_lift_I_1 π1 π2 a),
  },
  repeat { rw<- integral_lift_time_invariant <|>
           rw<- lift_integral_lift_time_invariant <|>
           rw<- integral_time_invariant },
  repeat { rw add_assoc },
  apply eq_of_sub_eq_zero,
  abel,
  abel,
  rw fold_join_helper,
  abel,
end

end equi_join.

noncomputable def incremental_closure_opt : operator Z[Edge Node] Z[Edge Node] :=
  λ dE,
    let E := ↑δ0 dE in
    (↑∫)^Δ $ fix2 (λ R, distinct_double_incremental
                  (↑(↑(zset.map πht))
                    (join_double_incremental prod.snd prod.fst (↑z⁻¹ R) E) +
                  E +
                  ↑(↑(zset.map πh)) E +
                  ↑(↑(zset.map πt)) E)).

theorem incremental_closure_opt_ok :
  @incremental_closure_opt Node _ = (↑closure)^Δ :=
begin
  rw<- incremental_closure2_ok,
  unfold incremental_closure_opt incremental_closure2,
  funext dE, dsimp,
  congr' 1,
  congr' 1,
  funext R,
  rw distinct_double_incremental_ok,
  rw join_double_incremental_ok,
end
