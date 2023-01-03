-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .linear

/-!
# Incremental version of an operator

A key idea of DBSP is to define for any `Q: operator a b` an incremental version
of it, `Q^Δ := D ∘ Q ∘ I`. Notice that `Q^Δ : operator a b` - it has the same
type as `Q`, but it takes as input a stream of changes and outputs a stream of
diffs.
-/

section groups.

variables {a : Type} [add_comm_group a].
variables {b : Type} [add_comm_group b].
variables {c : Type} [add_comm_group c].

/-- The core definition of DBSP is the incremental version of an operator Q, Q^Δ.

If we think of the operator Q as a transformation on databases, Q^Δ operates on
a stream of changes and outputs a stream of changes. It does this by simply
integrating the input, applying Q, and differentiating the output. The power of
DBSP comes from re-arranging incremental computations to produce more efficient plans.
-/
def incremental (Q: operator a b) : operator a b :=
  λ s, D (Q (I s)).

-- applied version of incremental that can be useful for rewriting
lemma incremental_unfold (Q: operator a b) (s: stream a) :
  incremental Q s = D (Q (I s)) := rfl.

/-- A version of incremental for curried operators, defined directly. Written
T^Δ2.  -/
def incremental2 (T: operator2 a b c) : operator2 a b c :=
  λ s1 s2, D (T (I s1) (I s2)).

-- applied version of incremental2 that can be useful for rewriting
lemma incremental2_unfold (Q: operator2 a b c) (s1: stream a) (s2: stream b) :
  incremental2 Q s1 s2 = D (Q (I s1) (I s2)) := rfl.

postfix `^Δ`:90 := incremental.
postfix `^Δ2`:90 := incremental2.

private def incremental_inv (Q: operator a b) : operator a b :=
  I ∘ Q ∘ D.

local attribute [simp] derivative_integral integral_derivative.

theorem incremental_inversion_l :
  function.left_inverse (@incremental a _ b _) incremental_inv :=
begin
  intros Q,
  unfold incremental incremental_inv,
  funext s, simp,
end

theorem incremental_inversion_r :
  function.right_inverse (@incremental a _ b _) incremental_inv :=
begin
  intros Q,
  unfold incremental incremental_inv,
  funext s, simp,
end

theorem incremental_bijection :
  function.bijective (@incremental a _ b _) :=
begin
  split,
  { apply function.left_inverse.injective,
    apply incremental_inversion_r, },
  { apply function.right_inverse.surjective,
    apply incremental_inversion_l, },
end

private meta def prove_incremental : tactic unit :=
  do
    tactic.interactive.unfold [``incremental, ``incremental2] (interactive.loc.ns [none]),
    tactic.interactive.funext [`s],
    tactic.interactive.simp none none false [] [] (interactive.loc.ns [none]),
    return ()

theorem delay_invariance : incremental (@delay a _) = delay :=
begin
  funext s, rw incremental_unfold,
  rw derivative_time_invariant,
  simp,
end

theorem integral_invariance : incremental (@I a _) = I :=
  by prove_incremental.

theorem derivative_invariance : incremental (@D a _) = D :=
  by prove_incremental.

theorem integrate_push (Q: operator a b) :
  Q ∘ I = I ∘ Q^Δ :=
  by prove_incremental.

theorem derivative_push (Q: operator a b) :
  D ∘ Q = Q^Δ ∘ D :=
  by prove_incremental.

theorem I_push (Q: operator a b) (s: stream a) :
  Q (I s) = I (Q^Δ s) :=
  by prove_incremental.

theorem D_push (Q: operator a b) (s: stream a) :
  D (Q s) = Q^Δ (D s) :=
  by prove_incremental.

theorem D_push2 (Q: operator2 a b c) (s1: stream a) (s2: stream b) :
  D (Q s1 s2) = Q^Δ2 (D s1) (D s2) :=
  by prove_incremental.

theorem chain_incremental (Q1: operator b c) (Q2: operator a b) :
  (Q1 ∘ Q2)^Δ = Q1^Δ ∘ Q2^Δ :=
  by prove_incremental.

theorem incremental_comp (Q1: operator b c) (Q2: operator a b) (s: stream a) :
  (λ s, Q1 (Q2 (s)))^Δ s = Q1^Δ (Q2^Δ s) :=
  by prove_incremental.

theorem add_incremental (Q1 Q2: operator a b) :
  (Q1 + Q2)^Δ = Q1^Δ + Q2^Δ :=
begin
  prove_incremental,
  rw derivative_linear,
end

lemma cycle_body_strict (T: operator2 a b b) (hcausal: causal (uncurry_op T)) :
  ∀ s, strict (λ (α : stream b), T s (z⁻¹ α)) :=
begin
  intros s,
  apply (causal_strict_strict delay delay_strict _ _),
  apply causal_uncurry_op_fixed, assumption,
end

lemma cycle_body_integral_strict (T: operator2 a b b) (hcausal: causal (uncurry_op T)) :
  ∀ s, strict (λ (α : stream b), T (I s) (z⁻¹ α)) :=
begin
  intros s,
  apply (causal_strict_strict delay delay_strict _ _),
  apply causal_uncurry_op_fixed, assumption,
end

lemma cycle_body_incremental_strict (T: operator2 a b b) (hcausal: causal (uncurry_op T))
  (s: stream a) : strict (λ α, T^Δ2 s (z⁻¹ α)) :=
begin
  apply (causal_strict_strict delay delay_strict
                              (λ α, D (T (I s) (I α))) _),
  apply (causal_comp_causal _ _ _ derivative_causal),
  apply (causal_comp_causal _ integral_causal _ _),
  apply causal_uncurry_op_fixed, assumption,
end

theorem cycle_incremental (T: operator2 a b b) (hcausal: causal (uncurry_op T)) :
  (λ (s: stream a), fix (λ α, T s (z⁻¹ α)))^Δ =
  λ s, fix (λ α, T^Δ2 s (z⁻¹ α)) :=
begin
  funext s,
  apply fix_unique,
  { -- strictness of the body
    apply cycle_body_incremental_strict, assumption, },
  { -- fixpoint equation
    unfold incremental incremental2,
    rw integral_time_invariant, simp,
    congr' 1,
    apply fix_eq, apply cycle_body_integral_strict; assumption, }
end

lemma incremental_sprod (f: operator (a×b) c) (s1: stream a) (s2: stream b) :
  f^Δ (sprod (s1, s2)) = (λ s1 s2, f (sprod (s1, s2)))^Δ2 s1 s2 :=
begin
  unfold incremental incremental2,
  rw integral_sprod,
end

theorem lifting_cycle_body_strict2 (T: operator2 a b b) (hcausal: causal (uncurry_op T)) :
  ∀ s, strict2 (λ (α : stream (stream b)), ↑²T s (↑↑z⁻¹ α)) :=
begin
  rw causal2 at hcausal,
  intros s,
  intros s1 s2 n t heq,
  apply hcausal, refl,
  intros n' hle,
  by_cases (n' = 0), { subst n', simp, },
  simp,
  rw delay_sub_1, swap, omega,
  rw delay_sub_1, swap, omega,
  apply heq; omega,
end

lemma sum_vals_nested (s: stream (stream a)) (n t: ℕ)  :
  sum_vals s n t = sum_vals (λ n, s n t) n :=
begin
  induction n with n; simp, finish,
end

lemma integral_lift_time_invariant (s: stream (stream a)) :
  I (↑↑z⁻¹ s) = ↑↑z⁻¹ (I s) :=
begin
  funext n t, simp,
  repeat { rw integral_sum_vals },
  rw sum_vals_nested,
  by_cases (t = 0),
  { subst t, simp, rw sum_vals_zero, finish, },
  simp,
  rw delay_linear, simp,
  rw delay_sub_1, swap, omega,
  rw sum_vals_nested,
  congr' 1,
  funext n,
  rw delay_sub_1, omega,
end

lemma lift_integral_lift_time_invariant (s: stream (stream a)) :
  ↑↑I (↑↑z⁻¹ s) = ↑↑z⁻¹ (↑↑I s) :=
begin
  funext n t, simp,
  rw integral_time_invariant,
end

lemma lifting_delay_linear : linear (↑↑(@delay a _)) :=
begin
  apply (lifting_lti _ _).1,
  intros, rw delay_linear,
end

lemma integral_causal_nested' (s1 s2: stream (stream a)) (n t: ℕ)
  (heq: ∀ n' ≤ n, s1 n' t = s2 n' t) :
  I s1 n t = I s2 n t :=
begin
  rw [integral_sum_vals, integral_sum_vals],
  repeat { rw sum_vals_nested }, simp,
  rw heq; try { omega }, simp,
  induction n with n; simp,
  rw heq; try { omega }, simp,
  apply n_ih,
  intros, apply heq; omega,
end

@[simp]
lemma integral_causal_nested : causal_nested (@I (stream a) _) :=
begin
  intros s1 s2 n t heq,
  apply integral_causal_nested',
  intros, apply heq; omega,
end

@[simp]
lemma derivative_causal_nested : causal_nested (@D (stream a) _) :=
begin
  intros s1 s2 n t heq,
  unfold D, simp,
  rw heq, rotate, omega, omega,
  simp,
  unfold delay, split_ifs, simp,
  rw heq; omega,
end

lemma cycle_body_strict2 (T: operator2 a (stream b) (stream b))
  (s: stream a) :
  causal_nested (T s) →
  strict2 (λ α, T s (↑↑z⁻¹ α)) :=
begin
  intros hcausal,
  unfold strict2, intros s1 s2 n t hseq,
  funext t,
  apply hcausal, intros,
  apply lifting_delay_strict2, intros,
  apply hseq; omega,
end

lemma cycle_body_incremental_strict2 (T: operator2 a (stream b) (stream b))
  (s: stream a) :
  causal_nested (T (I s)) →
  strict2 (λ α, T^Δ2 s (↑↑z⁻¹ α)) :=
begin
  intros hcausal,
  unfold incremental2,
  unfold strict2, intros s1 s2 n t hseq,
  funext t,
  apply derivative_causal_nested, intros,
  apply hcausal, intros,
  apply integral_causal_nested, intros,
  apply lifting_delay_strict2, intros,
  apply hseq; omega,
end

theorem lifting_cycle (T: operator2 a b b) (hcausal: causal (uncurry_op T)) :
  ↑↑(λ s, fix (λ α, T s (z⁻¹ α))) = λ s, fix2 (λ α, ↑²T s (↑↑z⁻¹ α)) :=
begin
  funext s,
  apply fix2_unique,
  { apply lifting_cycle_body_strict2, assumption, },
  { funext t, simp,
    apply fix_eq, apply cycle_body_strict, assumption,
   }
end

theorem cycle2_incremental (T: operator2 a (stream b) (stream b))
  (hcausal: ∀ s, causal_nested (T s)) :
  (λ (s: stream a), fix2 (λ α, T s (↑↑z⁻¹ α)))^Δ =
  λ s, fix2 (λ α, T^Δ2 s (↑↑z⁻¹ α)) :=
begin
  funext s,
  apply fix2_unique,
  { -- strictness of the body
    apply (cycle_body_incremental_strict2 T), finish, },
  { -- fixpoint equation
    unfold incremental incremental2,
    rw integral_lift_time_invariant, simp,
    congr' 1,
    apply fix2_eq, apply cycle_body_strict2, finish, },
end

theorem lti_incremental (Q: operator a b) (h: lti Q) :
  Q^Δ = Q :=
begin
  funext s, unfold incremental,
  unfold D,
  rw<- h.2,
  rw<- integral_time_invariant,
  rw<- (linear_sub h.1),
  rw<- (linear_sub integral_linear),
  change (s - z⁻¹ s) with (D s), simp,
end

@[simp]
theorem I_incremental :
  I^Δ = @I a _ :=
begin
  apply lti_incremental,
  apply integral_lti,
end

@[simp]
theorem D_incremental :
  D^Δ = @D a _ :=
begin
  apply lti_incremental,
  apply derivative_lti,
end

theorem delay_lti :
  lti (@delay a _) :=
begin
  split,
  apply delay_linear,
  apply delay_time_invariant,
end

@[simp]
theorem delay_incremental :
  z⁻¹^Δ = @delay a _ :=
begin
  apply lti_incremental,
  apply delay_lti,
end

lemma sprod_time_invariant (T : operator2 a b c)
  (s1 : stream a) (s2 : stream b) :
  ↑(z⁻¹ s1, z⁻¹ s2) = z⁻¹ (↑(s1, s2) : stream (a × b)) :=
begin
  funext t, simp,
  unfold delay,
  split_ifs; simp,
end

lemma time_invariant_map_fst (s: stream (a × b)) (n: ℕ) :
  (z⁻¹ s n).fst = z⁻¹ (λ (n : ℕ), (s n).fst) n :=
begin
  unfold delay,
  split_ifs; simp,
end

lemma time_invariant_map_snd (s: stream (a × b)) (n: ℕ) :
  (z⁻¹ s n).snd = z⁻¹ (λ (n : ℕ), (s n).snd) n :=
begin
  unfold delay,
  split_ifs; simp,
end

lemma time_invariant2 (T: operator2 a b c) :
  time_invariant (uncurry_op T) ↔
  (∀ s1 s2, T (z⁻¹ s1) (z⁻¹ s2) = z⁻¹ (T s1 s2)) :=
begin
  split,
  { intros hti, intros _ _,
    rw (uncurry_op_intro T),
    rw (uncurry_op_intro T),
    rw<- hti,
    congr,
    rw<- (sprod_time_invariant T), },
  { intros h s,
    funext t, simp [uncurry_op, lifting],
    rw<- h,
    congr' 1; funext t,
    { rw time_invariant_map_fst, },
    { rw time_invariant_map_snd, },
  }
end

@[simp]
theorem causal_incremental (Q: operator a b) :
  causal Q →
  causal (Q^Δ) :=
begin
  intros h,
  unfold incremental,
  apply causal_comp_causal, swap, apply derivative_causal,
  apply causal_comp_causal, swap, apply h,
  apply integral_causal,
end

theorem causal_incremental2 (Q: operator2 a b c) :
  causal (uncurry_op Q) →
  causal (λ s, Q^Δ2 (↑↑prod.fst s) (↑↑prod.snd s)) :=
begin
  intros h,
  apply causal_comp_causal, swap, apply derivative_causal,
  rw causal2 at h,
  intros s1 s2 n heq, simp,
  apply h,
  { apply causal_respects_agree_upto, apply integral_causal,
    apply causal_respects_agree_upto, apply lifting_causal,
    assumption,
  },
  { apply causal_respects_agree_upto, apply integral_causal,
    apply causal_respects_agree_upto, apply lifting_causal,
    assumption,
  },
end

@[simp]
theorem causal_nested_incremental
  (Q: operator (stream a) (stream b)) :
  causal_nested Q →
  causal_nested (Q^Δ) :=
begin
  intros h,
  unfold causal_nested, intros,
  rw [incremental_unfold, incremental_unfold],
  apply causal_nested_comp, apply derivative_causal_nested,
  apply h,
  intros,
  apply integral_causal_nested, intros, apply heq; omega,
end

@[simp]
theorem causal_nested_lifting2 {d: Type} [add_comm_group d]
  (f: stream b → stream c → stream d) (g: operator (stream a) (stream b)) (h: operator (stream a) (stream c)) :
  causal (uncurry_op f) →
  causal_nested g →
  causal_nested h →
  causal_nested (λ s, ↑²f (g s) (h s)) :=
begin
  intros hf hg hh,
  intros s1 s2 n t heq, simp,
  rw causal2 at hf,
  apply hf,
  { intros n' hle, apply hg, intros, apply heq; omega },
  { intros n' hle, apply hh, intros, apply heq; omega },
end

@[simp]
theorem causal_nested_lifting2_incremental {d: Type} [add_comm_group d]
  (f: stream b → stream c → stream d) (g: operator (stream a) (stream b)) (h: operator (stream a) (stream c)) :
  causal (uncurry_op f) →
  causal_nested g →
  causal_nested h →
  causal_nested (λ s, ↑²f^Δ2 (g s) (h s)) :=
begin
  intros hf hg hh,
  unfold incremental2,
  apply causal_nested_comp, simp,
  apply causal_nested_lifting2,
  { assumption, },
  { apply causal_nested_comp, simp, assumption, },
  { apply causal_nested_comp, simp, assumption, },
end

@[simp]
theorem causal_lifting2 {d: Type} [add_comm_group d]
  (f: b → c → d) (g: operator a b) (h: operator a c) :
  causal g →
  causal h →
  causal (λ s, ↑²f (g s) (h s)) :=
begin
  intros hg hh,
  intros s1 s2 n heq, simp,
  rw [hg, hh]; assumption,
end

@[simp]
theorem causal_lifting2_incremental {d: Type} [add_comm_group d]
  (f: b → c → d) (g: operator a b) (h: operator a c) :
  causal g →
  causal h →
  causal (λ s, ↑²f^Δ2 (g s) (h s)) :=
begin
  intros hg hh,
  apply causal_comp_causal, swap, simp,
  apply causal_lifting2,
  { apply causal_comp_causal; simp, assumption, },
  { apply causal_comp_causal; simp, assumption, },
end

lemma lifting2_sum (f g: a → b → c) :
  (↑² (λ x y, f x y + g x y)) = ↑²f + ↑²g := rfl.

theorem lifting2_incremental_sum (f g: a → b → c) :
  (↑² (λ x y, f x y + g x y))^Δ2 = ↑²f^Δ2 + ↑²g^Δ2 :=
begin
  unfold incremental2,
  funext s1 s2 t, simp,
  rw lifting2_sum, simp,
  rw derivative_linear, simp,
end

private lemma lifting2_incremental_unfold {d e: Type} [add_comm_group d] [add_comm_group e]
  (f: b → c → d) (g: a → b) (h: e → c) :
  ↑²(λ x y, f (g x) (h y))^Δ2 = λ s1 s2, D (↑²f (↑↑g (I s1)) (↑↑h (I s2))) :=
begin
  refl,
end

lemma lifting2_incremental_comp {d e: Type} [add_comm_group d] [add_comm_group e]
  (f: b → c → d) (g: a → b) (h: e → c) :
  ↑²(λ x y, f (g x) (h y))^Δ2 = λ s1 s2, ↑²f^Δ2 (↑↑g^Δ s1) (↑↑h^Δ s2) :=
begin
  funext s1 s2,
  rw lifting2_incremental_unfold, dsimp,
  rw incremental2_unfold,
  rw D_push2,
  refl,
end

@[simp]
lemma incremental_id :
  incremental (λ (x:stream a), x) = id :=
  by { funext s, rw incremental_unfold, simp, }.

@[simp]
lemma incremental_id' :
  incremental (@id (stream a)) = id :=
  by { funext s, rw incremental_unfold, simp, }.

lemma lifting2_incremental_comp_1' {d: Type} [add_comm_group d]
  (f: b → c → d) (g: a → b) :
  ↑²(λ x, f (g x))^Δ2 = λ s1, ↑²f^Δ2 (↑↑g^Δ s1) :=
begin
  funext s1 s2,
  rw lifting2_incremental_comp, simp,
end

lemma lifting2_incremental_comp_1 {d: Type} [add_comm_group d]
  (f: b → c → d) (g: a → b) :
  ↑²(λ x y, f (g x) y)^Δ2 = λ s1 s2, ↑²f^Δ2 (↑↑g^Δ s1) s2 :=
begin
  simp,
  apply lifting2_incremental_comp_1',
end

lemma lifting2_incremental_comp_2 {d e: Type} [add_comm_group d] [add_comm_group e]
  (f: b → c → d) (h: e → c) :
  ↑²(λ x y, f x (h y))^Δ2 = λ s1 s2, ↑²f^Δ2 s1 (↑↑h^Δ s2) :=
begin
  funext s1 s2,
  rw lifting2_incremental_comp, simp,
end

end groups.

-- This theorem is much more clearly stated using the metavariables a, b, c for
-- terms (to match the paper), so here we instead use α, β, γ for the types.
section bilinear.

variables {α : Type} [add_comm_group α].
variables {β : Type} [add_comm_group β].
variables {γ : Type} [add_comm_group γ].

variable (times: operator2 α β γ).

-- write times a b as a ** b for this section
-- NOTE: this isn't printed, sadly
local notation a ` ** `:70 b:70 := times a b.

local attribute [simp] derivative_integral integral_derivative.

def times_incremental : stream α → stream β → stream γ :=
  λ a b, a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b).

theorem bilinear_incremental  :
  time_invariant (uncurry_op times) →
  bilinear times →
  times^Δ2 = times_incremental times :=
begin
  intros hti hbil, funext a b,
  -- this calculation is almost a transcription of the paper proof in
  -- https://github.com/vmware/database-stream-processor/blob/main/doc/spec.pdf
  calc times^Δ2 a b = D (I a ** I b) : by refl
      ... = I a ** I b - z⁻¹ (I a ** I b) : by refl
      ... = I a ** I b - z⁻¹ (I a) ** z⁻¹ (I b) : by {
              rw (time_invariant2 _).mp hti
            }
      ... = I a ** I b - z⁻¹ (I a) ** z⁻¹ (I b)
                + z⁻¹ (I a) ** I b - z⁻¹ (I a) ** I b : by { abel }
      ... = D (I a) ** I b + z⁻¹ (I a) ** D (I b) : by {
              unfold D,
              rw (bilinear_sub_1 hbil),
              rw (bilinear_sub_2 hbil), abel,
            }
      ... = a ** I b + z⁻¹ (I a) ** b : by simp
      ... = a ** I b - a ** z⁻¹ (I b) + a ** z⁻¹ (I b)
            + z⁻¹ (I a) ** b : by abel
      ... = a ** D (I b) + a ** z⁻¹ (I b) + z⁻¹ (I a) ** b : by {
              unfold D,
              rw (bilinear_sub_2 hbil),
            }
      ... = a ** b + z⁻¹ (I a) ** b + a ** z⁻¹ (I b) : by { simp, abel, }
      -- this one extra step is needed that the paper skips over
      ... = a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) : by {
              repeat { rw integral_time_invariant },
           },
end

-- NOTE: this is a much simpler proof than the one in the paper
theorem bilinear_incremental_forward_proof :
  time_invariant (uncurry_op times) →
  bilinear times →
  ∀ a b, times^Δ2 a b =
  a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) :=
begin
  intros hti hbil a b,
  unfold incremental2 D,
  -- we're just going to expand (I a) and (I b) in the first occurrence
  conv {
    find (times (I a) (I b)) {
      rw [integral_unfold a, integral_unfold b]
    }
  },
  -- push delays as far inward as possible
  rw<- (time_invariant2 _).mp hti,
  repeat { rw<- integral_time_invariant },
  -- and now we can expand using bilinearity
  repeat { rw hbil.1 <|> rw hbil.2 },
  abel,
end

-- variant of [bilinear_incremental_forward_proof] written with [conv] so the
-- proof itself is readable
theorem bilinear_incremental_short_paper_proof  :
  time_invariant (uncurry_op times) →
  bilinear times →
  ∀ a b, times^Δ2 a b =
  a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) :=
begin
  intros hti hbil a b,
  calc times^Δ2 a b = D (I a ** I b) : by refl
      ... = I a ** I b - z⁻¹ (I a ** I b) : by refl
      ... = I a ** I b - z⁻¹ (I a) ** z⁻¹ (I b) : by {
        rw<- (time_invariant2 _).mp hti,
      }
      ... = (a + z⁻¹ (I a)) ** (b + z⁻¹ (I b)) - z⁻¹ (I a) ** z⁻¹ (I b) : by {
          congr' 1,
          conv_lhs {
            find (times (I a) (I b)) {
              rw [integral_unfold a, integral_unfold b]
            }
          },
      }
      ... = a ** b + z⁻¹ (I a) ** b + a ** z⁻¹ (I b) + z⁻¹ (I a) ** z⁻¹ (I b)
                - z⁻¹ (I a) ** z⁻¹ (I b) : by {
              -- bilinearity to distribute (a + b) × (c + d)
              rw [hbil.2, hbil.1, hbil.1],
              abel,
            }
      ... = a ** b + z⁻¹ (I a) ** b + a ** z⁻¹ (I b) : by {
              -- cancel terms
              abel,
            }
      ... = a ** b + I (z⁻¹ a) ** b + a ** I (z⁻¹ b) : by {
          rw [integral_time_invariant, integral_time_invariant],
      },
end

end bilinear.

attribute [irreducible] incremental incremental2.

-- #lint only doc_blame simp_nf
