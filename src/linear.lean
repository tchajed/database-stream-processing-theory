-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .operators
import algebra.group.defs
import algebra.group.pi
import algebra.ring.basic
import tactic.abel

/-!
# Linearity, differentiation, and integration

This file extends DBSP with two key operators: differentiation and integration.
These are based on the idea of linearity, a property of streams over Abelian
(commutative) groups.
-/

variables {a : Type} [add_comm_group a].
variables {b : Type} [add_comm_group b].
variables {c : Type} [add_comm_group c].

instance stream_group : add_comm_group (stream a) := by { unfold stream, apply_instance }.

/-- An operator `S` is linear if S (x + y) = S x + S y; that is, it should be a
homomorphism between `stream a` and `stream b`. -/
def linear (S: operator a b) :=
  -- note this is phrased in the stream group
  (∀ x y, S (x + y) = S x + S y).

-- for symmetry with the other properties derived from linear (and to avoid
-- directly depending on this definition)
lemma linear_add {S: operator a b} (h: linear S) :
  ∀ s1 s2, S (s1 + s2) = S s1 + S s2 := h.

lemma linear_zero {S: operator a b} (h: linear S) :
  S 0 = 0 :=
begin
  have h0 := h 0 0,
  simp at h0,
  apply h0,
end

lemma linear_neg {S: operator a b} (h: linear S) :
  ∀ s, S (-s) = -S s :=
begin
  intros s,
  have h0 := h (-s) s, simp at h0,
  rw (linear_zero h) at h0,
  apply add_eq_zero_iff_eq_neg.mp, rw<- h0,
end

lemma linear_sub {S: operator a b} (h: linear S) :
  ∀ s1 s2, S (s1 - s2) = S s1 - S s2 :=
begin
  intros,
  repeat { rw sub_eq_add_neg },
  rw h,
  rw (linear_neg h),
end

theorem lifted_linear (f: a → b) :
  (∀ x y, f (x + y) = f x + f y) →
  linear (lifting f) :=
begin
  intros hlin s1 s2, funext s, simp,
  rw hlin,
end

/-- LTI stands for linear time invariant. -/
def lti (S: operator a b) :=
  linear S ∧ time_invariant S.

-- a weak zero-preservation at only t=0
lemma lti_operator_zpp (S: operator a b) :
  lti S → S 0 0 = 0 := λ h, time_invariant_0_0 S h.2.

/-- A function of two arguments is bilinear if it is linear in each argument
separately (holding the other constant). A classic example is multiplication. -/
def bilinear (f: a → b → c) :=
  -- linear in each argument, separately
  (∀ x1 x2 y, f (x1 + x2) y = f x1 y + f x2 y) ∧
  (∀ x y1 y2, f x (y1 + y2) = f x y1 + f x y2).

lemma bilinear_sub_1 {f: operator2 a b c} (hblin: bilinear f) :
  ∀ x1 x2 y, f (x1 - x2) y = f x1 y - f x2 y :=
begin
  intros _ _ _,
  have h: linear (λ x, f x y) := by {
    unfold linear,
    intros _ _,
    apply hblin.1,
  },
  apply (linear_sub h),
end

lemma bilinear_sub_2 {f: operator2 a b c} (hblin: bilinear f) :
  ∀ x y1 y2, f x (y1 - y2) = f x y1 - f x y2 :=
begin
  intros _ _ _,
  have h: linear (f x) := hblin.2 x,
  apply (linear_sub h),
end

theorem lifting_bilinear (f: a → b → c) :
  bilinear f → bilinear ↑²f :=
begin
  intros hf, unfold lifting2,
  split,
  { intros x1 x2 z,
    funext t, simp,
    apply hf.1, },
  { intros x1 x2 z,
    funext t, simp,
    apply hf.2, },
end

-- note that this is for the specific group ℤ
theorem mul_Z_bilinear :
  bilinear (lifting2 (λ (z1 z2 : ℤ), z1 * z2)) :=
begin
  apply lifting_bilinear,
  split; intros _ _ _; ring_nf,
end

-- NOTE: it is important to take {a: Type} since we don't want to assume the
-- group and ring structures over a separately, we need the group structure to
-- be the one from the ring
theorem mul_ring_bilinear {a: Type} [ring a] :
  bilinear (@lifting2 a a a (λ (z1 z2 : a), z1 * z2)) :=
begin
  apply lifting_bilinear,
  split; intros _ _ _; ring_nf,
  { rw right_distrib, },
  { rw left_distrib, },
end

/--

A "feedback" circuit that keeps adding its output from the previous time step,
defined using a fixpoint. To be well-defined, `S` must be causal.

```
                ┌─────┐
 s ────▶ + ────▶│  S  │───▶ α
         ▲      └─────┘
         │         │
      ┌─────┐      │
      │ z⁻¹ │◀─────┘
      └─────┘
```
-/
def feedback (S: operator a a) : operator a a :=
  λ s, fix (λ α, S (s + delay α)).

theorem feedback_strict {S : operator a a}
  (hcausal : causal S) (s : stream a) :
  strict (λ (α : stream a), S (s + delay α)) :=
begin
  apply (feedback_ckt_body_strict _ delay_strict (λ s t, S (s + t))),
  rw causal2,
  introv h1 h2,
  apply hcausal,
  intros i hle, simp,
  rw [h1, h2]; omega
end

/-- As long as `S` is [causal], the body of the feedback loop is strict and
[feedback] can be unfolded according to its recursive definition. -/
theorem feedback_unfold (S: operator a a) :
  causal S →
  ∀ s, feedback S s = S (s + delay (feedback S s)) :=
begin
  intros hcausal s,
  unfold feedback,
  apply fix_eq,
  apply (feedback_strict hcausal),
end

lemma delay_linear : linear (@delay a _) :=
begin
  intros x y,
  funext t,
  unfold delay, simp,
  by_cases h_t : t = 0,
  { repeat { rw (if_pos h_t) }, simp, },
  { repeat { rw (if_neg h_t) } },
end

theorem add_linear :
  linear (uncurry_op ((+) : stream a → stream a → stream a)) :=
begin
  intros x y,
  funext t,
  unfold uncurry_op delay, simp,
  abel,
end

lemma agree_upto_respects_add (s1 s2 s1' s2': stream a) (n: ℕ) :
  s1 ==n== s1' →
  s2 ==n== s2' →
  (s1 + s2) ==n== (s1' + s2') :=
begin
  intros h1 h2,
  intros t hle, simp,
  rw [h1, h2]; assumption,
end

lemma agree_upto_respects_sub (s1 s2 s1' s2': stream a) (n: ℕ) :
  s1 ==n== s1' →
  s2 ==n== s2' →
  (s1 - s2) ==n== (s1' - s2') :=
begin
  intros h1 h2,
  intros t hle, simp,
  rw [h1, h2]; assumption,
end

-- TODO: can we give a general characterization of time invariance of fixpoints?

theorem feedback_time_invariant (S: operator a a) :
  causal S → time_invariant S →
  time_invariant (feedback S) :=
begin
  intros hcausal hti,
  intros s,
  rw agree_everywhere_eq,
  intros n,
  induction n with n,
  { rw agree_upto_0,
    unfold feedback, simp,
    rw (time_invariant_t hti), simp,
  },
  { rw feedback_unfold; try { assumption },
    rw<- delay_linear,
    rw hti,
    apply delay_succ_upto,
    have h : s + feedback S (delay s) ==n== s + delay (feedback S s) := by {
      apply agree_upto_respects_add,
      reflexivity, assumption,
    },
    have heq := (causal_respects_agree_upto _ hcausal _ _ _ h),
    transitivity, assumption,
    rw<- (feedback_unfold _ hcausal s),
  },
end

theorem feedback_causal (S: operator a a) :
  causal S →
  causal (feedback S) :=
begin
  intros hcausal,
  have h := hcausal,
  rw causal_to_agree at h |-,
  introv heq,
  induction n with n,
  { rw [feedback_unfold _ hcausal s1,
        feedback_unfold _ hcausal s2],
    apply h,
    rw agree_upto_0 at heq |-, simp, assumption,
   },
  { rw [feedback_unfold _ hcausal s1,
        feedback_unfold _ hcausal s2],
    apply h,
    apply agree_upto_respects_add, assumption,
    apply delay_succ_upto,
    apply n_ih,
    apply agree_upto_weaken1, assumption, }
end

theorem feedback_linear (S: operator a a) :
  causal S → lti S →
  linear (feedback S) :=
begin
  intros hcausal hlti,
  cases hlti with hlin hti,
  intros s1 s2,
  symmetry, apply fix_unique,
  { apply (feedback_strict hcausal) },
  conv_lhs begin
    rw [feedback_unfold _ hcausal s1,
        feedback_unfold _ hcausal s2]
  end,
  repeat { rw hlin <|> rw delay_linear },
  abel,
end

theorem feedback_lti (S: operator a a) :
  causal S → lti S →
  lti (feedback S) :=
begin
  intros hcausal hlti,
  split,
  { apply feedback_linear; assumption, },
  { apply feedback_time_invariant; cases hlti; assumption },
end

/-- The derivative operator, written simply `D`, is a core operator in DBSP. It
"differentiates" a stream: `(D s)(t) = s(t) - s(t - 1)` (with `(D s)(0) = 0`),
producing a stream of what we can think of as changes, although both the input
and output are streams of a's.

Theorem names related to the derivative will use 'derivative'.
-/
def D : operator a a := λ s, s - delay s.

@[simp]
lemma derivative_causal : causal (@D a _) :=
begin
  rw causal_to_agree,
  unfold D,
  intros s s' t hagree,
  apply agree_upto_respects_sub,
  assumption,
  apply agree_upto_weaken1,
  apply delay_succ_upto, assumption,
end

lemma derivative_time_invariant : time_invariant (@D a _) :=
begin
  unfold time_invariant D,
  intros s,
  rw (linear_sub delay_linear),
end

lemma derivative_linear : linear (@D a _) :=
begin
  intros s1 s2,
  unfold D,
  funext s, simp,
  repeat { rw delay_linear },
  abel, simp,
  rw add_comm,
end

lemma derivative_lti : lti (@D a _) :=
begin
  split, apply derivative_linear, apply derivative_time_invariant,
end

/-- The integral operator is another fundamental operator in DBSP. It takes a
stream of changes and computes the sum of the changes so far; this is
implemented recursively with a fixpoint.

Theorem names will use 'integral' even though the operator is named I.
-/
def I : operator a a := feedback id.

protected lemma id_causal : causal (@id (stream a)) :=
begin
  unfold causal,
  intros s s' t heq,
  apply heq, omega,
end

protected lemma id_time_invariant : time_invariant (@id (stream a)) :=
begin
  unfold time_invariant,
  simp,
end

protected lemma id_lti : lti (@id (stream a)) :=
begin
  split,
  { intros s1 s2, simp },
  apply id_time_invariant,
end

@[simp]
lemma integral_causal : causal (@I a _) :=
begin
  apply feedback_causal,
  apply id_causal
end

theorem integral_lti : lti (@I a _) :=
begin
  unfold I,
  apply feedback_lti,
  { apply id_causal, },
  { apply id_lti, }
end

theorem integral_time_invariant : time_invariant (@I a _) :=
  integral_lti.2.

theorem integral_linear : linear (@I a _) :=
  integral_lti.1.

theorem integral_unfold :
  ∀ (s: stream a), I s = s + delay (I s) :=
begin
  intros s,
  unfold I,
  apply feedback_unfold,
  apply id_causal,
end

/-- The sum of `s[0] .. s[n-1]`. This is a closed form version of the integral
operator (offset by 1), as proven in [integral_sum_vals]. -/
def sum_vals (s: stream a) : ℕ → a
| 0 := 0
| (nat.succ n) := s n + sum_vals n.

@[simp]
lemma sum_vals_0 (s: stream a) : sum_vals s 0 = 0 := rfl.

@[simp]
lemma sum_vals_1 (s: stream a) : sum_vals s 1 = s 0 :=
begin
  unfold sum_vals, simp,
end

attribute [simp] sum_vals.equations._eqn_2.

/- The sum of an all-zero stream is zero. -/
lemma sum_vals_zero (s: stream a) :
  (∀ n, s n = 0) →
  ∀ (n:ℕ), sum_vals s n = 0 :=
begin
  intros hz n,
  induction n with n,
  { simp, },
  { simp, rw [hz, n_ih], abel, },
end

@[simp]
lemma integral_0 (s: stream a) : I s 0 = s 0 :=
begin
  rw integral_unfold, simp,
end

theorem integral_sum_vals (s: stream a) (n: ℕ) :
  I s n = sum_vals s n.succ :=
begin
  induction n with n,
  { simp, },
  { rw integral_unfold, simp,
    rw n_ih, refl, }
end

@[simp]
lemma integral_zpp : I (0: stream a) = 0 :=
begin
  funext t,
  rw integral_sum_vals, simp,
  rw sum_vals_zero, simp,
end

-- simple expression for the values of derivative s
@[simp]
lemma derivative_0 (s: stream a) :
  D s 0 = s 0 :=
begin
  unfold D; simp,
end

theorem derivative_difference_t (s: stream a) (t: ℕ) :
  0 < t →
  D s t = s t - s (t - 1) :=
begin
  intros hnz,
  unfold D delay, dsimp,
  rw if_neg, omega,
end

@[simp]
lemma derivative_zpp : D (0: stream a) = 0 :=
begin
  funext t, unfold D, simp,
end

lemma add_causal :
  causal (uncurry_op ((+) : operator2 a a a)) :=
begin
  unfold causal, introv heq,
  unfold uncurry_op, simp, rw heq, linarith,
end

lemma sum_causal (f g: operator a b) :
  causal f →
  causal g →
  causal (λ x, f x + g x) :=
begin
  unfold causal, intros hf hg, introv heq,
  simp, rw [hf, hg]; assumption,
end

lemma sum_causal_nested (f g: operator (stream a) (stream b)) :
  causal_nested f →
  causal_nested g →
  causal_nested (λ x, f x + g x) :=
begin
  unfold causal_nested, intros hf hg, introv heq,
  simp, rw [hf, hg]; assumption,
end

lemma sum_vals_succ_n (s: stream a) (t: ℕ) :
  sum_vals (D s) t.succ = s t :=
begin
  induction t with t,
  { unfold sum_vals D, simp, },
  simp only [sum_vals] at t_ih |-,
  rw derivative_difference_t; try { omega },
  rw t_ih, simp,
end

@[simp]
theorem derivative_integral (s: stream a) :
  I (D s) = s :=
begin
  funext t,
  rw integral_sum_vals,
  rw sum_vals_succ_n,
end

-- We can give an alternative proof based on the fact that I is the unique
-- fixpoint of α = α + z⁻¹ α.
private theorem derivative_integral_alt (s: stream a) :
  I (D s) = s :=
begin
  symmetry,
  simp [I, feedback],
  apply fix_unique,
  { apply feedback_ckt_body_strict,
    apply delay_strict,
    apply add_causal,  },
  { unfold D, abel, },
end

-- And yet another proof, based on linearity, the fixpoint equation, and time
-- invariance.
private theorem derivative_integral_alt2 (s: stream a) :
  I (D s) = s :=
begin
  unfold D,
  rw (linear_sub integral_linear),
  rw (integral_unfold s),
  rw integral_time_invariant, abel,
end

@[simp]
theorem integral_derivative (s: stream a) :
  D (I s) = s :=
begin
  unfold D,
  calc I s - delay (I s)
        = s + delay (I s) - delay (I s) : by { congr', apply integral_unfold, }
  ...   = s : by { rw add_sub_cancel, },
end

theorem derivative_integral_inverse (α s: stream a):
  α = I s ↔ D α = s :=
begin
  split,
  { intros h, subst α,
    rw integral_derivative, },
  { intros h, subst s,
    rw derivative_integral,
   }
end

lemma i_d_comp :
  I ∘ D = @id (stream a) :=
begin
  funext s, simp,
end

lemma d_i_comp :
  D ∘ I = @id (stream a) :=
begin
  funext s, simp,
end

theorem lifting_linear (f: a → b) :
  (∀ x y, f (x + y) = f x + f y)  →
  linear (↑↑f) :=
begin
  intros hlin,
  intros x y, ext t, simp, apply hlin,
end

-- convenience for generating lti theorems
theorem lifting_lti (f: a → b) :
  (∀ x y, f (x + y) = f x + f y)  →
  lti (↑↑ f) :=
begin
  intros hlin,
  split,
  { apply lifting_linear, assumption, },
  { apply lifting_time_invariant,
    have h0 := hlin 0 0, simp at h0,
    apply h0, },
end

lemma derivative_sprod (s1: stream a) (s2: stream b) :
  D (sprod (s1, s2)) = sprod (D s1, D s2) :=
begin
  funext t, simp,
  by_cases (t = 0),
  { subst t, simp, },
  { repeat { rw derivative_difference_t }; try { omega },
    simp,
  },
end

lemma integral_sprod (s1: stream a) (s2: stream b) :
  I (sprod (s1, s2)) = sprod (I s1, I s2) :=
begin
  funext t, simp,
  repeat { rw integral_sum_vals },
  simp,
  induction t,
  { simp, },
  { simp, rw t_ih, refl, },
end

lemma integral_lift_comm (f: a → b) (s: stream a) :
  (∀ x y, f (x + y) = f x + f y) →
  I (↑↑f s) = ↑↑f (I s) :=
begin
  intros hlin,
  funext t, simp,
  repeat { rw integral_sum_vals },
  induction t,
  { simp, },
  { simp at t_ih |-,
    rw [hlin, t_ih],
  }
end

lemma integral_fst_comm (s: stream (a × b)) :
  I (↑↑prod.fst s) = ↑↑prod.fst (I s) :=
begin
  apply integral_lift_comm,
  intros x y, simp,
end

lemma integral_snd_comm (s: stream (a × b)) :
  I (↑↑prod.snd s) = ↑↑prod.snd (I s) :=
begin
  apply integral_lift_comm,
  intros x y, simp,
end

-- #lint only doc_blame simp_nf
