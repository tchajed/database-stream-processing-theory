-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .stream
-- for prod.has_zero
import algebra.group.prod
import tactic.omega.main
import tactic.linarith
import tactic.split_ifs

/-!
# DBSP operators

We define the DBSP core constructs (lifting, delay, and fixpoints) and the
associated properties of causality, time invariance, and strict causality.

This file defines properties over `stream a` that only depend on the existence
of an arbitrary "zero" element `0 : a`. This zero need not have particular
properties.

NOTE: paper implicitly assumes groups throughout, here we are able to weaken
that assumption.
-/

universes u v.

/-- An operator is a function between streams. -/
@[reducible]
def operator (a b: Type u) : Type u := stream a → stream b.
/-- An operator2 is a function on two streams.

This is isomorphic to `operator (a × b) c`, but in Lean this is easier to use;
there may be a better way to use the uncurried version to avoid defining this
specially. -/
@[reducible]
def operator2 (a b c: Type u) : Type u := stream a → stream b → stream c.

/-- ↑↑f turns an ordinary function into an operator by pointwise lifting.

The paper uses ↑f for this notion, but that means a different notion (also
called lift) in mathlib.
 -/
def lifting {a b: Type} (f: a → b) : operator a b :=
  λ s, λ n, f (s n).
-- lifting binds very tightly (similar to ⁻¹), so that ↑↑f x is (↑↑f) x
prefix `↑↑`:std.prec.max := lifting.

@[simp]
lemma lifting_eq {a b: Type} (f: a → b) (s: stream a) (n: ℕ) :
  ↑↑f s n = f (s n) := rfl.

/-- Lift a curried function. See [lifting]. -/
def lifting2 {a b c: Type} (f: a → b → c) : operator2 a b c :=
  λ s1 s2, λ n, f (s1 n) (s2 n).

@[simp]
lemma lifting2_apply {a b c: Type} (f: a → b → c)
  (s1: stream a) (s2: stream b) (n: ℕ) :
  lifting2 f s1 s2 n = f (s1 n) (s2 n) := rfl.

@[simp]
lemma lifting_id {a: Type} :
  lifting (λ (x:a), x) = id := rfl.

prefix `↑²`:std.prec.max := lifting2.

variables {a : Type} [has_zero a].
variables {b : Type} [has_zero b].
variables {c : Type} [has_zero c].

-- this is moderately dangerous because ↑ is actually recursive, so without a
-- type from the environment this can lift to `operator (stream a) (stream b)`
-- (with an arbitrary number of streams).
instance stream_lift : has_lift (a → b) (operator a b) := ⟨lifting⟩.

/-
note that we will overload 0 for
- 0 : ℕ
- 0 : a (the group element)
- 0 : stream a (which is just [λ _, (0:a)])
-/

/--
Product of two streams as a single stream.

This is part of how multi-argument streams are formalized, which is more
explicit than in the paper.
-/
def sprod {a b: Type} : stream a × stream b → stream (a × b) :=
  λ s, λ n, (s.1 n, s.2 n).

@[reducible]
instance sprod_coe : has_coe (stream a × stream b) (stream (a × b)) :=
  ⟨ λ ⟨s1, s2⟩ n, (s1 n, s2 n) ⟩.

@[simp]
lemma sprod_apply (s: stream a × stream b) (n: ℕ) :
  (sprod s) n = (s.1 n, s.2 n) := rfl.

@[simp]
lemma sprod_coe_unfold (s: stream a × stream b) (n: ℕ) :
  (↑s : stream (a × b)) n = (s.1 n, s.2 n) :=
begin
  cases s with s1 s2,
  refl,
end

/-- Convert a curried [operator2] into an ordinary [operator] over a tuple. -/
def uncurry_op (T: operator2 a b c) : operator (a × b) c :=
  λ s, T (↑↑prod.fst s) (↑↑prod.snd s).

lemma uncurry_op_intro (T: operator2 a b c) (s1: stream a) (s2: stream b) :
  T s1 s2 = uncurry_op T (s1, s2) := by { funext t, refl }.

theorem lifting_distributivity {a b c: Type} (f: a → b) (g: b → c) :
  lifting (g ∘ f) = lifting g ∘ lifting f := rfl.

theorem lifting_comp {a b c: Type} (f: a → b) (g: b → c) (s: stream a) :
  ↑↑ (λ x, g (f x)) s = ↑↑ g (↑↑ f s) := rfl.

theorem lifting2_comp {a b c d e: Type}
  (f: a → c) (g: b → d) (T: c → d → e)
  (s1: stream a) (s2: stream b) :
  ↑² (λ x y, T (f x) (g y)) s1 s2 = ↑²T (↑↑f s1) (↑↑g s2) := rfl.

theorem lifting2_comp' {a b c d e: Type}
  (f: a → c) (g: b → d) (T: c → d → e) :
  ↑² (λ x y, T (f x) (g y)) = λ s1 s2, ↑²T (↑↑f s1) (↑↑g s2) := rfl.

/-- The delay operator `z⁻¹` is a fundamental DBSP operator that shifts a stream over by one time
step. For `t=0` it inserts a zero element, which is the main reason a `0 : a`
(expressed with `has_zero a` here) is required.
-/
def delay : operator a a :=
  λ (s: stream a), λ t, if t = 0 then 0 else s (t - 1).

notation `z⁻¹` := delay.

/-- Time invariance intuitively expresses that an operator does not depend on
the exact time, only the sequence. It is expressed by saying that `S ∘ z⁻¹ = z⁻¹
∘ S`, that is, that the operator commutes with delay (see [time_invariant_comp]
for a proof that this definition equals that one).

Essentially all operators considered in DBSP are time invariant (although this
may not be strictly necessary).
 -/
def time_invariant (S: operator a b) :=
  ∀ s, S (z⁻¹ s) = z⁻¹ (S s).

/-- Show [time_invariant] is equivalent to the definition in the paper.

The definition of [time_invariant] is easier to use in Lean since it can be used
directly as a rewrite, whereas composed functions don't appear syntactically in
proofs. -/
lemma time_invariant_comp (S: operator a b) :
  time_invariant S ↔ S ∘ z⁻¹ = z⁻¹ ∘ S :=
begin
  split; intros h,
  { funext s, simp, rw h, },
  { intros s, apply (congr_fun h s), },
end

/-- Characterizes time invariance for lifted operators: they must satisfy the
"zero preservation property", namely `f 0 = 0`. This arises because the delay
inserts a 0 at `z⁻¹ (S ↑↑f) 0`, and the function must do the same in `S (z⁻¹ (↑↑
f)) 0`. -/
theorem lifting_time_invariance (f: a → b) :
  time_invariant (lifting f) ↔ f 0 = 0 :=
begin
  unfold time_invariant,
  split,
  { intro h,
    have heq := congr_fun (h 0) 0,
    simp [delay, lifting] at heq,
    assumption,
   },
  { intros h0 s,
    funext t,
    simp [delay, lifting],
    split_ifs; clarify,
  },
end

lemma lifting_time_invariant (f: a → b) :
  f 0 = 0 → time_invariant (↑↑ f) :=
 (lifting_time_invariance f).mpr.

-- delay by definition produces 0 at time t
@[simp]
lemma delay_t_0 (s: stream a) : z⁻¹ s 0 = 0
:= rfl.

@[simp]
lemma delay_0 : z⁻¹ (0 : stream a) = 0 :=
begin
  funext t, unfold delay, simp,
end

@[simp]
lemma delay_succ (s: stream a) (n: ℕ) : z⁻¹ s n.succ = s n
:= rfl.

lemma delay_sub_1 (s: stream a) (n: ℕ) :
  0 < n → z⁻¹ s n = s (n-1) :=
begin
  intros h,
  unfold delay, rw if_neg, omega,
end

lemma delay_eq_at (s1 s2: stream a) (t: ℕ) :
  (0 < t → s1 (t-1) = s2 (t-1)) →
  z⁻¹ s1 t = z⁻¹ s2 t :=
begin
  intros heq,
  unfold delay, split_ifs, simp,
  apply heq, omega,
end

lemma time_invariant_0_0 (S: operator a b) :
  time_invariant S → S 0 0 = 0 :=
begin
  intros hti,
  unfold time_invariant at hti,
  have h := congr_fun (hti 0) 0,
  simp at h,
  assumption,
end

-- time_invariant definition applied to a specific s and t
lemma time_invariant_t {S: operator a b} (h: time_invariant S) :
  ∀ s t, S (delay s) t = delay (S s) t :=
begin
  unfold time_invariant at h,
  intros s t,
  have heq := congr_fun (h s) t,
  assumption,
end

-- this is zero-preservation over zero streams
lemma time_invariant_zpp (S: operator a b) :
  time_invariant S → S 0 = 0 :=
begin
  intros hti,
  funext t,
  change ((0: stream b) t) with (0: b),
  induction t,
  { apply time_invariant_0_0, assumption, },
  { rw<- delay_0,
    rw (time_invariant_t hti), simp,
    assumption,
  }
end

lemma lift_time_invariant (f: a → b) :
  f 0 = 0 →
  time_invariant ↑↑f :=
begin
  intros hzpp s,
  funext t; simp,
  unfold delay, split_ifs,
  { apply hzpp },
  { simp }
end

lemma delay_time_invariant : time_invariant (@delay a _) :=
  by { intros s, refl }.


theorem lifting2_time_invariant (f: a → b → c) :
  time_invariant (uncurry_op (↑² f)) ↔ f 0 0 = 0 :=
begin
  split,
  { intros h,
    apply (congr_fun (h 0) 0), },
  { intros h0 s,
    funext t,
    simp [delay, lifting2, uncurry_op],
    split_ifs; clarify,
   }
end


/-- A causal operator intuitively depends at time `t` only on previous inputs.
Note that an operator can use its input at time `t` itself; imagine all
operators operate synchronously, and we compute all of them before emitting the
output. The formal definition says that if two streams agree up to time t, then
S must return the same result at time t for both.
-/
def causal (S: operator a b) :=
  ∀ (s s': stream a), ∀ t, s ==t== s' → S s t = S s' t.

@[simp]
theorem lifting_causal (f: a → b) : causal (lifting f) :=
begin
  intros s s' t hpre,
  simp [lifting],
  rw (hpre t),
  omega,
end

theorem delay_causal : causal (@delay a _) :=
begin
  intros s s' t hpre,
  simp [causal, delay],
  rw hpre,
  omega,
end

-- composition of two causal operators is causal
theorem causal_comp_causal
  (S1: operator a b) (h1: causal S1)
  (S2: operator b c) (h2: causal S2) :
  causal (λ s, S2 (S1 s)) :=
begin
  intros s1 s2 n heq, simp,
  apply h2,
  intros i hle,
  apply h1,
  intros j hle_j, apply heq, omega,
end

lemma causal_respects_agree_upto (S: operator a b) (h: causal S)
  (s1 s2: stream a) (n: ℕ) :
  s1 ==n== s2 →
  S s1 ==n== S s2 :=
begin
  intros heq n hle,
  apply h,
  intros _ hle', apply heq, omega,
end

lemma causal_to_agree (S: operator a b) :
  causal S ↔ (∀ s1 s2 n, s1 ==n== s2 → S s1 ==n== S s2) :=
begin
  split,
  { intros s1 s2 n h,
    apply causal_respects_agree_upto; assumption, },
  intros heq_n,
  intros s1 s2 t hagree,
  apply (heq_n _ _ t),
  { intros i, apply hagree, },
  omega,
end

-- More convenient definition of causal for two-argument operators. `causal
-- (uncurry_op T)` is a convenient way to re-use the definition of causal, but
-- this is easier to use for the curried operator directly.
lemma causal2 (T: operator2 a b c) :
  causal (uncurry_op T) ↔
  (∀ s1 s1' s2 s2' n, s1 ==n== s1' → s2 ==n== s2' →
                      T s1 s2 n = T s1' s2' n) :=
begin
  split,
  { intros hcausal,
    intros _ _ _ _ _ h1 h2,
    have h := hcausal (sprod (s1, s2)) (sprod (s1', s2')) n,
    unfold uncurry_op sprod at h, simp at h,
    apply h,
    { intros i hle, simp,
      rw [h1, h2]; try { omega },
      split; refl,
    },
  },
  { intros h, intros _ _ _ heq,
    unfold uncurry_op sprod at ⊢,
    apply h,
    { intros i hle, simp,
      rw heq, omega, },
    { intros i hle, simp,
      rw heq, omega, },
  },
end

lemma causal2_agree (T: operator2 a b c) :
  causal (uncurry_op T) →
  (∀ s1 s1' s2 s2' n, s1 ==n== s1' → s2 ==n== s2' →
                      T s1 s2 ==n== T s1' s2') :=
begin
  rw causal2, introv hcausal heq1 heq2,
  intros m hle,
  apply hcausal,
  apply agree_upto_weaken, assumption, omega,
  apply agree_upto_weaken, assumption, omega,
end

theorem uncurry_op_lifting {d:Type} [add_comm_group d] (f: c → d) (t: stream a → stream b → stream c) :
  uncurry_op (λ (x: stream a) (y: stream b), ↑↑f (t x y)) = ↑↑f ∘ uncurry_op t :=
begin
  funext xy t, simp [uncurry_op],
end

-- causal (uncurry_op T) can be weakened to a specific fixed first argument
lemma causal_uncurry_op_fixed (T: operator2 a b b) :
  causal (uncurry_op T) →
  ∀ s, causal (T s) :=
begin
  intros hcausal,
  intros s s' n heq,
  rw causal2 at hcausal,
  apply hcausal, refl,
end

lemma lifting_lifting2_comp {d: Type} [has_zero d] (f: c → d) (g: a → b → c) :
  ∀ s1 s2, ↑↑f (↑²g s1 s2) = ↑²(λ x y, f (g x y)) s1 s2 :=
begin
  intros s1 s2, funext t, simp,
end

lemma uncurry_op_lifting2 (f: a → b → c) :
  uncurry_op (↑²f) = ↑ (λ (xy: a × b), f xy.1 xy.2) := rfl.

/-- Strictly causal. Similar to [causal], a strictly causal (or simply _strict_)
operator depends only on past inputs; unlike causal, a strict operator at time
`n` can depend only on `t < n` and not `n` itself. -/
def strict (S: operator a b) :=
  ∀ (s s': stream a), ∀ t, (∀ i < t, s i = s' i) → S s t = S s' t.

/-- Strictly causal operators have a unique output at time 0 (because they
aren't allowed to depend on the input at time 0), but it need not actually be 0.
That requirement can come from [time_invariant].
-/
theorem strict_unique_zero (S: operator a b) (h: strict S) :
  ∀ s s', S s 0 = S s' 0 :=
begin
  intros s s',
  apply h,
  intros i hcontra,
  by_contradiction,
  apply nat.not_lt_zero, assumption,
end

theorem strict_causal_to_causal (S: operator a b) : strict S → causal S :=
begin
  intros hstrict,
  intros s s' t hpre,
  apply hstrict,
  intros i hlt,
  apply hpre, omega,
end

theorem delay_strict : strict (@delay a _) :=
begin
  intros s s' t hpre,
  simp [causal, delay],
  split_ifs; try { simp <|> assumption },
  apply hpre, omega,
end

theorem causal_strict_strict
  (F: operator a b) (hstrict: strict F)
  (T: operator b c) (hcausal: causal T) :
  strict (λ α, T (F α)) :=
begin
  intros s1 s2 n hagree,
  simp,
  apply hcausal,
  intros i hle,
  apply hstrict,
  intros j hjle,
  apply hagree, omega,
end

theorem strict_causal_strict
  (F: operator a b) (hcausal: causal F)
  (T: operator b c) (hstrict: strict T) :
  strict (λ α, T (F α)) :=
begin
  intros s1 s2 n hagree,
  simp,
  apply hstrict,
  intros i hle,
  apply hcausal,
  intros j hjle,
  apply hagree, omega,
end

/- To construct the fixpoint of F, we first define nth F n, which is F (F ... (F
0)) with (n+1) copies of F. The fixpoint [fix] turns out to be `nth F n n` - the nth
iterate is correct up to time n. -/
private def nth (F: operator a a) : ℕ → stream a
-- We apply F at the bottom so that fix F 0 is given by F rather than being
-- forced to be (0 : a). This seems to generalize the paper, which doesn't
-- consider such operators! (The assumption that everything is time invariant
-- forces operators to have F 0 0 = 0, as proven in [time_invariant_0_0].)
| nat.zero := F 0
| (nat.succ n) := F (nth n).

@[simp]
lemma nth_0 (F: operator a a) : nth F 0 = F 0 := rfl.

@[simp]
lemma nth_succ (F: operator a a) (n: ℕ) : nth F n.succ = F (nth F n) := rfl.

/-- `fix (α, F α)` for a [strict] operator `F` is a fundamental operator that
implements a form of recursion. It is a fixpoint in that `fix F` is a solution
to `α = F(α)`.  When `F` is [strict], this recursion is well-defined: `fix F = F
(fix F)` (see [fix_eq]), and the solution is unique (see [fix_unique]).

Note that in this formalization, `fix F` always produces _some_ stream; however,
if F is not strict, then it need not satisfy `fix F = F (fix F)`.
 -/
def fix (F: operator a a) : stream a :=
  λ t, nth F t t.

@[simp]
lemma fix_0 (F: operator a a) : fix F 0 = F 0 0 := rfl.

lemma strict_zpp_zero (S: operator a b) (hstrict: strict S) (hzpp: S 0 0 = 0) :
  ∀ s, S s 0 = 0 :=
begin
  intros s,
  calc S s 0 = S 0 0 : by {
    apply strict_unique_zero,
    assumption,
  }
        ... = 0 : by apply hzpp,
end

lemma strict_agree_at_next (S: operator a b) (hstrict: strict S) :
  ∀ s s' n, agree_upto n s s' → S s n.succ = S s' n.succ :=
begin
  unfold agree_upto,
  intros s s' n hagree,
  apply hstrict,
  intros i hlt,
  apply hagree, omega,
end

lemma agree_upto_strict_extend (S: operator a b) (hstrict: strict S) (s s': stream a) :
  ∀ n, s ==n== s' → S s ==n.succ== S s' :=
begin
  intros n hagree,
  intros t hle,
  apply hstrict,
  intros i hlt,
  apply hagree, omega,
end

/-
We don't actually use this characterization of strictness, but it might help
build intuition.
-/
lemma strict_as_agree_upto (S: operator a b) :
  strict S ↔ ((∀ s s', S s ==0== S s') ∧ ∀ s s' n, s ==n== s' → S s ==n.succ== S s') :=
begin
  unfold strict,
  split,
  { intros hstrict,
    split,
    { intros s s',
      rw agree_upto_0,
      apply hstrict,
      intros i hlt0,
      exfalso,
      apply (nat.not_lt_zero _ hlt0), },
    { intros s s' n hagree,
      apply agree_upto_strict_extend; assumption, }
  },
  { intros h,
    cases h with h_zpp h_agree_extend,
    intros s s' t hagree,
    have h: (t = 0 ∨ 0 < t) := by omega,
    cases h,
    { subst t, apply h_zpp, omega, },
    { apply (h_agree_extend _ _ (t-1)),
      intros i hle,
      apply hagree, omega, omega,
     }
  }
end

lemma delay_succ_upto (s1 s2: stream a) (n: ℕ) :
  s1 ==n== s2 →
  delay s1 ==n.succ== delay s2 :=
begin
  intros heqn,
  unfold agree_upto,
  intros t,
  intros hle,
  unfold delay,
  rw heqn; omega,
end

private lemma and_wlog2 {p1 p2: Prop} (h2: p2) (h21: p2 → p1) :
  p1 ∧ p2 := ⟨h21 h2, h2⟩ .

private lemma nth_fix_agree_aux (F: operator a a)  (hstrict: strict F) (n: ℕ) :
  nth F n ==n== fix F ∧ fix F ==n== F (fix F) :=
begin
  induction n with n,
  { rw [agree_upto_0, agree_upto_0],
    split,
    { refl, },
    { unfold fix, simp [nth],
      apply strict_unique_zero, assumption, }
  },
  change (nth F n.succ) with (F (nth F n)),
  cases n_ih with h_fix h_unfold,
  have h : F (nth F n) ==n.succ== F (fix F) := by {
    apply (agree_upto_strict_extend _ hstrict),
    exact h_fix,
  },
  apply and_wlog2,
  { apply agree_upto_extend,
    { exact h_unfold, },
    { simp [fix, nth],
      apply (strict_agree_at_next _ hstrict),
      exact h_fix,
     }
  },
  { intros h2,
    -- BUG: prove by reflexivity to instantiate the n argument to agree_upto
    -- (Lean seems to ignore the n in the first relation)
    calc F (nth F n) ==n.succ== F (nth F n) : by apply (agree_refl n.succ)
        ... ==n.succ== F (fix F) : by assumption
        ... ==n.succ== fix F : by { symmetry, assumption },
  },
end

-- The key characterization of fix F.
theorem fix_eq (F: operator a a) (hstrict: strict F) :
  fix F = F (fix F) :=
begin
  funext t,
  have h := nth_fix_agree_aux _ hstrict t,
  cases h with _ h_unfold,
  apply h_unfold, omega,
end

-- We show two solutions α to α = F(α) are equal, from which obviously
-- they are all equal to fix F, which is one such solution from [fix_eq]
--
-- Users will typically want the special case of [fix_unique], which is written
-- in terms of our particular solution [fix].
protected theorem fixpoints_unique (F: operator a a) (hstrict: strict F)
  (α β: stream a) :
  -- α and β are two possible solutions
  α = F α → β = F β →
  α = β :=
begin
  intros hα hβ,
  rw agree_everywhere_eq, intros n,
  induction n with n,
  { rw hα, rw hβ,
    rw agree_upto_0,
    apply strict_unique_zero, assumption, },
  { rw hα, rw hβ,
    apply agree_upto_strict_extend, assumption,
    assumption, }
end

theorem fix_unique (F: operator a a) (hstrict: strict F)
  (α: stream a) (h_fix: α = F α) :
  α = fix F :=
begin
  apply (fixpoints_unique _ hstrict α (fix F)),
  { assumption },
  { apply fix_eq, assumption, }
end

section fix2.

def fix2 (F: operator (stream a) (stream a)) : stream (stream a) :=
  λ n t, nth F t n t.

def causal_nested (Q: operator (stream a) (stream b)) :=
  ∀ (s s': stream (stream a)),
    ∀ n t, ∀ (heq: ∀ n' ≤ n, ∀ t' (hle_t': t' ≤ t), s n' t' = s' n' t'),
    Q s n t = Q s' n t.

def strict2 (Q: operator (stream a) (stream b)) :=
  ∀ (s s': stream (stream a)),
    ∀ n t, ∀ (heq: ∀ n' ≤ n, ∀ t' (hle_t': t' < t), s n' t' = s' n' t'),
    Q s n t = Q s' n t.

theorem strict2_is_causal_nested (Q: operator (stream a) (stream b)) :
  strict2 Q → causal_nested Q :=
begin
  unfold strict2 causal_nested, intros hstrict,
  intros,
  apply hstrict, intros, apply heq; omega,
end

meta def tauto_omega := `[tauto {closer := `[omega]}].

lemma strict2_agree_0 (F: operator (stream a) (stream b)) (hstrict: strict2 F) :
  ∀ s s' n, F s n 0 = F s' n 0 :=
begin
  intros, apply hstrict,
  intros,
  have hcontra : ¬(t' < 0) := by omega,
  contradiction,
end

lemma strict2_eq_0 (F: operator (stream a) (stream b)) (hstrict: strict2 F) :
  ∀ s n, F s n 0 = F 0 n 0 :=
begin
  intros, apply (strict2_agree_0 _ hstrict),
end

def agree_upto2 (t: ℕ) (s1 s2: stream (stream a)) :=
  ∀ n, ∀ t' (hle: t' ≤ t), s1 n t' = s2 n t'.
local notation (name := agree2) s1 ` ==` t `== ` s2:35 := agree_upto2 t s1 s2.

lemma agree_upto2_symm (t: ℕ) (s1 s2: stream (stream a)) :
  s1 ==t== s2 →
  s2 ==t== s1 :=
begin
  unfold agree_upto2, intros,
  finish,
end

lemma agree_upto2_trans (t: ℕ) (s1 s2 s3: stream (stream a)) :
  s1 ==t== s2 →
  s2 ==t== s3 →
  s1 ==t== s3 :=
begin
  unfold agree_upto2, intros,
  transitivity (s2 n t'); finish,
end

lemma agree_upto2_0 (s1 s2: stream (stream a)) :
  s1 ==0== s2 ↔ (∀ n, s1 n 0 = s2 n 0) :=
begin
  unfold agree_upto2,
  split; introv h; clarify,
end

lemma agree_upto2_extend (t: ℕ) (s s': stream (stream a)) :
  s ==t== s' →
  (∀ n, s n t.succ = s' n t.succ) →
  s ==t.succ== s' :=
begin
  intros hagree heqn,
  unfold agree_upto2, intros,
  have ht': (t' ≤ t ∨ t' = t.succ) := by omega,
  cases ht',
  { tauto_omega, },
  subst ht', tauto_omega,
end

lemma agree_upto2_strict_extend (S: operator (stream a) (stream b))
  (hstrict: strict2 S) (s s': stream (stream a)) :
  ∀ t, s ==t== s' →
  S s ==t.succ== S s' :=
begin
  introv hagree,
  unfold agree_upto2, intros,
  apply hstrict,
  intros n' _ t'' _,
  have h1 : t'' ≤ t := by omega,
  apply hagree, finish,
end

lemma strict_agree2_at_next (S: operator (stream a) (stream b)) (hstrict: strict2 S) :
  ∀ s s' t, s ==t== s' → ∀ n, S s n t.succ = S s' n t.succ :=
begin
  unfold agree_upto2,
  intros s s' t hagree n,
  apply hstrict,
  intros, apply hagree, omega,
end

private lemma nth_fix2_agree_aux (F: operator (stream a) (stream a))  (hstrict: strict2 F) (t: ℕ) :
  nth F t ==t== fix2 F ∧ fix2 F ==t== F (fix2 F) :=
begin
  induction t with t,
  { rw [agree_upto2_0, agree_upto2_0],
    split,
    { intros, unfold fix2,
    },
    { intros, unfold fix2, simp,
      apply (strict2_agree_0 _ hstrict),
    },
  },
  change (nth F t.succ) with (F (nth F t)),
  cases t_ih with h_fix h_unfold,
  have h : F (nth F t) ==t.succ== F (fix2 F) := by {
    apply agree_upto2_strict_extend; assumption,
  },
  apply and_wlog2,
  { apply agree_upto2_extend,
    { exact h_unfold, },
    { intros n,
      simp [fix2, nth],
      apply (strict_agree2_at_next _ hstrict),
      exact h_fix,
     }
  },
  { intros h2,
    apply agree_upto2_trans, assumption,
    apply agree_upto2_symm, assumption, },
end

theorem fix2_eq (F: operator (stream a) (stream a)) (hstrict: strict2 F) :
  fix2 F = F (fix2 F) :=
begin
  funext n t,
  have h := nth_fix2_agree_aux _ hstrict t,
  cases h with _ h_unfold,
  apply h_unfold, omega,
end

theorem agree2_everywhere_eq (s1 s2: stream (stream a)) :
  (∀ t, s1 ==t== s2) → s1 = s2 :=
begin
  intros heq,
  funext n t,
  apply (heq t), omega,
end

protected theorem fixpoints2_unique (F: operator (stream a) (stream a)) (hstrict: strict2 F)
  (α β: stream (stream a)) :
  -- α and β are two possible solutions
  α = F α → β = F β →
  α = β :=
begin
  intros hα hβ,
  apply agree2_everywhere_eq, intros n,
  induction n with n,
  { rw hα, rw hβ,
    intros n t' hle,
    have ht : t' = 0 := by omega, subst ht,
    apply strict2_agree_0, assumption, },
  { rw hα, rw hβ,
    apply agree_upto2_strict_extend, assumption,
    assumption, }
end

theorem fix2_unique (F: operator (stream a) (stream a)) (hstrict: strict2 F)
  (α: stream (stream a)) (h_fix: α = F α) :
  α = fix2 F :=
begin
  apply (fixpoints2_unique _ hstrict α (fix2 F)),
  { assumption },
  { apply fix2_eq, assumption, }
end

end fix2.

theorem lifting_delay_strict2 :
  strict2 (↑↑ (@delay a _)) :=
begin
  unfold strict2, introv heq,
  unfold delay, simp,
  split_ifs; try { refl },
  apply heq; omega,
end

@[simp]
theorem causal_nested_const (c: stream (stream b)) :
  causal_nested (λ (x: stream (stream a)), c) :=
begin
  unfold causal_nested, intros, refl,
end

theorem causal_nested_id :
  causal_nested (λ (x: stream (stream a)), x) :=
begin
  unfold causal_nested, intros, apply heq; omega
end

theorem causal_nested_comp
  (Q1: operator (stream b) (stream c))
  (Q2: operator (stream a) (stream b)) :
  causal_nested Q1 → causal_nested Q2 →
  causal_nested (λ s, Q1 (Q2 s)) :=
begin
  intros h1 h2,
  unfold causal_nested, intros,
  apply h1, intros,
  apply h2, intros,
  apply heq; omega,
end

@[simp]
theorem causal_nested_lifting
  (Q: operator a b) :
  causal Q →
  causal_nested (↑↑Q) :=
begin
  intros h,
  unfold causal_nested, intros, simp,
  rw h,
  intros t' hle,
  apply heq; omega,
end

theorem feedback_ckt_body_strict
  (F: operator b b) (hstrict: strict F)
  (T: operator2 a b b) (hcausal: causal (uncurry_op T)) (s: stream a) :
  strict (λ α, T s (F α)) :=
begin
  apply causal_strict_strict,
  { apply hstrict, },
  { apply causal_uncurry_op_fixed, assumption, },
end

lemma feedback_ckt_unfold
  (F: operator b b) (hstrict: strict F)
  (T: operator2 a b b) (hcausal: causal (uncurry_op T)) (s: stream a) :
  fix (λ α, T s (F α)) = T s (F (fix (λ α, T s (F α)))) :=
begin
  apply fix_eq,
  apply feedback_ckt_body_strict; assumption,
end

theorem feedback_ckt_causal
  (F: operator b b) (hstrict: strict F)
  (T: operator2 a b b) (hcausal: causal (uncurry_op T)) :
  causal (λ s, fix (λ α, T s (F α))) :=
begin
  have h := hcausal,
  rw causal_to_agree,
  rw causal2 at h,
  have h2 := causal2_agree _ hcausal,
  introv heq,
  induction n with n,
  { rw [feedback_ckt_unfold _ hstrict _ hcausal s1,
        feedback_ckt_unfold _ hstrict _ hcausal s2],
    rw agree_upto_0,
    apply h, assumption,
    rw agree_upto_0,
    apply strict_unique_zero, assumption,
   },
  { rw [feedback_ckt_unfold _ hstrict _ hcausal s1,
        feedback_ckt_unfold _ hstrict _ hcausal s2],
    apply h2, assumption,
    apply agree_upto_strict_extend, assumption,
    apply n_ih,
    apply agree_upto_weaken1, assumption, },
end

-- #lint only doc_blame simp_nf
