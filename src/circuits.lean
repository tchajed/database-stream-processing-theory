-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import .operators
import .linear
import .stream_elim
import .incremental

import tactic.induction

namespace ckt.

section ckts.

parameter (Func: ∀ (a b: Type) [add_comm_group a] [add_comm_group b], Type).
parameter (Func_denote: ∀ {a b: Type} [add_comm_group a] [add_comm_group b], Func a b → (a → b)).

inductive ckt : ∀ (a b: Type) [add_comm_group a] [add_comm_group b], Type 1
| delay {a: Type} [add_comm_group a]
  : ckt a a
| derivative {a: Type} [add_comm_group a]
  : ckt a a
| integral {a: Type} [add_comm_group a]
  : ckt a a
| incremental {a b: Type} [add_comm_group a] [add_comm_group b]
  (f: ckt a b) : ckt a b
| lifting {a b: Type} [add_comm_group a] [add_comm_group b]
  (f: Func a b) : ckt a b
-- | ckt_lift {a b: Type} [add_comm_group a] [add_comm_group b]
--   (f: ckt a b) : ckt (stream a) (stream b)
| seq {a b c: Type} [add_comm_group a] [add_comm_group b] [add_comm_group c]
  (f1: ckt a b) (f2: ckt b c) : ckt a c
| par {a₁ b₁ a₂ b₂: Type}
  [add_comm_group a₁] [add_comm_group a₂] [add_comm_group b₁] [add_comm_group b₂]
  (f1: ckt a₁ b₁) (f2: ckt a₂ b₂) : ckt (a₁ × a₂) (b₁ × b₂)
| feedback {a b: Type} [add_comm_group a] [add_comm_group b]
  (F: ckt (a × b) b) : ckt a b
-- | intro {a: Type} [add_comm_group a]
--   : ckt a (stream a)
-- | elim {a: Type} [add_comm_group a]
--   : ckt (stream a) a
.

local notation f1 ` ~~> ` f2:25 := ckt _ f1 f2.

variables {a b c d: Type} [add_comm_group a] [add_comm_group b] [add_comm_group c] [add_comm_group d].

section denote.

include Func_denote.

def denote (c: ckt a b) : (stream a → stream b) :=
begin
  -- unfreezingI { revert_deps a b, revert a b, },
  -- apply (@ckt.rec (λ {a b: Type} [_i1: add_comm_group a] [_i2: add_comm_group b] (f: @ckt a b _i1 _i2), (stream a → stream b))); dsimp; introv; resetI,

  -- resetI resets the (typeclass) instance cache, so that the new local
  -- hypotheses can be used for instance search
  -- unfortunately we need this unfreezingI thing and induction rather than
  -- mathlib induction' because of its improper handling of dependencies
  unfreezingI { induction c } ,
  { resetI, apply delay, },
  { resetI, apply D, },
  { resetI, apply I, },
  { resetI, apply c_ih^Δ, },
  { resetI, apply ↑↑(Func_denote c_f), },
  { -- seq
    exact (λ a, c_ih_f2 (c_ih_f1 a)), },
  { -- par
     resetI,
     apply (uncurry_op (λ x1 x2, sprod (c_ih_f1 x1, c_ih_f2 x2))), },
  { -- feedback
    resetI,
    intros s,
    apply fix (λ α, c_ih (sprod (s, z⁻¹ α))),
  },
  -- { resetI, exact ↑↑δ0, },
  -- { resetI, exact ↑↑stream_elim, }
end
end denote.

def equiv (f1 f2: ckt a b) := denote f1 = denote f2.

local infix ` === `:50 := equiv.

@[refl]
lemma equiv_refl (f: ckt a b) : f === f :=
  by { unfold equiv }.

@[symm]
lemma equiv_symm (f1 f2: ckt a b) : f1 === f2 → f2 === f1 :=
  by { unfold equiv, cc, }.

@[trans]
lemma equiv_trans (f1 f2 f3: ckt a b) : f1 === f2 → f2 === f3 → f1 === f3 :=
  by { unfold equiv, cc, }.

@[simp]
lemma denote_seq (f1: ckt a b) (f2: ckt b c) :
  denote (ckt.seq f1 f2) = λ x, denote f2 (denote f1 x) := rfl.

@[simp]
lemma denote_par
  (f1: ckt a b) (f2: ckt c d) :
  denote (ckt.par f1 f2) = uncurry_op (λ x1 x2, sprod (denote f1 x1, denote f2 x2))
  := rfl.

@[simp]
lemma denote_delay :
  denote (@ckt.delay a _) = delay := rfl.

@[simp]
lemma denote_derivative :
  denote (@ckt.derivative a _) = D := rfl.

@[simp]
lemma denote_incremental (f: ckt a b) :
  denote (ckt.incremental f) = (denote f)^Δ := rfl.

@[simp]
lemma denote_integral :
  denote (@ckt.integral a _) = I := rfl.

@[simp]
lemma denote_lifting (f: Func a b) :
  denote (ckt.lifting f) = ↑↑(Func_denote f) := rfl.

-- @[simp]
-- lemma denote_ckt_lift (f: ckt a b) :
--   denote (ckt.ckt_lift f) = ↑↑(denote f) := rfl.

@[simp]
lemma denote_feedback (F: ckt (a × b) b) :
  denote (ckt.feedback F) = λ s, fix (λ α, denote F (sprod (s, z⁻¹ α))) := rfl.

-- @[simp]
-- lemma denote_intro :
--   denote (@ckt.intro a _) = ↑↑δ0 := rfl.
--
-- @[simp]
-- lemma stream_elim_intro :
--   denote (@ckt.elim a _) = ↑↑∫ := rfl.

local notation x ` >>> `:55 y:55 := ckt.seq x y.

-- These definitions rely on being able to lift a few fixed functions; they
-- still make sense, but with relatively complicated assumptions that these
-- functions are available in [Func] with the appropriate meaning according to
-- [Func_denote].
/-
def lifting2 (f: a → b → c) : ckt (a × b) c :=
  ckt.lifting (λ xy, f xy.1 xy.2).

def derivative : ckt a a :=
  ckt.lifting (λ a, (a, a)) >>> ckt.par (ckt.lifting id) ckt.delay >>>
  ckt.lifting2 (λ x y, x - y).

theorem derivative_denote :
  @derivative a _ === ckt.derivative :=
begin
  unfold derivative,
  funext s, simp,
  unfold lifting2, simp,
  funext t, simp,
  refl,
end

def integral : ckt a a :=
  ckt.feedback (ckt.lifting2 (λ x y, x + y)).

theorem integral_denote :
  @integral a _ === ckt.integral :=
begin
  unfold integral,
  funext s, simp,
  unfold lifting2, simp,
  unfold I feedback, simp,
  refl,
end
-/

def ckt_causal (f: ckt a b) : causal (denote f) :=
begin
  unfreezingI { induction f }; resetI; try { simp },
  { apply delay_causal, },
  { apply causal_incremental, assumption, },
  { apply causal_comp_causal; assumption, },
  { rw causal2,
    introv heq1 heq2,
    simp,
    split,
    { apply f_ih_f1, assumption, },
    { apply f_ih_f2, assumption, },
  },
  { apply (feedback_ckt_causal delay _ (λ (s: stream f_a) (α: stream f_b), ckt.denote f_F (sprod (s, α)))),
    rw causal2,
    introv heq1 heq2,
    apply f_ih,
    intros m hle, simp,
    split, { apply heq1, omega, }, { apply heq2, omega, },
    apply delay_strict,
  },
end

def is_strict (f: ckt a b) : {b:bool | b → strict (denote f)} :=
begin
  unfreezingI { induction f }; simp,
  { use true, simp, apply delay_strict, },
  { -- derivative
    use false, },
  { -- integral
    use false, },
  { -- incremental
    cases f_ih with b hstrict, simp at *,
    use b, intros hb,
    unfold incremental,
    apply causal_strict_strict, swap, simp,
    apply strict_causal_strict, simp,
    tauto,
  },
  { -- lifting
    use false, },
  { -- seq (composition)
    cases f_ih_f1 with b1 hstrict1,
    cases f_ih_f2 with b2 hstrict2, simp at *,
    use (b1 || b2), simp,
    intros h, cases h; resetI,
    apply causal_strict_strict, tauto, apply ckt_causal,
    apply strict_causal_strict, apply ckt_causal, tauto,
   },
  { -- par
    cases f_ih_f1 with b1 hstrict1, cases f_ih_f2 with b2 hstrict2,
    use (b1 && b2), simp at *, intros h1 h2,
    intros s1 s2 n heq,
    unfold uncurry_op sprod, simp,
    split,
    { apply (hstrict1 h1), intros, simp, rw heq, omega, },
    { apply (hstrict2 h2), intros, simp, rw heq, omega, },
   },
   { use false, },
end

/-
def incrementalize (f: ckt a b) : ckt a b :=
  ckt.integral >>> f >>> ckt.derivative.

theorem incrementalize_ok (f: ckt a b) :
 denote (incrementalize f) = (denote f)^Δ :=
begin
  unfold incrementalize, simp,
  funext s, rw incremental_unfold,
end
-/

theorem seq_assoc (f1: ckt a b) (f2: ckt b c) (f3: ckt c d) :
  f1 >>> f2 >>> f3 === f1 >>> (f2 >>> f3) :=
begin
  unfold equiv, simp,
end

section recursive_opt.

variables (opt: Π {a b: Type} [inst1: add_comm_group a] [inst2: add_comm_group b],
      @ckt a b inst1 inst2 → option (@ckt a b inst1 inst2)).

include opt
def recursive_opt : ckt a b → ckt a b :=
begin
  intros f, unfreezingI { induction f },
  { apply (opt $ ckt.delay).get_or_else ckt.delay, },
  { apply (opt $ ckt.derivative).get_or_else ckt.derivative, },
  { apply (opt $ ckt.integral).get_or_else ckt.integral, },
  { apply (opt $ ckt.incremental f_f).get_or_else (ckt.incremental f_ih), },
  { resetI, apply (opt $ ckt.lifting f_f).get_or_else (ckt.lifting f_f), },
  { resetI, apply (opt $ ckt.seq f_f1 f_f2).get_or_else (ckt.seq f_ih_f1 f_ih_f2), },
  { resetI, apply (opt $ ckt.par f_f1 f_f2).get_or_else (ckt.par f_ih_f1 f_ih_f2), },
  { resetI, apply (opt $ ckt.feedback f_F).get_or_else (ckt.feedback f_ih), },
  -- { apply (opt $ ckt.intro).get_or_else ckt.intro, },
  -- { apply (opt $ ckt.elim).get_or_else ckt.elim, },
end

@[simp]
lemma recursive_opt_seq (f1: ckt a b) (f2: ckt b c) :
  recursive_opt @opt (ckt.seq f1 f2) =
    (opt $ ckt.seq f1 f2).get_or_else (ckt.seq (recursive_opt @opt f1) (recursive_opt @opt f2)) := rfl.

@[simp]
lemma recursive_opt_par (f1: ckt a b) (f2: ckt c d) :
  recursive_opt @opt (ckt.par f1 f2) =
    (opt $ ckt.par f1 f2).get_or_else (ckt.par (recursive_opt @opt f1) (recursive_opt @opt f2)) := rfl.

@[simp]
lemma recursive_opt_feedback (f: ckt (a × b) b) :
  recursive_opt @opt (ckt.feedback f) =
    (opt $ ckt.feedback f).get_or_else (ckt.feedback (recursive_opt @opt f)) := rfl.

@[simp]
lemma recursive_opt_incremental (f: ckt a b) :
  recursive_opt @opt (ckt.incremental f) =
    (opt $ ckt.incremental f).get_or_else (ckt.incremental (recursive_opt @opt f)) := rfl.

variables (h_opt: ∀ {a b: Type} [inst1: add_comm_group a] [inst2: add_comm_group b]
  (f1 f2: @ckt.ckt a b inst1 inst2),
    @opt a b inst1 inst2 f1 = some f2 ->
    @ckt.equiv a b inst1 inst2 f1 f2).

include h_opt

lemma opt_or_else_ok (f1 f2: ckt a b) :
  f2 === f1 →
  (opt f1).get_or_else f2 === f1 :=
begin
  intros heq,
  destruct (opt f1); introv hopt; rw hopt; simp,
  assumption,
  symmetry, apply h_opt, assumption,
end

theorem recursive_opt_ok :
  ∀ (f: ckt a b), recursive_opt @opt f === f :=
begin
  intros f, unfreezingI { induction f },
  { apply (opt_or_else_ok _ @Func_denote _ @h_opt), refl, },
  { apply (opt_or_else_ok _ @Func_denote _ @h_opt), refl, },
  { apply (opt_or_else_ok _ @Func_denote _ @h_opt), refl, },
  { simp, apply (opt_or_else_ok _ @Func_denote _ @h_opt),
    unfold equiv at f_ih |-,
    simp, dsimp, rw f_ih, },
  { apply (opt_or_else_ok _ @Func_denote _ @h_opt), refl, },
  { simp, apply (opt_or_else_ok _ @Func_denote _ @h_opt),
    unfold equiv at f_ih_f1 f_ih_f2 |-,
    simp, dsimp, rw [f_ih_f2, f_ih_f1],
  },
  { simp, apply (opt_or_else_ok _ @Func_denote _ @h_opt),
    unfold equiv at f_ih_f1 f_ih_f2 |-,
    simp, dsimp, rw [f_ih_f1, f_ih_f2],
  },
  { simp, apply (opt_or_else_ok _ @Func_denote _ @h_opt),
    unfold equiv at f_ih |-,
    simp, dsimp, rw f_ih,
  },
end

end recursive_opt.

section incrementalize.

parameters (is_linear: ∀ {a b: Type} [i1: add_comm_group a] [i2: add_comm_group b]
                      (f: @Func a b i1 i2), bool)
          (is_linear_ok: ∀ {a b: Type} [i1: add_comm_group a] [i2: add_comm_group b]
            (f: @Func a b i1 i2), @is_linear _ _ i1 i2 f →
            ∀ (x y: a),
            -- use tactic mode to run resetI; something is weird about
            -- elaboration here where instances aren't picked up
            (by { resetI,
            exact Func_denote f (x + y) = Func_denote f x + Func_denote f y })).

include is_linear.

-- returns an optimized version of c^Δ
def incrementalize (c: ckt a b) : ckt a b :=
begin
  unfreezingI { induction c },
  { exact ckt.delay, },
  { exact ckt.derivative, },
  { exact ckt.integral, },
  { apply ckt.incremental c_ih, },
  { apply (if is_linear c_f
          then ckt.lifting c_f
          else ckt.incremental (ckt.lifting c_f)), },
  { apply ckt.seq c_ih_f1 c_ih_f2, },
  { apply ckt.par c_ih_f1 c_ih_f2, },
  { apply ckt.feedback c_ih, },
end

@[simp]
lemma incrementalize_incremental (c: ckt a b) :
  incrementalize (ckt.incremental c) = ckt.incremental (incrementalize c) := rfl.

@[simp]
lemma incrementalize_lifting (f: Func a b) :
  incrementalize (ckt.lifting f) =
  if is_linear f then
  ckt.lifting f else ckt.incremental (ckt.lifting f) := rfl.

@[simp]
lemma incrementalize_seq (f1: ckt a b) (f2: ckt b c) :
  incrementalize (f1 >>> f2) = incrementalize f1 >>> incrementalize f2 := rfl.

@[simp]
lemma incrementalize_par (f1: ckt a b) (f2: ckt c d) :
  incrementalize (ckt.par f1 f2) = ckt.par (incrementalize f1) (incrementalize f2) := rfl.

@[simp]
lemma incrementalize_feedback (f: ckt (a × b) b) :
  incrementalize (ckt.feedback f) = ckt.feedback (incrementalize f) := rfl.

include is_linear_ok.

theorem incrementalize_ok (f: ckt a b) :
 denote (incrementalize f) = (denote f)^Δ :=
begin
  unfreezingI { induction f, }; try { unfold incrementalize; simp; done },
  { simp, rw f_ih, },
  { simp, split_ifs,
    { simp, rw lti_incremental,
      apply lifting_lti,
      intros, apply is_linear_ok, assumption,
    },
    { simp, },
  },
  { simp, rw [f_ih_f1, f_ih_f2],
    funext s,
    rw (incremental_comp
      (denote _ @Func_denote f_f2) (denote _ @Func_denote f_f1)), },
  { simp, funext s,
    rw [f_ih_f1, f_ih_f2],
    unfold uncurry_op,
    unfold incremental,
    rw [derivative_sprod, integral_fst_comm, integral_snd_comm],
  },
  { simp,
    rw cycle_incremental (λ s α, denote _ @Func_denote f_F (sprod (s, α))),
    { dsimp,
      rw f_ih,
      funext s,
      congr' 1, funext α,
      rw incremental_sprod, },
    { dsimp,
      rw causal2, introv heq1 heq2,
      apply ckt_causal,
      intros t hle, simp,
      rw [heq1, heq2], finish, assumption, assumption,
    },
  },
end

end incrementalize.

end ckts.
end ckt.
