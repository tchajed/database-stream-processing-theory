-- Copyright 2022-2023 VMware, Inc.
-- SPDX-License-Identifier: BSD-2-Clause

import tactic.omega.main
import tactic.linarith
import tactic.split_ifs

/-!

# Streams

Definition of streams and some basic properties. We don't use mathlib streams
because we hardly need any definitions from it.

A stream over a type `a` is a `ℕ → a`.

Defines agree_upto n s s', usually written with the notation s ==n== s', which
says that s and s' agree on all indices in 0..n (inclusive).

-/

universes u v.

/-- A stream is an infinite sequence of elements from `a`.

The indices usually use the metavariable `t`, meant to represent (a discrete
notion of) time.
 -/
def stream (a: Type u) : Type u := ℕ → a.

variable {a : Type u}.

/-- s₁ ==n== s₂ says that streams s₁ and s₂ are equal up to (and including) time
`n`. -/
def agree_upto (n: ℕ) (s₁ s₂: stream a) := ∀ t ≤ n, s₁ t = s₂ t.

notation s ` ==` n `== ` s':35 := agree_upto n s s'.

instance stream_po [partial_order a] : partial_order (stream a) :=
  by { unfold stream, apply_instance }.

@[ext]
lemma stream_le_ext [partial_order a] (s1 s2: stream a) :
  s1 ≤ s2 = (∀ t, s1 t ≤ s2 t) := rfl.

instance stream_zero [has_zero a] : has_zero (stream a) := ⟨λ (_: ℕ), 0⟩.

@[refl]
lemma agree_refl (n: ℕ) : ∀ (s: stream a), s ==n== s :=
begin
  unfold agree_upto,
  intros s i _,
  refl,
end

@[symm]
lemma agree_symm (n: ℕ) : ∀ (s1 s2: stream a), s1 ==n== s2 → s2 ==n== s1 :=
begin
  unfold agree_upto,
  intros s1 s2 h12 i hle,
  rw [h12]; assumption,
end

@[trans]
lemma agree_trans {n: ℕ} : ∀ (s1 s2 s3: stream a), s1 ==n== s2 → s2 ==n== s3 → s1 ==n== s3 :=
begin
  unfold agree_upto,
  intros s1 s2 s3 h12 h23 i hle,
  rw [h12, h23]; assumption,
end

-- TODO: these don't seem to do anything (don't help with rewriting)
instance agree_upto_refl (n: ℕ) : is_refl (stream a) (agree_upto n) := ⟨agree_refl n⟩.
instance agree_upto_symm (n: ℕ) : is_symm (stream a) (agree_upto n) := ⟨agree_symm n⟩.
instance agree_upto_trans (n: ℕ) : is_trans (stream a) (agree_upto n) := ⟨agree_trans⟩.
instance agree_upto_preorder (n: ℕ) : is_preorder (stream a) (agree_upto n) := ⟨⟩.
instance agree_upto_equiv (n: ℕ) : is_equiv (stream a) (agree_upto n) := ⟨⟩.

theorem agree_everywhere_eq (s s': stream a) :
  s = s' ↔ (∀ n, s ==n== s') :=
begin
  split,
  { intros h n,
    rw h, },
  { intros h,
    funext n,
    apply (h n), omega,
   }
end

lemma agree_upto_weaken {s s': stream a} (n n': ℕ) :
  s ==n== s' →
  n' ≤ n →
  s ==n'== s' :=
begin
  intros heq hle,
  intros i hle_i,
  apply heq, omega,
end

lemma agree_upto_weaken1 {s s': stream a} (n: ℕ) :
  s ==n.succ== s' →
  s ==n== s' :=
begin
  intros heq,
  apply (agree_upto_weaken n.succ), assumption, omega,
end

lemma agree_upto_0 (s s': stream a) :
  s ==0== s' ↔ s 0 = s' 0 :=
begin
  unfold agree_upto,
  split,
  { intros hagree,
    apply (hagree 0),
    omega, },
  { intros h0 t hle,
    have h: (t = 0) := by omega,
    cc, }
end

lemma agree_upto_extend (n: nat) (s s': stream a) :
  s ==n== s' → s n.succ = s' n.succ → s ==n.succ== s' :=
begin
  intros hagree heq,
  intros i hle,
  have h: (i ≤ n ∨ i = n.succ) := by omega,
  cases h,
  { apply hagree, assumption, },
  { subst i, assumption, }
end

-- We don't use this theory because everything is based on [agree_upto], but
-- formalize a little bit from the paper.
namespace cutting.

variables [has_zero a].

/-- Construct a stream that matches `s` up to time `t` and is 0 afterward. -/
def cut (s: stream a) (t: ℕ) : stream a :=
  λ i, if (i < t) then s i else 0.

lemma cut_at_0 (s: stream a) : cut s 0 = 0 :=
begin
  ext n,
  unfold cut, rw if_neg, simp,
  omega,
end

lemma cut_0 : cut (0 : stream a) = 0 :=
begin
  ext n,
  unfold cut, split_ifs; refl,
end

theorem cut_cut (s: stream a) (t1 t2: ℕ) :
  cut (cut s t1) t2 = cut s (min t1 t2) :=
begin
  funext i, simp [cut],
  split_ifs; try { simp },
  tauto,
  { exfalso, linarith, },
  { exfalso, linarith, },
end

theorem cut_comm (s: stream a) (t1 t2: ℕ) :
  cut (cut s t1) t2 = cut (cut s t2) t1 :=
begin
  rw [cut_cut, cut_cut],
  rw min_comm,
end

theorem cut_idem (s: stream a) (t: ℕ) :
  cut (cut s t) t = cut s t :=
begin
  rw cut_cut, simp,
end

/-- Relate [agree_upto] to equality on [cut]. -/
theorem agree_upto_cut (s1 s2: stream a) (n: ℕ) :
  s1 ==n== s2 ↔ cut s1 n.succ = cut s2 n.succ :=
begin
  split,
  { intros heq,
    funext t, simp [cut],
    split_ifs; try { refl },
    apply heq, omega, },
  { intros heq,
    intros t hle, simp [cut] at heq,
    have h := congr_fun heq t, simp at h,
    split_ifs at *,
    { assumption, },
    { exfalso, apply h_1, omega, },
  },
end

lemma cut_agree_succ (s1 s2: stream a) (t: ℕ) :
  cut s1 t = cut s2 t →
  s1 t = s2 t →
  cut s1 t.succ = cut s2 t.succ :=
begin
  cases t,
  { intros _hcut heq,
    ext n,
    unfold cut, split_ifs, swap, refl,
    have heq : n = 0 := by omega,
    subst n, assumption,
  },
  repeat { rw<- agree_upto_cut },
  apply agree_upto_extend,
end

theorem agree_with_cut (s: stream a) (n: ℕ) :
  s ==n== cut s n.succ :=
begin
  rw [agree_upto_cut, cut_idem],
end

end cutting.

-- #lint only doc_blame simp_nf
