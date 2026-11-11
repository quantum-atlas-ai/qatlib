/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel

/-!
# Corollary 5.6 — `QIP = QMAM(1, 2^{−r})`

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Corollary 5.6 (page 26).

Statement (verbatim): `QIP = QMAM(1, 2^{−r})`, i.e. the union of
`QMAM(1, 2^{−r})` over `r ∈ poly` equals `QIP`.

The inclusion `QMAM(1, 2^{−r}) ⊆ QIP` is immediate (a quantum AM game is a
quantum interactive proof).  The reverse `QIP ⊆ QMAM(1, 2^{−r})` is
Theorem 5.4 (`1/2 + 2^{−r}` soundness) followed by error reduction for `QMAM`,
driving the soundness to `2^{−r}`.

## What is formalised here

The class-level structural engine of the corollary: `QMAM` is monotone in its
soundness bound (`qmam_mono`), because relaxing the soundness constant only
weakens the pointwise verification inequality.  Consequently, any `QMAM` family
with soundness `2^{−r}` also lies in `QMAM` with soundness `1/2 + 2^{−r}`.

The inclusion `QMAM ⊆ QIP` and the QIP→QMAM error reduction are not formalised:
the `InQip` model is a length-indexed scalar `maxAccept` family with no explicit
strategy, so it cannot be constructed from an `InQmam` witness, and `QMAM`
amplification is absent from the shared library.  See the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Qmam

open Qatlib.Papers.ArthurMerlin05.StaticGames

/-- `QMAM` is monotone in its completeness and soundness constants: lowering the
required completeness `a` and raising the allowed soundness `b` preserves
membership.  Proved directly from the pointwise acceptance inequalities in
`InQmam`. -/
theorem qmam_mono {m1 m2 s : ℕ → ℕ} {a a' b b' : ℕ → ℝ} {L : List Bool → Prop}
    (ha : ∀ n, a' n ≤ a n) (hb : ∀ n, b n ≤ b' n)
    (h : InQmam m1 m2 s a b L) : InQmam m1 m2 s a' b' L := by
  obtain ⟨A, hcomp, hsound⟩ := h
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    obtain ⟨l, ψ, U, hψ, hU, hacc⟩ := hcomp x hx
    exact ⟨l, ψ, U, hψ, hU, le_trans (ha x.length) hacc⟩
  · intro x hx l ψ U hψ hU
    exact le_trans (hsound x hx l ψ U hψ hU) (hb x.length)

/-- Corollary 5.6 (page 26), soundness-weakening direction: `QMAM(1, 2^{−r})` is
contained in `QMAM(1, 1/2 + 2^{−r})`, since `2^{−r} ≤ 1/2 + 2^{−r}`.  This is
the class-level bookkeeping that Theorem 5.4's `1/2 + 2^{−r}` bound feeds into. -/
theorem corollary_5_6 {L : List Bool → Prop} {r : ℕ → ℕ}
    (hL : InQmamPoly (fun _ => 1) (fun n => (2 : ℝ) ^ (-(r n) : ℤ)) L) :
    InQmamPoly (fun _ => 1) (fun n => (1 / 2 : ℝ) + (2 : ℝ) ^ (-(r n) : ℤ)) L := by
  obtain ⟨m1, m2, s, hm⟩ := hL
  exact ⟨m1, m2, s, qmam_mono (fun _ => le_rfl) (fun n => by linarith) hm⟩

end Qatlib.Papers.ArthurMerlin05.StaticGames.Qmam
