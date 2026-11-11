/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic
import Qatlib.Papers.QDecoding25.MainResults.DecodingModel
import Qatlib.Papers.QDecoding25.MainResults.TypicalEntropy

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# The PGM layer and the analytic core of §3 (arXiv:2509.24796v2)

This module states the paper's measurement-theoretic and probabilistic core:

* Lemma 3 (p. 15) — the quantum Fourier transform of the codeword state;
* Proposition 5 (p. 16) — the PGM success probability `q^{-k}(∑_s Z_s)²`;
* Lemma 4 (p. 19) — second moment `E_G[Z̃_s(ε)²] ≥ (1-δ)/q^k`;
* Lemma 5 (p. 20) — variance bound for `Z̃_s(ε)²`;
* Lemmas 6 and 7 (pp. 21–22) — concentration of `Z̃_s(ε)²` and of the
  typical-set mass, with probability `1 - negl(i)`;
* Lemma 8 (p. 23) — normalisation of the truncated states and their inner
  product with the untruncated ones;
* Lemma 9 (p. 23) — at most `K/N` success probability for `N` states in
  dimension `K`;
* Lemma 10 (p. 24) — perturbation of the success probability by the trace
  distance (`p ≤ p̃ + δ`);
* Lemma 11 (p. 26) — rank-metric tail `O(q^{-b²ε²})`;
* Lemma 12 (p. 32) — lower concentration of `X` over the code ensemble;
* Lemma 13 (p. 33) — concentration of the ratio `Y/X`;
* Proposition 9 (p. 34) — with probability `1 - negl`, the dual code contains
  no nonzero low-weight codeword.

Source: arXiv:2509.24796v2 (4 Feb 2026); page numbers refer to that version.
-/

namespace Qatlib.Papers.QDecoding25.MainResults

open scoped BigOperators ComplexOrder
open Filter Topology Matrix

/-! ## Inner products on `ℂ^n` -/

/-- The Hermitian inner product `⟨u,v⟩ = ∑_i conj(u_i) v_i` on `ℂ^n`. -/
noncomputable def ip {d : ℕ} (u v : Fin d → ℂ) : ℂ :=
  ∑ i, star (u i) * v i

/-- The squared norm `‖u‖₂² = ∑_i |u_i|²`. -/
noncomputable def nmSq {d : ℕ} (u : Fin d → ℂ) : ℝ :=
  ∑ i, Complex.normSq (u i)

/-! ## Lemma 3: the QFT of a codeword state (p. 15, eq. (7)) -/

/-! ## Proposition 5: the PGM success probability (p. 16) -/

/-- **Proposition 5 (p. 16), PGM success probability.**  The pretty good
measurement succeeds in recovering `c` with probability
`P_PGM = q^{-k_i} (∑_{s ∈ F_q^{n_i}/C^⊥} Z_s)²`, where `Z_s = ‖|W_s⟩‖` and
`q^{k_i}` is the number of cosets.  Here the right-hand side is written with
the quotient cardinality `|quot| = q^{k_i}` (`QDPFamily.quot_card`). -/
theorem proposition5_pgm_success {F : Type*} [Field F] [Fintype F]
    (fam : QDPFamily F) (i : ℕ) (g : fam.Gen i) :
    fam.pgmSuccess i g =
      (1 / (Fintype.card F : ℝ) ^ fam.k i) *
        (∑ s ∈ fam.quots i, fam.Zs i g (fam.rep i s)) ^ 2 := by
  unfold QDPFamily.pgmSuccess
  have hcard : ((fam.quots i).card : ℝ) = (Fintype.card F : ℝ) ^ fam.k i := by
    rw [fam.quot_card i, Nat.cast_pow]
  rw [hcard]

/-! ## Lemmas 4 and 5: first and second moments of `Z̃_s(ε)²` (pp. 19–20) -/

/-! ## Lemmas 6 and 7: concentration (pp. 21–22) -/

/-- The typical-set mass carried by the coset `s + C^⊥` with `s` removed,
the statistic of Lemma 7 (p. 22). -/
noncomputable def typicalCosetSum {F : Type*} [Field F] [Fintype F]
    (fam : QDPFamily F) (j : ℕ) (ε : ℝ) (g : fam.Gen j)
    (s : FVec F (fam.nice.n j)) : ℝ := by
  classical
  exact ∑ y ∈ (fam.nice.typicalSet j ε).filter
    (fun y => y ∈ fam.coset j g s ∧ y ≠ s), fam.mass j y

/-! ## Lemma 8: truncated states (p. 23) -/

/-- The state `|ψ_c⟩ = ∑_y f̂(y) χ_c(y) |y⟩` in coordinates, with `χ_c(y)` a
character of modulus one along each coordinate. -/
noncomputable def psiState {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (f χc : FVec F n → ℂ) : FVec F n → ℂ :=
  fun y => f y * χc y

/-- The truncated state `|ψ̃_c⟩ = (1-δ)^{-1/2} Π_T |ψ_c⟩` of Lemma 8 (p. 23). -/
noncomputable def truncState {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (f χc : FVec F n → ℂ) (T : Finset (FVec F n)) (δ : ℝ) : FVec F n → ℂ := by
  classical
  exact fun y => if y ∈ T then (↑((Real.sqrt (1 - δ))⁻¹) : ℂ) * (f y * χc y) else 0

/-! ## Lemmas 9 and 10: dimension counting and perturbation (pp. 23–24) -/

/-! ## Lemma 11: rank-metric tail (p. 26) -/

/-- `BigOg f g` is the paper's `f = O(g)` for nonnegative sequences indexed by
the block length `b`, with an absolute constant independent of `b`, `a` and
`q` (the convention used in §3.4). -/
def BigOg (f g : ℕ → ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ b, f b ≤ C * g b

/-! ## Lemmas 12, 13 and Proposition 9: dual-codeword sampling (§4.2) -/

end Qatlib.Papers.QDecoding25.MainResults
