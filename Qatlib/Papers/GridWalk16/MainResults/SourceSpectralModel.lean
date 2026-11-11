/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# GridWalk16 — spectral source model

Fixed paper: Peter Høyer and Mojtaba Komeili, *Efficient quantum walk on the grid
with multiple marked elements*, **arXiv:1612.08958v1** (28 Dec 2016), STACS 2017.
Source read from the pinned PDF/text (`assets/1612.08958.pdf`); the metadata
`arxiv_version_used` field is null, so version v1 is recorded explicitly here.

This module records the paper's spectral vocabulary (§2, pp. 4–7) in the exact
form used in the proofs of Theorem 2, Corollary 3 and Lemma 6:

* `ε_S` — the stationary mass of a subset (p. 5);
* the normalised projection `|S_π⟩` and its eigenbasis amplitudes
  `⟨λ_k | S_π⟩` (p. 5);
* the escape time `E(P,S) = ∑_k |⟨λ_k|S_π⟩|² / (1−λ_k)` (Definition 5, Eq. (3), p. 7);
* the extended hitting time through Theorem 4 ([15]),
  `HT⁺(P,M) = Θ((1/ε_M)·E(P,M))` (Eq. (2), p. 6).  The paper drops the Θ-factor
  ("omitting asymptotic tight factors", p. 8), so the model keeps the exact
  representative `(1/ε_M)·E(P,M)`.

The non-principal eigenmodes are indexed by an abstract finite type `ι`; the
spectral gap is stored as `gap k = 1 − λ_k > 0`.  All quantities are genuine
finite sums, so the inequalities of the paper are proved against the actual
sums rather than placeholder constants.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.GridWalk16.MainResults

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]

/-- Stationary mass of a subset, `ε_S = ∑_{x∈S} π_x` (paper §2, p. 5). -/
def stationaryMass (π : X → ℝ) (S : Finset X) : ℝ := ∑ x ∈ S, π x

/-- Spectral data of a reversible ergodic walk: positive stationary masses, the
non-principal eigenmodes (`gap k = 1 − λ_k > 0`), and the real eigenbasis
amplitudes `coeff x k = ⟨λ_k|x⟩` (paper §2, pp. 4–7). -/
structure SpectralWalk (X ι : Type*) [Fintype X] [Fintype ι] where
  pi : X → ℝ
  pi_pos : ∀ x, 0 < pi x
  gap : ι → ℝ
  gap_pos : ∀ k, 0 < gap k
  coeff : X → ι → ℝ

namespace SpectralWalk

variable (W : SpectralWalk X ι)

/-- `ε_S`, the stationary probability that the walk is in a state of `S`. -/
def eps (S : Finset X) : ℝ := ∑ x ∈ S, W.pi x

/-- `ε_S` is positive for a nonempty `S`. -/
lemma eps_pos {S : Finset X} (hS : S.Nonempty) : 0 < W.eps S := by
  unfold eps
  exact Finset.sum_pos (fun x _ => W.pi_pos x) hS

/-- `ε_S` is nonnegative. -/
lemma eps_nonneg (S : Finset X) : 0 ≤ W.eps S := by
  unfold eps
  exact Finset.sum_nonneg fun x _ => (W.pi_pos x).le

/-- `ε` is additive on disjoint sets. -/
lemma eps_union {S T : Finset X} (h : Disjoint S T) :
    W.eps (S ∪ T) = W.eps S + W.eps T := by
  unfold eps
  rw [Finset.sum_union h]

/-- Spectral amplitude `⟨λ_k|S_π⟩ = (√ε_S)⁻¹ ∑_{x∈S} √π_x·⟨λ_k|x⟩`
(paper p. 5, Definition 5). -/
def proj (S : Finset X) (k : ι) : ℝ :=
  (Real.sqrt (W.eps S))⁻¹ * ∑ x ∈ S, Real.sqrt (W.pi x) * W.coeff x k

/-- Escape time `E(P,S) = ∑_k |⟨λ_k|S_π⟩|² / (1−λ_k)` (Definition 5, Eq. (3), p. 7). -/
def escape (S : Finset X) : ℝ := ∑ k, (W.proj S k)^2 / W.gap k

/-- Extended hitting time, via Theorem 4 ([15]) in the exact form
`HT⁺(P,M) = (1/ε_M)·E(P,M)` (paper Eq. (2), p. 6). -/
def extendedHitting (S : Finset X) : ℝ := (W.eps S)⁻¹ * W.escape S

/-- The escape time is a sum of nonnegative squared amplitudes over positive gaps. -/
lemma escape_nonneg (S : Finset X) : 0 ≤ W.escape S := by
  unfold escape
  exact Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (W.gap_pos k).le

/-- The escape time of the empty set vanishes (the projection `|π⟩` onto `∅` is the
zero vector, paper p. 5: "Let `|S_π⟩` be the vector of length zero if `S` is empty"). -/
lemma escape_empty : W.escape (∅ : Finset X) = 0 := by
  unfold escape proj
  simp

/-- The extended hitting time is nonnegative (product of `(ε_M)⁻¹ > 0` with a
nonnegative escape time). -/
lemma extendedHitting_nonneg (S : Finset X) : 0 ≤ W.extendedHitting S := by
  unfold extendedHitting
  exact mul_nonneg (inv_nonneg.mpr (W.eps_nonneg S)) (W.escape_nonneg S)

end SpectralWalk

end Qatlib.Papers.GridWalk16.MainResults
