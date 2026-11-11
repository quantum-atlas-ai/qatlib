/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceBeurlingWeight

/-!
# Coefficient products, truncations and the operator model `Y_w`

Fixed source: arXiv:2603.02021v1 (2026-03-02), §3.2 p.8 and the proof of Lemma 3,
p.9.  This file provides the coefficient-level vocabulary used to state and prove
the triangularity statements (3.3)–(3.4) of Lemma 3:

* `convCoeff c d n` — the `n`-th Fourier coefficient of the product of two `A_w`
  functions whose coefficient sequences are `c` and `d` (the convolution
  `∑_k c_k d_{n-k}`; the paper's `P_±` acts on the Fourier side, p.9);
* `SupportedLE c n` / `SupportedGE c` — Fourier support in `(-∞, n]` / in
  `[0, +∞)`, the two support conditions used on p.9 (`1/a` supported on
  `(-∞, 0]`, `a*` supported on `[0, +∞)`);
* `convCoeff_eq_zero_of_supported_le`, `convCoeff_eq_zero_of_supported_ge` —
  the two elementary support lemmas underlying `P₊(1/a)P₋ = 0` and
  `P_{>n}(1/a)P_{≤n} = 0` (p.9);
* `YCoeff`, `Ynorm`, `PnOp`, `RtildeOp`, `Cmul` — the Banach space
  `Y_w = A_w ⊕ A_w` of p.8, its norm, the projections
  `Pₙ = diag(P₊, P_{≤n})`, `R̃ₙ = diag(0, P_{>n})` and the operator `C` of
  multiplication by `[[1, b*/a], [-b/a*, 1]]`, all at coefficient level.
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

noncomputable section

/-- The `n`-th coefficient of the product of two `A_w` functions with coefficient
sequences `c` and `d`: the convolution `∑_k c_k d_{n-k}` (Fourier-side product,
cf. the projection computations of p.9). -/
def convCoeff (c d : ℤ → ℂ) (n : ℤ) : ℂ := ∑' k : ℤ, c k * d (n - k)

/-- Fourier support of `c` is contained in `(-∞, n]`, i.e. `P_{>n} c = 0`. -/
def SupportedLE (c : ℤ → ℂ) (n : ℤ) : Prop := ∀ k : ℤ, n < k → c k = 0

/-- Fourier support of `c` is contained in `[0, +∞)`, i.e. `P₋ c = 0`. -/
def SupportedGE (c : ℤ → ℂ) : Prop := ∀ k : ℤ, k < 0 → c k = 0

/-- Fourier support of `c` is contained in `(n, +∞)`, i.e. `P_{≤n} c = 0`. -/
def SupportedGT (c : ℤ → ℂ) (n : ℤ) : Prop := ∀ k : ℤ, k ≤ n → c k = 0

/-- If `c` is supported in `(-∞, 0]` and `d` in `(-∞, n]`, then the coefficient
convolution `c * d` is supported in `(-∞, n]`.  This is the support computation
behind `P₊(1/a)P₋ = 0` and `P_{>n}(1/a)P_{≤n} = 0` in the proof of Lemma 3 (p.9). -/
theorem convCoeff_eq_zero_of_supported_le {c d : ℤ → ℂ} {n j : ℤ}
    (hc : ∀ k : ℤ, 0 < k → c k = 0) (hd : SupportedLE d n) (hj : n < j) :
    convCoeff c d j = 0 := by
  unfold convCoeff
  have hterm : ∀ k : ℤ, c k * d (j - k) = 0 := by
    intro k
    by_cases hk : 0 < k
    · rw [hc k hk, zero_mul]
    · push Not at hk
      have hjk : n < j - k := by omega
      rw [hd (j - k) hjk, mul_zero]
  simp only [hterm]
  exact tsum_zero

/-- If `c` is supported in `[0, +∞)` and `d` in `(n, +∞)`, then the coefficient
convolution `c * d` is supported in `(n, +∞)` (the upper-triangular analogue of
the preceding support lemma, p.9). -/
theorem convCoeff_eq_zero_of_supported_ge {c d : ℤ → ℂ} {n j : ℤ}
    (hc : SupportedGE c) (hd : SupportedGT d n) (hj : j ≤ n) :
    convCoeff c d j = 0 := by
  unfold convCoeff
  have hterm : ∀ k : ℤ, c k * d (j - k) = 0 := by
    intro k
    by_cases hk : k < 0
    · rw [hc k hk, zero_mul]
    · push Not at hk
      have hjk : j - k ≤ n := by omega
      rw [hd (j - k) hjk, mul_zero]
  simp only [hterm]
  exact tsum_zero

/-- Coefficient sequence of a circle function. -/
def coeffs (f : CircleT → ℂ) : ℤ → ℂ := fun n => fourierCoeff f n

/-- The Banach space `Y_w = A_w ⊕ A_w` of column vectors (p.8), represented by
pairs of coefficient sequences. -/
abbrev YCoeff : Type := (ℤ → ℂ) × (ℤ → ℂ)

/-- The norm `‖y‖_{Y_w} = ‖y₁‖_{A_w} + ‖y₂‖_{A_w}` (p.8). -/
def Ynorm (W : StrongBeurlingWeight) (v : YCoeff) : ℝ :=
  L1wNorm W v.1 + L1wNorm W v.2

/-- The Riesz projection `P₊` onto nonnegative Fourier modes (`P₊ = P_{[0,∞)}`,
p.8, §2.1). -/
def PplusSeq (c : ℤ → ℂ) : ℤ → ℂ := fun n => if 0 ≤ n then c n else 0

/-- The projection `P_{≤n}` onto Fourier modes `≤ n` (p.8). -/
def PleSeq (n : ℤ) (c : ℤ → ℂ) : ℤ → ℂ := fun k => if k ≤ n then c k else 0

/-- The projection `P_{>n} = Id − P_{≤n}` (p.8). -/
def PgtSeq (n : ℤ) (c : ℤ → ℂ) : ℤ → ℂ := fun k => if n < k then c k else 0

/-- The projection `Pₙ = diag(P₊, P_{≤n})` on `Y_w` (p.8). -/
def PnOp (n : ℤ) (v : YCoeff) : YCoeff := (PplusSeq v.1, PleSeq n v.2)

/-- The projection `R̃ₙ = diag(0, P_{>n})` on `Y_w` (p.9). -/
def RtildeOp (n : ℤ) (v : YCoeff) : YCoeff := (fun _ => 0, PgtSeq n v.2)

/-- Multiplication by the matrix `C = [[1, b*/a], [-b/a*, 1]]` on `Y_w`
(p.8), at the level of Fourier coefficients: each matrix entry acts by the
coefficient convolution `convCoeff`. -/
def Cmul (a b : CircleT → ℂ) (v : YCoeff) : YCoeff :=
  (fun n => convCoeff (coeffs fun x => (a x)⁻¹) v.1 n +
      convCoeff (coeffs fun x => starFun b x / a x) v.2 n,
   fun n => convCoeff (coeffs fun x => -(b x / starFun a x)) v.1 n +
      convCoeff (coeffs (starFun a)) v.2 n)

/-- The truncated `A_w` norm `‖P_{>n} f‖_{A_w} = ∑_{k > n} |f̂(k)| w(k)` appearing
in Lemma 4 (p.9). -/
def truncatedAWnorm (W : StrongBeurlingWeight) (f : CircleT → ℂ) (n : ℤ) : ℝ :=
  ∑' k : ℤ, if n < k then ‖fourierCoeff f k‖ * W.w k else 0

end

end Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup
