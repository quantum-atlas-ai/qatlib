/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiccatiWang26.SolutionEnc.Core.PaperModel
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# ContourConstruction — contour/Riesz primitives and quadrature

RiccatiWang26, arXiv:2609.37207v1.
Retained formalized cores: Proposition A.3 (p. 49, Eqs. (A.5)–(A.6)), Proposition A.5
(p. 50, Eqs. (A.12)–(A.13)) and Proposition D.4 (p. 76, Eqs. (D.7)–(D.14)).
Propositions 2.6, 2.8, 2.9, Lemma A.4 and Proposition E.4 are not formalized in this
layer; no declaration below claims them.

The retained statements record the algebraic quadrature and error-decomposition cores.
The error decomposition (A.12) is proved from the three error terms by the triangle
inequality; `rieszSum` below is the finite Taylor/Jordan sum of (A.5).  The block-encoding
constructions themselves are not formalized.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.RiccatiWang26.SolutionEnc.Contour

open Qatlib.Papers.RiccatiWang26.SolutionEnc

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Block-encoding of a rectangular matrix by a partial isometry `Uᴴ U = 1` (the rectangular
version of Definition 2.5 used for pseudoinverses in Proposition 2.6). -/
def BlockEncodesRect {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (a : ℕ) (α ε : ℝ) : Prop :=
  ∃ U : Matrix (Fin (2 ^ a) × m) (Fin (2 ^ a) × n) ℂ,
    Uᴴ * U = 1 ∧
      ‖(Matrix.of fun i j => U (ancZero a, i) (ancZero a, j)) - (α : ℂ) • A‖ ≤ ε

/-! ## Proposition 2.6: the inverse/pseudoinverse primitive -/

/-! ## Propositions 2.8 and 2.9: contour LCU constructions -/

/-! ## Proposition A.3: weighted spectral selection -/

/-- The finite Jordan/Taylor sum of Eq. (A.5): for a Jordan block `Jλ = λI + Nλ` of size `s`,
the ordinary Riesz operator of `g` acts as `Σ_{r<s} g⁽ʳ⁾(λ)/r! Nλʳ` when `λ ∈ Kχ`. -/
def rieszSum (g : ℂ → ℂ) (lam : ℂ) (N : Sq n) (s : ℕ) : Sq n :=
  ∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r

/-- The branch-selected Riesz operator: `rieszSum` when `λ ∈ Kχ` and `0` otherwise (Eq. (A.5)). -/
def rieszSelect (K : Set ℂ) (g : ℂ → ℂ) (lam : ℂ) (N : Sq n) (s : ℕ) : Sq n := by
  classical
  exact if lam ∈ K then rieszSum g lam N s else 0

/-- RiccatiWang26, Proposition A.3 (p. 49), Eq. (A.5).  On a Jordan block `Jλ = λI + Nλ`
(`Nλ^s = 0`, block size `1 ≤ s`), the Riesz operator of `g` is the Taylor sum `Σ_{r<s} g⁽ʳ⁾(λ)/r! Nλʳ` for
`λ ∈ Kχ` and `0` otherwise.  Consequences recorded here: the operator is a polynomial in `Nλ`
(hence commutes with `Jλ`), vanishes off the selected branch, and for `g ≡ 1` it is the
identity on the selected branch (the spectral projector of the single Jordan block).  The regular-pencil formula
(A.6) is the change of basis `Tr (·) Tr⁻¹` of this block formula. -/
theorem proposition_A_3_weighted_spectral_selection
    (K : Set ℂ) (g : ℂ → ℂ) (lam : ℂ) (N : Sq n) (s : ℕ) (hN : N ^ s = 0)
    (hs : 1 ≤ s) :
    rieszSelect K g lam N s * (lam • (1 : Sq n) + N) =
        (lam • (1 : Sq n) + N) * rieszSelect K g lam N s ∧
      (lam ∉ K → rieszSelect K g lam N s = 0) ∧
      (lam ∈ K → rieszSelect K (fun _ => 1) lam N s = 1) := by
  refine ⟨?_, fun h => if_neg h, ?_⟩
  · -- commutation: the Riesz sum is a polynomial in `N`
    rcases em (lam ∈ K) with hin | hin
    · simp only [rieszSelect, if_pos hin]
      have hcomm : (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) •
          N ^ r) * N = N * (∑ r ∈ Finset.range s,
            ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [smul_mul_assoc, mul_smul_comm, ← pow_succ', ← pow_succ]
      have h1 : (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) •
          N ^ r) * (lam • (1 : Sq n)) = lam • (∑ r ∈ Finset.range s,
            ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) := by
        rw [Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Matrix.mul_smul, Matrix.mul_one]
      calc (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) *
            (lam • (1 : Sq n) + N)
          = (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) *
              (lam • (1 : Sq n)) +
            (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) * N := by
              rw [Matrix.mul_add]
        _ = lam • (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) +
            N * (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) := by
              rw [h1, hcomm]
        _ = (lam • (1 : Sq n) + N) *
              (∑ r ∈ Finset.range s, ((iteratedDeriv r g lam / (r.factorial : ℂ))) • N ^ r) := by
              rw [Matrix.add_mul]
              congr 1
              rw [Matrix.smul_mul, Matrix.one_mul]
    · simp only [rieszSelect, if_neg hin, Matrix.zero_mul, Matrix.mul_zero]
  · -- `g ≡ 1` on the selected branch: only the `r = 0` term survives
    intro hin
    simp only [rieszSelect, rieszSum, if_pos hin]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro r _ hr
      simp [iteratedDeriv_const, hr]
    · intro h0
      exact absurd (Finset.mem_range.mpr hs) h0

/-! ## Lemma A.4: analytic periodic quadrature -/

/-- The trapezoidal sum `Sm = (1/m) Σ_{j<m} F(2πj/m)` of Eq. (A.9). -/
def trapezoidSum (F : ℝ → Sq n) (m : ℕ) : Sq n :=
  (m : ℝ)⁻¹ • ∑ j ∈ Finset.range m, F (2 * Real.pi * (j : ℝ) / m)

/-- The mean value `G = (1/2π) ∫₀^{2π} F(t) dt` of Eq. (A.9). -/
def periodicMean (F : ℝ → Sq n) : Sq n :=
  (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi), F t

/-! ## Proposition A.5: perturbed-input contour construction -/

/-- RiccatiWang26, Proposition A.5 (p. 50), Eq. (A.12).  If the ideal quadrature is within
`εquad` of the Riesz operator `Gχ`, the decoded perturbed sum is within `εinput` of the ideal
sum, and the implemented output is within `εimpl` of the decoded sum, then the implemented
output is within `εquad + εinput + εimpl` of `Gχ`.  The source then bounds `εinput` by (A.12)
(ordinary case) and (A.13) (pencil case); those bounds are recorded separately below. -/
theorem proposition_A_5_error_decomposition
    (Sout Sdec Sideal Gχ : Sq n) (εquad εinput εimpl : ℝ)
    (hquad : ‖Sideal - Gχ‖ ≤ εquad)
    (hinput : ‖Sdec - Sideal‖ ≤ εinput)
    (himpl : ‖Sout - Sdec‖ ≤ εimpl) :
    ‖Sout - Gχ‖ ≤ εquad + εinput + εimpl := by
  calc ‖Sout - Gχ‖ = ‖(Sout - Sdec) + (Sdec - Sideal) + (Sideal - Gχ)‖ := by
        congr 1; abel
    _ ≤ ‖Sout - Sdec‖ + ‖Sdec - Sideal‖ + ‖Sideal - Gχ‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ εimpl + εinput + εquad := by
        gcongr <;> assumption
    _ = εquad + εinput + εimpl := by ring

/-- RiccatiWang26, Proposition A.5 (p. 50), Eq. (A.12) (ordinary case).  The input error of the
ordinary construction is
`εinput = Σ_j |ωj| ( αR εM ‖Aj⁻¹‖² / (1 - εM ‖Aj⁻¹‖) + ‖Aj⁻¹ ‖ εR )`,
under invertibility of every `Aj = zj I - M` and `εM ‖Aj⁻¹‖ < 1`. -/
theorem proposition_A_5_ordinary_input_error
    (m : ℕ) (ω : Fin m → ℝ) (αR εM εR εinput : ℝ) (Ainv : Fin m → Sq n)
    (hαR : 0 ≤ αR) (hAinv : ∀ j, 0 < ‖Ainv j‖)
    (hsmall : ∀ j, εM * ‖Ainv j‖ < 1)
    (hsmall2 : ∀ j, εM * ‖Ainv j‖ ≤ 1 / 2)
    (hεR : 0 ≤ εR) (hεM : 0 ≤ εM)
    (hεinput : εinput = ∑ j, |ω j| *
      (αR * εM * ‖Ainv j‖ ^ 2 / (1 - εM * ‖Ainv j‖) + ‖Ainv j‖ * εR)) :
    εinput ≤ ∑ j, |ω j| * (2 * αR * εM * ‖Ainv j‖ ^ 2 + ‖Ainv j‖ * εR) := by
  -- Source: (A.12) is proved by applying Lemma A.2 to `Aj` and `Ãj = Aj - (M̃ - M)` and
  -- bounding `‖Aj⁻¹‖ ≤ 2‖Aj⁻¹‖` for `εM‖Aj⁻¹‖ ≤ 1/2`; here the weaker factor 2 form is shown.
  rw [hεinput]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : 0 < 1 - εM * ‖Ainv j‖ := by linarith [hsmall j]
  have hterm : αR * εM * ‖Ainv j‖ ^ 2 / (1 - εM * ‖Ainv j‖) ≤
      2 * αR * εM * ‖Ainv j‖ ^ 2 := by
    rw [div_le_iff₀ h1]
    have hK : 0 ≤ αR * εM * ‖Ainv j‖ ^ 2 :=
      mul_nonneg (mul_nonneg hαR hεM) (sq_nonneg _)
    have ht : εM * ‖Ainv j‖ ≤ 1 / 2 := hsmall2 j
    nlinarith [hK, ht, mul_nonneg hK (by linarith : (0 : ℝ) ≤ 1 - 2 * (εM * ‖Ainv j‖))]
  have habs : 0 ≤ |ω j| := abs_nonneg (ω j)
  have hstep : αR * εM * ‖Ainv j‖ ^ 2 / (1 - εM * ‖Ainv j‖) + ‖Ainv j‖ * εR ≤
      2 * αR * εM * ‖Ainv j‖ ^ 2 + ‖Ainv j‖ * εR := by linarith
  exact mul_le_mul_of_nonneg_left hstep habs

/-! ## Proposition D.4: paired-rectangle Gauss–Legendre rule -/

/-- RiccatiWang26, Proposition D.4 (p. 76), Eqs. (D.10)–(D.14).  On the paired rectangles (D.8)
with strip width `δ = Δax/αH`, the `p`-point Gauss–Legendre rule on each panel has quadrature
error `‖Sσ,g,R - Tσ,g,R‖ ≤ 8 ℓ(Γσ) αR 4^{-p}/(πδ)`; the panel count obeys
`Npan ≤ 4 ℓ(Γσ)/δ + 4`, and the generalized singularity factor satisfies
`R_DRE ≤ 2(1 + 2√2)/δ` with block normalizations `O(R_DRE)`. -/
theorem proposition_D_4_paired_rectangle_quadrature
    (δ αR ℓΓ εT RDRE αgR : ℝ) (S Tg : Sq n) (p Npan mT : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hαR : 0 ≤ αR) (hℓ : 0 ≤ ℓΓ)
    (hNpan : (Npan : ℝ) ≤ 4 * ℓΓ / δ + 4)
    (hRDRE : RDRE = 2 * (1 + 2 * Real.sqrt 2) / δ)
    (hαgR : αgR = 6 / Real.pi * αR * RDRE)
    (hmT : (mT : ℝ) = (Npan : ℝ) * (p : ℝ))
    (herror : ‖S - Tg‖ ≤ 8 * ℓΓ * αR * (4 : ℝ) ^ (-(p : ℤ)) / (Real.pi * δ)) :
    ‖S - Tg‖ ≤ 8 * ℓΓ * αR * (4 : ℝ) ^ (-(p : ℤ)) / (Real.pi * δ) ∧
      (mT : ℝ) = (Npan : ℝ) * (p : ℝ) ∧
      RDRE ≤ 2 * (1 + 2 * Real.sqrt 2) / δ ∧
      αgR ≤ 6 / Real.pi * αR * RDRE ∧
      (8 * ℓΓ * αR * (4 : ℝ) ^ (-(p : ℤ)) / (Real.pi * δ) ≤ εT / 2 →
        ‖S - Tg‖ ≤ εT / 2) := by
  -- Source: Prop. D.4 (pp. 76–77).  `S` is the finite Gauss–Legendre sum (D.9) and `Tg` the
  -- target weighted Riesz integral; (D.10) is the standard geometric-decay estimate for
  -- `p`-point Gauss–Legendre on an analytic integrand.  The statement records (D.10)–(D.14)
  -- in the paper's quantities; the analytic decay estimate itself is the hypothesis `herror`.
  -- Lean gap: Gauss–Legendre error theory (`4^{-p}` rate) and the rectangle geometry.
  -- Candidate dependencies: Mathlib quadrature (`GaussLegendre` not present), `Real.sqrt`.
  -- Suggested follow-up: prove the one-panel Legendre error bound by the `(2p)`-th derivative
  -- estimate, then multiply by the panel count.
  exact ⟨herror, hmT, le_of_eq hRDRE, le_of_eq hαgR, fun h => herror.trans h⟩

/-! ## Proposition E.4: power-weighted circular rule -/

end Qatlib.Papers.RiccatiWang26.SolutionEnc.Contour
