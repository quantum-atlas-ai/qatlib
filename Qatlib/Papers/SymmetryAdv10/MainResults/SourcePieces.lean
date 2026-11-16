/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymmetryAdv10.MainResults.ProjectorAudit
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Preserved closed mathematical contracts from the fixed historical sources

Fixed source1012.2112v1. These statements retain their actual hypotheses;
conditional Schur equalities and an assumed symmetric commutant are not
claimed as constructions of the source representation or quantum programs.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder MatrixOrder
namespace Qatlib.Papers.SymmetryAdv10.MainResults.SourcePieces
open Qatlib.Papers.SymmetryAdv10.MainResults
variable (P : Problem)

/-- The complete historical closed AdvComparison mathematical contract, with source bridge limitations recorded separately. -/
theorem hybridImprove (lam eps eta : ℝ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heps1 : eps < 1)
    (hepslam : eps / (1 - eps) ≤ lam)
    (heta : eta < 1 / (1 + lam)) :
    Problem.hybridK lam eps eta >
      (1 - lam) * (Real.sqrt (1 - eps) - 1 / Real.sqrt (1 + lam)) ^ 2 := by
  have hlam_pos : 0 < 1 + lam := by linarith
  have h1mlam : 0 < 1 - lam := by linarith
  have hsqrt_pos : 0 < Real.sqrt (1 + lam) := Real.sqrt_pos.mpr hlam_pos
  have heps_eps : eps ≤ lam * (1 - eps) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - eps)] at hepslam
    linarith
  -- `1/(1+λ) ≤ 1 − ε`
  have hle_inner : 1 / (1 + lam) ≤ 1 - eps := by
    rw [div_le_iff₀ hlam_pos]
    nlinarith [heps_eps]
  have hb_le_a : 1 / Real.sqrt (1 + lam) ≤ Real.sqrt (1 - eps) := by
    have hbval : Real.sqrt (1 / (1 + lam)) = 1 / Real.sqrt (1 + lam) := by
      rw [one_div, Real.sqrt_inv, inv_eq_one_div]
    calc 1 / Real.sqrt (1 + lam) = Real.sqrt (1 / (1 + lam)) := hbval.symm
      _ ≤ Real.sqrt (1 - eps) := Real.sqrt_le_sqrt hle_inner
  -- `√η < 1/√(1+λ)`
  have hb_sq : (1 / Real.sqrt (1 + lam)) ^ 2 = 1 / (1 + lam) := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hlam_pos)]
  have hc_lt_b : Real.sqrt eta < 1 / Real.sqrt (1 + lam) := by
    rw [Real.sqrt_lt' (one_div_pos.mpr hsqrt_pos), hb_sq]
    exact heta
  -- both differences are nonnegative and the second is strictly larger
  have hb_nonneg : 0 ≤ Real.sqrt (1 - eps) - 1 / Real.sqrt (1 + lam) := by linarith
  have hgt : Real.sqrt (1 - eps) - 1 / Real.sqrt (1 + lam)
      < Real.sqrt (1 - eps) - Real.sqrt eta := by linarith
  have hpos : 0 < (Real.sqrt (1 - eps) - Real.sqrt eta)
      - (Real.sqrt (1 - eps) - 1 / Real.sqrt (1 + lam)) := by linarith
  have hsum : 0 < (Real.sqrt (1 - eps) - Real.sqrt eta)
      + (Real.sqrt (1 - eps) - 1 / Real.sqrt (1 + lam)) := by linarith
  have hsq : (Real.sqrt (1 - eps) - 1 / Real.sqrt (1 + lam)) ^ 2
      < (Real.sqrt (1 - eps) - Real.sqrt eta) ^ 2 := by
    nlinarith [mul_pos hpos hsum]
  have hfin := mul_lt_mul_of_pos_left hsq h1mlam
  simpa [Problem.hybridK, mul_comm, mul_left_comm, mul_assoc] using hfin

/-- The complete historical closed BlockStructure mathematical contract, with source bridge limitations recorded separately. -/
theorem weightedSum {ι : Type} [Fintype ι]
    (Pik : ι → Matrix P.F P.F ℂ) (Γ : Matrix P.F P.F ℂ) (gam : ι → ℂ)
    (hidem : ∀ k, Pik k * Pik k = Pik k)
    (hsum : ∑ k, Pik k = 1)
    (hcomm : ∀ k, Γ * Pik k = Pik k * Γ)
    (hschur : ∀ k, Pik k * Γ * Pik k = gam k • Pik k) :
    Γ = ∑ k, gam k • Pik k := by
  have hGamma : Γ = ∑ k, Γ * Pik k := by
    have h1 : Γ * 1 = ∑ k, Γ * Pik k := by
      rw [← hsum, Finset.mul_sum]
    simpa using h1
  rw [hGamma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : Γ * Pik k = Pik k * Γ * Pik k := by
    rw [mul_assoc, hcomm k, ← mul_assoc, hidem k]
  rw [h1, hschur k]

/-- The complete historical closed BlockStructure mathematical contract, with source bridge limitations recorded separately. -/
theorem degenerate {n : Type} [Fintype n]
    (Pii T : Matrix n n ℂ) (d : ℕ)
    (hproj : Pii * Pii = Pii) (htr : Pii.trace = (d : ℂ)) (hd : (0 : ℂ) < (d : ℂ))
    (hT : Pii * T = T) :
    (Pii * Pii * Pii * T).trace = (1 / (d : ℂ)) * (Pii * Pii).trace * (Pii * T).trace := by
  have hPii3 : Pii * Pii * Pii = Pii := by
    rw [mul_assoc, hproj, hproj]
  have htrace : (Pii * Pii).trace = (d : ℂ) := by rw [hproj, htr]
  have hd0 : (d : ℂ) ≠ 0 := ne_of_gt hd
  rw [hPii3, hT, htrace, one_div, inv_mul_cancel₀ hd0, one_mul]

/-- The complete historical closed IndexErasure mathematical contract, with source bridge limitations recorded separately. -/
def indexErasure (N M : ℕ) : Problem :=
  letI : Fintype { f : Fin N → Fin M // Function.Injective f } := by
    classical exact Fintype.ofFinite _
  letI : DecidableEq { f : Fin N → Fin M // Function.Injective f } := by
    classical exact inferInstance
  { F := { f : Fin N → Fin M // Function.Injective f }
    Hom := Fin N
    Out := Fin M
    Tgt := Fin M
    funMap := fun f x => f.1 x
    target := fun f y => ((Real.sqrt (Fintype.card (Fin N) : ℝ) : ℂ))⁻¹ *
      ((Finset.univ.filter (fun x : Fin N => f.1 x = y)).card : ℂ) }

/-- The complete historical closed Symmetrization mathematical contract, with source bridge limitations recorded separately. -/
theorem entrySymm (A : Matrix P.F P.F ℂ) (f g : P.F) (σ : P.F ≃ P.F)
    (hσf : σ f = g) (hσg : σ g = f)
    (hinv : ∀ i j, A i j = A (σ i) (σ j)) :
    A f g = A g f := by
  rw [hinv f g, hσf, hσg]

/-- The complete historical closed Symmetrization mathematical contract, with source bridge limitations recorded separately. -/
theorem mulComm {n : Type} [Fintype n]
    (A B : Matrix n n ℂ)
    (hA : Matrix.transpose A = A) (hB : Matrix.transpose B = B)
    (hAB : Matrix.transpose (A * B) = A * B) :
    A * B = B * A := by
  rw [← hAB, Matrix.transpose_mul, hB, hA]

/-- The complete historical closed Symmetrization mathematical contract, with source bridge limitations recorded separately. -/
theorem commutative (M : Set (Matrix P.F P.F ℂ))
    (hmul : ∀ A ∈ M, ∀ B ∈ M, A * B ∈ M)
    (hsym : ∀ A ∈ M, Matrix.transpose A = A) :
    ∀ A ∈ M, ∀ B ∈ M, A * B = B * A := by
  intro A hA B hB
  exact mulComm A B (hsym A hA) (hsym B hB) (hsym (A * B) (hmul A hA B hB))

/-- The complete historical closed Symmetrization mathematical contract, with source bridge limitations recorded separately. -/
theorem piZInvariant (x : P.Hom) (z : P.Out) (σ : P.F ≃ P.F)
    (hout : ∀ f : P.F, P.funMap (σ f) = P.funMap f) :
    ∀ f g : P.F, ProjectorAudit.PiZ P x z f g = ProjectorAudit.PiZ P x z (σ f) (σ g) := by
  intro f g
  by_cases hfg : f = g
  · subst hfg
    simp [ProjectorAudit.PiZ, hout]
  · have hne : σ f ≠ σ g := fun h => hfg (σ.injective h)
    simp [ProjectorAudit.PiZ, hfg, hne]

/-- The complete historical closed Symmetrization mathematical contract, with source bridge limitations recorded separately. -/
theorem gammaInvariant (x : P.Hom) (Γ : Matrix P.F P.F ℂ) (σ : P.F ≃ P.F)
    (hΓ : ∀ f g, Γ f g = Γ (σ f) (σ g))
    (hD : ∀ f g, P.D x f g = P.D x (σ f) (σ g)) :
    ∀ f g, P.GammaX Γ x f g = P.GammaX Γ x (σ f) (σ g) := by
  intro f g
  simp only [Problem.GammaX, Matrix.hadamard_apply, hΓ f g, hD f g]

end Qatlib.Papers.SymmetryAdv10.MainResults.SourcePieces
