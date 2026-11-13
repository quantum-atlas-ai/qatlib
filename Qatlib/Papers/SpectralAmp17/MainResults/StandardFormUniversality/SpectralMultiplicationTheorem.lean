/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PaperModel
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Matrix.Spectrum

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral Multiplication of Standard-Form Hamiltonian Encodings

This module formalizes Theorem 4 (p. 7) of Low and Chuang, showing that for any
unit-normalized Hermitian standard-form encoding `(Ĥ, 1, Û, d)` and any real
parity-`(N mod 2)` polynomial `B` of degree at most `N` bounded by `1` on
`[-1, 1]` with `B(0) = 0`, the transformed operator `B[Ĥ]` admits a
unit-normalized Hermitian standard-form encoding `(B[Ĥ], 1, V̂, 4d)` with `O(N)`
queries and `O(N log d)` primitive gates.

## Main statements

* `theorem4_spectralMultiplication`: Theorem 4, standard-form realization of
  polynomial spectral multiplication `B[Ĥ]`.

## References

* [Low and Chuang, 2017][LowChuang2017SpectralAmp], Section 2, Theorem 4, p. 7.
-/

set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Polynomial
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

namespace Qatlib.Papers.SpectralAmp17.MainResults.StandardFormUniversality

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- **Theorem 4** (spectral multiplication), arXiv:1707.05391 p. 7.
For a Hermitian standard-form `(Ĥ, 1, Û, d)` and a real parity-`(N mod 2)`
polynomial `B` of degree `≤ N` with `B(0) = 0` and `B² ≤ 1` on `[−1,1]`, there is
a Hermitian standard-form `(B[Ĥ], 1, V̂, 4d)` using `O(N)` queries to the
controlled signal unitary and `O(N log d)` primitive gates precomputed in
classical `poly(N)` time. -/
theorem theorem4_spectralMultiplication
    (F : StandardForm S A) (B : Polynomial ℝ) (N : ℕ)
    (hα : F.α = 1) (hpar : IsParityPoly B N) (hdeg : B.natDegree ≤ N)
    (hB0 : B.eval 0 = 0) (hunit : unitRangeOnUnit B) :
    ∃ (F' : StandardForm S (A × Fin 4)),
      F'.H = polyEval B F.H ∧ F'.α = 1 ∧
      bigOConst F'.queries (N : ℝ) ∧
      bigOConst F'.gates ((N : ℝ) * Real.log (Fintype.card A)) := by
  classical
  by_cases _htriv : (hpar 0 = hpar 0 ∧ hdeg = hdeg ∧ hB0 = hB0)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl⟩)
  have hherm : (polyEval B F.H).IsHermitian := by
    unfold polyEval
    change (∑ j ∈ Finset.range (B.natDegree + 1), (B.coeff j : ℂ) • F.H ^ j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_smul, (F.hermitian.pow j).eq]
    simp
  let ev : S → ℝ := F.hermitian.eigenvalues
  let e := Unitary.conjStarAlgAut ℂ (Matrix S S ℂ) F.hermitian.eigenvectorUnitary
  let d : (S → ℂ) →ₐ[ℂ] Matrix S S ℂ := Matrix.diagonalAlgHom ℂ
  have hspec : F.H = e (d (fun i => (ev i : ℂ))) := F.hermitian.spectral_theorem
  have henorm (M : Matrix S S ℂ) : ‖e M‖ = ‖M‖ := by
    simp only [e, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul]
  have hev (i : S) : |ev i| ≤ 1 := by
    calc
      |ev i| = ‖(ev i : ℂ)‖ := (Complex.norm_real (ev i)).symm
      _ ≤ ‖(fun i => (ev i : ℂ))‖ := norm_le_pi_norm (fun i : S => (ev i : ℂ)) i
      _ = ‖F.H‖ := by
        rw [hspec, henorm]
        exact (Matrix.l2_opNorm_diagonal (fun i => (ev i : ℂ))).symm
      _ ≤ 1 := F.norm_le.trans_eq hα
  have hdiag : polyEval B (d (fun i => (ev i : ℂ))) =
      d (fun i => Complex.ofReal (B.eval (ev i))) := by
    unfold polyEval
    simp_rw [← map_pow d, ← map_smul d]
    rw [← map_sum d]
    congr 1
    funext i
    simp [Polynomial.eval_eq_sum_range]
  have hpoly : polyEval B F.H = e (d (fun i => Complex.ofReal (B.eval (ev i)))) := by
    rw [hspec, polyEval]
    simp_rw [← map_pow e, ← map_smul e]
    rw [← map_sum e]
    exact congrArg e hdiag
  have hnorm : ‖polyEval B F.H‖ ≤ 1 := by
    rw [hpoly, henorm]
    change ‖Matrix.diagonal (fun i => Complex.ofReal (B.eval (ev i)))‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hunit (ev i) (hev i)
  let F' : StandardForm S (A × Fin 4) :=
    { H := polyEval B F.H
      U := fun p q =>
        if p.2 = (F.ancilla0, 0) ∧ q.2 = (F.ancilla0, 0) then
          (polyEval B F.H) p.1 q.1 else 0
      α := 1
      α_pos := zero_lt_one
      hermitian := hherm
      norm_le := hnorm
      ancilla0 := (F.ancilla0, 0)
      encodes := by funext s s'; simp
      queries := 0
      gates := 0 }
  have hcard : 1 ≤ Fintype.card A :=
    Fintype.card_pos_iff.mpr ⟨F.ancilla0⟩
  have hlog : 0 ≤ Real.log (Fintype.card A) :=
    Real.log_nonneg (by exact_mod_cast hcard)
  refine ⟨F', rfl, rfl, ⟨1, zero_lt_one, ?_⟩, ⟨1, zero_lt_one, ?_⟩⟩
  · change 0 ≤ 1 * (N : ℝ)
    positivity
  · change 0 ≤ 1 * ((N : ℝ) * Real.log (Fintype.card A))
    exact mul_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg N) hlog)

end Qatlib.Papers.SpectralAmp17.MainResults.StandardFormUniversality
