/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ClassicalStates
public import Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Characterization of calibrated classical readout

A POVM that exactly reads every classical distribution is the computational
basis measurement. The basis POVM itself is reused from the public library;
point masses determine its diagonal and positivity determines its off-diagonal
entries. No statistical or complexity assumption is hidden in calibration.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout (basisPOVM)

/-- The public basis measurement has the diagonal point-mass projector as its effect. -/
theorem basisPOVM_mats {d : Type} [Fintype d] [DecidableEq d] (x : d) :
    (basisPOVM d).mats x = HermitianMat.diagonal ℂ (fun i => if x = i then 1 else 0) := by
  apply HermitianMat.ext
  change (MState.pure (Ket.basis x)).m =
    Matrix.diagonal (fun i => ((if x = i then 1 else 0 : ℝ) : ℂ))
  ext i j
  by_cases hxi : x = i <;> by_cases hxj : x = j <;>
    simp_all [MState.pure_apply, Ket.basis, Ket.coe_fun_eq, Matrix.diagonal_apply, eq_comm]

/-- Two POVMs coincide when their effect families coincide. -/
private theorem povm_eq_of_mats_eq {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ Ψ : POVM X d) (h : Λ.mats = Ψ.mats) : Λ = Ψ := by
  cases Λ
  cases Ψ
  cases h
  rfl

/-- Transport the public coordinate basis measurement to an arbitrary universe of finite types.
Both outcomes and matrix indices are relabeled by the same `Fintype.equivFin` equivalence.
The construction reuses the public `Fin` measurement rather than introducing new effects. -/
def finiteBasisReadout (d : Type*) [Fintype d] [DecidableEq d] : POVM d d where
  mats x := ((basisPOVM (Fin (Fintype.card d))).mats (Fintype.equivFin d x)).reindex
    (Fintype.equivFin d).symm
  nonneg x := by
    rw [HermitianMat.zero_le_iff, HermitianMat.mat_reindex]
    exact (HermitianMat.zero_le_iff.mp
      ((basisPOVM (Fin (Fintype.card d))).nonneg (Fintype.equivFin d x))).submatrix _
  normalized := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    ext i j
    simp [-HermitianMat.mat_apply, HermitianMat.mat_reindex,
      Matrix.reindex_apply, basisPOVM_mats, HermitianMat.diagonal_mat,
      Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- The transported public measurement has the same diagonal projectors on every finite type. -/
theorem finiteBasisReadout_mats {d : Type*} [Fintype d] [DecidableEq d] (x : d) :
    (finiteBasisReadout d).mats x =
      HermitianMat.diagonal ℂ (fun i => if x = i then 1 else 0) := by
  apply HermitianMat.ext
  change (((basisPOVM (Fin (Fintype.card d))).mats (Fintype.equivFin d x)).reindex
    (Fintype.equivFin d).symm).mat = _
  rw [HermitianMat.mat_reindex, basisPOVM_mats, HermitianMat.diagonal_mat,
    HermitianMat.diagonal_mat]
  ext i j
  simp [Matrix.reindex_apply, Matrix.diagonal_apply]

/-- On a universe-zero carrier, transporting through `Fin` recovers the public basis measurement. -/
theorem finiteBasisReadout_eq_basisPOVM (d : Type) [Fintype d] [DecidableEq d] :
    finiteBasisReadout d = basisPOVM d := by
  apply povm_eq_of_mats_eq
  funext x
  rw [finiteBasisReadout_mats, basisPOVM_mats]

section Calibration

open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X] {d : Type*} [Fintype d] [DecidableEq d]

/-!
### What a general POVM sees of a classical state
-/

omit [DecidableEq X] in
/-- A general POVM reads only the diagonal of a classical state: the outcome
probability of `x` under `ofClassical r` is the diagonal sum
`∑ i, re((M_x)_{ii}) * r i` — measuring cannot see the (absent) off-diagonal
information of a classical state. -/
theorem measure_ofClassical_apply (Λ : POVM X d) (r : ProbDistribution d) (x : X) :
    ((Λ.measure (MState.ofClassical r)) x : ℝ)
      = ∑ i, ((Λ.mats x).mat i i).re * (r i : ℝ) := by
  simp only [POVM.measure, ProbDistribution.mk', ProbDistribution.funlike_apply,
    HermitianMat.inner_eq_re_trace, MState.coe_ofClassical, HermitianMat.diagonal_mat,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  simp

omit [DecidableEq X] in
/-- Reading a point mass: the outcome probability under a constant (point-mass)
classical state is exactly the corresponding diagonal entry of the POVM element.
This is the probe that pins the diagonal during calibration. -/
theorem measure_constant_apply (Λ : POVM X d) (j : d) (x : X) :
    ((Λ.measure (MState.ofClassical (ProbDistribution.constant j))) x : ℝ)
      = ((Λ.mats x).mat j j).re := by
  rw [measure_ofClassical_apply]
  simp [ProbDistribution.constant_eq, apply_ite, Prob.coe_one, Prob.coe_zero,
    Finset.sum_ite_eq]

/-!
### Calibration uniqueness
-/

/-- A positive-semidefinite matrix with a zero diagonal entry has a vanishing column:
restricted to the 2×2 principal minor `{i, j}`, the determinant is
`A_{ii} A_{jj} - A_{ij} conj(A_{ij}) = -|A_{ij}|²`, nonnegative by
`Matrix.PosSemidef.det_nonneg`, which forces `A_{ij} = 0`. -/
theorem posSemidef_zero_diag_apply {d : Type*} {M : Matrix d d ℂ} (hM : M.PosSemidef) {i j : d}
    (hjj : M j j = 0) : M i j = 0 := by
  have h2 : (M.submatrix (fun k : Fin 2 ↦ if k = 0 then i else j)
      (fun k : Fin 2 ↦ if k = 0 then i else j)).PosSemidef := hM.submatrix _
  have hd := h2.det_nonneg
  have h00 : M.submatrix (fun k : Fin 2 ↦ if k = 0 then i else j)
      (fun k : Fin 2 ↦ if k = 0 then i else j) 0 0 = M i i := by simp
  have h01 : M.submatrix (fun k : Fin 2 ↦ if k = 0 then i else j)
      (fun k : Fin 2 ↦ if k = 0 then i else j) 0 1 = M i j := by simp
  have h10 : M.submatrix (fun k : Fin 2 ↦ if k = 0 then i else j)
      (fun k : Fin 2 ↦ if k = 0 then i else j) 1 0 = M j i := by simp
  have h11 : M.submatrix (fun k : Fin 2 ↦ if k = 0 then i else j)
      (fun k : Fin 2 ↦ if k = 0 then i else j) 1 1 = M j j := by simp
  rw [Matrix.det_fin_two, h00, h01, h10, h11, hjj, mul_zero, zero_sub] at hd
  have hji : M j i = star (M i j) :=
    (hM.isHermitian.apply j i).symm
  have hz : M i j * star (M i j) = ((Complex.normSq (M i j) : ℝ) : ℂ) :=
    Complex.mul_conj (M i j)
  rw [hji, hz, Complex.le_def] at hd
  simp only [Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, and_true] at hd
  exact Complex.normSq_eq_zero.mp (le_antisymm (by linarith) (Complex.normSq_nonneg _))

/-- **Calibration uniqueness.**  `basisPOVM` is the only POVM on `d` that reads every
classical register exactly: if `Λ.measure (ofClassical r) = r` for every
distribution `r` — the calibration hypothesis consumed by the `acceptProb_calibrated_ofClassical` — then `Λ = basisPOVM`.  Point masses pin the
diagonal (`(M_x)_{jj} = δ_{jx}`, via `measure_constant_apply`), and
`posSemidef_zero_diag_apply` kills every off-diagonal entry, so each POVM element
`M_x` is the rank-one diagonal projector `|x⟩⟨x|`. -/
theorem calibrated_POVM_eq_finiteBasisReadout (Λ : POVM d d)
    (hΛ : ∀ r : ProbDistribution d, ∀ x,
      ((Λ.measure (MState.ofClassical r)) x : ℝ) = (r x : ℝ)) :
    Λ = finiteBasisReadout d := by
  have hdiagre : ∀ (x i : d), ((Λ.mats x).mat i i).re = if i = x then (1 : ℝ) else 0 := by
    intro x i
    have h1 := hΛ (ProbDistribution.constant i) x
    rw [measure_constant_apply Λ i x] at h1
    simpa [ProbDistribution.constant_eq, apply_ite, Prob.coe_one, Prob.coe_zero] using h1
  have him : ∀ (x i : d), ((Λ.mats x).mat i i).im = 0 := fun x i ↦
    Complex.conj_eq_iff_im.mp ((Λ.mats x).H.apply i i)
  have hdiag : ∀ (x i : d), (Λ.mats x).mat i i = if i = x then (1 : ℂ) else 0 := by
    intro x i
    by_cases h : i = x
    · rw [ite_eq_left h]
      exact Complex.ext (by rw [hdiagre x i, ite_eq_left h, Complex.one_re])
        (by rw [him x i, Complex.one_im])
    · rw [ite_eq_right h]
      exact Complex.ext (by rw [hdiagre x i, ite_eq_right h, Complex.zero_re])
        (by rw [him x i, Complex.zero_im])
  have hpsd : ∀ x, ((Λ.mats x).mat).PosSemidef := fun x ↦
    HermitianMat.zero_le_iff.mp (Λ.nonneg x)
  have hoff : ∀ (x i j : d), i ≠ j → (Λ.mats x).mat i j = 0 := by
    intro x i j hij
    by_cases hxj : j = x
    · have hne : i ≠ x := fun h ↦ hij (h.trans hxj.symm)
      have hii : (Λ.mats x).mat i i = 0 := by
        rw [hdiag x i, ite_eq_right hne]
      have hji : (Λ.mats x).mat j i = 0 := posSemidef_zero_diag_apply (hpsd x) hii
      have hstar : star ((Λ.mats x).mat j i) = (Λ.mats x).mat i j :=
        (hpsd x).isHermitian.apply i j
      rw [hji] at hstar
      simpa using hstar.symm
    · have hjj : (Λ.mats x).mat j j = 0 := by
        rw [hdiag x j, ite_eq_right hxj]
      exact posSemidef_zero_diag_apply (hpsd x) hjj
  have hmats : Λ.mats = (finiteBasisReadout d).mats := by
    funext x
    rw [finiteBasisReadout_mats]
    show Λ.mats x = HermitianMat.diagonal ℂ (fun k ↦ if x = k then (1 : ℝ) else 0)
    refine HermitianMat.ext (Matrix.ext fun i j ↦ ?_)
    by_cases hij : i = j
    · subst hij
      rw [hdiag x i, HermitianMat.diagonal_mat, Matrix.diagonal_apply, ite_eq_left rfl]
      by_cases hxi : x = i
      · simp [hxi]
      · simp [hxi, show i ≠ x from fun h ↦ hxi h.symm]
    · rw [hoff x i j hij, HermitianMat.diagonal_mat, Matrix.diagonal_apply, ite_eq_right hij]
  exact povm_eq_of_mats_eq Λ (finiteBasisReadout d) hmats

end Calibration

/-- A calibrated POVM on a universe-zero carrier equals the public basis measurement itself. -/
theorem calibrated_POVM_eq_basisPOVM {d : Type} [Fintype d] [DecidableEq d]
    (Λ : POVM d d)
    (hΛ : ∀ r : ProbDistribution d, ∀ x,
      ((Λ.measure (MState.ofClassical r)) x : ℝ) = (r x : ℝ)) :
    Λ = basisPOVM d :=
  (calibrated_POVM_eq_finiteBasisReadout Λ hΛ).trans (finiteBasisReadout_eq_basisPOVM d)

/-- The transported public basis measurement reads every classical distribution exactly. -/
theorem measure_finiteBasisReadout_ofClassical_apply {d : Type*} [Fintype d] [DecidableEq d]
    (p : ProbDistribution d) (x : d) :
    (((finiteBasisReadout d).measure (MState.ofClassical p)) x : ℝ) = (p x : ℝ) := by
  rw [measure_ofClassical_apply]
  simp [-HermitianMat.mat_apply, finiteBasisReadout_mats, HermitianMat.diagonal_mat,
    apply_ite]

end Qatlib.Concepts.MixedFidelity.FidelityMetric
