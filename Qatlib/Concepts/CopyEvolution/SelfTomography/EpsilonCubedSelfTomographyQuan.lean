/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.EpsilonCubedSelfTomographyStat
import Qatlib.Concepts.CopyEvolution.SelfTomography.SelfTomographyOnGridOutputQuan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Self-tomography with an inverse-cubic copy bound

This module proves `epsilonCubedSelfTomography` by combining phase-label decoding, a spectral
good-event projector, and fresh-copy QPE error bounds. For `0 < ε ≤ 1 / 2`, the chosen grid and
repetition budgets give decoding error at most `ε`, good-event mass at least `8 / π² - ε`, and
copy count at most `1000 / ε³`.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `label_decode`: the good-label decoding error bound.
* `selfTomography_budget`: explicit grid, repetition, and copy budgets.
* `epsilonCubedSelfTomography`: the complete self-tomography guarantee.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.SelfTomography
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false

/-- For `M ≥ 2` and `0 ≤ r ≤ 1`, a good phase label decodes to within `2 / M` of `r`. -/
private theorem label_decode (M : ℕ) (hM : 2 ≤ M) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : Fin M) (hz : z ∈ qpeGoodLabels M r) :
    |qpeLabelDecode M z-r| ≤ 2/(M:ℝ) := by
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  let x := (z.val:ℝ)/M
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := (div_lt_one hMr).mpr (by exact_mod_cast z.isLt)
  let c : ℤ := ⌊-r/2-x+1/2⌋
  have hc0 : c ≤ 0 := by
    have hh : c < 1 := Int.floor_lt.mpr (by norm_num; linarith)
    omega
  have hc1 : -1 ≤ c := Int.le_floor.mpr (by norm_num; linarith)
  have hw : |-r/2-x-(c:ℝ)| ≤ 1/(M:ℝ) := by
    simpa only [qpeGoodLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      phaseDistance] using! hz
  have hm0 : 0 ≤ min x (1-x) := le_min hx0 (by linarith)
  have hmx : min x (1-x) ≤ x := min_le_left _ _
  have hd : 2/(M:ℝ) = 2*(1/(M:ℝ)) := by ring
  obtain h | h : c = 0 ∨ c = -1 := by omega
  · rw [h] at hw
    norm_num only [Int.cast_zero, sub_zero] at hw
    have hl := (abs_le.mp hw).1
    apply abs_le.mpr
    rw [hd]
    dsimp [qpeLabelDecode]
    change - (2*(1/(M:ℝ))) ≤ 2*min x (1-x)-r ∧ 2*min x (1-x)-r ≤ 2*(1/(M:ℝ))
    constructor <;> linarith
  · rw [h] at hw
    norm_num only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] at hw
    obtain ⟨hl,hu⟩ := abs_le.mp hw
    apply abs_le.mpr
    rw [hd]
    dsimp [qpeLabelDecode]
    change - (2*(1/(M:ℝ))) ≤ 2*min x (1-x)-r ∧ 2*min x (1-x)-r ≤ 2*(1/(M:ℝ))
    rcases le_total x (1-x) with hx | hx
    · rw [min_eq_left hx]
      constructor <;> linarith
    · rw [min_eq_right hx]
      constructor <;> linarith

/-- For `0 < ε ≤ 1 / 2`, the prescribed ceilings give a valid grid, positive repetition count,
decoding and simulation errors at most `ε`, and copy count at most `1000 / ε³`. -/
private theorem selfTomography_budget (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    let M : ℕ := Nat.ceil (2/ε)
    let n : ℕ := Nat.ceil (8*(M:ℝ)*Real.pi^2/ε)
    2 ≤ M ∧ (2:ℝ)/M ≤ ε ∧
    8*(M-1:ℕ)*Real.pi^2/(n:ℝ) ≤ ε ∧
    ((M-1:ℕ)*n:ℝ) ≤ 1000/ε^3 ∧ 0<n := by
  (try dsimp only)
  let M := Nat.ceil (2/ε)
  let n := Nat.ceil (8*(M:ℝ)*Real.pi^2/ε)
  have hceilM : 2/ε ≤ (M:ℝ) := Nat.le_ceil _
  have hfour : (4:ℝ) ≤ (M:ℝ) := by
    have hh : 4 ≤ 2/ε := (le_div_iff₀ hε).mpr (by linarith)
    exact hh.trans hceilM
  have hM : 2 ≤ M := by exact_mod_cast (show (2:ℝ)≤M by linarith)
  have hMr : (0:ℝ)<M := by linarith
  have hA : 0 < 8*(M:ℝ)*Real.pi^2/ε := by positivity
  have hceiln : 8*(M:ℝ)*Real.pi^2/ε ≤ (n:ℝ) := Nat.le_ceil _
  have hnr : (0:ℝ)<n := hA.trans_le hceiln
  have hn : 0<n := by exact_mod_cast hnr
  have hprec : (2:ℝ)/M ≤ ε := by
    apply (div_le_iff₀ hMr).mpr
    have h := (div_le_iff₀ hε).mp hceilM
    linarith
  have hcount : (M-1:ℕ) ≤ M := Nat.sub_le _ _
  have herr : 8*(M-1:ℕ)*Real.pi^2/(n:ℝ) ≤ ε := by
    apply (div_le_iff₀ hnr).mpr
    have h := (div_le_iff₀ hε).mp hceiln
    have hm : ((M-1:ℕ):ℝ) ≤ M := by exact_mod_cast hcount
    nlinarith [mul_le_mul_of_nonneg_right hm (show 0≤Real.pi^2 by positivity)]
  have hMupper : (M:ℝ) ≤ 3/ε := by
    have h := le_of_lt (Nat.ceil_lt_add_one (show 0≤2/ε by positivity))
    have hh : 2/ε+1 ≤ 3/ε := by apply (le_div_iff₀ hε).mpr; field_simp; nlinarith
    exact h.trans hh
  have hnupper : (n:ℝ) ≤ (24*Real.pi^2+1)/ε^2 := by
    have h := le_of_lt (Nat.ceil_lt_add_one hA.le)
    have hh : 8*(M:ℝ)*Real.pi^2/ε ≤ 24*Real.pi^2/ε^2 := by
      calc
        _ ≤ 8*(3/ε)*Real.pi^2/ε := by gcongr
        _ = _ := by field_simp; ring
    have he2 : ε^2 ≤ 1 := by nlinarith
    have hone : 1 ≤ 1/ε^2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
    have hsum : 24*Real.pi^2/ε^2 + 1/ε^2 = (24*Real.pi^2+1)/ε^2 := by ring
    linarith
  have hcost : ((M-1:ℕ)*n:ℝ) ≤ 1000/ε^3 := by
    have hpi : Real.pi^2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc
      _ ≤ (M:ℝ)*(n:ℝ) := by exact_mod_cast Nat.mul_le_mul_right n hcount
      _ ≤ (3/ε)*((24*Real.pi^2+1)/ε^2) := by gcongr
      _ = (72*Real.pi^2+3)/ε^3 := by field_simp; ring
      _ ≤ 1000/ε^3 := by gcongr; nlinarith
  exact ⟨hM,hprec,herr,hcost,hn⟩

/-- Extends `V` to the phase-label and control registers by tensoring with their identity
operators. -/
private noncomputable def eigenBasis (D M : ℕ) (V : Operator D) :=
  TensorGate (1:Operator M) (TensorGate (1:Matrix Bool Bool ℂ) V)
/-- The diagonal indicator matrix of good label-eigenvalue pairs on the false control branch. -/
private noncomputable def goodDiagonal (D M : ℕ) (eig : Fin D → ℝ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  Matrix.diagonal fun p => if p.2.1 then 0 else
    if p.1 ∈ qpeGoodLabels M (eig p.2.2) then 1 else 0

/-- Extending a unitary eigenbasis by identity operators gives a unitary matrix on the full QPE
register. -/
private theorem basis_unitary (D M : ℕ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    eigenBasis D M V ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
  tensorGate_unitary one_mem_unitaryGroup_ℂ (tensorGate_unitary one_mem_unitaryGroup_ℂ hV)

/-- The self-tomography good-event matrix is the conjugate of `goodDiagonal` by `eigenBasis`. -/
private theorem projector_basis (D M : ℕ) (V : Operator D) (eig : Fin D → ℝ) :
    qpeSelfTomographyGoodProjector D M V eig =
      eigenBasis D M V * goodDiagonal D M eig * (eigenBasis D M V)ᴴ := by
  classical
  rw [goodDiagonal]
  ext ⟨p,b,i⟩ ⟨q,c,k⟩
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Fintype.sum_prod_type,
    eigenBasis, tensorGate_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, qpeSelfTomographyGoodProjector, Matrix.of_apply,
    Finset.sum_filter, Fintype.sum_bool]
  cases b <;> cases c <;> by_cases hp : p=q <;>
    simp [hp, ite_mul, apply_ite, RCLike.star_def]

/-- For unitary `V`, the operator norm of the self-tomography good-event matrix is at most one. -/
private theorem projector_norm (D M : ℕ) (V : Operator D) (eig : Fin D → ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ‖qpeSelfTomographyGoodProjector D M V eig‖ ≤ 1 := by
  have hW := l2_norm_unitary_le_one (basis_unitary D M V hV)
  have hWH : ‖(eigenBasis D M V)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact hW
  have hdiag : ‖goodDiagonal D M eig‖ ≤ 1 := by
    rw [goodDiagonal, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro p
    split <;> (try split) <;> norm_num
  rw [projector_basis]
  calc
    _ ≤ (‖eigenBasis D M V‖*‖goodDiagonal D M eig‖)*‖(eigenBasis D M V)ᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*1)*1 := by gcongr
    _ = 1 := by norm_num

/-- The QPE kernel state at eigenphase `-eig i / 2`, tensored with the false control state and
basis vector `i`. -/
private noncomputable def kernelBasisState (D M : ℕ) (eig : Fin D → ℝ) (i : Fin D) :
    QState (Fin M × (Bool × Fin D)) := fun p =>
  if p.2.1 then 0 else qpeKernel M (-eig i/2) p.1 * Qatlib.Foundations.PureStateMath.Ket i p.2.2

/-- Applying `eigenBasis` to `kernelBasisState` replaces the system basis vector by the
corresponding column of `V`. -/
private theorem basis_kernel (D M : ℕ) (V : Operator D) (eig : Fin D → ℝ) (i : Fin D) :
    ApplyGate (eigenBasis D M V) (kernelBasisState D M eig i) =
      fun p => if p.2.1 then 0 else qpeKernel M (-eig i/2) p.1 * V p.2.2 i := by
  classical
  funext ⟨z,b,k⟩
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    eigenBasis, tensorGate_apply, Matrix.one_apply, kernelBasisState, Fintype.sum_bool]
  cases b <;> simp [Qatlib.Foundations.PureStateMath.Ket, ite_mul, apply_ite]
  ring

/-- Conjugating an outer product by `U` gives the outer product of the vector transformed by
`U`. -/
private theorem outer_conj {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState I) :
    U*outerProduct ψ*Uᴴ = outerProduct (ApplyGate U ψ) := by
  ext i j
  simp only [outerProduct_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ApplyGate, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [RCLike.star_def]
  ring

/-- Simultaneous unitary conjugation of two matrices preserves the trace of their product. -/
private theorem trace_conj_pair {I : Type*} [Fintype I] [DecidableEq I]
    (W A B : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.trace ((W*A*Wᴴ)*(W*B*Wᴴ)) = Matrix.trace (A*B) := by
  have hh : Wᴴ*W=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hW
  calc
    _ = Matrix.trace (W*(A*B)*Wᴴ) := by
      congr 1
      calc
        _ = W*A*(Wᴴ*W)*B*Wᴴ := by noncomm_ring
        _ = _ := by rw [hh]; noncomm_ring
    _ = Matrix.trace (A*B) := by
      rw [Matrix.trace_mul_cycle, hh, Matrix.one_mul]

/-- The trace pairing of `goodDiagonal` with a kernel-state outer product equals the sum of
squared kernel amplitudes over good labels. -/
private theorem kernel_good_trace (D M : ℕ) (eig : Fin D → ℝ) (i : Fin D) :
    (Matrix.trace (goodDiagonal D M eig * outerProduct (kernelBasisState D M eig i))).re =
      ∑ z ∈ qpeGoodLabels M (eig i), ‖qpeKernel M (-eig i/2) z‖^2 := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, goodDiagonal, Matrix.diagonal_mul,
    outerProduct_apply, kernelBasisState, Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte, mul_zero, map_zero, Finset.sum_const_zero,
    zero_add, Complex.re_sum, Qatlib.Foundations.PureStateMath.Ket]
  simp [ite_mul, apply_ite, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- For a density operator with the stated unitary spectral decomposition and nonnegative
eigenvalues, ideal QPE has good-event mass at least `8 / π²` when `M ≥ 2`. -/
private theorem ideal_good_mass (D M : ℕ) (hM : 2 ≤ M) (ρ V : Operator D)
    (eig : Fin D → ℝ) (hρ : IsDensityOperator ρ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i:ℂ))*Vᴴ)
    (he : ∀ i, 0 ≤ eig i) :
    (Matrix.trace (qpeSelfTomographyGoodProjector D M V eig *
      copyQPEIdealOutput D M ρ)).re ≥ 8/Real.pi^2 := by
  classical
  have hW := basis_unitary D M V hV
  have hpart (i : Fin D) :
      (Matrix.trace (qpeSelfTomographyGoodProjector D M V eig *
        outerProduct (fun p : Fin M × (Bool × Fin D) =>
          if p.2.1 then 0 else qpeKernel M (-eig i/2) p.1 * V p.2.2 i))).re =
        ∑ z ∈ qpeGoodLabels M (eig i), ‖qpeKernel M (-eig i/2) z‖^2 := by
    rw [projector_basis, ← basis_kernel D M V eig i, ← outer_conj, trace_conj_pair _ _ _ hW,
      kernel_good_trace]
  have hsum : ∑ i, eig i = 1 := by
    have hh : Vᴴ*V=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hV
    have h := hρ.2
    rw [hs, Matrix.trace_mul_cycle, hh, Matrix.one_mul, Matrix.trace_diagonal] at h
    simpa using! congrArg Complex.re h
  rw [selfTomography_spectral_output D M (by omega) ρ V eig hV hs]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hpart]
  calc
    _ ≥ ∑ i, eig i*(8/Real.pi^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (he i)
      exact offgrid_phase_window_probability M (-eig i/2) hM
    _ = 8/Real.pi^2 := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Proves the self-tomography specification with good-event mass at least `8 / π² - ε` and copy
count at most `1000 / ε³` for `0 < ε ≤ 1 / 2` [LloydMohseniRebentrost2014]. -/
theorem epsilonCubedSelfTomography : EpsilonCubedSelfTomography := by
  intro D ρ V eig ε hρ hV hs he hε hε1
  (try dsimp only)
  let M := Nat.ceil (2/ε)
  let n := Nat.ceil (8*(M:ℝ)*Real.pi^2/ε)
  obtain ⟨hM,hprec,herr,hcost,hn⟩ := selfTomography_budget ε hε hε1
  have hstate := (copy_qpe_actual_program_state_error D M n hM hn ρ hρ).2.2
  have hideal := ideal_good_mass D M hM ρ V eig hρ hV hs (fun i => (he i).1)
  have hpn := projector_norm D M V eig hV
  let P := qpeSelfTomographyGoodProjector D M V eig
  have htransport : |(Matrix.trace (P*copyQPEOutput D M n ρ)).re -
      (Matrix.trace (P*copyQPEIdealOutput D M ρ)).re| ≤ ε := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.mul_sub]
    calc
      _ ≤ ‖Matrix.trace (P*(copyQPEOutput D M n ρ-copyQPEIdealOutput D M ρ))‖ :=
        Complex.abs_re_le_norm _
      _ ≤ Matrix.traceNorm (P*(copyQPEOutput D M n ρ-copyQPEIdealOutput D M ρ)) :=
        Matrix.abs_trace_le_traceNorm _
      _ ≤ ‖P‖*Matrix.traceNorm (copyQPEOutput D M n ρ-copyQPEIdealOutput D M ρ) :=
        Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
      _ ≤ 1*(8*(M-1:ℕ)*Real.pi^2/(n:ℝ)) := by
        exact mul_le_mul hpn hstate (Matrix.traceNorm_nonneg _) (by norm_num)
      _ ≤ ε := by simpa using! herr
  refine ⟨hM,hprec,herr,hcost,?_,hideal,?_,copy_qpe_same_path_fresh_resource_counts D M n hM hn⟩
  · intro i z hz
    exact label_decode M hM (eig i) (he i).1 (he i).2 z hz
  · have hh := (abs_le.mp htransport).1
    dsimp [P] at hh
    linarith
end Qatlib.Concepts.CopyEvolution.SelfTomography
