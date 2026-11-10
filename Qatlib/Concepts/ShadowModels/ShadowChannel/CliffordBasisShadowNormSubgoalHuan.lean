/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowNormSubgoalStat
import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowChannelSubgoalHuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ShadowChannel
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem clifford_square_expectation_norm {d : ℕ} (σ O : Operator d)
    (hσ : IsDensityOperator σ) :
    (Matrix.trace (σ*(O*O))).re ≤ ‖O*O‖ := by
  rw [Matrix.trace_mul_comm]
  exact (le_abs_self _).trans (abs_trace_density_le_norm (O*O) σ hσ.1 hσ.2)

theorem clifford_norm_weight_cycle {d : ℕ} (σ U : Operator d) (b : Fin d) :
    Matrix.trace (basisProjector b*(U*σ*Uᴴ)) =
      Matrix.trace (σ*(Uᴴ*basisProjector b*U)) := by
  calc
    _ = Matrix.trace (Uᴴ*basisProjector b*U*σ) := by
      simpa only [Matrix.mul_assoc] using! Matrix.trace_mul_cycle (basisProjector b*U) σ Uᴴ
    _ = _ := Matrix.trace_mul_comm _ _

theorem clifford_psd_norm_le_trace {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : A.PosSemidef) : ‖A‖ ≤ (Matrix.trace A).re := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let H := hA.isHermitian
  let U : Operator d := H.eigenvectorUnitary
  let ev := H.eigenvalues
  have hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ := H.eigenvectorUnitary.2
  have hnn : ∀ i, 0 ≤ ev i := hA.eigenvalues_nonneg
  have ht : (Matrix.trace A).re = ∑ i, ev i := by
    rw [H.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum]
    rfl
  have hsum : 0 ≤ ∑ i, ev i := Finset.sum_nonneg (fun i _ => hnn i)
  have hdiag : ‖Matrix.diagonal (fun i => (ev i : ℂ))‖ ≤ ∑ i, ev i := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hsum).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn i)]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have he : A = U*Matrix.diagonal (fun i => (ev i : ℂ))*Uᴴ := by
    have h := H.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h
    exact h
  have hun : ‖U‖ = 1 := l2_norm_unitary_eq_one hU
  have huadj : ‖Uᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose, hun]
  calc
    ‖A‖ = ‖U*Matrix.diagonal (fun i => (ev i : ℂ))*Uᴴ‖ := congrArg norm he
    _ ≤ ‖U*Matrix.diagonal (fun i => (ev i : ℂ))‖*‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖U‖*‖Matrix.diagonal (fun i => (ev i : ℂ))‖)*‖Uᴴ‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖Matrix.diagonal (fun i => (ev i : ℂ))‖ := by rw [hun, huadj, one_mul, mul_one]
    _ ≤ ∑ i, ev i := hdiag
    _ = (Matrix.trace A).re := ht.symm

theorem clifford_square_density_trace_le {d : ℕ} (hd : 2 ≤ d) (σ O : Operator d)
    (hσ : IsDensityOperator σ) (hO : O.IsHermitian) :
    (Matrix.trace (σ*(O*O))).re ≤ (Matrix.trace (O*O)).re := by
  have hp : (O*O).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self O
    simpa only [hO.eq] using! h
  exact (clifford_square_expectation_norm σ O hσ).trans
    (clifford_psd_norm_le_trace (by omega) (O*O) hp)

theorem cliffordBasisShadowNormSubgoal : CliffordBasisShadowNormSubgoal := by
  intro d hd I _ _ μ Uf _ h36 σ hσ O hO hO0
  let D : ℝ := (d : ℝ)*((d : ℝ)+1)*((d : ℝ)+2)
  let T : ℝ := (Matrix.trace (O*O)).re
  let S : ℝ := (Matrix.trace (σ*(O*O))).re
  have hb (b : Fin d) :
      (∑ i, μ.prob i*(Matrix.trace (σ*((Uf i)ᴴ*basisProjector b*Uf i))).re *
        (Matrix.trace (O*((Uf i)ᴴ*basisProjector b*Uf i))).re ^ 2) =
      T/D + (1/D)*(S+S) := by
    have h := congrArg (fun A : Operator d => (Matrix.trace (σ*A)).re)
      (h36 (basisProjector b) (basisProjector_pure b) O O hO hO hO0 hO0)
    simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul,
      Matrix.trace_smul, Complex.smul_re, Matrix.mul_add, Matrix.trace_add,
      Complex.add_re, hσ.2, Complex.one_re, smul_eq_mul, mul_one] at h
    change (∑ i : I, (μ.prob i *
      (Matrix.trace (O*((Uf i)ᴴ*basisProjector b*Uf i))).re *
      (Matrix.trace (O*((Uf i)ᴴ*basisProjector b*Uf i))).re) *
      (Matrix.trace (σ*((Uf i)ᴴ*basisProjector b*Uf i))).re) = T/D+(1/D)*(S+S) at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he : (∑ b : Fin d, ∑ i, (μ.prob i *
      (Matrix.trace (basisProjector b*(Uf i*σ*(Uf i)ᴴ))).re) *
      (((d : ℝ)+1)*(Matrix.trace (O*((Uf i)ᴴ*basisProjector b*Uf i))).re)^2) =
      ((d : ℝ)+1)/((d : ℝ)+2)*(T+2*S) := by
    simp_rw [basis_born_trace_cycle]
    have hi (b : Fin d) : (∑ i, μ.prob i *
        (Matrix.trace (σ*((Uf i)ᴴ*basisProjector b*Uf i))).re *
        (((d : ℝ)+1)*(Matrix.trace (O*((Uf i)ᴴ*basisProjector b*Uf i))).re)^2) =
        ((d : ℝ)+1)^2*(T/D+(1/D)*(S+S)) := by
      rw [← hb b, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hi]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    dsimp only [D]
    field_simp
    ring
  rw [he]
  have hT : 0 ≤ T := by
    have hp := Matrix.posSemidef_conjTranspose_mul_self O
    simpa only [T, hO.eq] using! (Complex.nonneg_iff.mp hp.trace_nonneg).1
  have hS : S ≤ T := clifford_square_density_trace_le hd σ O hσ hO
  have hr0 : 0 ≤ ((d : ℝ)+1)/((d : ℝ)+2) := by positivity
  have hr1 : ((d : ℝ)+1)/((d : ℝ)+2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  calc
    _ ≤ ((d : ℝ)+1)/((d : ℝ)+2)*(3*T) :=
      mul_le_mul_of_nonneg_left (by linarith) hr0
    _ ≤ 3*T := by nlinarith

end Qatlib.Concepts.ShadowModels.ShadowChannel
