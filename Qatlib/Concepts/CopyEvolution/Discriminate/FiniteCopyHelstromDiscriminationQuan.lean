/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationStat
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutQuan
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge


open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix MatrixOrder
open scoped Classical BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option warningAsError false

private theorem sign_diagonal_traceNorm {I R : Type*} [Fintype I] [DecidableEq I]
    [RCLike R] (x : I → ℝ) :
    Matrix.traceNorm (Matrix.diagonal (fun j => (x j : R))) = ∑ j, |x j| := by
  let A : Matrix I I R := Matrix.diagonal (fun j => (x j : R))
  change Matrix.traceNorm A = _
  letI : DecidableEq I := Classical.decEq _
  have hsq : Aᴴ*A = Matrix.diagonal (fun j => (((x j)^2 : ℝ) : R)) := by
    dsimp only [A]
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [sq]
    · simp [hij]
  open MatrixOrder in
  have hp : 0 ≤ (Matrix.diagonal (fun j => (((x j)^2 : ℝ) : R)) : Matrix I I R) :=
    Matrix.PosSemidef.nonneg (Matrix.posSemidef_diagonal_iff.mpr (fun j => by
      exact_mod_cast sq_nonneg (x j)))
  unfold Matrix.traceNorm
  rw [hsq, CFC.sqrt_eq_real_sqrt _ hp, cfcₙ_eq_cfc (by fun_prop) (by simp)]
  rw_mod_cast [Matrix.cfc_diagonal (𝕜 := R) (g := fun j => (x j)^2)]
  simp [Matrix.trace_diagonal, Function.comp_def, Real.sqrt_sq_eq_abs]

private theorem sign_trace_conjugation (d : ℕ) (V B : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : Matrix.trace (V*B*Vᴴ) = Matrix.trace B := by
  rw [Matrix.trace_mul_cycle]
  have hVV : Vᴴ*V=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hV
  rw [hVV, Matrix.one_mul]

private theorem sign_trace_spectral_mul (d : ℕ) (V A : Operator d) (f : Fin d → ℂ)
    : Matrix.trace ((V*Matrix.diagonal f*Vᴴ)*A) = ∑ j, f j*(Vᴴ*A*V) j j := by
  have hshape : Matrix.trace ((V*Matrix.diagonal f*Vᴴ)*A) =
      Matrix.trace (Matrix.diagonal f*(Vᴴ*A*V)) := by
    calc
      _ = Matrix.trace (V*(Matrix.diagonal f*(Vᴴ*A))) := congrArg Matrix.trace (by noncomm_ring)
      _ = Matrix.trace ((Matrix.diagonal f*(Vᴴ*A))*V) := Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc]
  rw [hshape, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]

private theorem sign_effect_diag (d : ℕ) (V A : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hA : A.PosSemidef) (hAc : (1-A).PosSemidef) (j : Fin d) :
    ((Vᴴ*A*V) j j).re ∈ Set.Icc 0 1 := by
  have ha : 0 ≤ ((Vᴴ*A*V) j j).re :=
    (RCLike.nonneg_iff.mp (hA.conjTranspose_mul_mul_same V).diag_nonneg).1
  have hc : 0 ≤ ((Vᴴ*(1-A)*V) j j).re :=
    (RCLike.nonneg_iff.mp (hAc.conjTranspose_mul_mul_same V).diag_nonneg).1
  have hVV : Vᴴ*V=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hV
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hVV] at hc
  simp only [Matrix.sub_apply, Complex.sub_re, Matrix.one_apply_eq, Complex.one_re] at hc
  exact ⟨ha, by linarith⟩

private theorem sign_projector_probability (d : ℕ) (V χ : Operator d) (x : Fin d → ℝ) :
    (Matrix.trace ((V*Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0)*Vᴴ)*χ)).re =
      ∑ j ∈ Finset.univ.filter (fun j => 0 < x j), ((Vᴴ*χ*V) j j).re := by
  rw [sign_trace_spectral_mul, Complex.re_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 0 < x j <;> simp [hj]

private theorem sign_effect_score (d : ℕ) (A ρ σ : Operator d) (hσ : Matrix.trace σ = 1) :
    ((Matrix.trace (A*ρ)).re + (Matrix.trace ((1-A)*σ)).re)/2 =
      1/2 + (Matrix.trace (A*(ρ-σ))).re/2 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hσ,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Complex.one_re]
  ring

theorem finiteCopyHelstromDiscrimination : FiniteCopyHelstromDiscrimination := by
  intro d M n γ ρ σ V x hM hn hγ hγ1 hρ hσ hV hs hgap
  let P := V*Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0)*Vᴴ
  let s := ∑ j ∈ Finset.univ.filter (fun j => 0 < x j), x j
  have hVV : V*Vᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff).mp hV
  have hP : P.PosSemidef := (Matrix.posSemidef_diagonal_iff.mpr (fun j => by
    by_cases hj : 0 < x j <;> simp [hj])).mul_mul_conjTranspose_same V
  have hPcshape : 1-P = V*Matrix.diagonal (fun j => if 0 < x j then (0 : ℂ) else 1)*Vᴴ := by
    have hd : (1 : Operator d)-Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) =
        Matrix.diagonal (fun j => if 0 < x j then (0 : ℂ) else 1) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
      congr 1
      funext j
      by_cases hj : 0 < x j <;> simp [hj]
    dsimp only [P]
    rw [← hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hVV]
  have hPc : (1-P).PosSemidef := by
    rw [hPcshape]
    exact (Matrix.posSemidef_diagonal_iff.mpr (fun j => by
      by_cases hj : 0 < x j <;> simp [hj])).mul_mul_conjTranspose_same V
  have hsum : ∑ j, x j = 0 := by
    have ht : Matrix.trace (ρ-σ) = 0 := by rw [Matrix.trace_sub, hρ.2, hσ.2, sub_self]
    rw [hs, sign_trace_conjugation d V _ hV, Matrix.trace_diagonal] at ht
    simpa only [Complex.re_sum, Complex.ofReal_re, Complex.zero_re] using! congrArg Complex.re ht
  have hnorm : Matrix.traceNorm (ρ-σ) = ∑ j, |x j| := by
    rw [hs]
    have hh : Vᴴ*V=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff').mp hV
    letI : DecidableEq (Fin d) := Classical.decEq _
    have hi : V.Isometry := by
      change Vᴴ*V=1
      convert! hh using 1
      first
        | exact Subsingleton.elim _ _
        | (ext i j; simp [Matrix.one_apply])
    rw [Matrix.traceNorm_isometry_right hi, Matrix.traceNorm_isometry_left hi]
    exact @sign_diagonal_traceNorm (Fin d) ℂ (Fin.fintype d)
        (instDecidableEqFin d) Complex.instRCLike x
  have hsrel : s = Matrix.traceNorm (ρ-σ)/2 := by
    have heach (j : Fin d) : |x j| = 2*(if 0 < x j then x j else 0)-x j := by
      by_cases hj : 0 < x j
      · rw [if_pos hj, abs_of_pos hj]; ring
      · rw [if_neg hj, abs_of_nonpos (le_of_not_gt hj)]; ring
    have he : (∑ j, |x j|) = 2*s-(∑ j, x j) := by
      simp only [heach, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← Finset.sum_filter]
    rw [hsum, sub_zero, ← hnorm] at he
    linarith
  have hdiff := timedTwoSpecies_spectral_difference d ρ σ V x hV hs
  have hdiag : Vᴴ*(ρ-σ)*V = Matrix.diagonal (fun j => (x j : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact hdiff
  have hptr : (Matrix.trace (P*(ρ-σ))).re = s := by
    dsimp only [P]
    rw [sign_projector_probability, hdiag]
    simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re]
    rfl
  have hscore : ((Matrix.trace (P*ρ)).re + (Matrix.trace ((1-P)*σ)).re)/2 =
      1/2 + Matrix.traceNorm (ρ-σ)/4 := by
    rw [sign_effect_score d P ρ σ hσ.2, hptr, hsrel]
    ring
  have hopt (A : Operator d) (hA : A.PosSemidef) (hAc : (1-A).PosSemidef) :
      ((Matrix.trace (A*ρ)).re + (Matrix.trace ((1-A)*σ)).re)/2 ≤
        1/2 + Matrix.traceNorm (ρ-σ)/4 := by
    have ht : (Matrix.trace (A*(ρ-σ))).re = ∑ j, x j*((Vᴴ*A*V) j j).re := by
      rw [Matrix.trace_mul_comm, hs, sign_trace_spectral_mul, Complex.re_sum]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hb : (∑ j, x j*((Vᴴ*A*V) j j).re) ≤ s := by
      dsimp only [s]
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro j _
      have hd := sign_effect_diag d V A hV hA hAc j
      by_cases hj : 0 < x j
      · rw [if_pos hj]
        nlinarith [hd.2]
      · rw [if_neg hj]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hj) hd.1
    rw [sign_effect_score d A ρ σ hσ.2, ht]
    linarith [hb, hsrel]
  have hx := timedTwoSpecies_density_difference_range d ρ σ V x hρ hσ hV hs
  have hsign := (finiteTwoSpeciesSignReadout d M n γ ρ σ V x hM hn hγ hγ1 hρ hσ hV hs hx hgap).1
  have hr := hsign ρ hρ
  have ht := hsign σ hσ
  have hpρ : (Matrix.trace (P*ρ)).re =
      ∑ j ∈ Finset.univ.filter (fun j => 0 < x j), ((Vᴴ*ρ*V) j j).re :=
    sign_projector_probability d V ρ x
  have hpσ : (Matrix.trace (P*σ)).re =
      ∑ j ∈ Finset.univ.filter (fun j => 0 < x j), ((Vᴴ*σ*V) j j).re :=
    sign_projector_probability d V σ x
  have hnσ := timedTwoSpecies_sign_masses_sum d M n ρ σ σ (by omega) hρ hσ hσ
  have hcomp : (Matrix.trace ((1-P)*σ)).re = 1-(Matrix.trace (P*σ)).re := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hσ.2, Complex.sub_re, Complex.one_re]
  refine ⟨hP, hPc, hscore, hopt, ?_, rfl⟩
  rw [← hpρ] at hr
  rw [← hpσ] at ht
  rw [hcomp] at hscore
  linarith [(abs_le.mp hr).1, (abs_le.mp ht).2]

end Qatlib.Concepts.CopyEvolution.Discriminate
