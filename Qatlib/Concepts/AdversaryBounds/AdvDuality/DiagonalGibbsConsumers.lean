/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel

/-!
# Concrete diagonal Gibbs-channel examples

This module evaluates diagonal Gibbs channels in two cases. At inverse temperature zero, every
positive iterate resets the system to its Gibbs density while retaining the reference marginal;
a two-level example at inverse temperature `Real.log 2` has an explicit density and geometric
trace-norm convergence.

The examples use the Gibbs-state and quantum-channel formalism of [NielsenChuang2010].

## Main statements

* `zero_beta_gibbs_reference_reset_consumer`: a positive iterate at zero inverse temperature
  acts as a reference-preserving reset.
* `two_level_gibbs_actual_consumer`: the two-level density has weights `2 / 3` and `1 / 3`, with
  trace-norm error `(2 / 3) * (1 / 4) ^ n` from the specified initial state.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

open scoped Matrix.Norms.L2Operator ComplexOrder Classical

/-- At zero inverse temperature, every positive thermal-channel iterate maps a joint operator to
the Gibbs density tensored with its reference marginal. -/
theorem zero_beta_gibbs_reference_reset_consumer (D : ℕ) (hD : 0 < D) (r : ℕ) (E : Fin D → ℝ)
    (n : ℕ) (hn : 0 < n) :
    ∀ ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      tensorLeft (thermalPowerChannel D hD E 0 n).map ρ
        = TensorGate (diagonalGibbsDensity D hD E 0) (Matrix.traceLeft ρ) := by
  intro ρ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hDne : ((D:ℕ) : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hacc : ∀ i j : Fin D, thermalAcceptance E 0 i j = 1 := by
    intro i j
    simp [thermalAcceptance]
  have hker : ∀ i j : Fin D, thermalKernel D E 0 i j = 1 / ((D:ℕ) : ℝ) := by
    intro i j
    by_cases hij : i = j
    · have h2 : ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E 0 i j' / ((D:ℕ) : ℝ)
          = ∑ j' ∈ Finset.univ.erase i, 1 / ((D:ℕ) : ℝ) :=
          Finset.sum_congr rfl fun j' _ => by rw [hacc i j']
      have h3 : ∑ j' ∈ Finset.univ.erase i, 1 / ((D:ℕ) : ℝ)
          = (((D:ℕ) : ℝ) - 1) / ((D:ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_sub (by omega : (1:ℕ) ≤ D)]
        push_cast
        ring
      show (if i = j then
            1 - ∑ j' ∈ Finset.univ.erase i, thermalAcceptance E 0 i j' / ((D:ℕ) : ℝ)
          else thermalAcceptance E 0 i j / ((D:ℕ) : ℝ)) = _
      rw [if_pos hij, h2, h3]
      field_simp
      ring
    · simp [thermalKernel, hij, hacc]
  have hp : ∀ j : Fin D, (diagonalGibbsDist D hD E 0).prob j = 1 / ((D:ℕ) : ℝ) := by
    intro j
    rw [diagonalGibbsDist_prob]
    have h1 : Real.exp (-(0:ℝ) * E j) = 1 := by simp
    have hZ : diagonalGibbsPartition D E 0 = ((D:ℕ) : ℝ) := by
      unfold diagonalGibbsPartition
      have h2 : ∑ j : Fin D, Real.exp (-(0:ℝ) * E j) = ∑ j : Fin D, (1:ℝ) :=
        Finset.sum_congr rfl fun j _ => by simp
      rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [h1, hZ]
  have hkπ : ∀ i x : Fin D, thermalKernel D E 0 i x
      = (diagonalGibbsDist D hD E 0).prob x := by
    intro i x
    rw [hker i x, hp x]
  rw [thermalPowerChannel_eq_reset hD E 0 hkπ m, tensorLeft_traceSmulLeft]

/-- For energies zero and one at inverse temperature `Real.log 2`, the Gibbs density is diagonal
with weights `2 / 3` and `1 / 3`. Starting in basis state zero, the displayed iterate has
trace-norm error `(2 / 3) * (1 / 4) ^ n`. -/
theorem two_level_gibbs_actual_consumer (n : ℕ) (hn : 0 < n) :
    let E := fun i : Fin 2 => if i = 0 then (0 : ℝ) else 1
    let β := Real.log 2
    diagonalGibbsDensity 2 (by omega) E β = !![2/3,0;0,1/3] ∧
    (thermalPowerChannel 2 (by omega) E β n).map (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) =
      Matrix.diagonal (fun i : Fin 2 => if i=0 then 2/3+(1/3)*(1/4 : ℂ)^n else 1/3-(1/3)*(1/4 : ℂ)^n) ∧
    Matrix.traceNorm ((thermalPowerChannel 2 (by omega) E β n).map (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) -
      diagonalGibbsDensity 2 (by omega) E β) = (2/3 : ℝ)*(1/4 : ℝ)^n := by
  intro E β
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hE0 : E 0 = 0 := by simp [E]
  have hE1 : E 1 = 1 := by simp [E]

  have hexpβ : Real.exp β = 2 := by
    show Real.exp (Real.log 2) = 2
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have ha01 : thermalAcceptance E β 0 1 = 1/2 := by
    show min 1 (Real.exp (-β*(E 1 - E 0))) = 1/2
    rw [hE1, hE0]
    norm_num
    rw [Real.exp_neg, hexpβ, inv_eq_one_div]
    norm_num
  have ha10 : thermalAcceptance E β 1 0 = 1 := by
    show min 1 (Real.exp (-β*(E 0 - E 1))) = 1
    have harg : -β*(E 0 - E 1) = β := by
      rw [hE1, hE0]
      ring
    rw [harg, hexpβ]
    norm_num
  have haii : ∀ i : Fin 2, thermalAcceptance E β i i = 1 := by
    intro i
    show min 1 (Real.exp (-β*(E i - E i))) = 1
    rw [sub_self, mul_zero, Real.exp_zero]
    norm_num
  have hk01 : thermalKernel 2 E β 0 1 = 1/4 := by
    rw [(diagonal_metropolis_transition_reversible 2 (by omega) E β).2.2.2 0 1
      (by decide : (0:Fin 2) ≠ 1), ha01]
    norm_num
  have hk10 : thermalKernel 2 E β 1 0 = 1/2 := by
    rw [(diagonal_metropolis_transition_reversible 2 (by omega) E β).2.2.2 1 0
      (by decide : (1:Fin 2) ≠ 0), ha10]
    norm_num
  have hrow : ∀ j : Fin 2, thermalKernel 2 E β j 0 + thermalKernel 2 E β j 1 = 1 := by
    intro j
    have h := (diagonal_metropolis_transition_reversible 2 (by omega) E β).1.2 j
    simpa [Fin.sum_univ_two] using h
  have hk00 : thermalKernel 2 E β 0 0 = 3/4 := by
    have h := hrow 0
    rw [hk01] at h
    linarith
  have hk11 : thermalKernel 2 E β 1 1 = 1/2 := by
    have h := hrow 1
    rw [hk10] at h
    linarith
  have hkall : ∀ i x : Fin 2, thermalKernel 2 E β i x
      = if i = 0 then (if x = 0 then 3/4 else 1/4) else (if x = 0 then 1/2 else 1/2) := by
    intro i x
    by_cases h1 : i = 0
    · subst h1
      by_cases h2 : x = 1
      · subst h2
        simp [hk01]
      · have hx0 : x = 0 := by
          fin_cases x <;> first | rfl | exact absurd rfl h2
        subst hx0
        simp [hk00]
    · have hi1 : i = 1 := by
        fin_cases i <;> first | exact absurd rfl h1 | rfl
      subst hi1
      by_cases h2 : x = 1
      · subst h2
        simp [hk11]
      · have hx0 : x = 0 := by
          fin_cases x <;> first | rfl | exact absurd rfl h2
        subst hx0
        simp [hk10]

  have hexpβ : Real.exp β = 2 := by
    show Real.exp (Real.log 2) = 2
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hZ : diagonalGibbsPartition 2 E β = 3 / 2 := by
    have h2 : diagonalGibbsPartition 2 E β = ∑ j : Fin 2, Real.exp (-β*(E j)) := rfl
    rw [h2, Fin.sum_univ_two]
    have e0 : Real.exp (-β*(E 0)) = 1 := by rw [hE0]; simp
    have e1 : Real.exp (-β*(E 1)) = 1/2 := by
      rw [hE1]
      simp only [mul_one, Real.exp_neg, hexpβ, inv_eq_one_div]
    rw [e0, e1]
    norm_num
  have hp0 : (diagonalGibbsDist 2 (by omega) E β).prob 0 = 2 / 3 := by
    rw [diagonalGibbsDist_prob, hE0]
    simp only [mul_zero, Real.exp_zero]
    rw [hZ]
    norm_num
  have hp1 : (diagonalGibbsDist 2 (by omega) E β).prob 1 = 1 / 3 := by
    rw [diagonalGibbsDist_prob, hE1]
    simp only [β, mul_one, Real.exp_neg,
      Real.exp_log (by norm_num : (0:ℝ) < 2), inv_eq_one_div]
    rw [hZ]
    norm_num
  have h1 : diagonalGibbsDensity 2 (by omega) E β = !![2/3,0;0,1/3] := by
    rw [(diagonal_gibbs_weight_density 2 (by omega) E β).2.1]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.diagonal_apply, hp0, hp1]
  have h2 : (thermalPowerChannel 2 (by omega) E β (m+1)).map (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) =
      Matrix.diagonal (fun i : Fin 2 => if i=0 then 2/3+(1/3)*(1/4 : ℂ)^(m+1) else 1/3-(1/3)*(1/4 : ℂ)^(m+1)) := by
    rw [thermalPowerChannel_eq_kernelDiagMap 2 (by omega) E β m, kernelDiagMap_apply]
    have hσ : ∀ i : Fin 2, (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) i i
        = if i = 0 then (1:ℂ) else 0 := by
      intro i
      fin_cases i <;> simp [outerProduct, Qatlib.Foundations.PureStateMath.Ket]

    have hind : ∀ (kk : ℕ) (i x : Fin 2),
        kernelPow (thermalKernel 2 E β) kk i x
          = if i = 0 ∧ x = 0 then 2/3 + (1/3)*((1/4:ℝ)^kk)
          else if i = 0 ∧ x = 1 then 1/3 - (1/3)*((1/4:ℝ)^kk)
          else if i = 1 ∧ x = 0 then 2/3 - (2/3)*((1/4:ℝ)^kk)
          else 1/3 + (2/3)*((1/4:ℝ)^kk) := by
      intro kk
      induction kk with
      | zero =>
        intro i x
        rw [kernelPow_zero]
        fin_cases i <;> fin_cases x <;> simp <;> norm_num
      | succ kk ih =>
        intro i x
        have hexp : kernelPow (thermalKernel 2 E β) (kk+1) i x
            = ∑ m' : Fin 2, thermalKernel 2 E β i m' * kernelPow (thermalKernel 2 E β) kk m' x :=
          rfl
        rw [hexp, Fin.sum_univ_two]
        simp only [hkall, ih]
        fin_cases i <;> fin_cases x <;> simp <;> field_simp <;> ring
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [Matrix.diagonal_apply, hσ, hind, Matrix.sum_apply]
  refine ⟨h1, h2, ?_⟩
  rw [h2, h1]
  have hdiff : Matrix.diagonal (fun i : Fin 2 =>
        if i=0 then 2/3+(1/3)*(1/4 : ℂ)^(m+1) else 1/3-(1/3)*(1/4 : ℂ)^(m+1)) - !![2/3,0;0,1/3]
      = (((1/3)*((1/4:ℝ)^(m+1)) : ℝ) : ℂ) • Matrix.diagonal (![(1:ℂ), -1]) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply] <;>
      push_cast <;> norm_num
  rw [hdiff, Matrix.traceNorm_smul]
  open MatrixOrder in
  have htn : Matrix.traceNorm (Matrix.diagonal (![(1:ℂ), -1])) = 2 := by
    have hsq : (Matrix.diagonal (![(1:ℂ), -1]))ᴴ * Matrix.diagonal (![(1:ℂ), -1]) = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
    unfold Matrix.traceNorm
    rw [hsq, CFC.sqrt_one]
    simp
  rw [htn]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1/3)*((1/4:ℝ)^(m+1)))]
  push_cast
  ring

end Qatlib.Concepts.AdversaryBounds.AdvDuality
