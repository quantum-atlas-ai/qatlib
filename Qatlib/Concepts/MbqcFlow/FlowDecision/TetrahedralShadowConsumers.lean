/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowStatistics
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder ComplexConjugate Kronecker

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem trace_pauliY_tetraSnapshot (a : Fin 4) :
    (Matrix.trace (pauliY * tetraSnapshot a)).re = Real.sqrt 3 * (tetraSigns a 1 : ℝ) := by
  have htY : Matrix.trace pauliY = 0 := trace_pauliMatrix 1
  have hcomb : Matrix.trace (pauliY * tetraSigmaComb a)
      = (2:ℂ) * ((tetraSigns a 1 / Real.sqrt 3 : ℝ) : ℂ) := by
    rw [show pauliY = pauliMatrix 1 from rfl, tetraSigmaComb, Matrix.mul_sum,
      Matrix.trace_sum]
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_pauliMatrix_mul, mul_ite,
        mul_zero])]
    rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin 3)) 1
      (fun k => ((tetraSigns a k / Real.sqrt 3 : ℝ) : ℂ) * 2)]
    simp only [Finset.mem_univ, if_true, mul_comm]
  have hprojc : Matrix.trace (pauliY * tetraProjector a)
      = ((tetraSigns a 1 / Real.sqrt 3 : ℝ) : ℂ) := by
    rw [tetraProjector, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul,
      smul_eq_mul, Matrix.trace_add, htY, zero_add, hcomb]
    ring
  have hmulc : Matrix.trace (pauliY * ((3:ℂ) • tetraProjector a - 1))
      = (3:ℂ) * ((tetraSigns a 1 / Real.sqrt 3 : ℝ) : ℂ) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_one, htY, sub_zero, hprojc]
  rw [tetraSnapshot, hmulc]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  ring

theorem tetrahedral_mixed_state_and_y_observable_consumers
    (hρ : IsDensityOperator ((1/2:ℂ) • (1:Operator 2))) :
    (∀ a, (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).prob a = 1/4) ∧
      (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).expect (tetraStatistic pauliY) = 0 ∧
      (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).expect
          (fun a => (tetraStatistic pauliY a)^2) = 3 := by
  have hprob : ∀ a : Fin 4,
      (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).prob a = 1/4 := by
    intro a
    rw [(tetrahedral_actual_record_born_law ((1/2:ℂ) • (1:Operator 2)) hρ a).2.2]
    have htr : Matrix.trace
        (tetraProjector a * ((1/2:ℂ) • (1:Operator 2))) = (1/2:ℂ) := by
      rw [Matrix.mul_smul]
      simp [tetraProjector_trace]
    rw [htr]
    norm_num
  have hstat : ∀ a : Fin 4, tetraStatistic pauliY a = Real.sqrt 3 * (tetraSigns a 1 : ℝ) :=
    fun a => trace_pauliY_tetraSnapshot a
  refine ⟨hprob, ?_, ?_⟩
  · show ∑ a : Fin 4, (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).prob a *
        tetraStatistic pauliY a = 0
    have hrew : ∀ a : Fin 4, (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).prob a *
        tetraStatistic pauliY a = (1/4) * (Real.sqrt 3 * (tetraSigns a 1 : ℝ)) := by
      intro a
      rw [hstat a, hprob a]
    rw [Finset.sum_congr rfl (fun a _ => hrew a), ← Finset.mul_sum, ← Finset.mul_sum,
      tetraSigns_col_sum 1]
    norm_num
  · show ∑ a : Fin 4, (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).prob a *
        (tetraStatistic pauliY a)^2 = 3
    have hrew : ∀ a : Fin 4, (tetraRecordLaw ((1/2:ℂ) • (1:Operator 2)) hρ).prob a *
        (tetraStatistic pauliY a)^2 = (1/4) * (3:ℝ) := by
      intro a
      rw [hstat a, hprob a, mul_pow, pow_two]
      have hn : (tetraSigns a 1)^2 = 1 := by
        fin_cases a <;> simp [tetraSigns]
      rw [hn, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      ring
    rw [Finset.sum_congr rfl (fun a _ => hrew a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num

set_option maxHeartbeats 10000000 in

theorem tetrahedral_xyz_joint_actual_consumer (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (m : ℕ) (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) :
    (∑ ω ∈ @Finset.univ.filter (Fin m → Fin 4)
        (fun ω => ∃ z : Fin 3, ε ≤ |tetraSampleMean (pauliMatrix z) m ω
            - (Matrix.trace (@HMul.hMul (Matrix (Fin 2) (Fin 2) ℂ) (Operator 2)
                (Matrix (Fin 2) (Fin 2) ℂ) inferInstance (pauliMatrix z) ρ)).re|)
        (fun a => @Fintype.decidableExistsFintype (Fin 3)
            (fun z => ε ≤
              |tetraSampleMean (pauliMatrix z) m a
                  - (Matrix.trace (@HMul.hMul (Matrix (Fin 2) (Fin 2) ℂ) (Operator 2)
                      (Matrix (Fin 2) (Fin 2) ℂ) inferInstance (pauliMatrix z) ρ)).re|)
            (fun z => inferInstance) (Fin.fintype 3)),
        (tetraFreshLaw ρ hρ m).prob ω)
      ≤ (∑ z : Fin 3, 9*(OperatorSpectralNorm (pauliMatrix z))^2)/((m:ℝ)*ε^2) :=
  @tetrahedral_many_observable_actual_mean_bound (Fin 3) (Fin.fintype 3) (instDecidableEqFin 3)
    ρ hρ pauliMatrix m ε hm hε (fun z => pauliMatrix_conjTranspose z)

theorem tetrahedral_zero_boundary (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (A : Operator 2) (ω : Fin 0 → Fin 4) :
    (tetraFreshLaw ρ hρ 0).prob ω = 1 ∧ tetraSampleMean A 0 ω = 0 := by
  refine ⟨?_, ?_⟩
  · show (∏ i : Fin 0, (tetraRecordLaw ρ hρ).prob (ω i)) = 1
    simp
  · show (∑ j : Fin 0, tetraStatistic A (ω j)) / ((0:ℕ):ℝ) = 0
    norm_num [Fin.sum_univ_zero]

end Qatlib.Concepts.MbqcFlow.FlowDecision
