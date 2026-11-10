/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.OverlapGapGoh26.Resources.Faults

def faultLaw (e : ℝ) : Measure Bool :=
  ENNReal.ofReal e • Measure.dirac true+ENNReal.ofReal (1-e) • Measure.dirac false

instance faultLaw_finite (e : ℝ) : IsFiniteMeasure (faultLaw e) := by
  constructor
  simp only [faultLaw,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem,
    Set.mem_univ,smul_eq_mul,mul_one]
  finiteness

theorem faultLaw_probability (e : ℝ) (he : 0≤e) (he1 : e≤1) : IsProbabilityMeasure (faultLaw e) := by
  constructor
  simp only [faultLaw,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem,
    Set.mem_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add he (by linarith),show e+(1-e)=1 by ring,ENNReal.ofReal_one]

theorem faultLaw_false (e : ℝ) : faultLaw e {false}=ENNReal.ofReal (1-e) := by
  simp [faultLaw]

def independentLaw (e : ℝ) (G : ℕ) : Measure (Fin G → Bool) :=
  Measure.pi (fun _ => faultLaw e)

theorem actual_no_fault_probability (e : ℝ) (he1 : e≤1) (G : ℕ) :
    independentLaw e G {x | ∀ i,x i=false}=ENNReal.ofReal ((1-e)^G) := by
  have he : {x : Fin G → Bool | ∀ i,x i=false}=Set.pi Set.univ (fun _ => ({false} : Set Bool)) := by
    ext x
    simp
  rw [independentLaw,he,Measure.pi_pi]
  simp only [faultLaw_false,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by linarith : 0≤1-e) G).symm

end Qatlib.Papers.OverlapGapGoh26.Resources.Faults
