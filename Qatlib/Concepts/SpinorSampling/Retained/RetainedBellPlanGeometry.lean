/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellDenseTail

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Retained Bell Plan Geometry

Retained Bell Plan Geometry constructions and identities for Spinor Sampling.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators

-- The identity branch is justified by the actual periodic shift, not the
-- number of observed matches or the cardinality of an unrelated site type.
/-- Along any axis of a periodic grid of side length one or two, the double shift is the identity permutation. -/
theorem periodic_double_shift_small_side (d N : ℕ) [NeZero N] (j : Fin d)
    (hN : N≤2) : periodicDoubleShift d N j=Equiv.refl (Fin d → Fin N) := by
  have hpos : 0<N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcases : N=1 ∨ N=2 := by omega
  have htwo : (2 : ZMod N)=0 := by
    rcases hcases with h | h <;> subst N <;> decide
  apply Equiv.ext
  intro x
  funext k
  apply (ZMod.finEquiv N).injective
  rw [periodic_double_shift_coordinates]
  split_ifs <;> simp [htwo]

/-- Matching each site with itself gives zero mean Bell hit probability for any spinor field. -/
theorem bell_mean_identity {S : Type} [Fintype S] (a b c k : S → ℝ) :
    bellMean a b c k (Equiv.refl S)=0 := by
  simp [bellMean,populationMean,bellProbability,determinant,mul_comm]

/-- A periodic double shift on a side of length one or two has zero Bell mean for any spinor field. -/
theorem periodic_bell_mean_small_side (d N : ℕ) [NeZero N] (j : Fin d)
    (a b c k : (Fin d → Fin N) → ℝ) (hN : N≤2) :
    bellMean a b c k (periodicDoubleShift d N j)=0 := by
  rw [periodic_double_shift_small_side d N j hN]
  exact bell_mean_identity a b c k

-- The zero-copy midpoint is p/2, whereas the identity output is zero.
/-- If the true mean lies in [0, p] and p ≤ 2ε, the rational midpoint p/2 is within ε of the mean. -/
theorem bell_midpoint_accuracy (p ε : ℚ) (μ : ℝ) (hμ0 : 0≤μ)
    (hμ : μ≤(p : ℝ)) (hmid : p≤2*ε) : |((p/2 : ℚ) : ℝ)-μ|≤(ε : ℝ) := by
  have hmidR : (p : ℝ)≤2*(ε : ℝ) := by exact_mod_cast hmid
  push_cast
  rw [abs_le]
  constructor <;> linarith

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.periodic_double_shift_small_side
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_mean_identity
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.periodic_bell_mean_small_side
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_midpoint_accuracy
