/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation13Stat

/-!
# Cubic identity for projected amplification

`equation13` proves the cubic expression for projected oblivious amplitude amplification on
vectors fixed by the projection. This algebraic identity underlies the robustness analysis in
[BerryEtAl2015Taylor].

## Main statements

* `equation13`: The projected cubic amplification formula.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix

/-- For a star projection and a unitary, projected oblivious amplification on a vector in the
projection range equals the stated cubic expression in the projected unitary. See
[BerryEtAl2015Taylor]. -/
theorem equation13 : Equation13 := by
  intro I _ _ P W hP hW ψ hψ
  have h := congrArg (fun M : Matrix I I ℂ => M *ᵥ ψ)
    (projected_obliviousAmplitudeAmplification_of_idempotent P W
      hP.isIdempotentElem hW)
  have hpoly : 3 * (P * W * P) - 4 * (P * W * P * star W * P * W * P) =
      (3 * (P * W) - 4 * (P * W * P * Wᴴ * P * W)) * P := by
    rw [Matrix.star_eq_conjTranspose]
    noncomm_ring
  rw [hpoly] at h
  simpa only [← Matrix.mulVec_mulVec, hψ] using h

end Qatlib.Concepts.CoherentSim.ResetDiscard
