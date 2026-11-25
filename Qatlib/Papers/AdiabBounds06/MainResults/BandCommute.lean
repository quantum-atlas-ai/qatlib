/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabBounds06.MainResults.Intertwining
public import Qatlib.Papers.AdiabBounds06.MainResults.Twiddle

@[expose] public section

/-!
# Commutation of the Hamiltonian with the band projection

The spectral-band data of [JansenRuskaiSeiler2007] describes a projection `P` onto a band of
eigenvalues of `H`, decomposed into orthogonal eigenprojections `Pj`. Because every `Pj` is an
eigenprojection of `H`, the total band projection commutes with `H`. This removes the separate
commutation hypothesis from the intertwining statement of Lemma 1.

## Main statements

* `BandData.H_mul_P`: spectral-band data gives `H * P = P * H`.
* `intertwining_of_bandData`: Lemma 1 with the commutation hypothesis derived from spectral-band
  data rather than assumed.

## References

* [Jansen et al., 2007][JansenRuskaiSeiler2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

/-- Spectral-band data forces the Hamiltonian to commute with the total band projection:
`H * P = P * H`. Each band component is an eigenprojection of `H`, so summing over the
orthogonal decomposition `P = ∑ j, Pj` gives the claim. This is the commutation used in
Lemma 1 of [JansenRuskaiSeiler2007]. -/
theorem BandData.H_mul_P {H : Matrix (Fin n) (Fin n) ℂ}
    (D : Qatlib.Papers.AdiabBounds06.MainResults.BandData H) :
    H * D.P = D.P * H := by
  rw [← D.Pj_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [D.H_Pj j, D.Pj_H j]

/-- The intertwining property of Lemma 1 of [JansenRuskaiSeiler2007] with the commutation
hypothesis derived from spectral-band data. If `P s` is the band projection of `H s` for every
parameter `s`, then the adiabatic comparison propagator transports `P 0` to `P s`. The remaining
hypotheses are differentiability of `P`, continuity of `H`, `P`, and `Pdot`, exactly as in the
matrix ODE uniqueness argument. -/
theorem intertwining_of_bandData (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (D : ∀ s, Qatlib.Papers.AdiabBounds06.MainResults.BandData (H s))
    (hP : ∀ s, (D s).P = P s)
    (hder : ∀ s, HasDerivAt P (Pdot s) s)
    (hHc : Continuous H) (hPc : Continuous P) (hPdc : Continuous Pdot) :
    ∀ s, Qatlib.Papers.AdiabBounds06.MainResults.UτA τ H P Pdot s * P 0
      = P s * Qatlib.Papers.AdiabBounds06.MainResults.UτA τ H P Pdot s := by
  refine Qatlib.Papers.AdiabBounds06.MainResults.intertwining τ H P Pdot ?_ ?_ hder hHc hPc hPdc
  · intro s
    have hcomm := BandData.H_mul_P (D s)
    rwa [hP s] at hcomm
  · intro s
    have hproj := (D s).P_proj.1
    rwa [hP s] at hproj

end Qatlib.Papers.AdiabBounds06.MainResults
