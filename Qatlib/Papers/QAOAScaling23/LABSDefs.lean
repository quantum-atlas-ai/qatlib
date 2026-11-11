/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.SequenceEnergy.Aperiodic

/-!
# Binary LABS energy and merit factor

Boolean sequences are interpreted as spins to define the aperiodic correlations
`lagCorrelation`, squared sidelobe `energy`, and `meritFactor`. The module proves positivity of
energy for length at least two, antitonicity of merit factor with respect to energy, and the
exact length-three energy expansion.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `one_le_energy`: The squared sidelobe energy of a Boolean sequence of length at least two is
  at least one.
* `energy_three`: The length-three LABS energy equals `3 + 2 * printed_core s`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.LABSDefs
open scoped Classical
open Qatlib.Foundations.SequenceEnergy.Aperiodic

/-- Maps `false` to spin `1` and `true` to spin `-1`. -/
def spin (b : Bool) : ℝ := if b then -1 else 1

/-- The aperiodic autocorrelation at lag `k` of the spin sequence encoded by `s`. -/
def lagCorrelation {N : ℕ} (s : Fin N → Bool) (k : Fin N) : ℝ :=
  correlation (fun i => spin (s i)) k

/-- The squared sidelobe energy of the spin sequence encoded by `s`. -/
def energy {N : ℕ} (s : Fin N → Bool) : ℝ :=
  squaredSidelobe (fun i => spin (s i))

/-- The LABS merit factor `N^2 / (2 * energy s)` of a Boolean sequence. -/
def meritFactor {N : ℕ} (s : Fin N → Bool) : ℝ := (N:ℝ)^2/(2*energy s)

/-- Every Boolean spin has square one. -/
theorem spin_sq (b : Bool) : spin b^2=1 := by cases b <;> norm_num [spin]

/-- The squared sidelobe energy of every Boolean sequence is nonnegative. -/
theorem energy_nonneg {N : ℕ} (s : Fin N → Bool) : 0≤energy s := by
  exact squaredSidelobe_nonneg _

/-- For a nonempty sequence, the autocorrelation at lag `N - 1` is the product of its first and
last spins. -/
theorem last_lag {N : ℕ} (hN : 0<N) (s : Fin N → Bool) :
    lagCorrelation s ⟨N-1,by omega⟩=spin (s ⟨0,hN⟩)*spin (s ⟨N-1,by omega⟩) := by
  exact correlation_last hN _

/-- The squared sidelobe energy of a Boolean sequence of length at least two is at least one.
See [ShaydulinEtAl2024]. -/
theorem one_le_energy {N : ℕ} (hN : 2≤N) (s : Fin N → Bool) : 1≤energy s := by
  have h:=endpoint_sq_le_sidelobe hN (fun i => spin (s i))
  simpa only [mul_pow,spin_sq,one_mul] using! h

/-- For sequences of length at least two, an energy comparison reverses the corresponding
merit-factor comparison. See [ShaydulinEtAl2024]. -/
theorem meritFactor_antitone {N : ℕ} (hN : 2≤N) (s t : Fin N → Bool)
    (hst : energy s≤energy t) : meritFactor t≤meritFactor s := by
  unfold meritFactor
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [one_le_energy hN s])
  linarith

/-- The product of the first and third spins in a length-three Boolean sequence. -/
def printed_core (s : Fin 3 → Bool) : ℝ := spin (s 0)*spin (s 2)

/-- The length-three LABS energy equals `3 + 2 * printed_core s`. See [ShaydulinEtAl2024]. -/
theorem energy_three (s : Fin 3 → Bool) : energy s=3+2*printed_core s := by
  let a:=s 0
  let b:=s 1
  let c:=s 2
  have hs : s=![a,b,c] := by funext i; fin_cases i <;> rfl
  rw [hs]
  cases ha : a <;> cases hb : b <;> cases hc : c <;>
    norm_num [energy,squaredSidelobe,correlation,printed_core,Fin.sum_univ_succ,spin,ha,hb,hc,Matrix.cons_val_two]
end Qatlib.Papers.QAOAScaling23.LABSDefs
