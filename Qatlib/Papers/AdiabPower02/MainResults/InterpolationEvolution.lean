/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic
public import Qatlib.Papers.AdiabPower02.MainResults.Lemma1
public import Qatlib.Papers.AdiabPower02.MainResults.Theorem1.Approximation
public import Qatlib.Papers.AdiabPower02.MainResults.Theorem1.Basic

@[expose] public section

/-!
# Evolution error of the ceiling-grid Hamiltonian

Section 4 of [VanDamMoscaVazirani2001] replaces the linear adiabatic path by a Hamiltonian that is
constant on each of the `r` intervals of length `T / r`. The pointwise difference of the two
Hamiltonians is at most `‖Hf - H0‖ / r`
(`Qatlib.Papers.AdiabPower02.MainResults.Theorem1.interpolation_step_bound`), and the evolution
stability estimate `Qatlib.Papers.AdiabPower02.MainResults.Lemma1.lemma1` turns that estimate
into a bound `Real.sqrt (2 * T * (‖Hf - H0‖ / r))` on the distance of the two unitaries:
`interpolation_evolution_bound`. This module supplies that bridge together with the ceiling-grid
Hamiltonian `ceilingGridPath` and the pointwise estimate it satisfies.

The ceiling grid is a step function whose values jump by `(Hf - H0) / r` at the grid times, so it
does not meet the continuity hypothesis of `interpolation_evolution_bound`. The paper defines the
approximating transformation as a product of `r` exponentials; identifying that product with the
ordered evolution of a piecewise-constant generator is outside the scope of this module.

## Main statements

* `interpolation_evolution_bound`: evolution difference bound for a generator within
  `‖Hf - H0‖ / r` of the linear path.
* `ceilingGridPath_pointwise_bound`: the ceiling grid differs from the path by at most
  `‖Hf - H0‖ / r` at nonnegative times.
* `ceilingGridPath_zero`, `ceilingGridPath_end`: the grid starts at `H0` and ends at `Hf`.
* `ceilingGridPath_isHermitian`: the grid consists of Hermitian matrices.
* `continuous_adiabaticPath`, `adiabaticPath_isHermitian`: the path supplies the shape hypotheses
  of `interpolation_evolution_bound`.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001], Section 4,
  [arXiv:quant-ph/0206003v1](https://arxiv.org/abs/quant-ph/0206003v1)
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabPower02.MainResults

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Papers.AdiabPower02.MainResults.Theorem1

namespace Theorem1

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The linear path `t ↦ (1 - t / T) • H0 + (t / T) • Hf` is continuous in `t`. -/
theorem continuous_adiabaticPath (H0 Hf : Matrix I I ℂ) (T : ℝ) :
    Continuous (adiabaticPath H0 Hf T) := by
  unfold adiabaticPath
  fun_prop

/-- The linear path consists of Hermitian matrices when both endpoints are Hermitian. -/
theorem adiabaticPath_isHermitian (H0 Hf : Matrix I I ℂ) (T : ℝ)
    (h0 : H0.IsHermitian) (hf : Hf.IsHermitian) :
    ∀ u, (adiabaticPath H0 Hf T u).IsHermitian := by
  intro u
  have h1 : IsSelfAdjoint (1 - u / T : ℝ) := by simp [IsSelfAdjoint]
  have h2 : IsSelfAdjoint (u / T : ℝ) := by simp [IsSelfAdjoint]
  simpa [adiabaticPath] using (Matrix.IsHermitian.smul h0 h1).add (Matrix.IsHermitian.smul hf h2)

/-- The Hamiltonian that is constant on each of the `r` intervals of length `T / r`, taking the
value of the linear path at the right endpoint `⌈r * t / T⌉ / r` of the interval containing `t`. -/
def ceilingGridPath (H0 Hf : Matrix I I ℂ) (T : ℝ) (r : ℕ) : ℝ → Matrix I I ℂ :=
  fun t => (1 - ((⌈(r : ℝ) * t / T⌉₊ : ℕ) : ℝ) / r) • H0
    + (((⌈(r : ℝ) * t / T⌉₊ : ℕ) : ℝ) / r) • Hf

omit [Fintype I] [DecidableEq I] in
/-- The ceiling grid starts at the initial Hamiltonian. -/
@[simp] theorem ceilingGridPath_zero (H0 Hf : Matrix I I ℂ) (T : ℝ) (r : ℕ) :
    ceilingGridPath H0 Hf T r 0 = H0 := by
  simp [ceilingGridPath]

omit [Fintype I] [DecidableEq I] in
/-- For positive total time and positive step count, the ceiling grid ends at the final
Hamiltonian. -/
theorem ceilingGridPath_end (H0 Hf : Matrix I I ℂ) {T : ℝ} {r : ℕ}
    (hT : T ≠ 0) (hr : 0 < r) : ceilingGridPath H0 Hf T r T = Hf := by
  have hrR : (r : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr)
  have hrt : (r : ℝ) * T / T = (r : ℝ) := by field_simp
  have hceil : ⌈((r : ℝ))⌉₊ = r := Nat.ceil_natCast r
  simp only [ceilingGridPath, hrt, hceil]
  rw [div_self hrR, sub_self, zero_smul, one_smul, zero_add]

/-- At nonnegative times the ceiling grid differs from the linear path by at most
`‖Hf - H0‖ / r` [VanDamMoscaVazirani2001]. -/
theorem ceilingGridPath_pointwise_bound (H0 Hf : Matrix I I ℂ) {T : ℝ} (r : ℕ)
    (hr : 0 < r) (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t) :
    ‖adiabaticPath H0 Hf T t - ceilingGridPath H0 Hf T r t‖ ≤ ‖Hf - H0‖ / r := by
  simpa [adiabaticPath, ceilingGridPath] using
    interpolation_step_bound (I := I) H0 Hf (T := T) (t := t) r hr hT ht

omit [Fintype I] [DecidableEq I] in
/-- The ceiling grid consists of Hermitian matrices when both endpoints are Hermitian. -/
theorem ceilingGridPath_isHermitian (H0 Hf : Matrix I I ℂ) (T : ℝ) (r : ℕ)
    (h0 : H0.IsHermitian) (hf : Hf.IsHermitian) :
    ∀ u, (ceilingGridPath H0 Hf T r u).IsHermitian := by
  intro u
  have h1 : IsSelfAdjoint (1 - ((⌈(r : ℝ) * u / T⌉₊ : ℕ) : ℝ) / r : ℝ) := by
    simp [IsSelfAdjoint]
  have h2 : IsSelfAdjoint (((⌈(r : ℝ) * u / T⌉₊ : ℕ) : ℝ) / r : ℝ) := by
    simp [IsSelfAdjoint]
  simpa [ceilingGridPath] using (Matrix.IsHermitian.smul h0 h1).add (Matrix.IsHermitian.smul hf h2)

/-- If two Hamiltonian families differ pointwise by at most `‖Hf - H0‖ / r`, the ordered
evolutions they generate over nonnegative time `T` differ by at most the square root of
`2 * T * (‖Hf - H0‖ / r)`. This applies Lemma 1 to the linear adiabatic path and is the first
step of Section 4 of [VanDamMoscaVazirani2001]. -/
theorem interpolation_evolution_bound
    (H0 Hf : Matrix I I ℂ) (H' : ℝ → Matrix I I ℂ) (T : ℝ) (r : ℕ)
    (hHc : Continuous (adiabaticPath H0 Hf T)) (hH'c : Continuous H')
    (hHerm : ∀ u, (adiabaticPath H0 Hf T u).IsHermitian)
    (hHerm' : ∀ u, (H' u).IsHermitian)
    (hT : 0 ≤ T) (hr : 0 < r)
    (hbound : ∀ u, ‖adiabaticPath H0 Hf T u - H' u‖ ≤ ‖Hf - H0‖ / r) :
    ‖orderedEvolution (fun u => Complex.I • adiabaticPath H0 Hf T u) 0 T
        - orderedEvolution (fun u => Complex.I • H' u) 0 T‖
      ≤ Real.sqrt (2 * T * (‖Hf - H0‖ / r)) :=
  Qatlib.Papers.AdiabPower02.MainResults.Lemma1.lemma1
    (H := adiabaticPath H0 Hf T) (H' := H') (T := T) (δ := ‖Hf - H0‖ / r)
    hHc hH'c hHerm hHerm' hT
    (div_nonneg (norm_nonneg _) (le_of_lt (by exact_mod_cast hr))) hbound

end Theorem1
end Qatlib.Papers.AdiabPower02.MainResults
