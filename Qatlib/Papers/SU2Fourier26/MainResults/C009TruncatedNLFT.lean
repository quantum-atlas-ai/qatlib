/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceNLFTModel
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lemma 5: convergence of the truncated NLFT data (c009)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Lemma 5, p.12.

There exists `n₀ = n₀(a, b)` such that for `n > n₀` the truncated NLFT data
`aₙ, bₙ` (defined as the solution of the truncated Riemann–Hilbert system
`Pₙ C Pₙ (aₙ, bₙ)ᵀ = (1/a*ₙ(0), 0)ᵀ`, (3.1)–(3.2)) lie in `A_w` and converge
to `a, b` in the `A_w` norm.

The paper's proof (p.12) writes the difference of solutions as

`(Pₙ C Pₙ)⁻¹ - (P₊ C P₊)⁻¹ = (Pₙ C Pₙ)⁻¹ (P₊ C P₊ - Pₙ C Pₙ)(P₊ C P₊)⁻¹`,

and uses the uniform inverse bound of Lemma 4 together with `(P₊ - Pₙ) v → 0`
in `Y_w`.  The operator identity behind this is the general continuity of
inversion at a unit.

Here we formalize that continuity step: in a normed ring with summable geometric
series, if a family of units `uₙ` converges to a unit `v`, then the inverses
`uₙ⁻¹` converge to `v⁻¹`.  This is exactly the algebraic mechanism that makes the
right-hand side of the display above go to `0`.  The specific sequences `aₙ, bₙ`
and the `A_w`-norm convergence are *not* formalized (no topology is installed on
`YCoeff` and the truncated system is only described implicitly).

The full statement is recorded for reference:

```
theorem truncated_nlft_converges (W : StrongBeurlingWeight) (a b : CircleT → ℂ)
    (h : OuterSetup W a b) :
    ∃ n₀ : ℤ, ∃ an bn : ℤ → CircleT → ℂ,
      (∀ n : ℤ, n₀ < n → MemAW W (an n) ∧ MemAW W (bn n)) ∧
        Tendsto (fun n : ℤ => AWnorm W (fun x => an n x - a x)) atTop (nhds 0) ∧
          Tendsto (fun n : ℤ => AWnorm W (fun x => bn n x - b x)) atTop (nhds 0)
```
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- Continuity of inversion at a unit (the mechanism of arXiv:2603.02021v1,
Lemma 5, p.12): if a sequence of units `uₙ` converges to the unit `v` in a normed
ring with summable geometric series, then the inverses converge to `v⁻¹`. -/
theorem tendsto_inv_of_tendsto_units {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {u : ℕ → Rˣ} {v : Rˣ} (h : Tendsto (fun n => (u n : R)) atTop (nhds (v : R))) :
    Tendsto (fun n => (((u n)⁻¹ : Rˣ) : R)) atTop (nhds (((v⁻¹ : Rˣ) : R))) := by
  have hc : Tendsto (fun n => Ring.inverse ((u n) : R)) atTop
      (nhds (Ring.inverse ((v : R)))) :=
    (NormedRing.inverse_continuousAt v).tendsto.comp h
  simpa only [Ring.inverse_unit] using hc

end

end Qatlib.Papers.SU2Fourier26.MainResults
