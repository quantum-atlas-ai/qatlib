/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReinfLearning16.MainResults.GibbsFreeEnergy.GibbsFreeEnergyGradient

set_option backward.isDefEq.respectTransparency false

/-!
# TD(0) Update Rules for the Clamped Quantum Boltzmann Machine

This module formalizes the TD(0) weight-update rules of
[Crawford et al., 2016][CrawfordEtAl2016] (§§2.7–2.8, Eqs. (14)–(15), pp. 12–13).

Combining the general TD(0) step `Δw = -ε · δ · ∂F/∂w`, the free-energy gradient
identity `∂F/∂w = ⟨∂H/∂w⟩` (`freeEnergy_hasDerivAt_gibbsExpectation`), and real-scalar
homogeneity of the Gibbs expectation yields:

* **Eq. (14)** (`td0Update_visible`, `td0Update_visible_full`):
  `Δw_vh = ε · δ · v · ⟨σ^z_h⟩`,
* **Eq. (15)** (`td0Update_hidden`, `td0Update_hidden_full`):
  `Δw_hh' = ε · δ · ⟨σ^z_h σ^z_h'⟩`,
* `td0_update_rules`: combined statement of Eqs. (14)–(15).

## Main statements

* `td0Update_visible`
* `td0Update_hidden`
* `td0Update_visible_full`
* `td0Update_hidden_full`
* `td0_update_rules`

## References

* [Crawford et al., 2016][CrawfordEtAl2016]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.ReinfLearning16.MainResults.TD0Update

open Qatlib.Papers.ReinfLearning16.MainResults.GibbsFreeEnergy

variable {I : Type} [Fintype I] [DecidableEq I]

/-! ## The TD(0) update map -/

/-- The TD(0) TD error `δ = r_n(s_n,a_n) + γ Q(s_{n+1},a_{n+1}) - Q(s_n,a_n)` of
Section 2.6 / Eq (14)–(15), p.12–13.  (`a_{n+1} = argmax_a Q(s_{n+1},a)` is folded
into the supplied `Qnext`.) -/
def td0Error (r γ Qnext Qcur : ℝ) : ℝ := r + γ * Qnext - Qcur

/-- The general TD(0) weight update `Δw = -ε · δ · ∂F/∂w` (paper, between Eq (13)
and Eq (14), p.12).  `dFdw` is the partial derivative of the free energy in that
weight. -/
def td0WeightUpdate (ε δ dFdw : ℝ) : ℝ := -ε * δ * dFdw

/-! ## Equation (14): visible–hidden weights `w_vh` -/

/-- **Eq (14)** (p.12–13): the TD(0) update for a visible–hidden weight `w_vh`.
The Hamiltonian term `-w_vh · v · σ^z_h` makes the free-energy gradient
`∂F/∂w_vh = ⟨-v σ^z_h⟩ = -v ⟨σ^z_h⟩` (Gibbs-expectation homogeneity), and
`Δw = -ε δ ∂F/∂w` then becomes `ε δ v ⟨σ^z_h⟩`.  Pure algebra given the gradient
substitution `∂F/∂w_vh = ⟨-v σ^z_h⟩`. -/
theorem td0Update_visible
    (β : ℝ) (H σz : Matrix I I ℂ) (v ε δ : ℝ) :
    td0WeightUpdate ε δ (gibbsExpectation β H ((-(v : ℂ)) • σz))
      = ε * δ * v * gibbsExpectation β H σz := by
  have hv : (-(v : ℂ)) = ((-v : ℝ) : ℂ) := by push_cast; ring
  rw [hv, gibbsExpectation_smul]
  unfold td0WeightUpdate
  ring

/-! ## Equation (15): hidden–hidden weights `w_hh'` -/

/-- **Eq (15)** (p.13): the TD(0) update for a hidden–hidden weight `w_hh'`.
The Hamiltonian term `-w_hh' · σ^z_h σ^z_h'` (here `σhh := σ^z_h σ^z_h'` as one
observable) makes the free-energy gradient `∂F/∂w_hh' = ⟨-σ^z_h σ^z_h'⟩`, and
`Δw = -ε δ ∂F/∂w` becomes `ε δ ⟨σ^z_h σ^z_h'⟩`.  Pure algebra given the gradient
substitution `∂F/∂w_hh' = ⟨-σhh⟩`. -/
theorem td0Update_hidden
    (β : ℝ) (H σhh : Matrix I I ℂ) (ε δ : ℝ) :
    td0WeightUpdate ε δ (gibbsExpectation β H ((-1 : ℂ) • σhh))
      = ε * δ * gibbsExpectation β H σhh := by
  have h1 : (-1 : ℂ) = ((-1 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, gibbsExpectation_smul]
  unfold td0WeightUpdate
  ring

/-! ## Connecting the update to the genuine free-energy derivative -/

/-- Free-energy gradient along a visible–hidden weight direction: the directional
derivative of `F` in the direction `-v σ^z_h` is the Gibbs expectation
`⟨-v σ^z_h⟩` (specialisation of the Eq (13) gradient identity, p.12). -/
theorem freeEnergy_gradient_visible [Nonempty I]
    (β : ℝ) (hβ : β ≠ 0) (H σz : Matrix I I ℂ)
    (hH : H.IsHermitian) (hσz : σz.IsHermitian) (v : ℝ) :
    HasDerivAt (fun w : ℝ => freeEnergy β (H + w • ((-(v : ℂ)) • σz)))
      (gibbsExpectation β H ((-(v : ℂ)) • σz)) 0 :=
  freeEnergy_hasDerivAt_gibbsExpectation β hβ H ((-(v : ℂ)) • σz) hH
    (hσz.smul (isSelfAdjoint_neg_real v))

/-- Free-energy gradient along a hidden–hidden weight direction: the directional
derivative of `F` in the direction `-σ^z_h σ^z_h'` is the Gibbs expectation
`⟨-σ^z_h σ^z_h'⟩` (specialisation of the Eq (13) gradient identity, p.12). -/
theorem freeEnergy_gradient_hidden [Nonempty I]
    (β : ℝ) (hβ : β ≠ 0) (H σhh : Matrix I I ℂ)
    (hH : H.IsHermitian) (hσhh : σhh.IsHermitian) :
    HasDerivAt (fun w : ℝ => freeEnergy β (H + w • ((-1 : ℂ) • σhh)))
      (gibbsExpectation β H ((-1 : ℂ) • σhh)) 0 :=
  freeEnergy_hasDerivAt_gibbsExpectation β hβ H ((-1 : ℂ) • σhh) hH
    (hσhh.smul (by simpa using isSelfAdjoint_neg_real 1))

/-- **Eq (14), full form** (p.12–13): the TD(0) update for `w_vh` written directly
through the genuine free-energy derivative equals `ε δ v ⟨σ^z_h⟩`.  Combines the
gradient identity (first conjunct, via `freeEnergy_gradient_visible`) with the
algebraic rewrite (second conjunct, `td0Update_visible`). -/
theorem td0Update_visible_full [Nonempty I]
    (β : ℝ) (hβ : β ≠ 0) (H σz : Matrix I I ℂ)
    (hH : H.IsHermitian) (hσz : σz.IsHermitian) (v ε δ : ℝ) :
    HasDerivAt (fun w : ℝ => freeEnergy β (H + w • ((-(v : ℂ)) • σz)))
        (gibbsExpectation β H ((-(v : ℂ)) • σz)) 0 ∧
      td0WeightUpdate ε δ (gibbsExpectation β H ((-(v : ℂ)) • σz))
        = ε * δ * v * gibbsExpectation β H σz :=
  ⟨freeEnergy_gradient_visible β hβ H σz hH hσz v,
   td0Update_visible β H σz v ε δ⟩

/-- **Eq (15), full form** (p.13): the TD(0) update for `w_hh'` written directly
through the genuine free-energy derivative equals `ε δ ⟨σ^z_h σ^z_h'⟩`.
Combines the gradient identity (first conjunct, via `freeEnergy_gradient_hidden`)
with the algebraic rewrite (second conjunct, `td0Update_hidden`). -/
theorem td0Update_hidden_full [Nonempty I]
    (β : ℝ) (hβ : β ≠ 0) (H σhh : Matrix I I ℂ)
    (hH : H.IsHermitian) (hσhh : σhh.IsHermitian) (ε δ : ℝ) :
    HasDerivAt (fun w : ℝ => freeEnergy β (H + w • ((-1 : ℂ) • σhh)))
        (gibbsExpectation β H ((-1 : ℂ) • σhh)) 0 ∧
      td0WeightUpdate ε δ (gibbsExpectation β H ((-1 : ℂ) • σhh))
        = ε * δ * gibbsExpectation β H σhh :=
  ⟨freeEnergy_gradient_hidden β hβ H σhh hH hσhh,
   td0Update_hidden β H σhh ε δ⟩

/-- **Eqs. (14)–(15)** ([Crawford et al., 2016][CrawfordEtAl2016], pp. 12–13), packaged:
for a clamped QBM with Hermitian Hamiltonian `H`, Hermitian Pauli observables `σz = σ^z_h` and
`σhh = σ^z_h σ^z_h'`, the TD(0) weight updates driven by the free-energy derivatives
in the directions `-v σ^z_h` and `-σ^z_h σ^z_h'` are respectively

* `Δw_vh = ε·δ·v·⟨σ^z_h⟩` (Eq. (14)), and
* `Δw_hh' = ε·δ·⟨σ^z_h σ^z_h'⟩` (Eq. (15)),

with `δ = r_n + γQ(s_{n+1},a_{n+1}) - Q(s_n,a_n)` and the thermodynamic beta absorbed
into `ε`. -/
theorem td0_update_rules [Nonempty I]
    (β : ℝ) (hβ : β ≠ 0) (H σz σhh : Matrix I I ℂ)
    (hH : H.IsHermitian) (hσz : σz.IsHermitian) (hσhh : σhh.IsHermitian)
    (v ε δ : ℝ) :
    (HasDerivAt (fun w : ℝ => freeEnergy β (H + w • ((-(v : ℂ)) • σz)))
        (gibbsExpectation β H ((-(v : ℂ)) • σz)) 0 ∧
      td0WeightUpdate ε δ (gibbsExpectation β H ((-(v : ℂ)) • σz))
        = ε * δ * v * gibbsExpectation β H σz) ∧
    (HasDerivAt (fun w : ℝ => freeEnergy β (H + w • ((-1 : ℂ) • σhh)))
        (gibbsExpectation β H ((-1 : ℂ) • σhh)) 0 ∧
      td0WeightUpdate ε δ (gibbsExpectation β H ((-1 : ℂ) • σhh))
        = ε * δ * gibbsExpectation β H σhh) :=
  ⟨td0Update_visible_full β hβ H σz hH hσz v ε δ,
   td0Update_hidden_full β hβ H σhh hH hσhh ε δ⟩

end Qatlib.Papers.ReinfLearning16.MainResults.TD0Update
