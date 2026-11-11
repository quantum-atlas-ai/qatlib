/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Conditional resource scaling of the state-preparation pipeline (source Eqs. (7)--(19))

Source: Ali Hamed Moosavian and Stephen Jordan, *Faster quantum algorithm to simulate
Fermionic Quantum Field Theory*, fixed version arXiv:1711.04006v3 (23 Oct 2019),
Section II B, Eqs. (7)--(19).

The source quotes three asymptotic costs. All three are *conditional*: they assume the
entanglement-entropy scaling of Eqs. (4) and (8), the practical DMRG runtime `O(n χ³)` of
Eq. (13), lattice spacing `a ∝ ε`, and a driving strength `λ ∝ ε` (from the success
probability `P = 1 - ε` of Eq. (15)). This module formalises the exponent arithmetic that
turns those assumptions into Eqs. (12), (14) and (19); it does not formalise the DMRG
runtime heuristic or the entropy scaling, which enter only as the stated hypotheses.

The three exponents are

* `bondExponent N = -N/6 - √(N/3)`, Eq. (12), the exponent of the bond dimension
  `χ = O(ε^{-N/6-√(N/3)})`, obtained by adding the Eq. (7) exponent `-N/6` and the
  Eq. (11) exponent `-√(N/3)`;
* `costExponent N = -N/2 - 1 - √(3N)`, Eq. (14), the exponent of the classical
  preprocessing cost `n χ³`: the site number contributes `-1` (because `n = L/a` and
  `a ∝ ε`) and `χ³` contributes `3 · bondExponent N`;
* `prepExponent = -3`, Eq. (19), the quantum preparation exponent, where `a ∝ ε` supplies
  `-2` in `(L/(a²λ))^{1+o(1)}` and `λ ∝ ε` supplies the remaining `-1`.

Boundary: the paper's error-vs-`k` relation of Eq. (8) and the `o(1)` refinements are not
formalised; only the exact exponent identities and the two displayed numeric facts
(`costExponent 1 = -3.23…` and classical dominance for `N ≥ 1`) are proved.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.FermionQFT17.PrepContracts.ResourceScaling

/-- Source Eq. (12): the exponent of the bond dimension `χ = O(ε^{-N/6-√(N/3)})`, the sum
of the Eq. (7) exponent `-N/6` and the Eq. (11) exponent `-√(N/3)`. -/
def bondExponent (N : ℝ) : ℝ :=
  -(N / 6) - Real.sqrt (N / 3)

/-- Source Eq. (14): the exponent of the classical DMRG preprocessing cost
`O(ε^{-N/2-1-√(3N)})`. -/
def costExponent (N : ℝ) : ℝ :=
  -(N / 2) - 1 - Real.sqrt (3 * N)

/-- Source Eq. (19): the exponent of the quantum state-preparation gate count
`O(ε^{-3-o(1)})`. -/
def prepExponent : ℝ :=
  -3

/-- Source Eqs. (7) and (11): the Eq. (12) exponent is the sum of the two contributing
exponents `-N/6` (entropy scaling) and `-√(N/3)` (bond-dimension enhancement of Eq. (11)). -/
theorem bondExponent_eq (N : ℝ) :
    bondExponent N = -(N / 6) + -(Real.sqrt (N / 3)) := by
  unfold bondExponent
  ring

/-- Elementary scaling used to turn Eq. (12) into Eq. (14): `√(3N) = 3 √(N/3)` for
`N ≥ 0`, so the `χ³` factor triples the Eq. (12) exponent exactly. -/
theorem sqrt_three_mul (N : ℝ) :
    Real.sqrt (3 * N) = 3 * Real.sqrt (N / 3) := by
  have h9 : (9 : ℝ) * (N / 3) = 3 * N := by ring
  rw [← h9, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
  have h3 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h3]

/-- Source Eq. (12) together with Eq. (13) gives Eq. (14): with `n χ³` and `n = L/a ∝ ε⁻¹`,
the cost exponent is `-1 + 3 · bondExponent N`. -/
theorem costExponent_eq (N : ℝ) :
    costExponent N = -1 + 3 * bondExponent N := by
  unfold costExponent bondExponent
  rw [sqrt_three_mul N]
  ring

/-- Source Eq. (14) at `N = 1`: the exponent is exactly `-3/2 - √3`. -/
theorem costExponent_one : costExponent 1 = -(3 / 2) - Real.sqrt 3 := by
  unfold costExponent
  norm_num

/-- Numerical bracket for `√3` used to pin the displayed `-3.23…` of Section II B. -/
theorem sqrt_three_bounds : (1.73 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.74 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.73)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.74)]
    norm_num

/-- Source Section II B: for `N = 1` the classical preprocessing exponent lies strictly
between `-3.24` and `-3.23`, matching the displayed `O(ε^{-3.23…})`. -/
theorem costExponent_one_bounds :
    (-3.24 : ℝ) < costExponent 1 ∧ costExponent 1 < -3.23 := by
  rw [costExponent_one]
  obtain ⟨h1, h2⟩ := sqrt_three_bounds
  constructor <;> linarith

/-- Source Section II B: for every species number `N ≥ 1` the classical DMRG preprocessing
is at least as expensive as the quantum preparation, i.e. its exponent is at most the
`-3` of Eq. (19); this is what makes the classical step the bottleneck. -/
theorem classical_dominates (N : ℝ) (hN : 1 ≤ N) : costExponent N ≤ prepExponent := by
  have hsqrt : Real.sqrt 3 ≤ Real.sqrt (3 * N) := Real.sqrt_le_sqrt (by linarith)
  have h173 : (1.73 : ℝ) < Real.sqrt 3 := sqrt_three_bounds.1
  unfold costExponent prepExponent
  linarith

/-- Source Eqs. (18)--(19): with lattice spacing `a = c ε` and driving strength `λ = d ε`,
the gate count `G_prep = O((L/(a²λ))^{1+o(1)})` has base cost `L/(c²d ε³)`, so its exponent
is the `-3` of `prepExponent`. -/
theorem prep_gate_scale (L c d ε : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (hε : ε ≠ 0) :
    L / ((c * ε) ^ 2 * (d * ε)) = L / (c ^ 2 * d * ε ^ 3) := by
  field_simp

/-- Source Eq. (19): the preparation exponent is `-3`. -/
theorem prepExponent_eq : prepExponent = -3 := rfl

/-- Source Eq. (14) as an exact power identity: with `n = ε⁻¹`, bond dimension
`χ = k ε^{bondExponent N}` and DMRG runtime `n χ³`, the cost is `k³ ε^{costExponent N}`,
i.e. the exponent of Eq. (14). -/
theorem dmrg_cost_rpow (k ε : ℝ) (N : ℝ) (hε : 0 < ε) :
    ε ^ (-1 : ℝ) * (k * ε ^ bondExponent N) ^ 3 = k ^ 3 * ε ^ costExponent N := by
  have hk3 : (k * ε ^ bondExponent N) ^ 3 = k ^ 3 * (ε ^ bondExponent N) ^ 3 := by
    rw [mul_pow]
  have hpow3 : (ε ^ bondExponent N) ^ 3 = ε ^ (3 * bondExponent N) := by
    rw [← Real.rpow_natCast (ε ^ bondExponent N) 3, ← Real.rpow_mul hε.le]
    ring_nf
  have hcomb : ε ^ (3 * bondExponent N) * ε ^ (-1 : ℝ) =
      ε ^ (costExponent N) := by
    rw [costExponent_eq N, ← Real.rpow_add hε]
    ring_nf
  rw [hk3, hpow3]
  calc ε ^ (-1 : ℝ) * (k ^ 3 * ε ^ (3 * bondExponent N))
      = k ^ 3 * (ε ^ (3 * bondExponent N) * ε ^ (-1 : ℝ)) := by ring
    _ = k ^ 3 * ε ^ costExponent N := by rw [hcomb]

end Qatlib.Papers.FermionQFT17.PrepContracts.ResourceScaling
