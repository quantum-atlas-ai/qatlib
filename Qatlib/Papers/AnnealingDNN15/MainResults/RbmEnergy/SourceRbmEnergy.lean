/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RBM energy functional and model expectations (Eqs. (1)–(3), (9))

Source: *Application of Quantum Annealing to Training of Deep Neural Networks*,
arXiv:1510.06356 (2015), fixed local PDF
`1510.06356.pdf` (SHA-256 `7c273ebf6340223d2ddbc2f0684298e9a16ed3cc89253d212008ae3e3e945f72`).
Section 2, Eqs. (1)–(3) and (9), pages 3–4.

The paper restricts a Restricted Boltzmann Machine to binary visible and hidden
units `v_i, h_j ∈ {0,1}` with the energy functional

`E(v,h) = -Σ_i b_i v_i - Σ_j c_j h_j - Σ_{i,j} W_ij v_i h_j`   (Eq. (2)),

joint probability `P(v,h) = exp(-E(v,h)) / Z`   (Eq. (1)), and model
expectation

`⟨v_i h_j⟩_model = (1/Z) Σ_{v,h} v_i h_j exp(-E(v,h))`   (Eq. (9)).

This module only records that vocabulary.  The chain-embedding comparison
`⟨v_i h_j⟩^{E''} ≅ ⟨v_i h_j⟩^E` of Eq. (22) is proved in
`MainResults.EmbeddedIsing.SourceEmbeddedIsing`.  No `sorry`, no extra axiom.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AnnealingDNN15.MainResults.RbmEnergy

open scoped BigOperators

/-- The RBM energy functional of Eq. (2) evaluated on real vectors `v, h`:
`E(v,h) = -Σ_i b_i v_i - Σ_j c_j h_j - Σ_{i,j} W_ij v_i h_j`.

The paper intends binary inputs `v_i, h_j ∈ {0,1}`; the binary restriction is
carried by `rbmConfigEnergy` below, which evaluates the energy only on the
`2^(n+m)` Boolean configurations. -/
noncomputable def rbmEnergy {n m : ℕ} (b : Fin n → ℝ) (c : Fin m → ℝ)
    (W : Fin n → Fin m → ℝ) (v : Fin n → ℝ) (h : Fin m → ℝ) : ℝ :=
  -(∑ i, b i * v i) - (∑ j, c j * h j) - (∑ i, ∑ j, W i j * v i * h j)

/-- The value of a binary unit, `true ↦ 1`, `false ↦ 0`. -/
def bitVal (z : Bool) : ℝ := if z then 1 else 0

/-- A binary unit is either zero or one (Eq. (2) domain restriction). -/
theorem bitVal_eq_zero_or_one (z : Bool) : bitVal z = 0 ∨ bitVal z = 1 := by
  cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A joint configuration of a `n×m` RBM: visible and hidden binary vectors. -/
abbrev RbmConfig (n m : ℕ) := (Fin n → Bool) × (Fin m → Bool)

/-- The RBM energy functional on Boolean configurations (Eq. (2)). -/
noncomputable def rbmConfigEnergy {n m : ℕ} (b : Fin n → ℝ) (c : Fin m → ℝ)
    (W : Fin n → Fin m → ℝ) (x : RbmConfig n m) : ℝ :=
  rbmEnergy b c W (fun i => bitVal (x.1 i)) (fun j => bitVal (x.2 j))

/-- Boltzmann weight `exp(-E(x))` of Eq. (1) at unit inverse temperature
(`β = 1`, the paper's Eq. (1); the annealing scale `β_eff` of Eq. (15) is the
same weight with `β = β_eff`). -/
noncomputable def boltzmannWeight {Ω : Type} (E : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-E x)

/-- Boltzmann weight at inverse temperature `β`: `exp(-β E(x))`, the form used
for the annealing distribution (15). -/
noncomputable def boltzmannWeightAt {Ω : Type} (β : ℝ) (E : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-(β * E x))

/-- The Boltzmann weight is strictly positive. -/
theorem boltzmannWeight_pos {Ω : Type} (E : Ω → ℝ) (x : Ω) :
    0 < boltzmannWeight E x := Real.exp_pos _

/-- The Boltzmann weight at inverse temperature `β` is strictly positive. -/
theorem boltzmannWeightAt_pos {Ω : Type} (β : ℝ) (E : Ω → ℝ) (x : Ω) :
    0 < boltzmannWeightAt β E x := Real.exp_pos _

/-- The partition function `Z = Σ_x exp(-β E(x))` over a finite configuration
space. -/
noncomputable def partitionFunction {Ω : Type} [Fintype Ω] (β : ℝ) (E : Ω → ℝ) : ℝ :=
  ∑ x, boltzmannWeightAt β E x

/-- The partition function is strictly positive on a nonempty configuration
space. -/
theorem partitionFunction_pos {Ω : Type} [Fintype Ω] [Nonempty Ω] (β : ℝ)
    (E : Ω → ℝ) : 0 < partitionFunction β E :=
  Finset.sum_pos (fun x _ => boltzmannWeightAt_pos β E x) Finset.univ_nonempty

/-- The model expectation `⟨f⟩ = (1/Z) Σ_x f(x) exp(-β E(x))` of an observable
on the Boltzmann distribution (Eq. (9) with `f = v_i h_j`). -/
noncomputable def modelExpectation {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (β : ℝ) (E : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  (∑ x, f x * boltzmannWeightAt β E x) / partitionFunction β E

/-- Eq. (9) as written in the paper: the model expectation of `v_i h_j` on the
RBM joint distribution is the normalized Boltzmann average of the product of
the two unit values.  This is `modelExpectation` at `β = 1` with the observable
`fun x => bitVal (x.1 i) * bitVal (x.2 j)`. -/
theorem rbm_modelExpectation_vis_hid {n m : ℕ} (b : Fin n → ℝ) (c : Fin m → ℝ)
    (W : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) :
    modelExpectation 1 (rbmConfigEnergy b c W)
        (fun x => bitVal (x.1 i) * bitVal (x.2 j))
      = (∑ x : RbmConfig n m,
            bitVal (x.1 i) * bitVal (x.2 j) * Real.exp (-(rbmConfigEnergy b c W x)))
          / (∑ x : RbmConfig n m, Real.exp (-(rbmConfigEnergy b c W x))) := by
  simp [modelExpectation, partitionFunction, boltzmannWeightAt, rbmConfigEnergy, one_mul]

end Qatlib.Papers.AnnealingDNN15.MainResults.RbmEnergy
