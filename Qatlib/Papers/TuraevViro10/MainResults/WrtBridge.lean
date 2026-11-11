/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Amplitude model for WRT and Turaev–Viro scaling

This module defines finite particle-dimension data and an abstract amplitude model
`TuraevViroModel` with amplitudes bounded in norm by one. It defines the model WRT and
Turaev–Viro quantities, proves their genus-dependent normalization identities, and constructs
examples from normalized states and actions preserving their norms. See [AlagicEtAl2010].

## Main statements

* `normalizedTvInvariant_eq_normSq`: For positive genus, the normalized invariant is the squared
  amplitude norm.
* `ofUnitaryRepresentation`: Construction from normalized states and the supplied actions.
* `additiveError_mono`: Monotonicity of the error scale with genus.

## References

* [Alagic et al., 2010][AlagicEtAl2010]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.WrtBridge

open scoped BigOperators

/-- Finite particle data with positive real quantum dimensions and a distinguished particle of
dimension one. -/
structure ParticleData (P : Type*) [Fintype P] where

  quantumDim : P → ℝ

  quantumDim_pos : ∀ i, 0 < quantumDim i

  trivial : P

  trivial_dim : quantumDim trivial = 1

namespace ParticleData

variable {P : Type*} [Fintype P]

/-- The square root of the sum of the squared particle quantum dimensions. -/
def totalQuantumDim (C : ParticleData P) : ℝ := Real.sqrt (∑ i, C.quantumDim i ^ 2)

/-- The total quantum dimension is at least one. -/
theorem one_le_totalQuantumDim (C : ParticleData P) : 1 ≤ C.totalQuantumDim := by
  have hmem : C.trivial ∈ (Finset.univ : Finset P) := Finset.mem_univ C.trivial
  have h1 : C.quantumDim C.trivial ^ 2 ≤ ∑ i, C.quantumDim i ^ 2 :=
    Finset.single_le_sum (f := fun i => C.quantumDim i ^ 2)
      (fun i _ => sq_nonneg (C.quantumDim i)) hmem
  calc (1 : ℝ) = Real.sqrt (C.quantumDim C.trivial ^ 2) := by
        rw [C.trivial_dim]; norm_num
    _ ≤ Real.sqrt (∑ i, C.quantumDim i ^ 2) := Real.sqrt_le_sqrt h1

/-- The total quantum dimension is strictly positive. -/
theorem totalQuantumDim_pos (C : ParticleData P) : 0 < C.totalQuantumDim :=
  lt_of_lt_of_le zero_lt_one C.one_le_totalQuantumDim

end ParticleData

/-- An abstract model containing particle data and genus- and input-dependent complex amplitudes
of norm at most one. -/
structure TuraevViroModel (P ι : Type*) [Fintype P] where

  particles : ParticleData P

  amplitude : ℕ → ι → ℂ

  amplitude_le_one : ∀ g x, ‖amplitude g x‖ ≤ 1

namespace TuraevViroModel

variable {P ι : Type*} [Fintype P]

/-- The total quantum dimension of the particle data in the model. -/
def D (M : TuraevViroModel P ι) : ℝ := M.particles.totalQuantumDim

/-- The model total quantum dimension `D` is positive. -/
theorem D_pos (M : TuraevViroModel P ι) : 0 < M.D :=
  M.particles.totalQuantumDim_pos

/-- The model total quantum dimension `D` is at least one. -/
theorem one_le_D (M : TuraevViroModel P ι) : 1 ≤ M.D :=
  M.particles.one_le_totalQuantumDim

/-- The model WRT invariant, defined by multiplying the amplitude by `D ^ (g - 1)`. See
[AlagicEtAl2010]. -/
def wrtInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) : ℂ :=
  ((M.D : ℝ) : ℂ) ^ (g - 1) * M.amplitude g x

/-- The model Turaev–Viro invariant, defined as the squared norm of its WRT invariant. -/
def tvInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) : ℝ :=
  ‖M.wrtInvariant g x‖ ^ 2

/-- The squared norm of the model WRT invariant equals its Turaev–Viro invariant. -/
theorem wrtInvariant_normSq (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    ‖M.wrtInvariant g x‖ ^ 2 = M.tvInvariant g x := rfl

/-- The WRT norm equals `D ^ (g - 1)` times the amplitude norm. -/
theorem norm_wrtInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    ‖M.wrtInvariant g x‖ = M.D ^ (g - 1) * ‖M.amplitude g x‖ := by
  unfold wrtInvariant
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos M.D_pos]

/-- The Turaev–Viro invariant equals `D ^ (2 * (g - 1))` times the squared amplitude norm. -/
theorem tvInvariant_eq_D_pow_mul_normSq (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    M.tvInvariant g x = M.D ^ (2 * (g - 1)) * ‖M.amplitude g x‖ ^ 2 := by
  unfold tvInvariant
  rw [norm_wrtInvariant, mul_pow, ← pow_mul, Nat.mul_comm]

/-- The model Turaev–Viro invariant is nonnegative. -/
theorem tvInvariant_nonneg (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    0 ≤ M.tvInvariant g x := by
  unfold tvInvariant
  positivity

/-- The normalized model invariant obtained by multiplying the Turaev–Viro invariant by the
integer power `D ^ (2 * (1 - g))`. -/
def normalizedTvInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) : ℝ :=
  M.D ^ (2 * ((1 : ℤ) - (g : ℤ))) * M.tvInvariant g x

/-- For genus at least one, the normalized Turaev–Viro invariant equals the squared amplitude
norm. See [AlagicEtAl2010]. -/
theorem normalizedTvInvariant_eq_normSq (M : TuraevViroModel P ι) {g : ℕ} (hg : 1 ≤ g)
    (x : ι) :
    M.normalizedTvInvariant g x = ‖M.amplitude g x‖ ^ 2 := by
  unfold normalizedTvInvariant
  rw [tvInvariant_eq_D_pow_mul_normSq]
  have hexp : ((2 * (g - 1) : ℕ) : ℤ) = 2 * ((g : ℤ) - 1) := by omega
  have hpow : M.D ^ (2 * (g - 1)) = M.D ^ (2 * ((g : ℤ) - 1)) := by
    rw [← hexp, zpow_natCast]
  rw [hpow, ← mul_assoc, ← zpow_add₀ (ne_of_gt M.D_pos)]
  have hcancel : 2 * ((1 : ℤ) - (g : ℤ)) + 2 * ((g : ℤ) - 1) = 0 := by ring
  rw [hcancel, zpow_zero, one_mul]

/-- For genus at least one, the normalized model invariant lies in `[0, 1]`. -/
theorem normalizedTvInvariant_mem_Icc (M : TuraevViroModel P ι) {g : ℕ} (hg : 1 ≤ g)
    (x : ι) :
    M.normalizedTvInvariant g x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · unfold normalizedTvInvariant
    exact mul_nonneg (zpow_nonneg (le_of_lt M.D_pos) _) (M.tvInvariant_nonneg g x)
  · rw [normalizedTvInvariant_eq_normSq M hg x]
    have h := M.amplitude_le_one g x
    nlinarith [norm_nonneg (M.amplitude g x)]

/-- For genera at least one, the additive-error scale `D ^ (2 * (g - 1))` is nondecreasing with
genus. -/
theorem additiveError_mono (M : TuraevViroModel P ι) {g g' : ℕ} (hg : 1 ≤ g)
    (hgg : g ≤ g') :
    M.D ^ (2 * (g - 1)) ≤ M.D ^ (2 * (g' - 1)) := by
  refine pow_le_pow_right₀ M.one_le_D ?_
  omega

/-- Constructs an amplitude model from unit states and actions preserving the norms of those
states, using their inner products as amplitudes. -/
def ofUnitaryRepresentation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (particles : ParticleData P) (v : ℕ → H) (hv : ∀ g, ‖v g‖ = 1)
    (act : ℕ → ι → H → H) (hact : ∀ g x, ‖act g x (v g)‖ = ‖v g‖) :
    TuraevViroModel P ι where
  particles := particles
  amplitude := fun g x => inner ℂ (v g) (act g x (v g))
  amplitude_le_one := by
    intro g x
    have h := norm_inner_le_norm (𝕜 := ℂ) (v g) (act g x (v g))
    rw [hv g, hact g x, hv g, mul_one] at h
    exact h

/-- For genus at least one, the normalized invariant of the state-action model is the squared
norm of the defining matrix element. -/
theorem ofUnitaryRepresentation_normalized_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (particles : ParticleData P) (v : ℕ → H)
    (hv : ∀ g, ‖v g‖ = 1) (act : ℕ → ι → H → H)
    (hact : ∀ g x, ‖act g x (v g)‖ = ‖v g‖) {g : ℕ} (hg : 1 ≤ g) (x : ι) :
    (ofUnitaryRepresentation particles v hv act hact).normalizedTvInvariant g x =
      ‖inner ℂ (v g) (act g x (v g))‖ ^ 2 :=
  normalizedTvInvariant_eq_normSq _ hg x

/-- The one-particle model with quantum dimension one and constant amplitude one. -/
def trivialModel (ι : Type*) : TuraevViroModel Unit ι where
  particles :=
    { quantumDim := fun _ => 1
      quantumDim_pos := fun _ => zero_lt_one
      trivial := ()
      trivial_dim := rfl }
  amplitude := fun _ _ => 1
  amplitude_le_one := by
    intro g x
    simp

/-- The trivial model has total quantum dimension one. -/
theorem trivialModel_D (ι : Type*) : (trivialModel ι).D = 1 := by
  simp [TuraevViroModel.D, ParticleData.totalQuantumDim, trivialModel]

/-- For genus at least one, the trivial model has normalized Turaev–Viro invariant one. -/
theorem trivialModel_normalizedTvInvariant (ι : Type*) {g : ℕ} (hg : 1 ≤ g) (x : ι) :
    (trivialModel ι).normalizedTvInvariant g x = 1 := by
  rw [normalizedTvInvariant_eq_normSq _ hg x]
  simp [trivialModel]

end TuraevViroModel

end Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
