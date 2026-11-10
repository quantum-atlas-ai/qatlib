/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.WrtBridge

open scoped BigOperators

structure ParticleData (P : Type*) [Fintype P] where

  quantumDim : P → ℝ

  quantumDim_pos : ∀ i, 0 < quantumDim i

  trivial : P

  trivial_dim : quantumDim trivial = 1

namespace ParticleData

variable {P : Type*} [Fintype P]

def totalQuantumDim (C : ParticleData P) : ℝ := Real.sqrt (∑ i, C.quantumDim i ^ 2)

theorem one_le_totalQuantumDim (C : ParticleData P) : 1 ≤ C.totalQuantumDim := by
  have hmem : C.trivial ∈ (Finset.univ : Finset P) := Finset.mem_univ C.trivial
  have h1 : C.quantumDim C.trivial ^ 2 ≤ ∑ i, C.quantumDim i ^ 2 :=
    Finset.single_le_sum (f := fun i => C.quantumDim i ^ 2)
      (fun i _ => sq_nonneg (C.quantumDim i)) hmem
  calc (1 : ℝ) = Real.sqrt (C.quantumDim C.trivial ^ 2) := by
        rw [C.trivial_dim]; norm_num
    _ ≤ Real.sqrt (∑ i, C.quantumDim i ^ 2) := Real.sqrt_le_sqrt h1

theorem totalQuantumDim_pos (C : ParticleData P) : 0 < C.totalQuantumDim :=
  lt_of_lt_of_le zero_lt_one C.one_le_totalQuantumDim

end ParticleData

structure TuraevViroModel (P ι : Type*) [Fintype P] where

  particles : ParticleData P

  amplitude : ℕ → ι → ℂ

  amplitude_le_one : ∀ g x, ‖amplitude g x‖ ≤ 1

namespace TuraevViroModel

variable {P ι : Type*} [Fintype P]

def D (M : TuraevViroModel P ι) : ℝ := M.particles.totalQuantumDim

theorem D_pos (M : TuraevViroModel P ι) : 0 < M.D :=
  M.particles.totalQuantumDim_pos

theorem one_le_D (M : TuraevViroModel P ι) : 1 ≤ M.D :=
  M.particles.one_le_totalQuantumDim

def wrtInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) : ℂ :=
  ((M.D : ℝ) : ℂ) ^ (g - 1) * M.amplitude g x

def tvInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) : ℝ :=
  ‖M.wrtInvariant g x‖ ^ 2

theorem wrtInvariant_normSq (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    ‖M.wrtInvariant g x‖ ^ 2 = M.tvInvariant g x := rfl

theorem norm_wrtInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    ‖M.wrtInvariant g x‖ = M.D ^ (g - 1) * ‖M.amplitude g x‖ := by
  unfold wrtInvariant
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos M.D_pos]

theorem tvInvariant_eq_D_pow_mul_normSq (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    M.tvInvariant g x = M.D ^ (2 * (g - 1)) * ‖M.amplitude g x‖ ^ 2 := by
  unfold tvInvariant
  rw [norm_wrtInvariant, mul_pow, ← pow_mul, Nat.mul_comm]

theorem tvInvariant_nonneg (M : TuraevViroModel P ι) (g : ℕ) (x : ι) :
    0 ≤ M.tvInvariant g x := by
  unfold tvInvariant
  positivity

def normalizedTvInvariant (M : TuraevViroModel P ι) (g : ℕ) (x : ι) : ℝ :=
  M.D ^ (2 * ((1 : ℤ) - (g : ℤ))) * M.tvInvariant g x

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

theorem normalizedTvInvariant_mem_Icc (M : TuraevViroModel P ι) {g : ℕ} (hg : 1 ≤ g)
    (x : ι) :
    M.normalizedTvInvariant g x ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · unfold normalizedTvInvariant
    exact mul_nonneg (zpow_nonneg (le_of_lt M.D_pos) _) (M.tvInvariant_nonneg g x)
  · rw [normalizedTvInvariant_eq_normSq M hg x]
    have h := M.amplitude_le_one g x
    nlinarith [norm_nonneg (M.amplitude g x)]

theorem additiveError_mono (M : TuraevViroModel P ι) {g g' : ℕ} (hg : 1 ≤ g)
    (hgg : g ≤ g') :
    M.D ^ (2 * (g - 1)) ≤ M.D ^ (2 * (g' - 1)) := by
  refine pow_le_pow_right₀ M.one_le_D ?_
  omega

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

theorem ofUnitaryRepresentation_normalized_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (particles : ParticleData P) (v : ℕ → H)
    (hv : ∀ g, ‖v g‖ = 1) (act : ℕ → ι → H → H)
    (hact : ∀ g x, ‖act g x (v g)‖ = ‖v g‖) {g : ℕ} (hg : 1 ≤ g) (x : ι) :
    (ofUnitaryRepresentation particles v hv act hact).normalizedTvInvariant g x =
      ‖inner ℂ (v g) (act g x (v g))‖ ^ 2 :=
  normalizedTvInvariant_eq_normSq _ hg x

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

theorem trivialModel_D (ι : Type*) : (trivialModel ι).D = 1 := by
  simp [TuraevViroModel.D, ParticleData.totalQuantumDim, trivialModel]

theorem trivialModel_normalizedTvInvariant (ι : Type*) {g : ℕ} (hg : 1 ≤ g) (x : ι) :
    (trivialModel ι).normalizedTvInvariant g x = 1 := by
  rw [normalizedTvInvariant_eq_normSq _ hg x]
  simp [trivialModel]

end TuraevViroModel

end Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
