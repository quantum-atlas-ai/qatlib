/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.SpinFreeSim13.CoeffModels

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def wignerProj {d : ℕ} (D : G → Matrix (Fin d) (Fin d) ℂ)
    (ρ : G →* Module.End ℂ V) (i j : Fin d) (Ψ : V) : V :=
  (((d : ℂ) * ((Fintype.card G : ℂ))⁻¹))
    • ∑ g : G, star (D g i j) • ρ g Ψ

noncomputable def phaseEstAmplitude {d : ℕ} (D : G → Matrix (Fin d) (Fin d) ℂ)
    (ρ : G →* Module.End ℂ V) (i j : Fin d) (Ψ : V) : V :=
  (((Real.sqrt (d : ℝ) : ℂ) * ((Fintype.card G : ℂ))⁻¹))
    • ∑ g : G, star (D g i j) • ρ g Ψ

noncomputable def controlledActionState (ρ : G →* Module.End ℂ V) (Ψ : V) : G → V :=
  fun g => (((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹) • ρ g Ψ

theorem phaseEstAmplitude_eq_wigner {d : ℕ} (D : G → Matrix (Fin d) (Fin d) ℂ)
    (ρ : G →* Module.End ℂ V) (i j : Fin d) (Ψ : V) (hd : d ≠ 0) :
    phaseEstAmplitude D ρ i j Ψ
      = (((Real.sqrt (d : ℝ) : ℂ))⁻¹) • wignerProj D ρ i j Ψ := by
  have hsqrt : ((Real.sqrt (d : ℝ) : ℂ)) * ((Real.sqrt (d : ℝ) : ℂ)) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    norm_num
  have hne : ((Real.sqrt (d : ℝ) : ℂ)) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt (d : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
    exact_mod_cast (ne_of_gt hpos)
  have hcard : ((Fintype.card G : ℂ)) ≠ 0 := by
    haveI : Nonempty G := ⟨1⟩
    exact_mod_cast Fintype.card_ne_zero
  have key :
      ((Real.sqrt (d : ℝ) : ℂ) * ((Fintype.card G : ℂ))⁻¹)
        = ((Real.sqrt (d : ℝ) : ℂ))⁻¹
            * ((d : ℂ) * ((Fintype.card G : ℂ))⁻¹) := by
    rw [← hsqrt]
    field_simp
  unfold phaseEstAmplitude wignerProj
  rw [key, smul_smul]

theorem wignerProj_smul {d : ℕ} (D : G → Matrix (Fin d) (Fin d) ℂ)
    (ρ : G →* Module.End ℂ V) (i j : Fin d) (c : ℂ) (Ψ : V) :
    wignerProj D ρ i j (c • Ψ) = c • wignerProj D ρ i j Ψ := by
  unfold wignerProj
  have hterm : ∀ g : G,
      star (D g i j) • ρ g (c • Ψ) = c • (star (D g i j) • ρ g Ψ) := by
    intro g
    rw [map_smul, smul_comm]
  simp only [hterm]
  rw [← Finset.smul_sum, smul_smul, smul_smul]
  congr 1
  ring

theorem wignerProj_add {d : ℕ} (D : G → Matrix (Fin d) (Fin d) ℂ)
    (ρ : G →* Module.End ℂ V) (i j : Fin d) (Ψ Φ : V) :
    wignerProj D ρ i j (Ψ + Φ) = wignerProj D ρ i j Ψ + wignerProj D ρ i j Φ := by
  unfold wignerProj
  simp only [map_add, smul_add, Finset.sum_add_distrib]

theorem controlledActionState_def (ρ : G →* Module.End ℂ V) (Ψ : V) (g : G) :
    controlledActionState ρ Ψ g
      = (((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹) • ρ g Ψ := rfl

end Qatlib.Papers.SpinFreeSim13.CoeffModels
