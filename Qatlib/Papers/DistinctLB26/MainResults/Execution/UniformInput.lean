/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.PhaseBridge
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Uniform computational inputs in the Fourier register

The canonical character indexing is complete. Consequently a uniform coherent
superposition of computational inputs is precisely the zero Fourier label.
All identities use finite sums of the actual normalized plane-wave states.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- Every character is indexed by exactly one computational input. -/
def inputCharEquiv : Label n q ≃ AddChar (Label n q) ℂ :=
  Equiv.ofBijective inputChar (by
    apply (Fintype.bijective_iff_injective_and_card inputChar).mpr
    exact ⟨inputChar_injective, (AddChar.card_eq (α := Label n q)).symm⟩)

/-- Orthogonality of the actual canonical input characters. -/
theorem sum_inputChar (σ : Label n q) :
    (∑ x : Label n q, inputChar x σ) =
      if σ = 0 then (Fintype.card (Label n q) : ℂ) else 0 := by
  classical
  rw [← AddChar.sum_apply_eq_ite σ]
  exact Fintype.sum_equiv inputCharEquiv _ _ (fun _ => rfl)

/-- Embed an arbitrary work state at the zero Fourier label. -/
def zeroInput (φ : Local n q W) : Joint n q W :=
  WithLp.toLp 2 (fun z => if z.1 = 0 then φ z.2 else 0)

/-- Coordinate evaluation of a finite joint Hilbert-space vector. -/
def jointCoord (z : Label n q × Work n q W) : Joint n q W →ₗ[ℂ] ℂ where
  toFun ψ := ψ z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype W] in
/-- The uniform superposition of computational inputs is the zero Fourier input. -/
theorem uniform_plane (φ : Local n q W) :
    ((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) •
      (∑ x : Label n q, plane x φ) = zeroInput φ := by
  classical
  let d : ℝ := Fintype.card (Label n q)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos (α := Label n q)
  have hs : (Real.sqrt d : ℂ) ^ 2 = (Fintype.card (Label n q) : ℂ) := by
    have h := Real.sq_sqrt hd.le
    exact_mod_cast h
  have hn : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hd)
  ext z
  change (jointCoord z) ((Real.sqrt d : ℂ)⁻¹ • ∑ x : Label n q, plane x φ) = _
  rw [map_smul, map_sum]
  change (Real.sqrt d : ℂ)⁻¹ *
    (∑ x : Label n q, inputChar x (-z.1) / (Real.sqrt d : ℂ) * φ z.2) =
    if z.1 = 0 then φ z.2 else 0
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [sum_inputChar]
  by_cases hz : z.1 = 0
  · simp only [hz, neg_zero, ite_true]
    rw [← hs]
    field_simp
  · simp only [neg_eq_zero, hz, ite_false, zero_mul, mul_zero]

end Qatlib.Papers.DistinctLB26.MainResults.Execution
