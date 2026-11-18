/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWeakness97.MainResults.PermCoupling

/-! Concrete regressions for the restricted in-place permutation coupling.
The normalized witness below satisfies the final estimate's hypotheses on a
nonempty finite space; no source QTM or probability-one separation is asserted. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace QatlibTests.QueryCoupling

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QWeakness97.MainResults.PermCoupling
open scoped BigOperators Classical

/-- A transposition oracle really moves a nonzero basis state. -/
theorem swap_moves :
    permAct (Equiv.swap false true) (Ket false) = Ket true := by
  funext b
  cases b <;> simp [permAct, Ket]

/-- Different permutation oracles are distinguishable on a supplied basis state. -/
theorem swap_diff :
    permAct (Equiv.swap false true) (Ket false) ≠
      permAct (Equiv.refl Bool) (Ket false) := by
  rw [swap_moves]
  intro h
  have h' := congrFun h true
  norm_num [permAct, Ket] at h'

/-- Repeated draw values produce a valid chain even when the transposition is trivial. -/
theorem repeated_draw :
    chainPerm (Equiv.refl Bool) (fun _ => false) 3 = Equiv.refl Bool := by
  simp [chainPerm]

/-- The disagreement estimate applies to a normalized nonzero basis state. -/
theorem basis_bound :
    ∑ b : Bool, ‖permAct (Equiv.refl Bool) (Ket false) b -
      permAct (Equiv.swap false true) (Ket false) b‖ ^ 2 ≤
      4 * ∑ b ∈ differSet (Equiv.refl Bool) (Equiv.swap false true),
        ‖Ket false b‖ ^ 2 :=
  permDiff_le _ _ _

/-- Without fair-share mass, a normalized basis state violates the seed hypothesis. -/
theorem no_fair_share :
    ¬ ‖Ket false false‖ ^ 2 ≤ (Fintype.card Bool : ℝ)⁻¹ := by
  norm_num [Ket]

/-- A zero step budget cannot satisfy the final estimate's positive-budget hypothesis. -/
theorem zero_excluded : ¬ (1 ≤ (0 : ℕ)) := by omega

/-- A normalized basis seed away from the pinned preimage has fair-share mass. -/
theorem witness_seed :
    (∑ x : Bool × Fin 10000, ‖Ket (false, (1 : Fin 10000)) x‖ ^ 2) = 1 ∧
      ‖Ket (false, (1 : Fin 10000)) (false, (0 : Fin 10000))‖ ^ 2 ≤
        (Fintype.card (Bool × Fin 10000) : ℝ)⁻¹ := by
  constructor
  · simpa [Normalized, BornProb] using normalized_ket (false, (1 : Fin 10000))
  · simp [Ket]

/-- The two Boolean label classes are balanced on the concrete witness space. -/
theorem witness_labels :
    2 * (Finset.univ.filter
      (fun x : Bool × Fin 10000 => x.1 ≠ (false, (0 : Fin 10000)).1)).card ≥
        Fintype.card (Bool × Fin 10000) := by
  have hf : (Finset.univ.filter (fun x : Bool × Fin 10000 => x.1 ≠ false)) =
      ({true} : Finset Bool) ×ˢ (Finset.univ : Finset (Fin 10000)) := by
    ext x
    cases x with
    | mk b i => cases b <;> simp
  rw [hf]
  norm_num

/-- The small-query regime is satisfiable with one query and 20000 basis states. -/
theorem witness_regime :
    100 * ((1 : ℕ) : ℝ) * Real.sqrt (((1 + 1 : ℕ) : ℝ) *
      (Fintype.card (Bool × Fin 10000) : ℝ)) ≤
        (Fintype.card (Bool × Fin 10000) : ℝ) := by
  have hsqrt : Real.sqrt (40000 : ℝ) = 200 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [hsqrt]

/-- The witness space size follows symbolically from the product and `Fin` card
lemmas; no component of the 20000-point space is ever enumerated. -/
theorem witness_card : Fintype.card (Bool × Fin 10000) = 20000 := by
  simp [Fintype.card_prod]

/-- The complete finite counting estimate applies to the normalized concrete witness. -/
theorem estimate_wit :
    4 * (Finset.univ.filter (fun s : Fin 1 → Bool × Fin 10000 =>
      runDist 1 (Equiv.refl _) (false, 0) (fun _ => 1) (Ket (false, 1)) s ≤ 2 / 25 ∧
      ((chainPerm (Equiv.refl _) (pinnedSeq (false, 0) 1 s) 1).symm (false, 0)).1
        ≠ false)).card ≥ (Fintype.card (Bool × Fin 10000)) ^ 1 := by
  have key := thm36Core (I := Bool × Fin 10000) (T := 1) (hT1 := by omega)
      (lab := Prod.fst) (π0 := Equiv.refl (Bool × Fin 10000)) (y₀ := (false, 0))
      (x₀ := (false, 0)) (hx₀ := rfl) (hbal := witness_labels)
      (U := fun _ => 1) (hU := fun _ => one_mem _) (init := Ket (false, 1))
      (hinit := le_of_eq witness_seed.1) (hx₀m := witness_seed.2)
      (hregime := witness_regime)
  simpa only [witness_card, pow_one] using key

end QatlibTests.QueryCoupling
