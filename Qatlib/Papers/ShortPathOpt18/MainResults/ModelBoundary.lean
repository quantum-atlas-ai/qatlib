/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShortPathOpt18.MainResults.HypercubeMoment
public import Qatlib.Papers.ShortPathOpt18.MainResults.SourceModel

@[expose] public section


/-! Finite counterexamples to missing dimension and state restrictions. -/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ShortPathOpt18.MainResults

open Qatlib.Papers.ShortPathOpt18.MainResults

/-- On the one-site cube every even normalized walk moment equals one. -/
theorem moment_one (L : ℕ) (hL : Even L) : cubeMoment 1 L = 1 := by
  classical
  have hall : ∀ w : Fin L → Fin 1, EvenFiber w := by
    intro w i
    have hc : Fintype.card {j : Fin L // w j = i} = L := by
      let e : {j : Fin L // w j = i} ≃ Fin L := {
        toFun := Subtype.val
        invFun := fun j => ⟨j, Subsingleton.elim _ _⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      simpa using Fintype.card_congr e
    simpa only [hc] using hL
  have heq : (EvenFiber : (Fin L → Fin 1) → Prop) = fun _ => True := by
    funext w
    exact propext ⟨fun _ => trivial, fun _ => hall w⟩
  simp [cubeMoment, closedWalkCount, heq]

/-- The legacy strict monotonicity claim fails for N=1, L=2 and L'=4. -/
theorem moment_not_strict : ¬ cubeMoment 1 2 > cubeMoment 1 4 := by
  rw [moment_one 2 (by decide), moment_one 4 (by decide)]
  exact lt_irrefl _

/-- An arbitrary unit state can have negative signed overlap with the uniform state. -/
theorem negative_overlap :
    ∃ ψ : Config 0 → ℝ,
      Qatlib.Papers.ShortPathOpt18.MainResults.IsUnit ψ ∧ plusOverlap 0 ψ < 0 := by
  refine ⟨fun _ => -1, ?_, ?_⟩
  · norm_num [Qatlib.Papers.ShortPathOpt18.MainResults.IsUnit, normSq]
  · norm_num [plusOverlap, overlap, plusState]

/-- Negative basis states disprove signed positive overlap bounds in every dimension. -/
theorem negative_basis (N : ℕ) :
    ∃ ψ : Config N → ℝ,
      Qatlib.Papers.ShortPathOpt18.MainResults.IsUnit ψ ∧ plusOverlap N ψ < 0 := by
  refine ⟨fun u => -basisVec (zeroConfig N) u, ?_, ?_⟩
  · simpa [Qatlib.Papers.ShortPathOpt18.MainResults.IsUnit, normSq]
      using basisVec_zero_isUnit N
  · classical
    simp [plusOverlap, overlap, basisVec, plusState]
    positivity

end Qatlib.Papers.ShortPathOpt18.MainResults
