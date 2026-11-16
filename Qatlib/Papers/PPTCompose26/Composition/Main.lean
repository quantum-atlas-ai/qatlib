/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PPTCompose26.Composition.Iteration
public import Qatlib.Papers.PPTCompose26.Composition.Reduction
public import Qatlib.Papers.PPTCompose26.Composition.Pair

@[expose] public section




/-!
# Main results

* `hasSchmidtNumberLE_refMap_comp` — **Lemma 5**: a pair of PPT maps lowers a Schmidt-number
  bound `s` to `max (s - 1) 1`.
* `hasSchmidtNumberLE_refMap_compList` — Eq. (25): `j` pairs lower it to `max (s - j) 1`.
* `isEntanglementBreaking_compList` — **Theorem 1**: if `|n| ≤ j + 1`, every ordered composition
  of `2 j` PPT maps on `M_n` is entanglement breaking. The maps may all differ and need not
  preserve the trace.
* `ebIndex_le` — the entanglement-breaking index of a PPT map on `M_n` is at most `2 j`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n : Type*}

/-- **Lemma 5.** If `Φ`, `Ψ` are PPT maps on `M_n` and `X` has Schmidt number at most `s`, then
`(id ⊗ (Ψ ∘ Φ))(X)` has Schmidt number at most `max (s - 1) 1`. -/
theorem hasSchmidtNumberLE_refMap_comp [Fintype κ] [Fintype n] [DecidableEq n]
    {Φ Ψ : Module.End ℂ (Matrix n n ℂ)} (hΦ : IsPPTMap Φ) (hΨ : IsPPTMap Ψ) {s : ℕ}
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : HasSchmidtNumberLE s X) :
    HasSchmidtNumberLE (max (s - 1) 1) (refMap κ (Ψ ∘ₗ Φ) X) :=
  hasSchmidtNumberLE_refMap_of_pair (hΨ.comp hΦ).1
    (fun _ hY => isSeparable_refMap_comp hΦ hΨ hY) hX

/-- Eq. (25): `j` pairs of PPT maps lower a Schmidt-number bound `s` to `max (s - j) 1`. -/
theorem hasSchmidtNumberLE_refMap_compList [Fintype κ] [Fintype n]
    [DecidableEq n] (j : ℕ) (L : List (Module.End ℂ (Matrix n n ℂ))) (hL : L.length = 2 * j)
    (hP : ∀ φ ∈ L, IsPPTMap φ) {s : ℕ} {X : Matrix (κ × n) (κ × n) ℂ}
    (hX : HasSchmidtNumberLE s X) :
    HasSchmidtNumberLE (max (s - j) 1) (refMap κ (compList L) X) :=
  hasSchmidtNumberLE_refMap_compList_of_core
    (fun _ _ h₁ h₂ _ _ h => hasSchmidtNumberLE_refMap_comp h₁ h₂ h) j L hL hP s X hX

/-- **Theorem 1.** If `|n| ≤ j + 1`, every ordered composition of `2 j` PPT maps on `M_n` is
entanglement breaking. -/
theorem isEntanglementBreaking_compList [Fintype n] [DecidableEq n] (j : ℕ)
    (L : List (Module.End ℂ (Matrix n n ℂ))) (hL : L.length = 2 * j)
    (hP : ∀ φ ∈ L, IsPPTMap φ) (hj : Fintype.card n ≤ j + 1) :
    IsEntanglementBreaking (compList L) :=
  isEntanglementBreaking_compList_of_core
    (fun _ _ _ h₁ h₂ _ _ h => hasSchmidtNumberLE_refMap_comp h₁ h₂ h) j L hL hP hj

/-- If `|n| ≤ j + 1`, the power `T ^ (2 j)` of a PPT map on `M_n` is entanglement breaking. -/
theorem isEntanglementBreaking_pow [Fintype n] [DecidableEq n]
    {T : Module.End ℂ (Matrix n n ℂ)} (hT : IsPPTMap T) (j : ℕ)
    (hj : Fintype.card n ≤ j + 1) : IsEntanglementBreaking (T ^ (2 * j)) :=
  isEntanglementBreaking_pow_of_core
    (fun _ _ _ h₁ h₂ _ _ h => hasSchmidtNumberLE_refMap_comp h₁ h₂ h) hT j hj

/-- The entanglement-breaking index of a PPT map on `M_n` is at most `2 j` when `|n| ≤ j + 1`
and `1 ≤ j`. -/
theorem ebIndex_le [Fintype n] [DecidableEq n] {T : Module.End ℂ (Matrix n n ℂ)}
    (hT : IsPPTMap T) (j : ℕ) (hj1 : 1 ≤ j) (hj : Fintype.card n ≤ j + 1) :
    ebIndex T ≤ ((2 * j : ℕ) : ℕ∞) :=
  ebIndex_le_of_core (fun _ _ _ h₁ h₂ _ _ h => hasSchmidtNumberLE_refMap_comp h₁ h₂ h) hT j hj1 hj

end Qatlib.Papers.PPTCompose26.Composition
