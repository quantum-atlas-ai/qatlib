module

public import Qatlib.Papers.HiddenTransl02.MainResults.FiniteCosetState

@[expose] public section

/-! Concrete consumer for the exact translating-coset state.  The ambient
group is the nontrivial four-element group obtained by transporting addition
on `ZMod 4` to multiplication. -/

set_option autoImplicit false

namespace QatlibTests.HiddenTransl02CosetStateRegression

open Qatlib.Papers.HiddenTransl02.MainResults

abbrev G4 := Multiplicative (ZMod 4)

noncomputable instance topFintype : Fintype (⊤ : Subgroup G4) := Fintype.ofFinite _

example :
    ∃ ψ : G4 → ℂ,
      l2NormSq ψ = 1 ∧
        ψ (Multiplicative.ofAdd (2 : ZMod 4)) ≠ 0 ∧
        ψ (Multiplicative.ofAdd (1 : ZMod 4)) ≠ 0 := by
  classical
  let H : Subgroup G4 := ⊤
  let : Fintype H := Fintype.ofFinite H
  let u : G4 := Multiplicative.ofAdd (1 : ZMod 4)
  let hspec := translatingCosetState_spec u H
  refine ⟨translatingCosetState u H, hspec.1, ?_, ?_⟩
  · apply (hspec.2.1 (Multiplicative.ofAdd (2 : ZMod 4))).2
    simp [H, u]
  · apply (hspec.2.1 (Multiplicative.ofAdd (1 : ZMod 4))).2
    simp [H, u]

example :
    ∀ h x : G4, h ∈ (⊤ : Subgroup G4) →
      translatingCosetState (Multiplicative.ofAdd (1 : ZMod 4)) (⊤ : Subgroup G4)
        (x * h) = translatingCosetState (Multiplicative.ofAdd (1 : ZMod 4)) (⊤ : Subgroup G4) x := by
  classical
  let : Fintype (⊤ : Subgroup G4) := Fintype.ofFinite _
  intro h x hh
  exact translatingCosetState_mul_right (Multiplicative.ofAdd (1 : ZMod 4)) (⊤ : Subgroup G4) hh

end QatlibTests.HiddenTransl02CosetStateRegression
