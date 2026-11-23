module

public import Qatlib.Papers.NilpotentHSP07.Proposition1Aut.PhiAut
public import Qatlib.Papers.NilpotentHSP07.CosetFourier.Lemma4Superposition

@[expose] public section

/-!
# Consumer regression for the NilpotentHSP07 automorphism and coset-normalization increment

This ordinary-module consumer specializes the new results to concrete non-degenerate instances:
the alternating coordinate form on `ZMod 3` with two first coordinates and one second
coordinate, the five-element cyclic group `Multiplicative (ZMod 5)`, and the two-point Fourier
register `Fin 1 → ZMod 2`.
-/

set_option autoImplicit false

namespace QatlibTests.NilpotentHSP07AutCosetRegression

open Qatlib.Papers.NilpotentHSP07.MainResults
open Qatlib.Papers.NilpotentHSP07.Proposition1Aut
open Qatlib.Papers.NilpotentHSP07.CosetFourier

/-- The alternating bilinear correction `x 0 * y 1 - x 1 * y 0` on `ZMod 3`. -/
def cmt3 (x y : Fin 2 → ZMod 3) : Fin 1 → ZMod 3 :=
  fun _ => x 0 * y 1 - x 1 * y 0

local instance nil2Form3 : Nil2Form 3 2 1 where
  cmt := cmt3
  cmt_zero_left := by
    intro y
    funext i
    fin_cases i
    simp [cmt3]
  cmt_add_left := by
    intro x1 x2 y
    funext i
    fin_cases i
    simp [cmt3, Pi.add_apply]
    ring
  cmt_zero_right := by
    intro x
    funext i
    fin_cases i
    simp [cmt3]
  cmt_add_right := by
    intro x y1 y2
    funext i
    fin_cases i
    simp [cmt3, Pi.add_apply]
    ring
  cmt_self := by
    intro x
    funext i
    fin_cases i
    simp [cmt3]
    ring
  surj_comm := by
    intro w
    refine ⟨fun i => if i = 0 then 2 * w 0 else 0,
      fun i => if i = 0 then 0 else 1, ?_⟩
    funext i
    fin_cases i
    simp [cmt3]
    ring_nf
    rw [show (4 : ZMod 3) = 1 by decide, mul_one]

/-- A concrete nonidentity coordinate element with first coordinates `(1, 0)`. -/
def gConcrete : Coord 3 2 1 :=
  ⟨fun i => if i = 0 then 1 else 0, fun _ => 0⟩

/-- The nonzero scaling by `2` sends `(1, 0)` to `(2, 0)`. -/
theorem phi_two_gConcrete :
    phi (p := 3) (m := 2) (d := 1) (2 : ZMod 3) gConcrete =
      (⟨fun i => if i = 0 then 2 else 0, fun _ => 0⟩ : Coord 3 2 1) := by
  apply Coord.ext <;> funext i
  · fin_cases i
    all_goals simp [phi, gConcrete]
  · fin_cases i
    all_goals simp [phi, gConcrete]

/-- The bundled automorphism for `j = 2` acts as the concrete coordinate scaling. -/
theorem phiAut_two_gConcrete :
    phiAut (p := 3) (m := 2) (d := 1) (2 : ZMod 3) (by decide) gConcrete =
      phi (p := 3) (m := 2) (d := 1) (2 : ZMod 3) gConcrete :=
  phiAut_apply _ _ _

/-- The automorphism family from Proposition 1 evaluated on the concrete coordinate model. -/
theorem proposition1_concrete :
    ∃ Phi : (ZMod 3)ˣ →* MulAut (Coord 3 2 1),
      (∀ (j : (ZMod 3)ˣ) (g : Coord 3 2 1), Phi j g = phi (j : ZMod 3) g) ∧
        (∀ (j : (ZMod 3)ˣ) (z : Coord 3 2 1), z ∈ gPrime →
          Phi j z = z ^ (((j : ZMod 3) * (j : ZMod 3))).val) :=
  proposition1_phi_automorphism (p := 3) (m := 2) (d := 1) (by norm_num)

/-- The five-element cyclic group used for the coset-state consumers. -/
abbrev G5 := Multiplicative (ZMod 5)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The normalized coset state of the full subgroup of the five-element cyclic group is a unit
vector in the true complex Euclidean norm. -/
theorem coset_norm_concrete :
    ‖toEuclidean (cosetState (⊤ : Subgroup G5) (1 : G5)
      (((Real.sqrt (Nat.card (⊤ : Subgroup G5))) : ℂ)⁻¹))‖ = 1 :=
  norm_cosetState_sqrt ⊤ 1

/-- The uniform form of the coset normalization specializes to the concrete five-element group,
with the constant `1` exposed outside the universal quantifiers. -/
theorem coset_norm_uniform_concrete :
    ∃ C : ℝ, 0 < C ∧
      ‖toEuclidean (cosetState (⊤ : Subgroup G5) (1 : G5)
        (((Real.sqrt (Nat.card (⊤ : Subgroup G5))) : ℂ)⁻¹))‖ = C := by
  obtain ⟨C, hC, h⟩ := norm_cosetState_sqrt_uniform
  exact ⟨C, hC, h (G := G5) (⊤ : Subgroup G5) 1⟩

/-- The two-point Fourier register `Fin 1 → ZMod 2` is non-degenerate. -/
theorem fourier_register_card : Fintype.card (Fin 1 → ZMod 2) = 2 := by
  simp

/-- The Lemma 4 superposition over the two-point Fourier register and full cosets in the
five-element cyclic group is a unit vector in the true complex Euclidean norm. -/
theorem fourier_norm_concrete :
    ‖fourierCosetVector (G := G5) (U := Fin 1 → ZMod 2)
      (fun _ => (⊤ : Subgroup G5)) (1 : G5)‖ = 1 :=
  norm_fourierCosetVector _ _

/-- The uniform form of the Lemma 4 superposition specializes to the concrete two-point Fourier
register and full cosets in the five-element cyclic group. -/
theorem fourier_norm_uniform_concrete :
    ∃ C : ℝ, 0 < C ∧
      ‖fourierCosetVector (G := G5) (U := Fin 1 → ZMod 2)
        (fun _ => (⊤ : Subgroup G5)) (1 : G5)‖ = C := by
  obtain ⟨C, hC, h⟩ := lemma4_superposition_uniform
  exact ⟨C, hC, h (G := G5) (U := Fin 1 → ZMod 2)
    (fun _ => (⊤ : Subgroup G5)) 1⟩

/-- Central coordinates of the five-element cyclic group, viewed as a one-dimensional register. -/
def centralCoordinates (x : G5) : Fin 1 → ZMod 5 := fun _ => x.toAdd

/-- The character-weighted superposition on the five-point register has Euclidean norm one. -/
theorem character_superposition_norm_concrete :
    ‖characterCosetSuperposition (⊤ : Subgroup G5) 1 centralCoordinates‖ = 1 :=
  norm_characterCosetSuperposition _ _ _

/-- One constant simultaneously normalizes the full-group and singleton coset superpositions. -/
theorem character_superposition_uniform_concrete :
    ∃ C : ℝ, 0 < C ∧
      ‖characterCosetSuperposition (⊤ : Subgroup G5) 1 centralCoordinates‖ = C ∧
      ‖characterCosetSuperposition (⊥ : Subgroup G5) 1 centralCoordinates‖ = C := by
  obtain ⟨C, hC, h⟩ := characterCosetSuperposition_uniform
  exact ⟨C, hC, h (G := G5) (p := 5) (d := 1) ⊤ 1 centralCoordinates,
    h (G := G5) (p := 5) (d := 1) ⊥ 1 centralCoordinates⟩

end QatlibTests.NilpotentHSP07AutCosetRegression
