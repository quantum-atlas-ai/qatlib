/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.ShrinkLemma
import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanSamplingProbability
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open scoped Classical
open Finset

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.HspRecovery.Distinguisher

namespace Qatlib.Papers.ExactSimon97.MainResults

def charFun {n : ℕ} (a : BoolVec n) : BoolVec n → ℂ :=
  fun x => ZMod.stdAddChar (dot a x)

@[simp] theorem charFun_apply {n : ℕ} (a x : BoolVec n) :
    charFun a x = ZMod.stdAddChar (dot a x) := rfl

theorem charFun_comm {n : ℕ} (a x : BoolVec n) : charFun a x = charFun x a := by
  simp [charFun, dot, mul_comm]

theorem charFun_add {n : ℕ} (a b x : BoolVec n) :
    charFun (a + b) x = charFun a x * charFun b x := by
  simp only [charFun, dot, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    AddChar.map_add_eq_mul]

theorem charFun_add_right {n : ℕ} (a x y : BoolVec n) :
    charFun a (x + y) = charFun a x * charFun a y := by
  simp only [charFun, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    AddChar.map_add_eq_mul]

def signPair {n : ℕ} (g h : BoolVec n) : ℂ :=
  ZMod.stdAddChar (dot g h)

theorem signPair_eq_charFun {n : ℕ} (g h : BoolVec n) :
    signPair g h = charFun g h := rfl

theorem signPair_comm {n : ℕ} (g h : BoolVec n) : signPair g h = signPair h g := by
  simp [signPair, dot, mul_comm]

def phaseCoset {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n))
    (x₀ g : BoolVec n) : BoolVec n → ℂ :=
  fun x => if x - x₀ ∈ S then normFactor S * charFun g x else 0

theorem phaseCoset_apply_mem {n : ℕ} {S : Submodule (ZMod 2) (BoolVec n)}
    {x₀ g x : BoolVec n} (hx : x - x₀ ∈ S) :
    phaseCoset S x₀ g x = normFactor S * charFun g x := by
  simp [phaseCoset, hx]

theorem phaseCoset_apply_not_mem {n : ℕ} {S : Submodule (ZMod 2) (BoolVec n)}
    {x₀ g x : BoolVec n} (hx : x - x₀ ∉ S) :
    phaseCoset S x₀ g x = 0 := by
  simp [phaseCoset, hx]

def ambientNorm (n : ℕ) : ℂ :=
  ((Real.sqrt ((2 : ℝ) ^ n) : ℂ))⁻¹

def walshHadamard {n : ℕ} (f : BoolVec n → ℂ) : BoolVec n → ℂ :=
  fun y => ambientNorm n * ∑ x, charFun y x * f x

theorem sum_coset_eq_sum_submodule {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n))
    (x₀ : BoolVec n) (F : BoolVec n → ℂ) :
    (∑ x, if x - x₀ ∈ S then F x else 0) = ∑ s : S, F (x₀ + s) := by
  classical
  let p : BoolVec n → Prop := fun x => x - x₀ ∈ S
  let e : {x : BoolVec n // p x} ≃ S := {
    toFun := fun x => ⟨x.1 - x₀, x.2⟩
    invFun := fun s => ⟨x₀ + s.1, by
      show x₀ + s.1 - x₀ ∈ S
      rw [show x₀ + s.1 - x₀ = s.1 by abel]
      exact s.2⟩
    left_inv := fun x => by
      apply Subtype.ext
      (try dsimp only)
      abel
    right_inv := fun s => by
      apply Subtype.ext
      (try dsimp only)
      abel }
  calc
    (∑ x, if x - x₀ ∈ S then F x else 0) =
        ∑ x ∈ Finset.univ.filter p, F x := by
      rw [← Finset.sum_filter]
    _ = ∑ x : {x : BoolVec n // p x}, F x.1 := by
      rw [Finset.sum_subtype (s := Finset.univ.filter p)]
      intro x
      simp
    _ = ∑ s : S, F (x₀ + s.1) := by
      refine Fintype.sum_equiv e (fun x : {x : BoolVec n // p x} => F x.1)
        (fun s : S => F (x₀ + s.1)) ?_
      intro x
      have hex : (e x).1 = x.1 - x₀ := rfl
      change F x.1 = F (x₀ + (e x).1)
      rw [hex, show x₀ + (x.1 - x₀) = x.1 by abel]

theorem sum_charFun_submodule {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n))
    (r : BoolVec n) :
    (∑ s : S, charFun r s) =
      if r ∈ ortho S then (Fintype.card S : ℂ) else 0 := by
  classical
  have hsum := sum_character_subgroup S.toAddSubgroup (booleanCharacter r)
  have hchars : (∑ s : S, charFun r s) =
      ∑ s : S.toAddSubgroup, booleanCharacter r s := by
    apply Finset.sum_congr rfl
    intro s _
    rfl
  rw [hchars, hsum]
  have hmem : booleanCharacter r ∈ characterAnnihilator S.toAddSubgroup ↔
      r ∈ ortho S := by
    rw [booleanCharacter_mem_characterAnnihilator_iff]
    constructor
    · intro h s hs
      exact h ⟨s, hs⟩
    · intro h s
      exact h s.1 s.2
  rw [if_congr hmem rfl rfl]
  split_ifs with hr
  · rfl
  · rfl

theorem mem_ortho_iff_mem_booleanOrthogonal {n : ℕ}
    (S : Submodule (ZMod 2) (BoolVec n)) (x : BoolVec n) :
    x ∈ ortho S ↔ x ∈ booleanOrthogonal S.toAddSubgroup := by
  rw [mem_ortho, mem_booleanOrthogonal]
  constructor
  · intro h s
    exact h s.1 s.2
  · intro h s hs
    exact h ⟨s, hs⟩

def orthoEquivBooleanOrthogonal {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n)) :
    ortho S ≃ booleanOrthogonal S.toAddSubgroup :=
  Equiv.subtypeEquivRight (fun x => mem_ortho_iff_mem_booleanOrthogonal S x)

theorem card_ortho_eq_card_characterAnnihilator {n : ℕ}
    (S : Submodule (ZMod 2) (BoolVec n)) :
    Fintype.card (ortho S) = Fintype.card (characterAnnihilator S.toAddSubgroup) := by
  classical
  calc
    Fintype.card (ortho S) =
        Fintype.card (booleanOrthogonal S.toAddSubgroup) :=
      Fintype.card_congr (orthoEquivBooleanOrthogonal S)
    _ = Fintype.card (characterAnnihilator S.toAddSubgroup) :=
      Fintype.card_congr (booleanOrthogonalCharacterEquiv S.toAddSubgroup).toEquiv

theorem card_mul_card_ortho {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n)) :
    Fintype.card S * Fintype.card (ortho S) = 2 ^ n := by
  classical
  have hann := card_characterAnnihilator S.toAddSubgroup
  have hcard := card_ortho_eq_card_characterAnnihilator S
  have hambient : Fintype.card (BooleanVec n) = 2 ^ n := by
    simp [BooleanVec, ZMod.card]
  calc
    Fintype.card S * Fintype.card (ortho S) =
        Fintype.card S * Fintype.card (characterAnnihilator S.toAddSubgroup) := by
      rw [hcard]
    _ = Fintype.card (characterAnnihilator S.toAddSubgroup) * Fintype.card S :=
      Nat.mul_comm _ _
    _ = Fintype.card (characterAnnihilator S.toAddSubgroup) *
          Fintype.card S.toAddSubgroup := rfl
    _ = Fintype.card (BooleanVec n) := hann
    _ = 2 ^ n := hambient

theorem ambientNorm_mul_card_mul_normFactor {n : ℕ}
    (S : Submodule (ZMod 2) (BoolVec n)) :
    ambientNorm n * (Fintype.card S : ℂ) * normFactor S = normFactor (ortho S) := by
  classical
  set A : ℝ := (Fintype.card S : ℝ) with hA
  set B : ℝ := (Fintype.card (ortho S) : ℝ) with hB
  set N : ℝ := (2 : ℝ) ^ n with hN
  have hApos : 0 < A := by
    rw [hA]
    exact_mod_cast Fintype.card_pos (α := S)
  have hBpos : 0 < B := by
    rw [hB]
    exact_mod_cast Fintype.card_pos (α := ortho S)
  have hNpos : 0 < N := by
    rw [hN]
    positivity
  have hAB : A * B = N := by
    have h := card_mul_card_ortho S
    have hcast : ((Fintype.card S * Fintype.card (ortho S) : ℕ) : ℝ) = (2 : ℝ) ^ n := by
      rw [h]
      norm_num
    push_cast at hcast
    simpa [hA, hB, hN] using hcast
  have hBreal : B = N / A := by
    field_simp [ne_of_gt hApos]
    linarith [hAB]
  have hsqrtB : Real.sqrt B = Real.sqrt N / Real.sqrt A := by
    rw [hBreal, Real.sqrt_div' _ (le_of_lt hApos)]
  have hreal : (Real.sqrt N)⁻¹ * A * (Real.sqrt A)⁻¹ = (Real.sqrt B)⁻¹ := by
    rw [hsqrtB, inv_div]
    have hsq : Real.sqrt A * Real.sqrt A = A := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hApos)]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hApos),
      ne_of_gt (Real.sqrt_pos.2 hNpos)]
    nlinarith [hsq]
  have hamb : ambientNorm n = ((Real.sqrt N : ℝ) : ℂ)⁻¹ := by
    simp [ambientNorm, hN]
  have hnf : normFactor S = ((Real.sqrt A : ℝ) : ℂ)⁻¹ := by
    rw [normFactor, hA, Nat.card_eq_fintype_card]
  have hnt : normFactor (ortho S) = ((Real.sqrt B : ℝ) : ℂ)⁻¹ := by
    rw [normFactor, hB, Nat.card_eq_fintype_card]
  rw [hamb, hnf, hnt]
  have hrealC : ((Real.sqrt N)⁻¹ * A * (Real.sqrt A)⁻¹ : ℝ) = (Real.sqrt B)⁻¹ := hreal
  calc
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (Fintype.card S : ℂ) *
        ((Real.sqrt A : ℝ) : ℂ)⁻¹
      = (((Real.sqrt N)⁻¹ * A * (Real.sqrt A)⁻¹ : ℝ) : ℂ) := by
        have hcard : (Fintype.card S : ℂ) = (A : ℂ) := by
          rw [hA]
          norm_num
        rw [hcard]
        push_cast
        ring
    _ = ((Real.sqrt B : ℝ) : ℂ)⁻¹ := by
      rw [hrealC]
      push_cast
      ring

theorem sum_phaseCoset_eq {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n))
    (x₀ g : BoolVec n) (F : BoolVec n → ℂ) :
    (∑ x, F x * phaseCoset S x₀ g x) =
      normFactor S * ∑ s : S, F (x₀ + s) * charFun g (x₀ + s) := by
  classical
  have hcoset : (∑ x, F x * phaseCoset S x₀ g x) =
      ∑ x ∈ Finset.univ.filter (fun x => x - x₀ ∈ S),
        F x * (normFactor S * charFun g x) := by
    calc
      (∑ x, F x * phaseCoset S x₀ g x) =
          ∑ x, if x - x₀ ∈ S then F x * (normFactor S * charFun g x) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x - x₀ ∈ S
        · rw [if_pos hx]
          simp [phaseCoset, hx]
        · rw [if_neg hx]
          simp [phaseCoset, hx]
      _ = ∑ x ∈ Finset.univ.filter (fun x => x - x₀ ∈ S),
            F x * (normFactor S * charFun g x) := by
        rw [Finset.sum_filter]
  rw [hcoset]

  calc
    ∑ x ∈ Finset.univ.filter (fun x => x - x₀ ∈ S),
        F x * (normFactor S * charFun g x) =
        ∑ x : {x : BoolVec n // x - x₀ ∈ S},
          F x.1 * (normFactor S * charFun g x.1) := by
      rw [Finset.sum_subtype (s := Finset.univ.filter (fun x => x - x₀ ∈ S))]
      intro x
      simp
    _ = ∑ s : S, F (x₀ + s.1) * (normFactor S * charFun g (x₀ + s.1)) := by
      let e : {x : BoolVec n // x - x₀ ∈ S} ≃ S := {
        toFun := fun x => ⟨x.1 - x₀, x.2⟩
        invFun := fun s => ⟨x₀ + s.1, by
          show x₀ + s.1 - x₀ ∈ S
          rw [show x₀ + s.1 - x₀ = s.1 by abel]
          exact s.2⟩
        left_inv := fun x => by
          apply Subtype.ext
          (try dsimp only)
          abel
        right_inv := fun s => by
          apply Subtype.ext
          (try dsimp only)
          abel }
      refine Fintype.sum_equiv e
        (fun x : {x : BoolVec n // x - x₀ ∈ S} =>
          F x.1 * (normFactor S * charFun g x.1))
        (fun s : S => F (x₀ + s.1) * (normFactor S * charFun g (x₀ + s.1))) ?_
      intro x
      have hex : (e x).1 = x.1 - x₀ := rfl
      change F x.1 * (normFactor S * charFun g x.1) =
        F (x₀ + (e x).1) * (normFactor S * charFun g (x₀ + (e x).1))
      rw [hex, show x₀ + (x.1 - x₀) = x.1 by abel]
    _ = normFactor S * ∑ s : S, F (x₀ + s) * charFun g (x₀ + s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem neg_eq_self_zmod2 (a : ZMod 2) : -a = a :=
  neg_eq_of_add_eq_zero_right (CharTwo.add_self_eq_zero a)

theorem boolVec_sub_eq_add {n : ℕ} (x h : BoolVec n) : x - h = x + h := by
  ext i
  show x i - h i = x i + h i
  rw [sub_eq_add_neg, neg_eq_self_zmod2]

theorem walshHadamard_phaseCoset {n : ℕ} (K : Submodule (ZMod 2) (BoolVec n))
    (g h : BoolVec n) :
    walshHadamard (phaseCoset K g h) =
      fun y => signPair g h * phaseCoset (ortho K) h g y := by
  classical
  funext y
  simp only [walshHadamard]
  rw [sum_phaseCoset_eq K g h (fun x => charFun y x)]
  have hterm : ∀ s : K,
      charFun y (g + s) * charFun h (g + s) =
        charFun (y + h) g * charFun (y + h) s := by
    intro s
    rw [charFun_add_right, charFun_add_right, charFun_add, charFun_add]
    ring
  have hsum_eq : (∑ s : K, charFun y (g + s) * charFun h (g + s)) =
      charFun (y + h) g * ∑ s : K, charFun (y + h) s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [hterm]
  rw [hsum_eq, sum_charFun_submodule]
  by_cases hy : y + h ∈ ortho K
  · have hy' : y - h ∈ ortho K := by
      rw [boolVec_sub_eq_add]
      exact hy
    rw [if_pos hy]
    simp only [phaseCoset, if_pos hy']
    rw [signPair_comm]
    have hsplit : charFun (y + h) g = charFun g y * charFun g h := by
      rw [charFun_add, charFun_comm y g, charFun_comm h g]
    rw [hsplit]
    have hscalar := ambientNorm_mul_card_mul_normFactor K
    calc
      ambientNorm n *
          (normFactor K * (charFun g y * charFun g h * (Fintype.card K : ℂ))) =
          (ambientNorm n * (Fintype.card K : ℂ) * normFactor K) *
            (charFun g y * charFun g h) := by ring
      _ = normFactor (ortho K) * (charFun g y * charFun g h) := by rw [hscalar]
      _ = charFun g h * (normFactor (ortho K) * charFun g y) := by ring
      _ = signPair h g * (normFactor (ortho K) * charFun g y) := by
        rw [signPair_eq_charFun, charFun_comm h g]
  · have hy' : y - h ∉ ortho K := by
      intro hcon
      apply hy
      rw [← boolVec_sub_eq_add]
      exact hcon
    rw [if_neg hy]
    simp [phaseCoset, hy']

end Qatlib.Papers.ExactSimon97.MainResults
