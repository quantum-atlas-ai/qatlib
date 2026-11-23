/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.SimulationWord

/-!
# Uniform bounds for the actual compiled Suzuki simulation

All estimates concern the genuine matrix generator list and its nested
commutators. Their constants are independent of the oracle and dimension.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Papers.SpectralGap11.MainResults.SimulationWord

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The free phase generator has exactly the norm of the ancilla projector. -/
theorem phase_norm (P : Matrix I I ℂ) : ‖phaseGenerator P‖ = ‖P‖ := by
  simp [phaseGenerator, norm_smul]

/-- Normalized projector and oracle bounds give a uniform total generator
mass, independent of the Hilbert-space dimension and the oracle entries. -/
theorem generators_mass (U P : Matrix I I ℂ) (η : ℝ)
    (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hη : |η| ≤ 1) :
    suzukiMass (generators U P η) ≤ 4 := by
  have hfirst : ‖firstGenerator U P‖ ≤ 1 := by
    calc
      _ ≤ ‖U‖ * ‖phaseGenerator P‖ * ‖U‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * 1 * 1 := by rw [phase_norm]; gcongr
      _ = 1 := by norm_num
  have hone : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := l2_norm_unitary_le_one (by simp)
  have hrem : ‖(1 : Matrix I I ℂ) - P‖ ≤ 2 := by
    have h := norm_sub_le (1 : Matrix I I ℂ) P
    linarith
  have hsecond : ‖secondGenerator P η‖ ≤ 3 := by
    rw [secondGenerator, phase_norm]
    have h := norm_add_le (-P) ((η : ℂ) • (1 - P))
    rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
    nlinarith [norm_nonneg ((1 : Matrix I I ℂ) - P), abs_nonneg η]
  change ‖firstGenerator U P‖ + (‖secondGenerator P η‖ + 0) ≤ 4
  linarith

/-- Every member norm is bounded by the actual sum of generator norms. -/
theorem member_norm_mass (xs : List (Matrix I I ℂ)) (X : Matrix I I ℂ) (hX : X ∈ xs) :
    ‖X‖ ≤ suzukiMass xs := by
  induction xs with
  | nil => simp at hX
  | cons Y ys ih =>
    simp only [List.mem_cons] at hX
    change ‖X‖ ≤ ‖Y‖ + suzukiMass ys
    rcases hX with rfl | hX
    · exact le_add_of_nonneg_right (general_trotter_mass_nonneg ys)
    · exact (ih hX).trans (le_add_of_nonneg_left (norm_nonneg Y))

/-- A commutator has norm at most twice the product of its two input norms. -/
theorem commutator_norm (Y D : Matrix I I ℂ) :
    ‖pfComm Y D‖ ≤ 2 * ‖Y‖ * ‖D‖ := by
  calc
    _ ≤ ‖Y * D‖ + ‖D * Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖ * ‖D‖ + ‖D‖ * ‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

/-- Each additional commutator contributes a factor at most `2B`. -/
theorem fold_norm (xs : List (Matrix I I ℂ)) (B : ℝ) (hB : 0 ≤ B)
    (hxs : ∀ X ∈ xs, ‖X‖ ≤ B) (D : Matrix I I ℂ) :
    ‖xs.foldl (fun Z Y => pfComm Y Z) D‖ ≤ ‖D‖ * (2 * B) ^ xs.length := by
  induction xs generalizing D with
  | nil => simp
  | cons X xs ih =>
    have hX := hxs X (by simp)
    have htail : ∀ Y ∈ xs, ‖Y‖ ≤ B := fun Y hY => hxs Y (by simp [hY])
    have hc : ‖pfComm X D‖ ≤ 2 * B * ‖D‖ :=
      (commutator_norm X D).trans (by gcongr)
    calc
      _ ≤ ‖pfComm X D‖ * (2 * B) ^ xs.length := ih htail _
      _ ≤ (2 * B * ‖D‖) * (2 * B) ^ xs.length :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- A nested commutator on `m` bounded generators has norm at most `(2B)^m`. -/
theorem nested_norm (xs : List (Matrix I I ℂ)) (B : ℝ) (hB : 0 ≤ B)
    (hxs : ∀ X ∈ xs, ‖X‖ ≤ B) :
    ‖pfNestedCommList xs‖ ≤ (2 * B) ^ xs.length := by
  cases xs with
  | nil => simp [pfNestedCommList]
  | cons X xs =>
    have hX : ‖X‖ ≤ 2 * B := (hxs X (by simp)).trans (by linarith)
    have htail : ∀ Y ∈ xs, ‖Y‖ ≤ B := fun Y hY => hxs Y (by simp [hY])
    calc
      _ ≤ ‖X‖ * (2 * B) ^ xs.length := fold_norm xs B hB htail X
      _ ≤ (2 * B) * (2 * B) ^ xs.length :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      _ = _ := by rw [List.length_cons, pow_succ']

/-- The actual nested-commutator coefficient is bounded by the number of
generator tuples times a uniform bound for each tuple. -/
theorem commutator_budget (xs : List (Matrix I I ℂ)) (B : ℝ) (hB : 0 ≤ B)
    (hxs : ∀ X ∈ xs, ‖X‖ ≤ B) (n : ℕ) :
    pfCommAlphaSelf xs n ≤ (2 * B * (xs.length : ℝ)) ^ n := by
  have hchosen (idx : Fin n → Fin xs.length) :
      ‖pfNestedCommList (pfChosenList xs idx)‖ ≤ (2 * B) ^ n := by
    have hb : ∀ X ∈ pfChosenList xs idx, ‖X‖ ≤ B := by
      intro X hX
      obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hX
      apply hxs
      rw [← List.getElem_eq_getD (h := (idx j).isLt)]
      exact List.getElem_mem _
    simpa [pfChosenList] using nested_norm (pfChosenList xs idx) B hB hb
  calc
    _ ≤ ∑ _idx : Fin n → Fin xs.length, (2 * B) ^ n :=
      Finset.sum_le_sum fun idx _hi => hchosen idx
    _ = (xs.length : ℝ) ^ n * (2 * B) ^ n := by simp
    _ = (2 * B * (xs.length : ℝ)) ^ n := by rw [mul_pow]; ring

/-- An explicit dimension-independent bound on the true recursive Suzuki
commutator coefficient for the normalized amplified Hamiltonian. -/
theorem recursive_budget (U P : Matrix I I ℂ) (η : ℝ)
    (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hη : |η| ≤ 1) (k n : ℕ) :
    pfCommAlphaSelf (recursiveSuzukiGenerators (generators U P η) k) n ≤
      (2 * (4 * (3 : ℝ) ^ k) * (4 * (5 : ℝ) ^ k)) ^ n := by
  have hmass := (recursive_suzuki_length_and_mass I (generators U P η) k).2
  have hm : suzukiMass (recursiveSuzukiGenerators (generators U P η) k) ≤
      4 * (3 : ℝ) ^ k := by
    have hbase := generators_mass U P η hU hP hη
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) k]
  have hlen := (recursive_suzuki_length_and_mass I (generators U P η) k).1
  have hnorms : ∀ X ∈ recursiveSuzukiGenerators (generators U P η) k,
      ‖X‖ ≤ 4 * (3 : ℝ) ^ k := fun X hX => (member_norm_mass _ X hX).trans hm
  have hb := commutator_budget _ (4 * (3 : ℝ) ^ k) (by positivity) hnorms n
  rw [hlen] at hb
  simpa [generators] using hb

omit [Fintype I] [DecidableEq I] in
/-- Taking the order root of the time polynomial gives the uniform source
exponent, with a harmless unit offset that includes zero time. -/
theorem root_time_bound (p : ℕ) (hp : 0 < p) (A τ : ℝ) (hA : 0 ≤ A) :
    (A * |τ| ^ (p + 1)) ^ (1 / (p : ℝ)) ≤
      A ^ (1 / (p : ℝ)) * (1 + |τ|) ^ (1 + 1 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hR : 0 ≤ 1 + |τ| := by positivity
  have hpow : |τ| ^ (p + 1) ≤ (1 + |τ|) ^ (p + 1) :=
    pow_le_pow_left₀ (abs_nonneg τ) (by linarith [abs_nonneg τ]) _
  have hroot := Real.rpow_le_rpow (by positivity) hpow
    (by positivity : 0 ≤ (1 / (p : ℝ)))
  have hexp : ((p + 1 : ℕ) : ℝ) * (1 / (p : ℝ)) = 1 + 1 / (p : ℝ) := by
    push_cast
    field_simp
  have hRpow : ((1 + |τ|) ^ (p + 1)) ^ (1 / (p : ℝ)) =
      (1 + |τ|) ^ (1 + 1 / (p : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR, hexp]
  rw [Real.mul_rpow hA (by positivity)]
  exact mul_le_mul_of_nonneg_left (hroot.trans hRpow.le) (Real.rpow_nonneg hA _)

omit [Fintype I] [DecidableEq I] in
/-- Rounding an explicitly bounded order-root expression contributes only a
uniform additive unit to the segment-count coefficient. -/
theorem rounded_root_bound (p : ℕ) (hp : 0 < p) (A τ : ℝ) (hA : 0 ≤ A) :
    ((max 1 (Nat.ceil ((A * |τ| ^ (p + 1)) ^ (1 / (p : ℝ)))) : ℕ) : ℝ) ≤
      (1 + A ^ (1 / (p : ℝ))) * (1 + |τ|) ^ (1 + 1 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hunit : 1 ≤ (1 + |τ|) ^ (1 + 1 / (p : ℝ)) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by positivity)
  have hrate : 0 ≤ A ^ (1 / (p : ℝ)) := Real.rpow_nonneg hA _
  have hr := root_time_bound p hp A τ hA
  have hc := (Nat.ceil_lt_add_one
    (Real.rpow_nonneg (show 0 ≤ A * |τ| ^ (p + 1) by positivity) (1 / (p : ℝ)))).le
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le <;> nlinarith

/-- A fixed bound for the matched-order commutator coefficient. -/
def uniformBudget (k : ℕ) : ℝ :=
  (2 * (4 * (3 : ℝ) ^ k) * (4 * (5 : ℝ) ^ k)) ^ (2 * (k + 1) + 1)

/-- The order-root coefficient depends only on the Suzuki order and accuracy. -/
def uniformRate (k : ℕ) (ε : ℝ) : ℝ :=
  ((((2 * (k + 1)).factorial : ℝ) * uniformBudget k) /
    (((2 * (k + 1) + 1).factorial : ℝ) * ε)) ^ (1 / (2 * (k + 1) : ℝ))

/-- The full fixed query coefficient includes the actual `4*5^k` calls per segment. -/
def uniformConstant (k : ℕ) (ε : ℝ) : ℝ :=
  (4 * (5 : ℝ) ^ k) * (1 + uniformRate k ε)

omit [Fintype I] [DecidableEq I] in
/-- The uniform coefficient is strictly positive for every positive accuracy. -/
theorem uniformConstant_pos (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < uniformConstant k ε := by
  unfold uniformConstant uniformRate uniformBudget
  positivity

/-- The library's actual segment choice obeys a fixed power-law upper bound
for all normalized oracle/projector inputs and all real simulation times. -/
theorem segments_uniform (U P : Matrix I I ℂ) (η : ℝ)
    (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hη : |η| ≤ 1)
    (k : ℕ) (τ ε : ℝ) (hε : 0 < ε) :
    (segments U P η k τ ε : ℝ) ≤
      (1 + uniformRate k ε) * (1 + |τ|) ^ (1 + 1 / (2 * (k + 1) : ℝ)) := by
  let p := 2 * (k + 1)
  let α := pfCommAlphaSelf (recursiveSuzukiGenerators (generators U P η) k) (p + 1)
  let A := ((p.factorial : ℝ) * uniformBudget k) / (((p + 1).factorial : ℝ) * ε)
  have hp : 0 < p := by dsimp [p]; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hα0 : 0 ≤ α := Finset.sum_nonneg fun _idx _hi => norm_nonneg _
  have hα : α ≤ uniformBudget k := recursive_budget U P η hU hP hη k (p + 1)
  have hA : 0 ≤ A := by dsimp [A, uniformBudget]; positivity
  have hinside : ((p.factorial : ℝ) * α * |τ| ^ (p + 1)) /
      (((p + 1).factorial : ℝ) * ε) ≤ A * |τ| ^ (p + 1) := by
    calc
      _ ≤ ((p.factorial : ℝ) * uniformBudget k * |τ| ^ (p + 1)) /
          (((p + 1).factorial : ℝ) * ε) := by gcongr
      _ = _ := by dsimp [A]; ring
  have hroot := Real.rpow_le_rpow (by positivity) hinside
    (by positivity : 0 ≤ (1 / (p : ℝ)))
  have hceil := Nat.ceil_mono hroot
  have hcount : segments U P η k τ ε ≤
      max 1 (Nat.ceil ((A * |τ| ^ (p + 1)) ^ (1 / (p : ℝ)))) := by
    unfold segments Qatlib.Papers.TrotterSuzuki15.MainResults.SourceMainTheorem.sourceRecursiveSegments
    apply max_le_max_left 1
    simpa only [p, α, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hceil
  have hreal : (segments U P η k τ ε : ℝ) ≤
      ((max 1 (Nat.ceil ((A * |τ| ^ (p + 1)) ^ (1 / (p : ℝ)))) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hbound := hreal.trans (rounded_root_bound p hp A τ hA)
  simpa only [A, p, uniformRate, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hbound

/-- The syntactic oracle count has a coefficient fixed before all oracle,
dimension, penalty and time parameters. No scalar cost is supplied by the caller. -/
theorem program_uniform (U P : Matrix I I ℂ) (η : ℝ)
    (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hη : |η| ≤ 1)
    (k : ℕ) (τ ε : ℝ) (hε : 0 < ε) :
    (queryCount (program k τ (segments U P η k τ ε)) : ℝ) ≤
      uniformConstant k ε * (1 + |τ|) ^ (1 + 1 / (2 * (k + 1) : ℝ)) := by
  have hs := segments_uniform U P η hU hP hη k τ ε hε
  calc
    _ = (segments U P η k τ ε : ℝ) * (4 * (5 : ℝ) ^ k) := by
      rw [program_queries]
      push_cast
      rfl
    _ ≤ ((1 + uniformRate k ε) * (1 + |τ|) ^ (1 + 1 / (2 * (k + 1) : ℝ))) *
        (4 * (5 : ℝ) ^ k) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by unfold uniformConstant; ring

end Qatlib.Papers.SpectralGap11.MainResults.SimulationWord
