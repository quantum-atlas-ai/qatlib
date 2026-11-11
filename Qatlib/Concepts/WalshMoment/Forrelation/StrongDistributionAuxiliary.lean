/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Character energies and strong Bernoulli weights

`bitDot` and `regXor` express Boolean characters on registers. `gammaOfMultiset` is the
normalized pairwise character sum; `gammaOfMultiset_eq_characterSquare` rewrites it as a square,
yielding nonnegativity and the bound by the sample length. `strongBernoulliWeight` assigns
product weights to Boolean functions whose zero input is false, and its nonnegativity and
equality with `strongBernoulliWeight_absVersion` are established.

For Boolean Fourier and quantum register background, see [Roetteler, 2008][Roetteler2008] and
[NielsenChuang2010].

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010].
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Matrix
open scoped BigOperators
open Classical
set_option autoImplicit false

/-- The Boolean dot product of two registers, computed modulo two using `booleanDotBool`. -/
def bitDot {n : ℕ} (y z : Reg n) : Bool :=
  Qatlib.Concepts.HspRecovery.ReductionCore.booleanDotBool y z

/-- The coordinatewise exclusive-or of two registers. -/
abbrev regXor {n : ℕ} (x y : Reg n) : Reg n :=
  Qatlib.Concepts.HspRecovery.ReductionCore.regXor x y

/-- The sum of the character signs of all ordered pairwise exclusive-ors of the indexed sample
`s`, divided by `ℓ`. -/
noncomputable def gammaOfMultiset (n ℓ : ℕ) (s : Fin ℓ → Reg n) (y : Reg n) : ℝ :=
  (1 / (ℓ : ℝ)) *
    ∑ i : Fin ℓ, ∑ j : Fin ℓ,
      (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)

/-- The product weight with false factor `exp (-κ * |gammaOfMultiset n ℓ s y|) / 2` at each
nonzero input `y` and the complementary true factor. The weight is zero when `u` is true at
the zero register. -/
noncomputable def strongBernoulliWeight_absVersion (n ℓ : ℕ) (κ : ℝ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) : ℝ :=
  if u (ZeroStr n) then 0
  else
    ∏ y : Reg n,
      if y = ZeroStr n then 1
      else if u y then 1 - Real.exp (-(κ : ℝ) * |gammaOfMultiset n ℓ s y|) / 2
      else Real.exp (-(κ : ℝ) * |gammaOfMultiset n ℓ s y|) / 2

/-- The product weight with false factor `exp (-κ * gammaOfMultiset n ℓ s y) / 2` at each
nonzero input `y` and the complementary true factor. The weight is zero when `u` is true at
the zero register. -/
noncomputable def strongBernoulliWeight (n ℓ : ℕ) (κ : ℝ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) : ℝ :=
  if u (ZeroStr n) then 0
  else
    ∏ y : Reg n,
      if y = ZeroStr n then 1
      else if u y then 1 - Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) / 2
      else Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) / 2

/-- The complex Boolean character on the converted registers equals the sign determined by their
Boolean dot product. -/
private theorem booleanCharacter_eq_bitDotSign {n : ℕ} (y z : Reg n) :
    Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n y)
      (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n z) =
        (if bitDot y z then (-1 : ℂ) else 1) := by
  rw [Qatlib.Concepts.WalshMoment.Forrelation.booleanCharacter_regBooleanEquiv_apply]
  have hzero : bitDot y z = false ↔
      (∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (y i && z i)) = 0 := by
    simpa [bitDot, Qatlib.Concepts.WalshMoment.Forrelation.booleanDot_regBooleanEquiv] using!
      Qatlib.Concepts.HspRecovery.ReductionCore.booleanDotBool_eq_false_iff y z
  cases hb : bitDot y z with
  | false =>
      simp [hzero.mp hb]
  | true =>
      let d : ZMod 2 :=
          ∑ i, Qatlib.Concepts.WalshMoment.Forrelation.boolZModEquiv (y i && z i)
      have hne : d ≠ 0 := by
        intro hz
        have : bitDot y z = false := hzero.mpr (by simpa [d] using! hz)
        simp [hb] at this
      have hone : d = 1 := by
        have hv : d.val < 2 := ZMod.val_lt d
        have hv0 : d.val ≠ 0 := fun hval => hne ((ZMod.val_eq_zero d).mp hval)
        have hv1 : d.val = 1 := by omega
        apply ZMod.val_injective 2
        simpa using! hv1
      simp [d, hone, Qatlib.Concepts.WalshMoment.Forrelation.zmod2_stdAddChar_one]

/-- The real character sign of an exclusive-or is the product of the character signs of its two
inputs. -/
private theorem bitDot_sign_xor {n : ℕ} (y x z : Reg n) :
    (if bitDot y (regXor x z) then (-1 : ℝ) else 1) =
      (if bitDot y x then (-1 : ℝ) else 1) *
        (if bitDot y z then (-1 : ℝ) else 1) := by
  have hchar :
      Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n y)
        (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n (regXor x z)) =
      Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n y)
        (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n x) *
      Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n y)
        (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n z) := by
    rw [Qatlib.Concepts.HspRecovery.ReductionCore.regBooleanEquiv_xor]
    exact (Qatlib.Concepts.PauliClifford.ExactRank.booleanCharacter (Qatlib.Concepts.WalshMoment.Forrelation.regBooleanEquiv n y)).map_add_eq_mul _ _
  rw [booleanCharacter_eq_bitDotSign, booleanCharacter_eq_bitDotSign,
    booleanCharacter_eq_bitDotSign] at hchar
  have hre := congrArg Complex.re hchar
  cases hx : bitDot y x <;> cases hz : bitDot y z <;>
    cases hxor : bitDot y (regXor x z) <;>
    simp [hx, hz, hxor] at hre ⊢ <;> assumption

/-- The pairwise character energy `gammaOfMultiset` equals the square of the sample's character
sum divided by `ℓ`. -/
theorem gammaOfMultiset_eq_characterSquare (n ℓ : ℕ) (s : Fin ℓ → Reg n)
    (y : Reg n) :
    gammaOfMultiset n ℓ s y =
      (1 / (ℓ : ℝ)) *
        (∑ i : Fin ℓ, (if bitDot y (s i) then (-1 : ℝ) else 1)) ^ 2 := by
  have hterm (i j : Fin ℓ) :
      (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1) =
        (if bitDot y (s i) then (-1 : ℝ) else 1) *
          (if bitDot y (s j) then (-1 : ℝ) else 1) :=
    bitDot_sign_xor y (s i) (s j)
  have hsum :
      (∑ i : Fin ℓ, (if bitDot y (s i) then (-1 : ℝ) else 1)) ^ 2 =
        ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          (if bitDot y (s i) then (-1 : ℝ) else 1) *
            (if bitDot y (s j) then (-1 : ℝ) else 1) := by
    calc
      _ = (∑ i : Fin ℓ, (if bitDot y (s i) then (-1 : ℝ) else 1)) *
          (∑ j : Fin ℓ, (if bitDot y (s j) then (-1 : ℝ) else 1)) := by ring
      _ = ∑ i : Fin ℓ,
          (if bitDot y (s i) then (-1 : ℝ) else 1) *
            (∑ j : Fin ℓ, (if bitDot y (s j) then (-1 : ℝ) else 1)) := by
          rw [Finset.sum_mul]
      _ = ∑ i : Fin ℓ, ∑ j : Fin ℓ,
          (if bitDot y (s i) then (-1 : ℝ) else 1) *
            (if bitDot y (s j) then (-1 : ℝ) else 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
  unfold gammaOfMultiset
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hterm i j

/-- The character energy `gammaOfMultiset` is nonnegative for every indexed sample and
character. -/
theorem gammaOfMultiset_nonneg (n ℓ : ℕ) (s : Fin ℓ → Reg n) (y : Reg n) :
    0 ≤ gammaOfMultiset n ℓ s y := by
  rw [gammaOfMultiset_eq_characterSquare]
  exact mul_nonneg (by positivity) (sq_nonneg _)

/-- The absolute value of `gammaOfMultiset` is at most the sample length `ℓ`. -/
theorem gammaOfMultiset_abs_le (n ℓ : ℕ) (s : Fin ℓ → Reg n) (y : Reg n) :
    |gammaOfMultiset n ℓ s y| ≤ (ℓ : ℝ) := by
  unfold gammaOfMultiset
  by_cases hℓ : ℓ = 0
  · simp [hℓ]
  · have h1 : 0 < (ℓ : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hℓ)
    have hε : ∀ i j : Fin ℓ,
        (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1) = 1
          ∨ (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1) = -1 := by
      intro i j
      by_cases h : bitDot y (regXor (s i) (s j)) <;> simp [h]
    have h2 : |(∑ i : Fin ℓ, ∑ j : Fin ℓ,
        (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1))| ≤ (ℓ : ℝ) * ℓ := by
      have h3 : ∀ i j : Fin ℓ,
          |(if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)| ≤ 1 := by
        intro i j
        rcases hε i j with h | h <;> rw [h] <;> norm_num
      have h4 : |(∑ i : Fin ℓ, ∑ j : Fin ℓ,
          (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1))|
          ≤ ∑ i : Fin ℓ, |∑ j : Fin ℓ,
            (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      have h5 : ∀ i : Fin ℓ, |∑ j : Fin ℓ,
          (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)| ≤ (ℓ : ℝ) := by
        intro i
        have h6 : |∑ j : Fin ℓ,
            (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)|
            ≤ ∑ j : Fin ℓ, |(if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)| :=
          Finset.abs_sum_le_sum_abs _ _
        have h7 : (∑ j : Fin ℓ,
            |(if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)|) ≤ ∑ j : Fin ℓ, (1:ℝ) :=
          Finset.sum_le_sum fun j _ => h3 i j
        have h8 : (∑ j : Fin ℓ, (1:ℝ)) = (ℓ : ℝ) := by simp
        linarith
      have h9 : (∑ i : Fin ℓ, |∑ j : Fin ℓ,
          (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1)|)
          ≤ ∑ i : Fin ℓ, (ℓ : ℝ) :=
        Finset.sum_le_sum fun i _ => h5 i
      have h10 : (∑ i : Fin ℓ, (ℓ : ℝ)) = (ℓ : ℝ) * ℓ := by simp
      linarith
    have h3 : |1 / (ℓ : ℝ)| = 1 / (ℓ : ℝ) := abs_of_pos (by positivity)
    rw [abs_mul, h3]
    have h4 : (1 / (ℓ : ℝ)) * ((ℓ : ℝ) * ℓ) = (ℓ : ℝ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt h1)]
      ring
    have h5 : (1 / (ℓ : ℝ)) * |(∑ i : Fin ℓ, ∑ j : Fin ℓ,
        (if bitDot y (regXor (s i) (s j)) then (-1 : ℝ) else 1))|
        ≤ (1 / (ℓ : ℝ)) * ((ℓ : ℝ) * ℓ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [h4] at h5
    exact h5

/-- For nonnegative `κ`, every strong Bernoulli product weight is nonnegative. -/
theorem strongBernoulliWeight_nonneg (n ℓ : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (s : Fin ℓ → Reg n)
    (u : Reg n → Bool) : 0 ≤ strongBernoulliWeight n ℓ κ s u := by
  unfold strongBernoulliWeight
  by_cases h : u (ZeroStr n)
  · simp [h]
  · simp only [h]
    apply Finset.prod_nonneg
    intro y _
    by_cases hy : y = ZeroStr n
    · simp [hy]
    · by_cases hu : u y
      · simp only [hy, hu, ite_true, ite_false]
        have hγ : 0 ≤ gammaOfMultiset n ℓ s y := gammaOfMultiset_nonneg n ℓ s y
        have h1 : Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : -(κ : ℝ) * gammaOfMultiset n ℓ s y ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) hγ
          linarith
        have : (0:ℝ) ≤ 1 - Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) / 2 := by
          nlinarith
        exact this
      · simp only [hy, hu, ite_false]
        have : (0:ℝ) ≤ Real.exp (-(κ : ℝ) * gammaOfMultiset n ℓ s y) / 2 :=
          div_nonneg (Real.exp_nonneg _) (by norm_num)
        exact this

/-- The strong Bernoulli weight agrees with the version using the absolute value of the
character energy, since that energy is nonnegative. -/
theorem strongBernoulliWeight_original_eq_absVersion (n ℓ : ℕ) (κ : ℝ)
    (s : Fin ℓ → Reg n) (u : Reg n → Bool) :
    strongBernoulliWeight n ℓ κ s u = strongBernoulliWeight_absVersion n ℓ κ s u := by
  by_cases hzero : u (ZeroStr n)
  · simp [strongBernoulliWeight, strongBernoulliWeight_absVersion, hzero]
  · simp only [strongBernoulliWeight, strongBernoulliWeight_absVersion, hzero]
    congr 1
    apply Finset.prod_congr rfl
    intro y hy
    by_cases hyzero : y = ZeroStr n
    · simp [hyzero]
    · by_cases huy : u y <;>
        simp [hyzero, huy, abs_of_nonneg (gammaOfMultiset_nonneg n ℓ s y)]

end Qatlib.Concepts.WalshMoment.Forrelation
