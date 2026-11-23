module

public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.ColoredCycleCount
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.PermanentSecondMoment

@[expose] public section


/-! # Concrete consumer checks for the LinearOptics10 advance

This ordinary module instantiates the corrected Proposition 55 colored-cycle
enumeration and the Lemma 56 normalized permanent second moment on concrete
non-degenerate inputs, verifying the resulting numerals against the fixed
source identities.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace QatlibTests.Papers.LinearOptics10.AdvanceRows
open Qatlib.Foundations.ProbabilityCore.Concentration.CycleCount
open Qatlib.Papers.LinearOptics10.StockmeyerSrc.ColoredCycleCount
open Qatlib.Papers.LinearOptics10.StockmeyerSrc.PermanentSecondMoment

/-- The concrete full cycle count of the actual transposition on `Fin 2`. -/
theorem swap_allCycles_value : allCycles (Equiv.swap (0 : Fin 2) 1) = 1 :=
  allCycles_swap_fin_two

/-- Proposition 55 at `(n, c) = (1, 2)`: the mean of `2^{cyc(σ)}` over `S_1` is `2`. -/
theorem prop55_one_at_two :
    (∑ sigma : Equiv.Perm (Fin 1), ((2 : ℕ) : ℝ) ^ allCycles sigma) / (Nat.factorial 1 : ℝ) = 2 := by
  have h := prop55_one 2 (by norm_num)
  rw [h]
  norm_num

/-- Proposition 55 at `(n, c) = (2, 3)`: the mean of `3^{cyc(σ)}` over `S_2` is `6`. -/
theorem prop55_two_at_three :
    (∑ sigma : Equiv.Perm (Fin 2), ((3 : ℕ) : ℝ) ^ allCycles sigma) / (Nat.factorial 2 : ℝ) = 6 := by
  have h := prop55_two 3 (by norm_num)
  rw [h]
  have hc : (2 + 3 - 1).choose (3 - 1) = 6 := by decide
  rw [hc]
  norm_num

/-- Lemma 56 at `n = 1`: the actual second moment of the normalized permanent
random variable equals `1 + 1 = 2`. -/
theorem permSqMoment_one_consumer : permSqMoment 1 = 2 :=
  permSqMoment_one

/-- Lemma 56 at `n = 2`: the actual second moment of the normalized permanent
random variable equals `2 + 1 = 3`. -/
theorem permSqMoment_two_consumer : permSqMoment 2 = 3 :=
  permSqMoment_two

end QatlibTests.Papers.LinearOptics10.AdvanceRows
