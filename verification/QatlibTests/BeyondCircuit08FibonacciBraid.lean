module

public import Qatlib.Papers.BeyondCircuit08.MainResults.BraidApprox.ErrorPropagation
public import Qatlib.Papers.BeyondCircuit08.MainResults.Density.DensityBase
public import Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport.HalfProdUnitary
public import Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf.EndpointRange

@[expose] public section

/-!
# Concrete consumers for the Fibonacci braid representation

Concrete non-degenerate consumers for the Dev theorems on error
propagation for composed braid words (Proposition 1), the one-dimensional
density base cases (Proposition 3 and Corollary 1), products of
half-support unitaries (Lemma 4), and the exact value range of the
Zeckendorf encoding (Proposition 4) of Stephen P. Jordan,
*Quantum Computation Beyond the Circuit Model*, arXiv:0809.2307v1 (2008).

The braid-word instance uses the swap unitary on `Fin 2` with words using
both generator signs; the half-support instance clears a column of an
explicit permutation matrix on `Fin 4`; the Zeckendorf instances evaluate
at lengths `3` and `4`, whose Fibonacci bounds are `5` and `8`.
-/

set_option autoImplicit false

open scoped Matrix Matrix.Norms.L2Operator

namespace QatlibTests.BeyondCircuit08FibonacciBraid

open Qatlib.Papers.BeyondCircuit08.MainResults.Model
open Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
open Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf
open Qatlib.Papers.BeyondCircuit08.MainResults.BraidApprox
open Qatlib.Papers.BeyondCircuit08.MainResults.Density
open Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
open Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf

/-- The swap matrix on two basis states, a non-identity unitary. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The swap matrix squares to the identity. -/
theorem swap2_mul_self : swap2 * swap2 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [swap2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The swap matrix is unitary, since it is real and squares to `1`. -/
theorem swap2_mem_unitaryGroup : swap2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hstar : star swap2 = swap2 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [swap2]
  rw [Matrix.mem_unitaryGroup_iff', hstar]
  exact swap2_mul_self

/-- The swap matrix is its own inverse. -/
theorem swap2_inv : swap2⁻¹ = swap2 :=
  Matrix.inv_eq_right_inv swap2_mul_self

/-- The single unitary generator used by the concrete braid words. -/
def genSwap : Fin (2 - 1) → Matrix (Fin 2) (Fin 2) ℂ := fun _ => swap2

/-- A word of crossing count one evaluating to the swap. -/
def wordPos : BraidWord 2 := [(⟨0, by decide⟩, true)]

/-- A word of crossing count one evaluating to the inverse swap. -/
def wordNeg : BraidWord 2 := [(⟨0, by decide⟩, false)]

/-- The positive word evaluates exactly to the swap target. -/
theorem eval_wordPos : evalWord genSwap wordPos = swap2 := by
  simp [evalWord, genSwap, wordPos]

/-- The negative word evaluates exactly to the swap target, because the
swap is self-inverse. -/
theorem eval_wordNeg : evalWord genSwap wordNeg = swap2 := by
  simp [evalWord, genSwap, wordNeg, swap2_inv]

/-- Concrete Proposition 1 error propagation: concatenating the positive
and negative swap words gives exactly the identity `swap2 * swap2`, as
witnessed by the operator-norm bound `‖·‖ ≤ 0 + 0` from
`evalWord_append_error_le_pair`. Both words are nonempty and the swap
is a non-identity unitary. -/
theorem eval_append_swap : evalWord genSwap (List.append wordPos wordNeg) = 1 := by
  have h1 : ‖evalWord genSwap wordPos - swap2‖ ≤ (0 : ℝ) := by
    rw [eval_wordPos]
    simp
  have h2 : ‖evalWord genSwap wordNeg - swap2‖ ≤ (0 : ℝ) := by
    rw [eval_wordNeg]
    simp
  have h := (evalWord_append_error_le_pair (extraStrands := 0) (gen := genSwap) (gen' := genSwap)
    (fun _ => swap2_mem_unitaryGroup) (fun _ => swap2_mem_unitaryGroup)
    wordPos wordNeg swap2_mem_unitaryGroup swap2_mem_unitaryGroup h1 h2 h1 h2).1
  rw [swap2_mul_self] at h
  have hnorm : ‖evalWord genSwap (List.append wordPos wordNeg) - 1‖ ≤ (0 : ℝ) := by
    simpa using h
  have hzero : evalWord genSwap (List.append wordPos wordNeg) - 1 = 0 :=
    norm_le_zero_iff.mp hnorm
  exact sub_eq_zero.mp hzero

/-- The concatenated swap word has crossing count two. -/
theorem crossing_append_swap :
    crossingCount (List.append wordPos wordNeg) = 2 := by
  exact (crossingCount_append wordPos wordNeg).trans rfl

/-- Concrete Proposition 3 base case: density modulo phase on the
one-dimensional `∗…∗` block at `n = 3`, exercised at the identity target
with tolerance `1 / 2`. -/
example :
    ∃ M ∈ Set.range (evalWord (starStarGen 3)), ∃ θ : ℝ,
      ‖(Complex.exp (θ * Complex.I)) • M -
        (1 : Matrix (StarStarBasis 3) (StarStarBasis 3) ℂ)‖ ≤ (1 / 2 : ℝ) :=
  proposition3_base_case 1 ⟨one_mem _, Matrix.det_one⟩ (1 / 2) (by norm_num)

/-- The `∗…∗` basis at `n = 3` is a singleton, as `card_starStarBasis_three`
states. -/
example : Fintype.card (StarStarBasis 3) = 1 := card_starStarBasis_three

/-- Concrete Corollary 1 base case: density modulo phase on the
one-dimensional `∗…p` block at `n = 1`, exercised at the identity target
with tolerance `1 / 3`. -/
example :
    ∃ M ∈ Set.range (evalWord (starPGen 1)), ∃ θ : ℝ,
      ‖(Complex.exp (θ * Complex.I)) • M -
        (1 : Matrix (StarPBasis 1) (StarPBasis 1) ℂ)‖ ≤ (1 / 3 : ℝ) :=
  corollary1_starP_base_case 1 ⟨one_mem _, Matrix.det_one⟩ (1 / 3)
    (by norm_num)

/-- The other endpoint order also gives phase density at one strand. -/
example : PhaseDenseOn (PStarBasis 1) (Set.range (evalWord (pStarGen 1))) :=
  corollary1_pStar_base_case

/-- The permutation matrix that moves the pivot entry in column zero to row one. -/
def swapRows01 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Concrete Lemma 4 step: a single unitary product of half-support
factors clears column `0` of an explicit permutation matrix on `Fin 4`
below the pivot row. -/
example :
    ∃ L : HalfSupports 4, AllHalf L ∧ halfProd L ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      ∀ r : Fin 4, r ≠ 0 → (halfProd L * swapRows01) r 0 = 0 :=
  exists_unitary_halfProd_clear_column swapRows01 (by norm_num) 0

/-- The empty product of half-support factors is the identity unitary. -/
example : halfProd ([] : HalfSupports 4) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  halfProd_mem_unitaryGroup (fun _ hp => (List.not_mem_nil hp).elim)

/-- A witnessed list of half-support factors fixes the complement of a common support. -/
example {L : HalfSupports 4} {S : Finset (Fin 4)} (hAll : AllHalf L)
    (hsub : ∀ p ∈ L, p.1 ⊆ S) : FixesComplement S (halfProd L) :=
  halfProd_fixes_complement hAll hsub

/-- At length `3` the Zeckendorf value `4` is attained, since
`4 < Nat.fib 5 = 5`. -/
example : (4 : ℕ) ∈ Set.range (fun s : PStrings 3 => (zMap s).val) := by
  rw [proposition4_value_range]
  exact Set.mem_Iio.mpr (by decide)

/-- At length `3` the printed top endpoint `5 = Nat.fib 5` of
Proposition 4 is not attained. -/
example : (5 : ℕ) ∉ Set.range (fun s : PStrings 3 => (zMap s).val) := by
  rw [proposition4_value_range]
  change ¬5 < Nat.fib 5
  decide

/-- There are `Nat.fib 6 = 8` allowed strings of length `4`. -/
example : Fintype.card (PStrings 4) = 8 := by
  rw [proposition4_card]
  decide

end QatlibTests.BeyondCircuit08FibonacciBraid
