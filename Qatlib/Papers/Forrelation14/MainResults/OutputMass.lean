/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Forrelation14.MainResults.ForrelationModel
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# The Forrelation output distribution

Equation (1) of arXiv:1411.5729v1 is the squared norm of the amplitude
vector after alternating diagonal sign oracles and register Hadamards.
The layer recurrence below is linked to the existing finite path sum.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.Forrelation14.MainResults.Model

namespace Qatlib.Papers.Forrelation14.MainResults

variable {n : ℕ}

/-- The character of the additive two-element group. -/
private def bitPhase (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

/-- A sum of binary phases corresponds to multiplication of their signs. -/
private theorem bitPhase_add (a b : ZMod 2) : bitPhase (a + b) = bitPhase a * bitPhase b := by
  have h (c : ZMod 2) : c = 0 ∨ c = 1 := by decide +revert
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;>
    norm_num [bitPhase]; decide

/-- Expanding the parity into its terms yields the product of the bitwise signs. -/
private theorem walsh_eq_prod (x y : Cube n) :
    (walsh x y : ℂ) = ∏ i, if x i && y i then (-1 : ℂ) else 1 := by
  classical
  have hsum (s : Finset (Fin n)) :
      bitPhase (∑ i ∈ s, bitVal (x i) * bitVal (y i)) =
        ∏ i ∈ s, bitPhase (bitVal (x i) * bitVal (y i)) := by
    induction s using Finset.induction_on with
    | empty => simp [bitPhase]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bitPhase_add, ih]
  have hlo (i : Fin n) :
      bitPhase (bitVal (x i) * bitVal (y i)) = if x i && y i then (-1 : ℂ) else 1 := by
    cases hx : x i <;> cases hy : y i <;> norm_num [hx, hy, bitVal, bitPhase]
  calc
    (walsh x y : ℂ) = bitPhase (dot x y) := by unfold walsh bitPhase; split <;> simp_all
    _ = _ := by unfold dot; rw [hsum]; simp_rw [hlo]

/-- The register's uniform-amplitude denominator factors over its qubits. -/
private theorem sqrt_card_cube (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- The formal register Hadamard has the source Walsh coefficient at each matrix entry. -/
private theorem hadamardN_walsh (x y : Cube n) :
    HadamardN n y x = ((walsh x y / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) := by
  rw [hadamardN_apply]
  simp_rw [Bool.and_comm (y _) (x _), ← walsh_eq_prod]
  push_cast
  rw [sqrt_card_cube, div_eq_mul_inv, inv_pow, mul_comm, Complex.ofReal_pow]

/-- The real Walsh transform inherits norm preservation from the register Hadamard. -/
theorem hadamardOf_sum_sq (v : RealCube n) :
    (∑ z, hadamardOf v z ^ 2) = ∑ z, v z ^ 2 := by
  have h := sum_normSq_mulVec_of_mem_unitaryGroup (hadamardN_unitary n) (fun z => (v z : ℂ))
  have hentry (z : Cube n) :
      (HadamardN n *ᵥ (fun x => (v x : ℂ))) z = (hadamardOf v z : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, hadamardN_walsh, hadamardOf, Complex.ofReal_div,
      Complex.ofReal_sum, Complex.ofReal_mul, div_mul_eq_mul_div, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  simpa only [hentry, Complex.normSq_ofReal, ← sq] using h

/-- Begin with uniform amplitudes, then apply each sign oracle followed by the Walsh transform. -/
def forrelationAmplitude (n : ℕ) :
    (k : ℕ) → (Fin k → Cube n → Bool) → RealCube n
  | 0, _ => fun _ => 1 / Real.sqrt ((2 : ℝ) ^ n)
  | k + 1, f => hadamardOf fun x =>
      forrelationAmplitude n k (fun j => f j.castSucc) x * sign (f (Fin.last k) x)

/-- The recurrence retains squared norm one at each oracle depth. -/
theorem forrelationAmplitude_sum_sq (k : ℕ) (f : Fin k → Cube n → Bool) :
    (∑ z, forrelationAmplitude n k f z ^ 2) = 1 := by
  induction k with
  | zero =>
    simp only [forrelationAmplitude, div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ)^n),
      Finset.sum_const, Finset.card_univ, Cube, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  | succ k ih =>
    rw [forrelationAmplitude, hadamardOf_sum_sq]
    rw [← ih (fun j => f j.castSucc)]
    apply Finset.sum_congr rfl
    intro z _
    cases f (Fin.last k) z <;> simp

/-- The Walsh factor at one position, using the output label after the final oracle. -/
private def pathWalsh {k : ℕ} (x : Fin k → Cube n) (z : Cube n) (j : Fin k) : ℝ :=
  if h : j.val + 1 < k then walsh (x j) (x ⟨j.val + 1, h⟩)
  else if _ : j.val + 1 = k then walsh (x j) z else 1

/-- The product of oracle and Walsh factors of one path in the source sum. -/
private def pathWeight {k : ℕ} (f : Fin k → Cube n → Bool) (x : Fin k → Cube n)
    (z : Cube n) : ℝ :=
  (∏ j : Fin k, sign (f j (x j))) * ∏ j : Fin k, pathWalsh x z j

/-- Splitting off the path's last register gives the last oracle and the last Walsh factor. -/
private theorem pathWeight_snoc {k : ℕ} (f : Fin (k + 1) → Cube n → Bool)
    (x : Fin k → Cube n) (a z : Cube n) :
    pathWeight f (Fin.snoc x a) z =
      pathWeight (fun j => f j.castSucc) x a * sign (f (Fin.last k) a) * walsh a z := by
  let t : Fin (k + 1) → Cube n := Fin.snoc x a
  have hterm (j : Fin k) : pathWalsh t z j.castSucc = pathWalsh x a j := by
    have hlt : j.castSucc.val + 1 < k + 1 := by simp
    unfold pathWalsh
    rw [dite_eq_left hlt]
    dsimp only [t]
    rw [Fin.snoc_castSucc]
    by_cases hj : j.val + 1 < k
    · rw [dite_eq_left hj]
      have hi : (⟨j.castSucc.val + 1, hlt⟩ : Fin (k + 1)) =
          (⟨j.val + 1, hj⟩ : Fin k).castSucc := Fin.ext rfl
      rw [hi, Fin.snoc_castSucc]
    · rw [dite_eq_right hj]
      have he : j.val + 1 = k := by omega
      have hi : (⟨j.castSucc.val + 1, hlt⟩ : Fin (k + 1)) = Fin.last k := Fin.ext he
      rw [hi, Fin.snoc_last]
      simp [he]
  have hlast : pathWalsh t z (Fin.last k) = walsh a z := by
    simp [pathWalsh, t]
  change pathWeight f t z = _
  unfold pathWeight
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, hlast]
  simp_rw [hterm]
  dsimp only [t]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- Reindexing the finite path sum by its final intermediate register. -/
private theorem sum_pathWeight_succ {k : ℕ} (f : Fin (k + 1) → Cube n → Bool) (z : Cube n) :
    (∑ x, pathWeight f x z) =
      ∑ a, (∑ x, pathWeight (fun j => f j.castSucc) x a) * sign (f (Fin.last k) a) * walsh a z := by
  let e := Fin.snocEquiv (n := k) (fun _ => Cube n)
  rw [← Equiv.sum_comp e (fun x => pathWeight f x z), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  exact pathWeight_snoc f x a z

/-- The normalized layer recurrence is the explicit path sum divided by
one uniform factor and one Walsh factor per layer. -/
private theorem forrelationAmplitude_path (k : ℕ) (f : Fin k → Cube n → Bool) (z : Cube n) :
    forrelationAmplitude n k f z =
      (∑ x, pathWeight f x z) / (Real.sqrt ((2 : ℝ) ^ n)) ^ (k + 1) := by
  induction k generalizing z with
  | zero => simp [forrelationAmplitude, pathWeight]
  | succ k ih =>
    rw [forrelationAmplitude, hadamardOf, sum_pathWeight_succ, pow_succ, ← div_div]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    rw [ih]
    ring

/-- For a nonempty sequence, the public normalization agrees with all the layer factors. -/
private theorem kfoldNorm_eq_amplitudeNorm (k n : ℕ) (hk : 0 < k) :
    kfoldNorm k n = (Real.sqrt ((2 : ℝ) ^ n)) ^ (k + 1) := by
  have hsq : (Real.sqrt ((2 : ℝ) ^ n)) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  have hmul : (Real.sqrt 2) ^ ((k - 1) * n) =
      (Real.sqrt ((2 : ℝ) ^ n)) ^ (k - 1) := by
    rw [sqrt_card_cube, ← pow_mul, Nat.mul_comm]
  calc
    kfoldNorm k n = (Real.sqrt ((2 : ℝ) ^ n)) ^ 2 * (Real.sqrt ((2 : ℝ) ^ n)) ^ (k - 1) := by
      rw [kfoldNorm, hmul, hsq]
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The public twisted sum is the final amplitude of the normalized layers. -/
theorem kfoldForrelationAt_eq_amplitude {k : ℕ} (hk : 0 < k)
    (f : Fin k → Cube n → Bool) (z : Cube n) :
    kfoldForrelationAt f z = forrelationAmplitude n k f z := by
  rw [forrelationAmplitude_path, ← kfoldNorm_eq_amplitudeNorm k n hk]
  rfl

/-- Equation (1): the squared output amplitudes sum to one for every nonempty Boolean tuple. -/
theorem kfoldForrelationAt_sum_sq {k : ℕ} (hk : 0 < k) (f : Fin k → Cube n → Bool) :
    (∑ z, kfoldForrelationAt f z ^ 2) = 1 := by
  simp_rw [kfoldForrelationAt_eq_amplitude hk]
  exact forrelationAmplitude_sum_sq k f

/-- The zero direction in Lemma 35 selects every outcome, so its mass
deviates from one half by exactly one half. -/
theorem kfoldForrelationAt_zero_slice {k : ℕ} (hk : 0 < k) (f : Fin k → Cube n → Bool) :
    |(∑ z : Cube n, if dot z (fun _ => false) = 0 then kfoldForrelationAt f z ^ 2 else 0) -
      1 / 2| = 1 / 2 := by
  simp only [dot_zero_right, ite_true]
  rw [kfoldForrelationAt_sum_sq hk]
  norm_num

/-- The concentration tolerance displayed in Lemma 35. -/
def sliceTolerance (n : ℕ) : ℝ :=
  Real.rpow (Real.log ((2 : ℝ) ^ n)) (5 / 2) / Real.sqrt ((2 : ℝ) ^ n)

/-- The existing good-tuple predicate with the half-mass estimate
restricted to the nonzero directions used in the proof of Lemma 35. -/
def GoodTupleNonzero {k : ℕ} (f : Fin k → Cube n → Bool) : Prop :=
  (∀ x : Cube n, |kfoldForrelationAt f x| ≤ Real.log ((2 : ℝ) ^ n)) ∧
    ∀ y : Cube n, y ≠ (fun _ => false) →
      |(∑ z : Cube n, if dot z y = 0 then kfoldForrelationAt f z ^ 2 else 0) - 1 / 2| ≤
        sliceTolerance n

/-- The uniform fraction of oracle tuples satisfying the corrected event. -/
def goodTupleNonzeroFraction (k n : ℕ) : ℝ := by
  classical
  exact uniformProb (k := k) (n := n) GoodTupleNonzero

/-- The sole extra condition imposed by the all-direction predicate
is that the tolerance accommodate a deviation of one half. -/
theorem goodTuple_iff_nonzero {k : ℕ} (hk : 0 < k) (f : Fin k → Cube n → Bool) :
    GoodTuple f ↔ GoodTupleNonzero f ∧ 1 / 2 ≤ sliceTolerance n := by
  constructor
  · intro h
    have hz := h.2 (fun _ => false)
    rw [kfoldForrelationAt_zero_slice hk f] at hz
    exact ⟨⟨h.1, fun y _ => h.2 y⟩, hz⟩
  · intro h
    refine ⟨h.1.1, fun y => ?_⟩
    by_cases hy : y = (fun _ => false)
    · subst y
      rw [kfoldForrelationAt_zero_slice hk f]
      exact h.2
    · exact h.1.2 y hy

/-- A tolerance below one half rules out every tuple in the all-direction model. -/
theorem not_goodTuple_of_small_budget {k : ℕ} (hk : 0 < k) (f : Fin k → Cube n → Bool)
    (hbudget : sliceTolerance n < 1 / 2) : ¬ GoodTuple f := by
  intro h
  exact (not_le_of_gt hbudget) ((goodTuple_iff_nonzero hk f).mp h).2

end Qatlib.Papers.Forrelation14.MainResults
