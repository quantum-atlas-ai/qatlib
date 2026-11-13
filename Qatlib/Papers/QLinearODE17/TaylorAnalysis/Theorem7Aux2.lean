/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Aux
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux2
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec

/-!
# History and padding mass of Taylor-system solutions

`taylorNatBlock` extends block extraction to natural labels by zero. A partition of the full
squared norm, factorial tail estimates, and adjacent-boundary estimates yield
`taylorV2_history_mass_le`; padding blocks are identified with the terminal time block. See
[BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylorNatBlock`: The block of `x` at natural label `l`, defined to be zero when `l` lies
  outside the finite label range.
* `taylorNatBlock_pad`: Every terminal-padding block of a V2 solution equals its terminal time
  block.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator BigOperators

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The block of `x` at natural label `l`, defined to be zero when `l` lies outside the finite
label range. -/
def taylorNatBlock {L : ℕ} (x : QState (Fin L × N)) (l : ℕ) : QState N :=
  fun n => if hl : l < L then x (⟨l,hl⟩,n) else 0

omit [Fintype N] [DecidableEq N] in

/-- At a valid finite label, `taylorNatBlock` agrees with `taylorBlock`. -/
theorem taylorNatBlock_eq {m k p : ℕ}
    (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (l : Fin (m * (k + 1) + p + 1)) : taylorNatBlock x l.val = taylorBlock x l := by
  funext n
  simp [taylorNatBlock, taylorBlock, l.isLt]

/-- A sum over `m*K` consecutive natural indices splits into `m` blocks of `K` terms. -/
theorem taylor_sum_range_mul (m K : ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ Finset.range (m * K), f l) =
      ∑ a ∈ Finset.range m, ∑ j ∈ Finset.range K, f (a * K + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

omit [DecidableEq N] in

/-- The full squared Euclidean norm splits into the sum of history-block squared norms and
terminal-padding squared norms. -/
theorem taylorV2_norm_partition (m k p : ℕ)
    (x : QState (Fin (m * (k + 1) + p + 1) × N)) :
    ‖stateVector x‖ ^ 2 =
      (∑ a ∈ Finset.range m, ∑ j ∈ Finset.range (k + 1),
        ‖stateVector (taylorNatBlock x (a * (k + 1) + j))‖ ^ 2) +
      ∑ j ∈ Finset.range (p + 1),
        ‖stateVector (taylorNatBlock x (m * (k + 1) + j))‖ ^ 2 := by
  have hlabels : ‖stateVector x‖ ^ 2 =
      ∑ l ∈ Finset.range (m * (k + 1) + p + 1),
        ‖stateVector (taylorNatBlock x l)‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [stateVector_norm_sq, MeasureProb, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    simp [BornProb, taylorNatBlock, l.isLt]
  rw [hlabels]
  change (∑ l ∈ Finset.range (m * (k + 1) + (p + 1)),
    ‖stateVector (taylorNatBlock x l)‖ ^ 2) = _
  rw [Finset.sum_range_add, taylor_sum_range_mul]

/-- The sum of the first `m` positive odd numbers is `m²`. -/
theorem taylor_sum_odd (m : ℕ) :
    (∑ i ∈ Finset.range m, (2 * (i : ℝ) + 1)) = (m : ℝ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- For `m > 0`, the sum of `(2*i+1)/(25*m)` over `i < m` equals `m / 25`. -/
theorem taylor_time_error_sum (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m, (2 * (i : ℝ) + 1) / (25 * m)) = (m : ℝ) / 25 := by
  rw [← Finset.sum_div, taylor_sum_odd]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp

/-- For `k ≥ 1`, the indicated reciprocal-factorial tail starting at `2!` is at most `23 / 32`. -/
theorem taylor_factorial_tail_le (k : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.range (k - 1), (Nat.factorial (j + 2) : ℝ)⁻¹) ≤ 23 / 32 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) (k + 1)
  rw [show k + 1 = 2 + (k - 1) by omega, Finset.sum_range_add] at h
  norm_num [Finset.sum_range_succ, add_comm] at h
  linarith [exp_one_le]

/-- The initial sum of squared reciprocal factorials starting at `1!` is at most `32 / 25`. -/
theorem taylor_factorial_sq_positive_le (k : ℕ) :
    (∑ j ∈ Finset.range k, (Nat.factorial (j + 1) : ℝ)⁻¹ ^ 2) ≤ 32 / 25 := by
  have h := factorial_recip_sq_sum_le k
  rw [Finset.sum_range_succ'] at h
  norm_num at h
  simp only [inv_pow]
  linarith

/-- For a V2 Taylor-system solution, the next boundary block is the sum of the preceding history
block. -/
theorem taylorNatBlock_jump (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (a : ℕ) (ha : a < m) :
    taylorNatBlock x ((a + 1) * (k + 1)) =
      ∑ j ∈ Finset.range (k + 1), taylorNatBlock x (a * (k + 1) + j) := by
  have hJ := taylorV2_block_jump m k p M h x_in b x hx (a + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hJ
  rw [← Fin.sum_univ_eq_sum_range]
  rw [taylorNatBlock_eq x ⟨(a + 1) * (k + 1), jump_label_lt _ _ _ _ (by omega)⟩]
  rw [hJ]
  apply Finset.sum_congr rfl
  intro j _
  exact (taylorNatBlock_eq x ⟨a * (k + 1) + j, step_label_lt _ _ _ _ _ ha (by omega)⟩).symm

/-- For a V2 solution with `‖M‖ ≤ 1`, the positive-order block norm is at most the first-order
block norm divided by its factorial. -/
theorem taylorNatBlock_positive_le (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (hM : ‖M‖ ≤ 1) (hk : 1 ≤ k) (a : ℕ) (ha : a < m)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖stateVector (taylorNatBlock x (a * (k + 1) + j))‖ ≤
      (Nat.factorial j : ℝ)⁻¹ * ‖stateVector (taylorNatBlock x (a * (k + 1) + 1))‖ := by
  rw [taylorNatBlock_eq x ⟨_,step_label_lt _ _ _ _ _ ha hjk⟩,
    taylorNatBlock_eq x ⟨_,step_label_lt _ _ _ _ _ ha hk⟩]
  exact taylorV2_positiveBlock_norm_le m k p M h x_in b x hx hM hk a ha j hj hjk

omit [Fintype N] [DecidableEq N] in

/-- The map `stateVector` preserves finite sums of states. -/
theorem taylor_stateVector_sum (s : Finset ℕ) (f : ℕ → QState N) :
    stateVector (∑ i ∈ s, f i) = ∑ i ∈ s, stateVector (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, stateVector_add, ih]

/-- For a V2 solution with `‖M‖ ≤ 1`, `9 / 32` times the first-order block norm is at most the
sum of the adjacent boundary norms. -/
theorem taylorNatBlock_first_le (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (hM : ‖M‖ ≤ 1) (hk : 1 ≤ k) (a : ℕ) (ha : a < m) :
    (9 / 32 : ℝ) * ‖stateVector (taylorNatBlock x (a * (k + 1) + 1))‖ ≤
      ‖stateVector (taylorNatBlock x (a * (k + 1)))‖ +
        ‖stateVector (taylorNatBlock x ((a + 1) * (k + 1)))‖ := by
  let B := fun j => stateVector (taylorNatBlock x (a * (k + 1) + j))
  have hJ := congrArg stateVector (taylorNatBlock_jump m k p M h x_in b x hx a ha)
  conv at hJ => rhs; arg 1; arg 1; rw [show k + 1 = 2 + (k - 1) by omega]
  rw [Finset.sum_range_add,
    stateVector_add, taylor_stateVector_sum, taylor_stateVector_sum] at hJ
  have hvec : B 1 = stateVector (taylorNatBlock x ((a + 1) * (k + 1))) - B 0 -
      ∑ j ∈ Finset.range (k - 1), B (j + 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hJ
    rw [hJ]
    dsimp [B]
    simp only [add_comm 2]
    abel
  have htail : ‖∑ j ∈ Finset.range (k - 1), B (j + 2)‖ ≤ (23 / 32 : ℝ) * ‖B 1‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (k - 1), ‖B (j + 2)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (k - 1), (Nat.factorial (j + 2) : ℝ)⁻¹ * ‖B 1‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact taylorNatBlock_positive_le m k p M h x_in b x hx hM hk a ha (j+2)
          (by omega) (by have := Finset.mem_range.mp hj; omega)
      _ = (∑ j ∈ Finset.range (k - 1), (Nat.factorial (j + 2) : ℝ)⁻¹) * ‖B 1‖ :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (taylor_factorial_tail_le k hk) (norm_nonneg _)
  have htri := norm_sub_le (stateVector (taylorNatBlock x ((a+1)*(k+1))) - B 0)
    (∑ j ∈ Finset.range (k-1), B (j+2))
  rw [← hvec] at htri
  have htri2 := norm_sub_le (stateVector (taylorNatBlock x ((a+1)*(k+1)))) (B 0)
  dsimp [B] at *
  linarith

/-- For `g ≥ 1` and `0 ≤ u ≤ 2/25`, the square `(2*g+u)²` is at most `(4 + (102/25)*u)*g²`. -/
theorem taylor_adjacent_error_sq (g u : ℝ) (hg : 1 ≤ g) (hu : 0 ≤ u) (hu' : u ≤ 2/25) :
    (2*g+u)^2 ≤ (4+(102/25)*u)*g^2 := by
  have hg2 : g ≤ g^2 := by nlinarith
  have hg2' : 1 ≤ g^2 := by nlinarith
  have h1 := mul_nonneg hu (sub_nonneg.mpr hg2)
  have h2 := mul_nonneg hu (sub_nonneg.mpr hg2')
  have h3 := mul_nonneg hu (sub_nonneg.mpr hu')
  nlinarith

/-- The stated pointwise bounds on `Z` and `F` imply a total weighted squared mass at most
`70*m*g²*q²`. -/
theorem taylor_history_sum_bound (m : ℕ) (hm : 0 < m) (g q : ℝ)
    (hg : 1 ≤ g) (Z F : ℕ → ℝ)
    (hZ : ∀ i < m, 0 ≤ Z i ∧ Z i ≤ (26/25)*g*q)
    (hF : ∀ i < m, 0 ≤ F i ∧
      (9/32)*F i ≤ (2*g+(2*(i : ℝ)+1)/(25*m))*q) :
    (∑ i ∈ Finset.range m, ((Z i)^2+(32/25)*(F i)^2)) ≤ 70*m*g^2*q^2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let u := fun i : ℕ => (2*(i : ℝ)+1)/(25*m)
  have hu (i : ℕ) (hi : i < m) : 0 ≤ u i ∧ u i ≤ 2/25 := by
    have hiR : (i : ℝ)+1 ≤ m := by exact_mod_cast hi
    dsimp [u]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 25*m)).mpr
      linarith
  have hb (i : ℕ) (hi : i < m) :
      (Z i)^2+(32/25)*(F i)^2 ≤
      ((26/25)^2+(32/25)*(32/9)^2*(4+(102/25)*u i))* (g^2*q^2) := by
    have hz := hZ i hi
    have hf := hF i hi
    have hfs : F i ≤ (32/9)*(2*g+u i)*q := by dsimp [u]; linarith
    have hZsq := pow_le_pow_left₀ hz.1 hz.2 2
    have hFsq := pow_le_pow_left₀ hf.1 hfs 2
    have hquad := taylor_adjacent_error_sq g (u i) hg (hu i hi).1 (hu i hi).2
    have hFfinal : (F i)^2 ≤ (32/9)^2*(4+(102/25)*u i)*(g^2*q^2) := by
      calc
        _ ≤ ((32/9)*(2*g+u i)*q)^2 := hFsq
        _ = (32/9)^2*(2*g+u i)^2*q^2 := by ring
        _ ≤ (32/9)^2*((4+(102/25)*u i)*g^2)*q^2 := by gcongr
        _ = _ := by ring
    calc
      _ ≤ ((26/25)*g*q)^2+(32/25)*
          ((32/9)^2*(4+(102/25)*u i)*(g^2*q^2)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ Finset.range m,
      ((26/25)^2+(32/25)*(32/9)^2*(4+(102/25)*u i))*(g^2*q^2) :=
      Finset.sum_le_sum (fun i hi => hb i (Finset.mem_range.mp hi))
    _ = (((26/25)^2+(32/25)*(32/9)^2*4)*m+
        ((32/25)*(32/9)^2*(102/25))*(m/25))*(g^2*q^2) := by
      have hform (i : ℕ) :
          ((26/25)^2+(32/25)*(32/9)^2*(4+(102/25)*u i))*(g^2*q^2) =
          (((26/25)^2+(32/25)*(32/9)^2*4)*(g^2*q^2)) +
          (((32/25)*(32/9)^2*(102/25))*(g^2*q^2))*u i := by ring
      simp_rw [hform]
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum (Finset.range m) u
        (((32/25)*(32/9)^2*(102/25))*(g^2*q^2))]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [show (∑ i ∈ Finset.range m, u i) = (m : ℝ)/25 from taylor_time_error_sum m hm]
      ring
    _ ≤ 70 * ((m : ℝ)*(g^2*q^2)) := by
      have hC : ((26/25 : ℝ)^2+(32/25)*(32/9)^2*4)+
          ((32/25)*(32/9)^2*(102/25))/25 ≤ 70 := by norm_num
      have hnonneg : 0 ≤ (m : ℝ)*(g^2*q^2) := by positivity
      convert! mul_le_mul_of_nonneg_right hC hnonneg using 1
      ring
    _ = _ := by ring

/-- For a V2 solution satisfying the stated boundary norm bounds, the total history-region
squared mass is at most `70*m*g²*q²`. -/
theorem taylorV2_history_mass_le (m k p : ℕ) (M : Matrix N N ℂ) (h g q : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hm : 0 < m) (hk : 1 ≤ k) (hg : 1 ≤ g) (hq : 0 ≤ q)
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (hM : ‖M‖ ≤ 1)
    (hbase : ∀ i ≤ m, ‖stateVector (taylorNatBlock x (i*(k+1)))‖ ≤
      (g+(i : ℝ)/(25*m))*q) :
    (∑ a ∈ Finset.range m, ∑ j ∈ Finset.range (k+1),
      ‖stateVector (taylorNatBlock x (a*(k+1)+j))‖^2) ≤ 70*m*g^2*q^2 := by
  let Z := fun a => ‖stateVector (taylorNatBlock x (a*(k+1)))‖
  let F := fun a => ‖stateVector (taylorNatBlock x (a*(k+1)+1))‖
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hZ (a : ℕ) (ha : a < m) : 0 ≤ Z a ∧ Z a ≤ (26/25)*g*q := by
    refine ⟨norm_nonneg _, (hbase a (by omega)).trans ?_⟩
    have he : (a : ℝ)/(25*m) ≤ 1/25 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 25*m)]
      have ham : (a : ℝ) ≤ m := by exact_mod_cast ha.le
      linarith
    have hcoeff : g+(a : ℝ)/(25*m) ≤ (26/25)*g := by linarith
    exact mul_le_mul_of_nonneg_right hcoeff hq
  have hF (a : ℕ) (ha : a < m) : 0 ≤ F a ∧
      (9/32)*F a ≤ (2*g+(2*(a : ℝ)+1)/(25*m))*q := by
    refine ⟨norm_nonneg _, ?_⟩
    have h1 := taylorNatBlock_first_le m k p M h x_in b x hx hM hk a ha
    have h2 := add_le_add (hbase a (by omega)) (hbase (a+1) (by omega))
    have he : (g+(a : ℝ)/(25*m))*q + (g+((a+1 : ℕ) : ℝ)/(25*m))*q =
        (2*g+(2*(a : ℝ)+1)/(25*m))*q := by push_cast; ring
    rw [he] at h2
    exact h1.trans h2
  have hgroup (a : ℕ) (ha : a < m) :
      (∑ j ∈ Finset.range (k+1), ‖stateVector (taylorNatBlock x (a*(k+1)+j))‖^2) ≤
        (Z a)^2+(32/25)*(F a)^2 := by
    rw [Finset.sum_range_succ']
    change (∑ j ∈ Finset.range k, ‖stateVector (taylorNatBlock x (a*(k+1)+(j+1)))‖^2)+
      (Z a)^2 ≤ _
    have hs : (∑ j ∈ Finset.range k, ‖stateVector (taylorNatBlock x (a*(k+1)+(j+1)))‖^2) ≤
        (32/25)*(F a)^2 := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((Nat.factorial (j+1) : ℝ)⁻¹)^2*(F a)^2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hterm := taylorNatBlock_positive_le m k p M h x_in b x hx hM hk a ha
            (j+1) (by omega) (by have := Finset.mem_range.mp hj; omega)
          simpa only [mul_pow] using! pow_le_pow_left₀ (norm_nonneg _) hterm 2
        _ = (∑ j ∈ Finset.range k, ((Nat.factorial (j+1) : ℝ)⁻¹)^2)*(F a)^2 :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (taylor_factorial_sq_positive_le k) (sq_nonneg _)
    linarith
  calc
    _ ≤ ∑ a ∈ Finset.range m, ((Z a)^2+(32/25)*(F a)^2) :=
      Finset.sum_le_sum (fun a ha => hgroup a (Finset.mem_range.mp ha))
    _ ≤ _ := taylor_history_sum_bound m hm g q hg Z F hZ hF

/-- Every terminal-padding block of a V2 solution equals its terminal time block. -/
theorem taylorNatBlock_pad (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ)
    (x_in b : QState N) (x : QState (Fin (m * (k+1)+p+1) × N))
    (hx : taylorStepMatrixV2 m k p M *ᵥ x = taylorRHS m k p h x_in b)
    (j : ℕ) (hj : j ≤ p) :
    taylorNatBlock x (m*(k+1)+j) = taylorBlock x (taylorTimeLabel m k p m (le_refl m)) := by
  rw [taylorNatBlock_eq x ⟨_,pad_label_lt _ _ _ _ hj⟩]
  by_cases hj0 : j = 0
  · subst j; rfl
  · exact taylorV2_pad_copies m k p M h x_in b x hx j (by omega) hj

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
