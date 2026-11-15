/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
public import Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStabilityThec
public import Qatlib.Foundations.ProbabilityCore.Concentration.GaussianShiftTVDBoundThec
public import Qatlib.Concepts.BosonFock.PermAnalysis.BosonDistributionNormalizationThec
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
open Qatlib.Concepts.BosonFock.PermAnalysis
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.CountingClasses.ClassTransport

set_option autoImplicit false

open Qatlib

open scoped BigOperators Nat ComplexConjugate Matrix

open Module MeasureTheory

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib.Foundations.ComplexGeometry.PhaseRecovery Qatlib.Foundations.ProbabilityCore.Concentration

/-- The isometry distribution of a complex matrix with orthonormal columns sums to one over all
Fock occupations. -/
theorem clause17_clause2 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∑ S : FockOccupation m n, loIsometryDist m n A S = 1 := by
  intro m n A hA
  exact Qatlib.Concepts.BosonFock.PermAnalysis.bosonDistributionNormalization m n A hA
open MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000

/-- Reindexing by a permutation moves its inverse from the second index to the first in a finite
product. -/
private theorem clause17Aux_permProd_symm {n : ℕ} {R : Type*} [CommMonoid R]
    (f : Fin n → Fin n → R) (σ : Equiv.Perm (Fin n)) :
    ∏ i, f i (σ.symm i) = ∏ i, f (σ i) i := by
  calc ∏ i, f i (σ.symm i)
      = ∏ i, (fun j => f j (σ.symm j)) i := rfl
    _ = ∏ i, (fun j => f j (σ.symm j)) (σ i) :=
        (Equiv.prod_comp σ (fun j => f j (σ.symm j))).symm
    _ = ∏ i, f (σ i) i :=
        Finset.prod_congr rfl fun i _ => by simp only [Equiv.symm_apply_apply]

/-- The permutation sum of matrix entry products is the permanent. -/
private theorem clause17Aux_permSum_permanent {n : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin n) (Fin n) R) :
    ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i) = Matrix.permanent M := by
  rw [Matrix.permanent]
  refine Fintype.sum_equiv
    (⟨fun σ => σ.symm, fun σ => σ.symm, fun σ => Equiv.symm_symm σ,
      fun σ => Equiv.symm_symm σ⟩ : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n)) _ _ ?_
  intro σ
  exact clause17Aux_permProd_symm (fun a b => M a b) (Equiv.symm σ)

/-- Bounds the change of a product under coordinatewise perturbations by the number of factors
times the perturbation bound times `B` to that power. -/
private theorem clause17Aux_prod_perturb : ∀ (n : ℕ) (x y : Fin n → ℂ) (δ B : ℝ),
    0 ≤ δ → 1 ≤ B → (∀ i, ‖x i‖ ≤ B) → (∀ i, ‖y i‖ ≤ B) → (∀ i, ‖x i - y i‖ ≤ δ) →
    ‖∏ i, x i - ∏ i, y i‖ ≤ (n : ℝ) * δ * B ^ n := by
  intro n
  induction n with
  | zero =>
    intro x y δ B _hδ _hB _hx _hy _hd
    simp
  | succ n ih =>
    intro x y δ B hδ hB hx hy hd
    have hpx : (∏ i : Fin (n + 1), x i) = x 0 * ∏ i : Fin n, x i.succ := Fin.prod_univ_succ x
    have hpy : (∏ i : Fin (n + 1), y i) = y 0 * ∏ i : Fin n, y i.succ := Fin.prod_univ_succ y
    rw [hpx, hpy]
    have hkey : x 0 * ∏ i : Fin n, x i.succ - y 0 * ∏ i : Fin n, y i.succ
        = x 0 * (∏ i : Fin n, x i.succ - ∏ i : Fin n, y i.succ)
          + (x 0 - y 0) * ∏ i : Fin n, y i.succ := by ring
    rw [hkey]
    have h1 : ‖x 0 * (∏ i : Fin n, x i.succ - ∏ i : Fin n, y i.succ)‖
        ≤ B * ((n : ℝ) * δ * B ^ n) := by
      rw [norm_mul]
      exact mul_le_mul (hx 0)
        (ih (fun i => x i.succ) (fun i => y i.succ) δ B hδ hB
          (fun i => hx i.succ) (fun i => hy i.succ) (fun i => hd i.succ))
        (norm_nonneg _) (by positivity)
    have h2 : ‖(x 0 - y 0) * ∏ i : Fin n, y i.succ‖ ≤ δ * B ^ n := by
      rw [norm_mul]
      have h2b : ‖∏ i : Fin n, y i.succ‖ ≤ B ^ n := by
        rw [norm_prod (Finset.univ : Finset (Fin n)) (fun i => y i.succ)]
        have h2b' : (∏ i : Fin n, ‖y i.succ‖) ≤ ∏ i : Fin n, B :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hy i.succ)
        rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2b'
      exact mul_le_mul (hd 0) h2b (norm_nonneg _) hδ
    have hadd := norm_add_le (x 0 * (∏ i : Fin n, x i.succ - ∏ i : Fin n, y i.succ))
      ((x 0 - y 0) * ∏ i : Fin n, y i.succ)
    have h3 : (B : ℝ) * ((n : ℝ) * δ * B ^ n) = (n : ℝ) * δ * B ^ (n + 1) := by
      rw [pow_succ]
      ring
    have h4 : δ * B ^ n ≤ δ * B ^ (n + 1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (pow_nonneg (by positivity : (0:ℝ) ≤ B) n) hB) hδ
    have h5 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hfin : ‖x 0 * (∏ i : Fin n, x i.succ - ∏ i : Fin n, y i.succ)
          + (x 0 - y 0) * ∏ i : Fin n, y i.succ‖
        ≤ ((n + 1 : ℕ) : ℝ) * δ * B ^ (n + 1) := by
      have h3' : (B : ℝ) * ((n : ℝ) * δ * B ^ n) = (n : ℝ) * δ * B ^ (n + 1) := h3
      nlinarith [h1, h2, hadd, h3', h4, h5,
        mul_nonneg (norm_nonneg (x 0))
          (norm_nonneg (∏ i : Fin n, x i.succ - ∏ i : Fin n, y i.succ)),
        mul_nonneg hδ (pow_nonneg (by positivity : (0:ℝ) ≤ B) (n + 1))]
    exact hfin

/-- An entrywise norm bound `B` bounds the permanent norm by `n` factorial times `B` to the
power `n`. -/
private theorem clause17Aux_permanent_norm_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B : ℝ)
    (hB : ∀ i j, ‖X i j‖ ≤ B) : ‖Matrix.permanent X‖ ≤ (n ! : ℝ) * B ^ n := by
  rw [← clause17Aux_permSum_permanent X]
  have h1 : ‖∑ σ : Equiv.Perm (Fin n), ∏ i, X i (σ i)‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i)‖ := norm_sum_le _ _
  have h2 : ∀ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i)‖ ≤ B ^ n := by
    intro σ
    rw [norm_prod (Finset.univ : Finset (Fin n)) (fun i => X i (σ i))]
    have h2' : (∏ i : Fin n, ‖X i (σ i)‖) ≤ ∏ i : Fin n, B :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hB i (σ i))
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2'
  have h3 : (∑ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i)‖) ≤ (n ! : ℝ) * B ^ n := by
    calc (∑ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i)‖)
        ≤ ∑ σ : Equiv.Perm (Fin n), (B ^ n : ℝ) := Finset.sum_le_sum fun σ _ => h2 σ
      _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * B ^ n := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (n ! : ℝ) * B ^ n := by rw [Fintype.card_perm, Fintype.card_fin]
  exact le_trans h1 h3

/-- For matrices with entry norms at most two, bounds the permanent difference using their
entrywise distance. -/
private theorem clause17Aux_permanent_perturb {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hX : ∀ i j, ‖X i j‖ ≤ 2) (hY : ∀ i j, ‖Y i j‖ ≤ 2)
    (hd : ∀ i j, ‖X i j - Y i j‖ ≤ δ) :
    ‖Matrix.permanent X - Matrix.permanent Y‖ ≤ (n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n) := by
  rw [← clause17Aux_permSum_permanent X, ← clause17Aux_permSum_permanent Y]
  have hsub : (∑ σ : Equiv.Perm (Fin n), ∏ i, X i (σ i))
        - (∑ σ : Equiv.Perm (Fin n), ∏ i, Y i (σ i))
      = ∑ σ : Equiv.Perm (Fin n), (∏ i, X i (σ i) - ∏ i, Y i (σ i)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsub]
  have hnorm : ‖∑ σ : Equiv.Perm (Fin n), (∏ i, X i (σ i) - ∏ i, Y i (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i) - ∏ i, Y i (σ i)‖ := norm_sum_le _ _
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖∏ i, X i (σ i) - ∏ i, Y i (σ i)‖ ≤ (n : ℝ) * δ * (2 : ℝ) ^ n := by
    intro σ
    exact clause17Aux_prod_perturb n (fun i => X i (σ i)) (fun i => Y i (σ i)) δ 2 hδ (by norm_num)
      (fun i => hX i (σ i)) (fun i => hY i (σ i)) (fun i => hd i (σ i))
  have hsum : (∑ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i) - ∏ i, Y i (σ i)‖)
      ≤ (n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n) := by
    calc (∑ σ : Equiv.Perm (Fin n), ‖∏ i, X i (σ i) - ∏ i, Y i (σ i)‖)
        ≤ ∑ σ : Equiv.Perm (Fin n), ((n : ℝ) * δ * (2 : ℝ) ^ n) :=
          Finset.sum_le_sum fun σ _ => hterm σ
      _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n) := by rw [Fintype.card_perm, Fintype.card_fin]
  exact le_trans hnorm hsum

/-- The product of two copies of two to the power `n` is two raised to twice `n`. -/
private theorem clause17Aux_two_pow_sq (n : ℕ) :
    (2 : ℝ) ^ n * (2 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
  rw [← pow_add, show n + n = 2 * n by ring]

/-- Casting a natural power of two to the reals agrees with taking the real power with the same
natural exponent. -/
private theorem clause17Aux_two_pow_cast (k : ℕ) :
    ((2 : ℕ) ^ k : ℝ) = (2 : ℝ) ^ k := by
  simp

/-- Casting a natural power of two to the reals agrees with the real power with the exponent
cast to the reals. -/
private theorem clause17Aux_two_pow_rpow (k : ℕ) :
    ((2 : ℕ) ^ k : ℝ) = (2 : ℝ) ^ ((k : ℕ) : ℝ) := by
  rw [clause17Aux_two_pow_cast, Real.rpow_natCast]

/-- Every positive real number is bounded above by two raised to the natural ceiling of its
base-two logarithm. -/
private theorem clause17Aux_two_pow_ceil_logb (y : ℝ) (hy : 0 < y) :
    y ≤ ((2 : ℕ) ^ (Nat.ceil (Real.logb 2 y)) : ℝ) := by
  have h : Real.logb 2 y ≤ (Nat.ceil (Real.logb 2 y) : ℝ) := Nat.le_ceil _
  have h2 : y ≤ (2 : ℝ) ^ (Nat.ceil (Real.logb 2 y) : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) hy).mp h
  rwa [← clause17Aux_two_pow_rpow] at h2

/-- The reciprocal dyadic scale chosen by the ceiling of the logarithm of reciprocal error is at
most that error. -/
private theorem clause17Aux_inv_two_pow_ceil (ε : ℝ) (hε : 0 < ε) :
    (1 : ℝ) / ((2 : ℕ) ^ (Nat.ceil (Real.logb 2 (1 / ε))) : ℝ) ≤ ε := by
  have hy : (0:ℝ) < 1 / ε := by positivity
  have h : (1 / ε : ℝ) ≤ ((2 : ℕ) ^ (Nat.ceil (Real.logb 2 (1 / ε))) : ℝ) :=
    clause17Aux_two_pow_ceil_logb (1 / ε) hy
  have h2 : (0:ℝ) < ((2 : ℕ) ^ (Nat.ceil (Real.logb 2 (1 / ε))) : ℝ) := by
    exact_mod_cast Nat.two_pow_pos _
  have h4 : (1 : ℝ) ≤ ε * ((2 : ℕ) ^ (Nat.ceil (Real.logb 2 (1 / ε))) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hε)
    have hcancel : ε * (1 / ε) = 1 := by field_simp
    rw [hcancel] at hmul
    exact hmul
  rw [div_le_iff₀ h2]
  exact h4

/-- The prescribed dyadic precision makes the total Fock-state rounding-error budget at most the
positive target error. -/
private theorem clause17Aux_budget3 (m n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card (FockOccupation m n) : ℝ)
        * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
        * (1 / ((2 : ℕ) ^ (m * (n + 1) + 2 * n * n + 3 * n
            + Nat.ceil (Real.logb 2 (1 / ε)) + 3) : ℝ))
      ≤ ε := by
  classical
  set c : ℕ := Nat.ceil (Real.logb 2 (1 / ε))
  set pexp : ℕ := m * (n + 1) + 2 * n * n + 3 * n
  have hN : (Fintype.card (FockOccupation m n) : ℝ) ≤ (2 : ℝ) ^ (m * (n + 1)) := by
    have hnat : Fintype.card (FockOccupation m n) ≤ 2 ^ (m * (n + 1)) := by
      have h1 : Fintype.card (FockOccupation m n) ≤ Fintype.card (Fin m → Fin (n + 1)) :=
        Fintype.card_subtype_le _
      have h2 : Fintype.card (Fin m → Fin (n + 1)) = (n + 1) ^ m := by
        simp
      have h3 : n + 1 ≤ 2 ^ (n + 1) := le_of_lt (Nat.lt_two_pow_self (n := n + 1))
      have h4 : (n + 1) ^ m ≤ (2 ^ (n + 1)) ^ m := by gcongr
      have h5 : (2 ^ (n + 1)) ^ m = 2 ^ ((n + 1) * m) := (Nat.pow_mul 2 (n + 1) m).symm
      calc Fintype.card (FockOccupation m n) ≤ (n + 1) ^ m := by rw [h2] at h1; exact h1
        _ ≤ (2 ^ (n + 1)) ^ m := h4
        _ = 2 ^ ((n + 1) * m) := h5
        _ = 2 ^ (m * (n + 1)) := by rw [Nat.mul_comm]
    exact_mod_cast hnat
  have hF : ((n ! : ℝ) ^ 2) ≤ (2 : ℝ) ^ (2 * n * n) := by
    have hnat : (n !) ^ 2 ≤ 2 ^ (2 * n * n) := by
      have h1 : n ! ≤ n ^ n := Nat.factorial_le_pow n
      have h2 : n ≤ 2 ^ n := le_of_lt (Nat.lt_two_pow_self (n := n))
      have h3 : n ^ n ≤ (2 ^ n) ^ n := by gcongr
      have h4 : (2 ^ n) ^ n = 2 ^ (n * n) := (Nat.pow_mul 2 n n).symm
      have h5 : n ! ≤ 2 ^ (n * n) := le_trans h1 (by rw [← h4]; exact h3)
      have h6 : (n !) ^ 2 ≤ (2 ^ (n * n)) ^ 2 := by gcongr
      have h7 : (2 ^ (n * n)) ^ 2 = 2 ^ (2 * (n * n)) := by
        conv_lhs => rw [← Nat.pow_mul]
        congr 1
        ring
      rw [h7] at h6
      rwa [show (2 * (n * n) : ℕ) = 2 * n * n by ring] at h6
    exact_mod_cast hnat
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast le_of_lt (Nat.lt_two_pow_self (n := n))
  have hpowE : (2 : ℝ) ^ pexp
      = (2 : ℝ) ^ (m * (n + 1)) * ((2 : ℝ) ^ (2 * n * n) * ((2 : ℝ) ^ n * (2 : ℝ) ^ (2 * n))) := by
    rw [show pexp = m * (n + 1) + (2 * n * n + (n + 2 * n)) by ring,
      pow_add, pow_add, pow_add]
  have hcore : (Fintype.card (FockOccupation m n) : ℝ)
        * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
      ≤ (2 : ℝ) ^ pexp := by
    have hmain : (Fintype.card (FockOccupation m n) : ℝ)
          * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
        ≤ (2 : ℝ) ^ (m * (n + 1)) * ((2 : ℝ) ^ (2 * n * n) * ((n : ℝ) * (2 : ℝ) ^ (2 * n))) := by
      gcongr
    have hmain2 : (2 : ℝ) ^ (m * (n + 1)) * ((2 : ℝ) ^ (2 * n * n) * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
        ≤ (2 : ℝ) ^ (m * (n + 1)) * ((2 : ℝ) ^ (2 * n * n) * ((2 : ℝ) ^ n * (2 : ℝ) ^ (2 * n))) := by
      gcongr
    rw [hpowE]
    exact le_trans hmain hmain2
  have hsplit : ((2 : ℕ) ^ (pexp + (c + 3)) : ℝ)
      = ((2 : ℕ) ^ pexp : ℝ) * ((2 : ℕ) ^ (c + 3) : ℝ) := by
    rw [pow_add]
  have hpowCast : ((2 : ℕ) ^ pexp : ℝ) = (2 : ℝ) ^ pexp := clause17Aux_two_pow_cast pexp
  have hgoal : (Fintype.card (FockOccupation m n) : ℝ)
        * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
        * (1 / ((2 : ℕ) ^ (pexp + (c + 3)) : ℝ))
      ≤ ε := by
    have h3split : (1 / (((2 : ℕ) ^ pexp : ℝ) * ((2 : ℕ) ^ (c + 3) : ℝ)) : ℝ)
        = (1 / ((2 : ℕ) ^ pexp : ℝ)) * (1 / ((2 : ℕ) ^ (c + 3) : ℝ)) := by
      field_simp
    rw [hsplit, h3split]
    have h4 : (Fintype.card (FockOccupation m n) : ℝ)
          * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
          / ((2 : ℕ) ^ pexp : ℝ)
        ≤ 1 := by
      have hthis : (Fintype.card (FockOccupation m n) : ℝ)
          * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n))) ≤ ((2 : ℕ) ^ pexp : ℝ) := by
        have := hcore
        rwa [← hpowCast] at this
      have hA : (0:ℝ) < ((2 : ℕ) ^ pexp : ℝ) := by exact_mod_cast Nat.two_pow_pos _
      rw [div_le_one hA]
      exact hthis
    have h5 : (1 : ℝ) / ((2 : ℕ) ^ (c + 3) : ℝ) = (1 / 8) * (1 / ((2 : ℕ) ^ c : ℝ)) := by
      rw [pow_add]
      have h3 : ((2 : ℕ) ^ 3 : ℝ) = 8 := by norm_num
      rw [h3]
      have hc : (0:ℝ) < ((2 : ℕ) ^ c : ℝ) := by exact_mod_cast Nat.two_pow_pos _
      field_simp
    rw [h5]
    have h6 : (1 : ℝ) / ((2 : ℕ) ^ c : ℝ) ≤ ε := clause17Aux_inv_two_pow_ceil ε hε
    have hrest : (0:ℝ) ≤ (1 / 8) * (1 / ((2 : ℕ) ^ c : ℝ)) := by positivity
    have hre : (Fintype.card (FockOccupation m n) : ℝ)
          * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
          * ((1 / ((2 : ℕ) ^ pexp : ℝ)) * ((1 / 8) * (1 / ((2 : ℕ) ^ c : ℝ))))
        = ((Fintype.card (FockOccupation m n) : ℝ)
            * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n)))
            / ((2 : ℕ) ^ pexp : ℝ)) * ((1 / 8) * (1 / ((2 : ℕ) ^ c : ℝ))) := by
      field_simp
    rw [hre]
    have hstep := mul_le_mul_of_nonneg_right h4 hrest
    have hrest2 : ((1 / 8) * (1 / ((2 : ℕ) ^ c : ℝ)) : ℝ) ≤ (1 / 8) * ε := by
      gcongr
    have hfin : (1 / 8) * ε ≤ ε := by nlinarith [hε]
    have hmid : (1 : ℝ) * ((1 / 8) * (1 / ((2 : ℕ) ^ c : ℝ))) ≤ (1 / 8) * ε := by
      nlinarith
    exact le_trans (le_trans hstep hmid) hfin
  exact hgoal

/-- Rounding the entries of a bounded real isometry to the specified dyadic precision changes
its output distribution by at most the target total variation error. -/
theorem clause17_clause3 : ∀ (m n : ℕ) (ε : ℝ), 0 < ε →
    ∀ (A : Matrix (Fin m) (Fin n) ℝ),
      (∀ i j, |A i j| ≤ 1) → (A.map (algebraMap ℝ ℂ))ᴴ * A.map (algebraMap ℝ ℂ) = 1 →
      loTvDist
          (loIsometryDist m n
            (loOfRat m n (loRoundToDyadic m n
              (m * (n + 1) + 2 * n * n + 3 * n + Nat.ceil (Real.logb 2 (1 / ε)) + 3) A)))
          (loIsometryDist m n (A.map (algebraMap ℝ ℂ)))
        ≤ ε := by
  intro m n ε hε A hA1 _hA2
  classical
  set b : ℕ := m * (n + 1) + 2 * n * n + 3 * n + Nat.ceil (Real.logb 2 (1 / ε)) + 3 with hbdef
  set δ : ℝ := 1 / ((2:ℕ)^b : ℝ) with hδdef
  set Bm : Matrix (Fin m) (Fin n) ℂ := A.map (algebraMap ℝ ℂ)
  set Am : Matrix (Fin m) (Fin n) ℂ := loOfRat m n (loRoundToDyadic m n b A)
  set p : FockOccupation m n → ℝ := loIsometryDist m n Am
  set q : FockOccupation m n → ℝ := loIsometryDist m n Bm
  have hδpos : 0 < δ := by positivity
  have hδle1 : δ ≤ 1 := by
    have h1 : (1:ℝ) ≤ ((2:ℕ)^b : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ b)
    have h2 : (0:ℝ) < ((2:ℕ)^b : ℝ) := by positivity
    rw [div_le_iff₀ h2, one_mul]
    exact h1

  have hBm : ∀ i j, Bm i j = ((A i j : ℝ) : ℂ) := by
    intro i j
    simp only [Bm, Matrix.map_apply]
    rfl
  have hAm : ∀ i j, Am i j = (((loRoundToDyadicEntry b (A i j) : ℝ) : ℂ)) := by
    intro i j
    simp only [Am, loOfRat, Matrix.map_apply, loRoundToDyadic, Matrix.of_apply]
    rfl

  have hentry : ∀ i j, ‖Bm i j - Am i j‖ ≤ δ := by
    intro i j
    rw [hBm, hAm]
    have h1 : ((A i j : ℝ) : ℂ) - (((loRoundToDyadicEntry b (A i j) : ℝ) : ℂ))
        = (((A i j : ℝ) - (loRoundToDyadicEntry b (A i j) : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub]
    rw [h1, hδdef]
    exact_mod_cast loRoundToDyadicEntry_err b (A i j)

  have hBle : ∀ i j, ‖Bm i j‖ ≤ 1 := by
    intro i j
    rw [hBm]
    exact_mod_cast hA1 i j
  have hA'le : ∀ i j, ‖Am i j‖ ≤ 1 + δ := by
    intro i j
    have h3 : ‖Am i j - Bm i j‖ = ‖Bm i j - Am i j‖ := by
      rw [← neg_sub, norm_neg]
    have h1 : ‖Am i j‖ ≤ ‖Bm i j‖ + ‖Am i j - Bm i j‖ := by
      have key : Bm i j + (Am i j - Bm i j) = Am i j := by ring
      conv_lhs => rw [← key]
      exact norm_add_le (Bm i j) (Am i j - Bm i j)
    have h2 : ‖Bm i j - Am i j‖ ≤ δ := hentry i j
    linarith [hBle i j, h2, h3]

  have hrowEntry : ∀ (X : Matrix (Fin m) (Fin n) ℂ) (S : FockOccupation m n)
      (j k : Fin n), bosonRowMatrix X S j k = X ((bosonRows (fun i => (S.1 i : ℕ))).get
        ⟨j.val, by
          have hlen : (bosonRows (fun i => (S.1 i : ℕ))).length = n :=
            (bosonRows_length (fun i => (S.1 i : ℕ))).trans S.2
          rw [hlen]
          exact j.isLt⟩) k := by
    intro X S j k
    rfl
  have hrowDiff : ∀ (S : FockOccupation m n) (j k : Fin n),
      ‖bosonRowMatrix Am S j k - bosonRowMatrix Bm S j k‖ ≤ δ := by
    intro S j k
    rw [show (bosonRowMatrix Am S j k - bosonRowMatrix Bm S j k)
        = -(bosonRowMatrix Bm S j k - bosonRowMatrix Am S j k) by ring, norm_neg]
    exact hentry _ _
  have hrowA' : ∀ (S : FockOccupation m n) (j k : Fin n),
      ‖bosonRowMatrix Am S j k‖ ≤ 2 := by
    intro S j k
    rw [hrowEntry]
    exact le_trans (hA'le _ _) (by linarith [hδle1])
  have hrowB : ∀ (S : FockOccupation m n) (j k : Fin n),
      ‖bosonRowMatrix Bm S j k‖ ≤ 2 := by
    intro S j k
    rw [hrowEntry]
    exact le_trans (hBle _ _) (by norm_num)

  have hpdiff : ∀ S : FockOccupation m n,
      ‖Matrix.permanent (bosonRowMatrix Am S) - Matrix.permanent (bosonRowMatrix Bm S)‖
        ≤ (n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n) := by
    intro S
    exact clause17Aux_permanent_perturb (bosonRowMatrix Am S) (bosonRowMatrix Bm S) δ
      (le_of_lt hδpos) (hrowA' S) (hrowB S) (hrowDiff S)
  have hpA' : ∀ S : FockOccupation m n,
      ‖Matrix.permanent (bosonRowMatrix Am S)‖ ≤ (n ! : ℝ) * (2 : ℝ) ^ n := by
    intro S
    exact clause17Aux_permanent_norm_le (bosonRowMatrix Am S) 2 (hrowA' S)
  have hpB : ∀ S : FockOccupation m n,
      ‖Matrix.permanent (bosonRowMatrix Bm S)‖ ≤ (n ! : ℝ) * (2 : ℝ) ^ n := by
    intro S
    exact clause17Aux_permanent_norm_le (bosonRowMatrix Bm S) 2 (hrowB S)

  have hns : ∀ S : FockOccupation m n,
      |Complex.normSq (Matrix.permanent (bosonRowMatrix Am S))
          - Complex.normSq (Matrix.permanent (bosonRowMatrix Bm S))|
        ≤ 2 * (n ! : ℝ) ^ 2 * n * δ * (2 : ℝ) ^ (2 * n) := by
    intro S
    set u := Matrix.permanent (bosonRowMatrix Am S)
    set v := Matrix.permanent (bosonRowMatrix Bm S)
    have huv : ∀ w : ℂ, Complex.normSq w = ‖w‖ ^ 2 := fun w => Complex.normSq_eq_norm_sq w
    rw [huv u, huv v]
    have hsq : |‖u‖ ^ 2 - ‖v‖ ^ 2| = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v))]
      exact mul_comm _ _
    rw [hsq]
    have h1 : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
    have h2 : ‖u - v‖ ≤ (n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n) := hpdiff S
    have h3 : ‖u‖ + ‖v‖ ≤ 2 * ((n ! : ℝ) * (2 : ℝ) ^ n) := by
      linarith [hpA' S, hpB S]
    have h4 : |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖)
        ≤ ((n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n)) * (2 * ((n ! : ℝ) * (2 : ℝ) ^ n)) :=
      mul_le_mul (le_trans h1 h2) h3 (add_nonneg (norm_nonneg u) (norm_nonneg v))
        (by positivity)
    have h5 : ((n ! : ℝ) * ((n : ℝ) * δ * (2 : ℝ) ^ n)) * (2 * ((n ! : ℝ) * (2 : ℝ) ^ n))
        = 2 * (n ! : ℝ) ^ 2 * n * δ * (2 : ℝ) ^ (2 * n) := by
      conv_rhs => rw [← clause17Aux_two_pow_sq n]
      ring
    linarith

  have hw : ∀ S : FockOccupation m n,
      |p S - q S| ≤ 2 * (n ! : ℝ) ^ 2 * n * δ * (2 : ℝ) ^ (2 * n) := by
    intro S
    have hpS : p S = Complex.normSq (Matrix.permanent (bosonRowMatrix Am S))
        / ∏ i, ((S.1 i : ℕ)! : ℝ) := by
      show loIsometryDist m n Am S = _
      simp only [loIsometryDist, bosonWeight]
      rw [Nat.cast_prod]
    have hqS : q S = Complex.normSq (Matrix.permanent (bosonRowMatrix Bm S))
        / ∏ i, ((S.1 i : ℕ)! : ℝ) := by
      show loIsometryDist m n Bm S = _
      simp only [loIsometryDist, bosonWeight]
      rw [Nat.cast_prod]
    rw [hpS, hqS, ← sub_div]
    have hden1 : (1:ℝ) ≤ ∏ i : Fin m, ((S.1 i : ℕ)! : ℝ) := by
      refine Finset.one_le_prod₀ fun (i : Fin m) _ => ?_
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (S.1 i)))
    have hDpos : (0:ℝ) < ∏ i : Fin m, ((S.1 i : ℕ)! : ℝ) :=
      lt_of_lt_of_le (by norm_num) hden1
    rw [abs_div, abs_of_pos hDpos]
    have hnum := hns S
    have hdiv : |Complex.normSq (Matrix.permanent (bosonRowMatrix Am S))
          - Complex.normSq (Matrix.permanent (bosonRowMatrix Bm S))|
          / ∏ i : Fin m, ((S.1 i : ℕ)! : ℝ)
        ≤ |Complex.normSq (Matrix.permanent (bosonRowMatrix Am S))
          - Complex.normSq (Matrix.permanent (bosonRowMatrix Bm S))| := by
      rw [div_le_iff₀ hDpos]
      have h := mul_le_mul_of_nonneg_left hden1 (abs_nonneg
        (Complex.normSq (Matrix.permanent (bosonRowMatrix Am S))
          - Complex.normSq (Matrix.permanent (bosonRowMatrix Bm S))))
      rw [mul_one] at h
      exact h
    exact le_trans hdiv hnum

  have hTV : loTvDist p q ≤ (Fintype.card (FockOccupation m n) : ℝ)
      * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n))) * δ := by
    have h1 : (∑ S : FockOccupation m n, |p S - q S|)
        ≤ ∑ S : FockOccupation m n, 2 * (n ! : ℝ) ^ 2 * n * δ * (2 : ℝ) ^ (2 * n) :=
      Finset.sum_le_sum fun S _ => hw S
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : loTvDist p q = (∑ S : FockOccupation m n, |p S - q S|) / 2 := rfl
    rw [h2]
    have h3 : (Fintype.card (FockOccupation m n) : ℝ)
          * (2 * (n ! : ℝ) ^ 2 * n * δ * (2 : ℝ) ^ (2 * n)) / 2
        = (Fintype.card (FockOccupation m n) : ℝ)
          * ((n ! : ℝ) ^ 2 * ((n : ℝ) * (2 : ℝ) ^ (2 * n))) * δ := by
      ring
    have h4 : (∑ S : FockOccupation m n, |p S - q S|) / 2
        ≤ (Fintype.card (FockOccupation m n) : ℝ)
            * (2 * (n ! : ℝ) ^ 2 * n * δ * (2 : ℝ) ^ (2 * n)) / 2 :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    rw [← h3]
    exact h4

  have hbudget := clause17Aux_budget3 m n ε hε
  have hδeq : δ = 1 / ((2 : ℕ) ^ (m * (n + 1) + 2 * n * n + 3 * n
      + Nat.ceil (Real.logb 2 (1 / ε)) + 3) : ℝ) := by
    rw [hδdef, hbdef]
  rw [hδeq] at hTV
  exact le_trans hTV hbudget

/-- Summing the indicator of equality over list positions gives the number of occurrences of the
element. -/
private theorem clause17Aux_sum_get_count {α : Type} [DecidableEq α] :
    ∀ (l : List α) (S : α),
      (∑ t : Fin l.length, if l[t.val] = S then (1 : ℕ) else 0) = l.count S := by
  intro l
  induction l with
  | nil =>
    intro S
    simp
  | cons a l ih =>
    intro S
    have hsum : (∑ t : Fin (a :: l).length, if (a :: l)[t.val] = S then (1 : ℕ) else 0)
        = (if a = S then (1 : ℕ) else 0)
            + ∑ t : Fin l.length, if l[t.val] = S then (1 : ℕ) else 0 := by
      show (∑ t : Fin (l.length + 1), if (a :: l)[t.val] = S then (1 : ℕ) else 0) = _
      rw [Fin.sum_univ_succ]
      have h0 : (a :: l)[((0 : Fin (l.length + 1)) : ℕ)] = a :=
        List.getElem_cons_zero a l _
      have hs : ∀ t : Fin l.length,
          (a :: l)[((Fin.succ t : Fin (l.length + 1)) : ℕ)] = l[(t : ℕ)] := by
        intro t
        show (a :: l)[(t : ℕ) + 1] = l[(t : ℕ)]
        exact List.getElem_cons_succ a l t.val (Nat.succ_lt_succ t.isLt)
      refine congrArg₂ (· + ·) ?_ ?_
      · rw [h0]
      · exact Finset.sum_congr rfl fun t _ => by rw [hs t]
    rw [hsum, ih, List.count_cons]
    by_cases h : a = S <;> simp [h, Nat.add_comm]

/-- The number of occurrences in a flattened list is the sum of the occurrence counts in its
constituent lists. -/
private theorem clause17Aux_count_flatten {α : Type} [BEq α] (l : List (List α)) (S : α) :
    l.flatten.count S = (l.map (fun t => t.count S)).sum := by
  rw [List.count_eq_countP, List.countP_flatten]
  congr 1

/-- Counts an element in a replicated list, yielding the replication count when the elements
agree and zero otherwise. -/
private theorem clause17Aux_count_replicate {α : Type} [DecidableEq α] (n : ℕ) (a S : α) :
    (List.replicate n a).count S = if a = S then n else 0 := by
  rw [List.count_eq_countP, List.countP_replicate]
  by_cases h : a = S <;> simp [h]

/-- Enumerating each element with multiplicity `k` produces a flattened list whose count at `S`
is the value of `k` at `S`. -/
private theorem clause17Aux_count_outList {Φ : Type} [Fintype Φ] [DecidableEq Φ]
    (k : Φ → ℕ) (N : ℕ) (e : Φ ≃ Fin N) (S : Φ) :
    (List.ofFn (fun j : Fin N => List.replicate (k (e.symm j)) (e.symm j))).flatten.count S
      = k S := by
  rw [clause17Aux_count_flatten, List.map_ofFn]
  simp only [Function.comp_def]
  have h : (fun j : Fin N => (List.replicate (k (e.symm j)) (e.symm j)).count S)
      = (fun j : Fin N => if (e.symm j) = S then k (e.symm j) else 0) :=
    funext fun j => clause17Aux_count_replicate (k (e.symm j)) (e.symm j) S
  rw [h, List.sum_ofFn]
  have h2 := Fintype.sum_equiv e (fun S' : Φ => if S' = S then k S' else 0)
    (fun j : Fin N => if (e.symm j) = S then k (e.symm j) else 0)
    (fun S' => by simp only [Equiv.symm_apply_apply])
  rw [← h2]
  rw [Finset.sum_ite_eq']
  simp

/-- The length of the flattened multiplicity list equals the sum of the multiplicities. -/
private theorem clause17Aux_length_outList {Φ : Type} [Fintype Φ] [DecidableEq Φ]
    (k : Φ → ℕ) (N : ℕ) (e : Φ ≃ Fin N) :
    (List.ofFn (fun j : Fin N => List.replicate (k (e.symm j)) (e.symm j))).flatten.length
      = ∑ S : Φ, k S := by
  rw [List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def]
  have h : (fun j : Fin N => (List.replicate (k (e.symm j)) (e.symm j)).length)
      = (fun j : Fin N => k (e.symm j)) :=
    funext fun j => List.length_replicate
  rw [h, List.sum_ofFn]
  exact (Fintype.sum_equiv e (fun S : Φ => k S) (fun j : Fin N => k (e.symm j))
    (fun x => by simp only [Equiv.symm_apply_apply])).symm

/-- Any natural multiplicities summing to two to the power `L` can be realized as the output
frequencies of a sampler using `L` random bits. -/
private theorem clause17Aux_sampler_fibers {m n L : ℕ} (k : FockOccupation m n → ℕ)
    (hk : ∑ S, k S = (2 : ℕ) ^ L) :
    ∃ Sam : LoSampler m n, Sam.L = L ∧
      ∀ S : FockOccupation m n, loSamplerDist Sam S = ((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) := by
  classical
  have hcard : Fintype.card (Fin L → Bool) = (2 : ℕ) ^ L := by
    simp [Fintype.card_fin]
  have hcardΦ : Fintype.card (FockOccupation m n) = Fintype.card (FockOccupation m n) := rfl
  let eΦ : FockOccupation m n ≃ Fin (Fintype.card (FockOccupation m n)) :=
    Fintype.equivFin (FockOccupation m n)
  let e0 : (Fin L → Bool) ≃ Fin ((2 : ℕ) ^ L) :=
    (Fintype.equivFin (Fin L → Bool)).trans (finCongr hcard)
  have hlen : (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
        List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten.length = (2 : ℕ) ^ L := by
    rw [clause17Aux_length_outList]
    exact hk
  have hcount : ∀ S : FockOccupation m n,
      (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
        List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten.count S = k S :=
    fun S => clause17Aux_count_outList k _ eΦ S
  refine ⟨⟨L, fun r =>
      (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
        List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
        (e0 r).val]'(by rw [hlen]; exact (e0 r).isLt)⟩, rfl, ?_⟩
  intro S
  have hsum : (∑ r : Fin L → Bool,
        if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
              List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
            (e0 r).val]'(by rw [hlen]; exact (e0 r).isLt) = S
          then (1 : ℝ) else 0)
      = ∑ t : Fin ((2 : ℕ) ^ L),
        if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
              List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
            t.val]'(by rw [hlen]; exact t.isLt) = S
          then (1 : ℝ) else 0 :=
    Fintype.sum_equiv e0 _ _ (fun _ => rfl)
  have hcount' : (∑ t : Fin ((2 : ℕ) ^ L),
        if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
              List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
            t.val]'(by rw [hlen]; exact t.isLt) = S
          then (1 : ℕ) else 0)
      = k S := by
    have hbase := clause17Aux_sum_get_count
      (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
        List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten S
    have hre : (∑ t : Fin ((2 : ℕ) ^ L),
          if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
                List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
              t.val]'(by rw [hlen]; exact t.isLt) = S
            then (1 : ℕ) else 0)
        = (∑ t : Fin (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
              List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten.length,
          if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
                List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[t.val] = S
            then (1 : ℕ) else 0) :=
      (Fintype.sum_equiv (finCongr hlen) _ _ (fun _ => rfl)).symm
    rw [hre, hbase]
    exact hcount S
  have hdist : loSamplerDist
      ⟨L, fun r =>
        (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
          List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
          (e0 r).val]'(by rw [hlen]; exact (e0 r).isLt)⟩ S
      = ((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) := by
    show (∑ r : Fin L → Bool,
        if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
              List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
            (e0 r).val]'(by rw [hlen]; exact (e0 r).isLt) = S
          then (1 : ℝ) else 0) / ((2 : ℕ) ^ L : ℝ)
      = ((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ)
    rw [hsum]
    have hmid : (∑ t : Fin ((2 : ℕ) ^ L),
        if (List.ofFn (fun j : Fin (Fintype.card (FockOccupation m n)) =>
              List.replicate (k (eΦ.symm j)) (eΦ.symm j))).flatten[
            t.val]'(by rw [hlen]; exact t.isLt) = S
          then (1 : ℝ) else 0)
        = ((k S : ℕ) : ℝ) := by
      exact_mod_cast hcount'
    rw [hmid]
  exact hdist

/-- A finite probability distribution admits integer counts summing to the dyadic total, with
coordinatewise rounding error at most one. -/
private theorem clause17Aux_rounding {Φ : Type} [Fintype Φ] [DecidableEq Φ]
    (p : Φ → ℝ) (hp0 : ∀ S, 0 ≤ p S) (hp1 : ∑ S, p S = 1) (L : ℕ) :
    ∃ k : Φ → ℕ, (∑ S, k S = (2 : ℕ) ^ L)
      ∧ (∀ S, |((k S : ℕ) : ℝ) - ((2 : ℕ) ^ L : ℝ) * p S| ≤ 1) := by
  classical
  set N := Fintype.card Φ
  set e : Φ ≃ Fin N := Fintype.equivFin Φ
  have hTpos : (0:ℝ) < ((2 : ℕ) ^ L : ℝ) := by exact_mod_cast Nat.two_pow_pos L
  have ha_le : ∀ S : Φ, ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ)
      ≤ ((2 : ℕ) ^ L : ℝ) * p S := by
    intro S
    exact Nat.floor_le (mul_nonneg (by exact_mod_cast (Nat.zero_le _)) (hp0 S))
  have ha_lt : ∀ S : Φ, ((2 : ℕ) ^ L : ℝ) * p S
      < ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ) + 1 := by
    intro S
    exact Nat.lt_floor_add_one _
  have hsum_a : (∑ S : Φ, Nat.floor (((2 : ℕ) ^ L : ℝ) * p S)) ≤ (2 : ℕ) ^ L := by
    have h1 : (∑ S : Φ, ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ))
        ≤ ∑ S : Φ, ((2 : ℕ) ^ L : ℝ) * p S := Finset.sum_le_sum fun S _ => ha_le S
    have h2 : (∑ S : Φ, ((2 : ℕ) ^ L : ℝ) * p S) = ((2 : ℕ) ^ L : ℝ) := by
      rw [← Finset.mul_sum, hp1, mul_one]
    have h3 : (∑ S : Φ, ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ))
        = (((∑ S : Φ, Nat.floor (((2 : ℕ) ^ L : ℝ) * p S)) : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    rw [h3] at h1
    exact_mod_cast (le_trans h1 (le_of_eq h2))
  set R : ℕ := (2 : ℕ) ^ L - ∑ S : Φ, Nat.floor (((2 : ℕ) ^ L : ℝ) * p S)
  have hRcast : ((R : ℕ) : ℝ) = ((2 : ℕ) ^ L : ℝ)
      - ∑ S : Φ, ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsum_a, Nat.cast_sum, Nat.cast_pow]
  have hf_nonneg : ∀ S : Φ, 0 ≤ ((2 : ℕ) ^ L : ℝ) * p S
      - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ) := by
    intro S
    linarith [ha_le S]
  have hf_lt : ∀ S : Φ, ((2 : ℕ) ^ L : ℝ) * p S
      - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ) < 1 := by
    intro S
    linarith [ha_lt S]
  have hsumf : (∑ S : Φ, (((2 : ℕ) ^ L : ℝ) * p S
      - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ))) = ((R : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, mul_one]
    rw [← hRcast]
  have hR_le : R ≤ N := by
    have h1 : (∑ S : Φ, (((2 : ℕ) ^ L : ℝ) * p S
        - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ))) ≤ (N : ℝ) := by
      have h2 : ∀ S : Φ, ((2 : ℕ) ^ L : ℝ) * p S
          - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ) ≤ 1 :=
        fun S => le_of_lt (hf_lt S)
      calc (∑ S : Φ, (((2 : ℕ) ^ L : ℝ) * p S
            - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ)))
          ≤ ∑ S : Φ, (1:ℝ) := Finset.sum_le_sum fun S _ => h2 S
        _ = (N : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    rw [hsumf] at h1
    exact_mod_cast h1
  refine ⟨fun S => Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) + if (e S : ℕ) < R then 1 else 0, ?_, ?_⟩
  · rw [Finset.sum_add_distrib]
    have hr : (∑ S : Φ, if (e S : ℕ) < R then (1 : ℕ) else 0) = R := by
      rw [Fintype.sum_equiv e (fun S : Φ => if (e S : ℕ) < R then (1 : ℕ) else 0)
        (fun t : Fin N => if (t : ℕ) < R then (1 : ℕ) else 0) (fun _ => rfl)]
      have hsplit : ∑ t ∈ Finset.range R, (if t < R then (1 : ℕ) else 0)
          = ∑ t ∈ Finset.range N, (if t < R then (1 : ℕ) else 0) :=
        Finset.sum_subset (Finset.range_subset_range.mpr hR_le)
          (fun x _ hx => ite_eq_right (by simpa [Finset.mem_range] using hx))
      have hRsum : ∑ t ∈ Finset.range R, (if t < R then (1 : ℕ) else 0) = R := by
        have h1 : ∑ t ∈ Finset.range R, (if t < R then (1 : ℕ) else 0)
            = ∑ t ∈ Finset.range R, (1 : ℕ) :=
          Finset.sum_congr rfl fun t ht => ite_eq_left (Finset.mem_range.mp ht)
        have h2 : (∑ t ∈ Finset.range R, (1 : ℕ)) = R := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp
        rw [h1, h2]
      have hre : (∑ t : Fin N, if (t : ℕ) < R then (1 : ℕ) else 0)
          = ∑ t ∈ Finset.range N, if t < R then (1 : ℕ) else 0 := by
        symm
        rw [← Fin.sum_univ_eq_sum_range]
      rw [hre, ← hsplit]
      exact hRsum
    rw [hr]
    exact Nat.add_sub_cancel' hsum_a
  · intro S
    by_cases hr : (e S : ℕ) < R
    · have h1 : (((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) + 1 : ℕ) : ℝ)
          - ((2 : ℕ) ^ L : ℝ) * p S
          = 1 - (((2 : ℕ) ^ L : ℝ) * p S
              - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ)) := by
        push_cast
        ring
      have h2 : |(((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) + 1 : ℕ) : ℝ)
          - ((2 : ℕ) ^ L : ℝ) * p S| ≤ 1 := by
        rw [h1, abs_of_nonneg (by linarith [hf_nonneg S, hf_lt S])]
        linarith [hf_nonneg S, hf_lt S]
      simpa [hr] using h2
    · have h1 : ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ)
          - ((2 : ℕ) ^ L : ℝ) * p S
          = -(((2 : ℕ) ^ L : ℝ) * p S
              - ((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ)) := by
        push_cast
        ring
      have h2 : |((Nat.floor (((2 : ℕ) ^ L : ℝ) * p S) : ℕ) : ℝ)
          - ((2 : ℕ) ^ L : ℝ) * p S| ≤ 1 := by
        rw [h1, abs_neg, abs_of_nonneg (hf_nonneg S)]
        linarith [hf_lt S]
      simpa [hr] using h2

/-- The specified logarithmic random-bit budget bounds the ratio of the number of outcomes to
the dyadic denominator by the target error. -/
private theorem clause17Aux_budget5 (m N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : 0 < N) :
    (N : ℝ) / ((2 : ℕ) ^ (m + Nat.ceil (Real.logb 2 (N : ℝ))
        + Nat.ceil (Real.logb 2 (1 / ε)) + 2 + 1) : ℝ) ≤ ε := by
  set cN : ℕ := Nat.ceil (Real.logb 2 (N : ℝ))
  set cE : ℕ := Nat.ceil (Real.logb 2 (1 / ε))
  have hNle : (N : ℝ) ≤ ((2 : ℕ) ^ cN : ℝ) :=
    clause17Aux_two_pow_ceil_logb (N : ℝ) (by exact_mod_cast hN)
  have hEle : (1 / ε : ℝ) ≤ ((2 : ℕ) ^ cE : ℝ) :=
    clause17Aux_two_pow_ceil_logb (1 / ε) (by positivity)
  have hden : ((2 : ℕ) ^ (m + cN + cE + 3) : ℝ)
      = ((2 : ℕ) ^ m : ℝ) * (((2 : ℕ) ^ cN : ℝ) * (((2 : ℕ) ^ cE : ℝ) * ((2 : ℕ) ^ 3 : ℝ))) := by
    rw [show (m + cN + cE + 3 : ℕ) = m + (cN + (cE + 3)) by ring, pow_add, pow_add, pow_add]
  have hbig : (8 : ℝ) * (N : ℝ) / ε ≤ ((2 : ℕ) ^ (m + cN + cE + 3) : ℝ) := by
    rw [hden]
    have h3 : ((2 : ℕ) ^ 3 : ℝ) = 8 := by norm_num
    rw [h3]
    set M : ℝ := ((2 : ℕ) ^ m : ℝ)
    set A : ℝ := ((2 : ℕ) ^ cN : ℝ)
    set B : ℝ := ((2 : ℕ) ^ cE : ℝ)
    have hM : (1:ℝ) ≤ M := by
      show (1:ℝ) ≤ ((2 : ℕ) ^ m : ℝ)
      exact_mod_cast (Nat.one_le_two_pow : (1:ℕ) ≤ 2 ^ m)
    have hNp : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hE1 : (0:ℝ) ≤ (1 / ε : ℝ) := by positivity
    have hAB : (0:ℝ) ≤ A * B := by
      show (0:ℝ) ≤ ((2 : ℕ) ^ cN : ℝ) * ((2 : ℕ) ^ cE : ℝ)
      exact_mod_cast (mul_nonneg (Nat.zero_le _) (Nat.zero_le _))
    have hprod1 : (N : ℝ) * (1 / ε) ≤ A * B :=
      mul_le_mul hNle hEle hE1 (by
        show (0:ℝ) ≤ ((2 : ℕ) ^ cN : ℝ)
        exact_mod_cast (Nat.zero_le _))
    have hprod2 : (8:ℝ) * ((N : ℝ) * (1 / ε)) ≤ 8 * (A * B) :=
      mul_le_mul_of_nonneg_left hprod1 (by norm_num)
    have hprod3 : (8:ℝ) * (A * B) ≤ M * (A * (B * 8)) := by
      have h1 : A * B ≤ M * (A * B) := le_mul_of_one_le_left hAB hM
      have h2 : (8:ℝ) * (A * B) ≤ 8 * (M * (A * B)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h3' : (M * (A * (B * 8)) : ℝ) = 8 * (M * (A * B)) := by ring
      rw [h3']
      exact h2
    have hLHS : (8 : ℝ) * (N : ℝ) / ε = (8:ℝ) * ((N : ℝ) * (1 / ε)) := by
      have hεne : ε ≠ 0 := ne_of_gt hε
      field_simp [hεne]
    rw [hLHS]
    exact le_trans hprod2 hprod3
  have hmain : (N : ℝ) / ((2 : ℕ) ^ (m + cN + cE + 2 + 1) : ℝ) ≤ ε := by
    have hpos : (0:ℝ) < ((2 : ℕ) ^ (m + cN + cE + 2 + 1) : ℝ) := by
      exact_mod_cast Nat.two_pow_pos _
    rw [show (m + cN + cE + 2 + 1 : ℕ) = m + cN + cE + 3 by ring, div_le_iff₀ hpos]
    have hbig' : (8:ℝ) * (N : ℝ) ≤ ε * ((2 : ℕ) ^ (m + cN + cE + 3) : ℝ) := by
      have := hbig
      rw [div_le_iff₀ hε] at this
      exact this.trans (le_of_eq (mul_comm _ _))
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  exact hmain

/-- Every dyadically encoded isometry admits a sampler with the specified random-bit bound and
total variation error at most the positive target error. -/
theorem clause17_clause5 : ∀ (m n b : ℕ) (Enc : LoDyadicEncoding m n b) (ε : ℝ), 0 < ε →
    (loOfRat m n Enc.mat)ᴴ * loOfRat m n Enc.mat = 1 →
    ∃ Sam : LoSampler m n,
      Sam.L ≤ m + Nat.ceil (Real.logb 2 (Fintype.card (FockOccupation m n) : ℝ))
          + Nat.ceil (Real.logb 2 (1 / ε)) + 2
      ∧ loTvDist (loSamplerDist Sam) (loIsometryDist m n (loOfRat m n Enc.mat)) ≤ ε := by
  intro m n _b Enc ε hε hA
  classical
  set Φ := FockOccupation m n
  set N := Fintype.card Φ
  set A : Matrix (Fin m) (Fin n) ℂ := loOfRat m n Enc.mat
  set p : Φ → ℝ := loIsometryDist m n A
  have hp1 : ∑ S : Φ, p S = 1 := clause17_clause2 m n A hA
  have hp0 : ∀ S : Φ, 0 ≤ p S := by
    intro S
    show 0 ≤ bosonWeight A S
    unfold bosonWeight
    exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
  have hNpos : 0 < N := by
    by_contra h
    have h0 : N = 0 := Nat.eq_zero_of_not_pos h
    have hcard0 : (Finset.univ : Finset Φ).card = 0 := by
      rw [Finset.card_univ]
      exact h0
    have he : (Finset.univ : Finset Φ) = ∅ := Finset.card_eq_zero.mp hcard0
    rw [he, Finset.sum_empty] at hp1
    norm_num at hp1
  set L := m + Nat.ceil (Real.logb 2 (N : ℝ)) + Nat.ceil (Real.logb 2 (1 / ε)) + 2
  have hbudget : (N : ℝ) / ((2 : ℕ) ^ (L + 1) : ℝ) ≤ ε :=
    clause17Aux_budget5 m N ε hε hNpos
  obtain ⟨k, hksum, hk⟩ := clause17Aux_rounding p hp0 hp1 L
  obtain ⟨Sam, hSamL, hSam⟩ := clause17Aux_sampler_fibers k hksum
  refine ⟨Sam, ?_, ?_⟩
  · show Sam.L ≤ _
    rw [hSamL]
  · have htv : loTvDist (loSamplerDist Sam) p
        = (∑ S : Φ, |((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p S|) / 2 := by
      unfold loTvDist
      congr 1
      exact Finset.sum_congr rfl fun S _ => by rw [hSam S]
    have hterm : ∀ S : Φ, |((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p S|
        ≤ 1 / ((2 : ℕ) ^ L : ℝ) := by
      intro S
      have hTpos : (0:ℝ) < ((2 : ℕ) ^ L : ℝ) := by exact_mod_cast Nat.two_pow_pos L
      have hTne : ((2 : ℕ) ^ L : ℝ) ≠ 0 := ne_of_gt hTpos
      have h1 : ((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p S
          = (((k S : ℕ) : ℝ) - ((2 : ℕ) ^ L : ℝ) * p S) / ((2 : ℕ) ^ L : ℝ) := by
        field_simp [hTne]
      rw [h1, abs_div, abs_of_pos hTpos]
      rw [div_le_iff₀ hTpos, div_mul_cancel₀ _ hTne]
      exact hk S
    have hsum : (∑ S : Φ, |((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p S|)
        ≤ (N : ℝ) / ((2 : ℕ) ^ L : ℝ) := by
      have h1 : (∑ S : Φ, |((k S : ℕ) : ℝ) / ((2 : ℕ) ^ L : ℝ) - p S|)
          ≤ ∑ S : Φ, 1 / ((2 : ℕ) ^ L : ℝ) := Finset.sum_le_sum fun S _ => hterm S
      have h2 : (∑ S : Φ, 1 / ((2 : ℕ) ^ L : ℝ)) = (N : ℝ) / ((2 : ℕ) ^ L : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        show (N : ℝ) * (1 / ((2 : ℕ) ^ L : ℝ)) = (N : ℝ) / ((2 : ℕ) ^ L : ℝ)
        ring
      linarith
    have hstep : loTvDist (loSamplerDist Sam) p
        ≤ ((N : ℝ) / ((2 : ℕ) ^ L : ℝ)) / 2 := by
      rw [htv, div_le_iff₀ (by norm_num : (0:ℝ) < 2),
        div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      exact hsum
    have hconv : ((N : ℝ) / ((2 : ℕ) ^ L : ℝ)) / 2 = (N : ℝ) / ((2 : ℕ) ^ (L + 1) : ℝ) := by
      rw [pow_succ]
      exact div_div _ _ _
    rw [hconv] at hstep
    exact le_trans hstep hbudget
end Qatlib.Concepts.BosonFock.PermAnalysis
