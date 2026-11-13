/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.SparsePauliCovariance

/-!
# Counted sparse Pauli energy estimators

`sparseLocalRat` and `countedSparsePauli` evaluate sparse Pauli estimators over the rationals
while recording multiplication and addition counts. The resource theorem connects this
computation to the real estimator and to fresh quantum measurement records, and a qubit example
gives the exact variance for two incompatible Pauli directions. See [HuangKuengPreskill2020] for
background.

## Main statements

* `sparse_pauli_counted_classical_and_quantum_resources`: estimator correctness and exact
  classical and quantum resource counts.
* `sparse_pauli_incompatible_qubit_energy_consumer`: variance of a two-direction qubit energy
  estimator.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ShadowModels.FairBitRecords
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 4000000

/-- The rational local Pauli estimator: identity factors contribute one, matching measurement
axes contribute three times the recorded sign, and other axes contribute zero. -/
def sparseLocalRat : Option (Fin 3) → (Fin 3 × Bool) → ℚ
  | none, _ => 1
  | some a, o => if o.1 = a then 3 * (if o.2 then 1 else -1) else 0

/-- Evaluate a rational linear combination of tensor Pauli estimators, recording the numbers of
multiplications and additions performed by the folds. -/
def countedSparsePauli {n m : ℕ} (w : Fin m → Fin n → Option (Fin 3)) (c : Fin m → ℚ)
    (o : Fin n → Fin 3 × Bool) : ℚ × ℕ × ℕ :=
  (List.ofFn (fun j : Fin m =>
    let v := (List.ofFn (fun i : Fin n => (sparseLocalRat (w j i) (o i), 1))).foldl
      (fun s v : ℚ × ℕ => (s.1 * v.1, s.2 + v.2)) (1, 0)
    (c j * v.1, v.2 + 1))).foldl
      (fun s v => (s.1 + v.1, s.2.1 + v.2, s.2.2 + 1)) (0, 0, 0)

/-- Casting the rational local estimator to the reals gives `tensorPauliLocalValue`. -/
private theorem sparseLocalRat_cast (w : Option (Fin 3)) (o : Fin 3 × Bool) :
    (sparseLocalRat w o : ℝ) = tensorPauliLocalValue w o := by
  cases w with
  | none => norm_num [sparseLocalRat, tensorPauliLocalValue]
  | some a =>
    rcases o with ⟨b, s⟩
    by_cases h : b = a <;> cases s <;> norm_num [sparseLocalRat, tensorPauliLocalValue, h]

/-- The counted product fold multiplies the initial value by the list product and increases the
counter by the list length. -/
private theorem counted_product (xs : List ℚ) (r : ℚ) (k : ℕ) :
    (xs.map (fun x => (x, (1 : ℕ)))).foldl
      (fun s v : ℚ × ℕ => (s.1 * v.1, s.2 + v.2)) (r, k) =
      (r * xs.prod, k + xs.length) := by
  induction xs generalizing r k with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The counted sum fold adds all values and their multiplication counts, and increases the
addition counter by the list length. -/
private theorem counted_sum (xs : List (ℚ × ℕ)) (r : ℚ) (k t : ℕ) :
    xs.foldl (fun s v => (s.1 + v.1, s.2.1 + v.2, s.2.2 + 1)) (r, k, t) =
      (r + (xs.map Prod.fst).sum, k + (xs.map Prod.snd).sum, t + xs.length) := by
  induction xs generalizing r k t with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, Nat.add_comm]

/-- The counted rational estimator equals the real sparse Pauli estimator, with `m * (n + 1)`
multiplications and `m` additions, and the fresh-record resource tuple has the stated exact
counts. This implements resource bookkeeping for the measurement procedure of
[HuangKuengPreskill2020]. -/
theorem sparse_pauli_counted_classical_and_quantum_resources (n m L K : ℕ)
    (w : Fin m → Fin n → Option (Fin 3)) (c : Fin m → ℚ) (o : Fin n → Fin 3 × Bool)
    (ω : Fin K → Fin L → Fin n → Fin 3 × Bool) :
    ((countedSparsePauli w c o).1 : ℝ) = sparsePauliValue w c o ∧
    (countedSparsePauli w c o).2.1 = m * (n + 1) ∧
    (countedSparsePauli w c o).2.2 = m ∧
    tensorPauliFreshResourceCounts n L K ω = (K * L, 2 * n * (K * L), n * (K * L), 0) := by
  have hi : ∀ j : Fin m,
      (List.ofFn (fun i : Fin n => (sparseLocalRat (w j i) (o i), 1))).foldl
        (fun s v : ℚ × ℕ => (s.1 * v.1, s.2 + v.2)) (1, 0) =
      (∏ i, sparseLocalRat (w j i) (o i), n) := by
    intro j
    rw [show List.ofFn (fun i : Fin n => (sparseLocalRat (w j i) (o i), (1 : ℕ))) =
      (List.ofFn (fun i => sparseLocalRat (w j i) (o i))).map (fun x => (x, (1 : ℕ))) by
        simp only [List.map_ofFn]; rfl]
    rw [counted_product]
    simp [Fin.prod_ofFn]
  have he : countedSparsePauli w c o =
      (∑ j, c j * ∏ i, sparseLocalRat (w j i) (o i), m * (n + 1), m) := by
    unfold countedSparsePauli
    simp_rw [hi]
    rw [counted_sum]
    simp [List.map_ofFn, Function.comp_def, Fin.sum_ofFn]
  rw [he]
  refine ⟨?_, rfl, rfl, ?_⟩
  · simp only [sparsePauliValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod,
      sparseLocalRat_cast, tensorPauliValue]
  · exact tensorPauliFreshResourceCounts_spec n L K ω

/-- For qubit Pauli axes zero and two with rational coefficients `a` and `b`, the
energy-estimator variance is `3 * (a² + b²)` minus the squared mean. This specializes the
shadow variance framework of [HuangKuengPreskill2020]. -/
theorem sparse_pauli_incompatible_qubit_energy_consumer (ρ : Operator 2)
    (hρ : IsDensityOperator ρ) (a b : ℚ) :
    let w : Fin 2 → Fin 1 → Option (Fin 3) := fun j _ => some (if j = 0 then 0 else 2)
    let c : Fin 2 → ℚ := fun j => if j = 0 then a else b
    (tensorPauliLaw 1 ρ hρ).variance (sparsePauliValue w c) =
      3 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) -
        (Matrix.trace (sparsePauliObservable w c * ρ)).re ^ 2 := by
  classical
  (try dsimp only)
  rw [(sparse_pauli_exact_energy_variance_and_bound 1 2 ρ hρ
    (fun j _ => some (if j = 0 then 0 else 2)) (fun j => if j = 0 then a else b)).2.1]
  have hd : ∀ z : Fin 3,
      sparsePauliMoment ρ (fun _ : Fin 1 => some z) (fun _ : Fin 1 => some z) = 3 := by
    intro z
    have hc : pauliWordsCompatible (fun _ : Fin 1 => some z) (fun _ => some z) := by
      intro i x y hx hy
      simpa using hx.symm.trans hy
    have hw : pauliWordCancel (fun _ : Fin 1 => some z) (fun _ => some z) = fun _ => none := rfl
    simp [sparsePauliMoment, hc, pauliWordOverlap, hw, tensorPauliWord,
      tensorPauliWordFactor, tensorPauliProduct_one, hρ.2]
  have hz : ∀ x y : Fin 3, x ≠ y →
      sparsePauliMoment ρ (fun _ : Fin 1 => some x) (fun _ => some y) = 0 := by
    intro x y hxy
    have hc : ¬ pauliWordsCompatible (fun _ : Fin 1 => some x) (fun _ => some y) :=
      fun hh => hxy (hh 0 x y rfl rfl)
    simp [sparsePauliMoment, hc]
  simp only [Fin.sum_univ_two]
  norm_num [hd, hz 0 2 (by decide), hz 2 0 (by decide)]
  ring
end Qatlib.Concepts.ShadowModels.FairBitRecords
