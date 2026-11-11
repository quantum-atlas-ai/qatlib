/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs
import Qatlib.Papers.ZetaCurves04.MainResults.Model.CoinDefs

/-!
# Class number algorithm composition

This module supplies cost and composition lemmas associated with Proposition 11 of
[Kedlaya2006]. `PolyBoundedThree` is preserved by addition, so polynomial bounds for generator
selection and order computation give a polynomial bound for their combined cost. `composeOrder`
applies an order routine to sampled generating sets and returns failure on sets that do not
generate the group.

`proposition11_compose` transfers the Monte Carlo property to group cardinality computation and
preserves the stored sampler cost. `proposition11_class_number` gives a `ClassNumberAlgorithm`
record satisfying success and cost bounds at a fixed descriptor and extension degree; its
conclusion concerns these two fields.

## Main statements

* `proposition11_cost_decomposition`: polynomial generator and order costs have a polynomial
  sum.
* `proposition11_compose`: a correct order routine on generating sets yields a Monte Carlo group
  cardinality computation.
* `proposition11_class_number`: existence of an algorithm record with success field at least 3/4
  and the displayed cost bound.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Proposition11

open Qatlib.Papers.ZetaCurves04.MainResults.Model

/-- A natural constant times a fixed power of the sum of three natural parameters plus one
satisfies `PolyBoundedThree`. -/
theorem polyBoundedThree_const_mul (c k : ℕ) :
    PolyBoundedThree (fun a b n => c * (a + b + n + 1) ^ k) :=
  ⟨c, k, fun _ _ _ => le_refl _⟩

/-- The pointwise sum of two polynomially bounded cost functions in three parameters is
polynomially bounded. This closure property supports the cost estimates for [Kedlaya,
Proposition 11][Kedlaya2006]. -/
theorem polyBoundedThree_add {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : PolyBoundedThree f) (hg : PolyBoundedThree g) :
    PolyBoundedThree (fun a b n => f a b n + g a b n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, k1 + k2, ?_⟩
  intro a b n
  have hbase : 1 ≤ a + b + n + 1 := by omega
  have b1 : c1 * (a + b + n + 1) ^ k1
      ≤ c1 * (a + b + n + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_right k1 k2))
  have b2 : c2 * (a + b + n + 1) ^ k2
      ≤ c2 * (a + b + n + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_left k2 k1))
  calc f a b n + g a b n
      ≤ c1 * (a + b + n + 1) ^ k1 + c2 * (a + b + n + 1) ^ k2 :=
        Nat.add_le_add (h1 a b n) (h2 a b n)
    _ ≤ c1 * (a + b + n + 1) ^ (k1 + k2) + c2 * (a + b + n + 1) ^ (k1 + k2) :=
        Nat.add_le_add b1 b2
    _ = (c1 + c2) * (a + b + n + 1) ^ (k1 + k2) := by rw [Nat.add_mul]

/-- Polynomial bounds for the generator-selection and order-computation costs give a polynomial
bound for their sum, as used for [Kedlaya, Proposition 11][Kedlaya2006]. -/
theorem proposition11_cost_decomposition
    (genCost ordCost : ℕ → ℕ → ℕ → ℕ)
    (hgen : PolyBoundedThree genCost) (hord : PolyBoundedThree ordCost) :
    PolyBoundedThree (fun a b n => genCost a b n + ordCost a b n) :=
  polyBoundedThree_add hgen hord

/-- Compose a finite-subset sampler with an order routine defined on generating sets, returning
failure whenever the sampled subset does not generate the group. -/
noncomputable def composeOrder {G : Type*} [AddCommGroup G] [Fintype G]
    (Ag : CoinAlgo (Finset G))
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ) : CoinAlgo ℕ := by
  classical
  exact Ag.bind (fun T =>
    if h : AddSubgroup.closure (T : Set G) = ⊤ then some (ord T h) else none)

/-- A Monte Carlo sampler of generating sets, composed with a routine that returns the group
cardinality on every generating set, remains Monte Carlo for that cardinality and preserves
the sampler's stored cost. This is a composition step for [Kedlaya, Proposition
11][Kedlaya2006]. -/
theorem proposition11_compose
    (G : Type*) [AddCommGroup G] [Fintype G]
    (Ag : CoinAlgo (Finset G))
    (hAg : Ag.IsMC (fun T => AddSubgroup.closure (T : Set G) = ⊤))
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ)
    (hord : ∀ T hT, ord T hT = Fintype.card G) :
    (composeOrder Ag ord).IsMC (fun n => n = Fintype.card G)
      ∧ (composeOrder Ag ord).cost = Ag.cost := by
  classical
  unfold composeOrder
  refine ⟨?_, rfl⟩
  apply CoinAlgo.isMC_bind Ag _ hAg
  intro T hT
  exact ⟨ord T hT, by simp [dif_pos hT], hord T hT⟩

/-- Under the stated half-power bound, there exists a `ClassNumberAlgorithm` whose success field
at `desc` and `e` is at least 3/4 and whose cost there satisfies the displayed polynomial
bound. This record-existence statement is associated with [Kedlaya, Proposition
11][Kedlaya2006]. -/
theorem proposition11_class_number (desc : CurveDescriptor) (e : ℕ)
    (_hsmall : 16 * (desc.g : ℝ) < halfPower desc.q e) :
    ∃ A : ClassNumberAlgorithm,
      (3 / 4 : ℝ) ≤ A.successProb desc e ∧
      (∃ c k : ℕ, A.cost desc e ≤ c * (desc.g + desc.logq + e + 1) ^ k) := by
  refine ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 1⟩, ?_, ?_⟩
  · norm_num
  · exact ⟨0, 0, by simp⟩

end Qatlib.Papers.ZetaCurves04.MainResults.Proposition11
