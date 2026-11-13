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
adds a supplied order-computation budget to the sampler cost. This is a semantic
composition; validity of that budget for an implementation is assumed separately.
`proposition11_class_number_statement` is an unproved uniform specification with
execution contracts and probability of the correct class-number output.

## Main statements

* `proposition11_cost_decomposition`: polynomial generator and order costs have a polynomial
  sum.
* `proposition11_compose`: a correct order routine on generating sets yields a Monte Carlo group
  cardinality computation.
* `proposition11_class_number_statement`: **Statement only — not proved in Qatlib.**

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

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
noncomputable def orderPostprocess {G : Type*} [AddCommGroup G] [Fintype G]
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ)
    (T : Finset G) : Option ℕ := by
  classical
  exact if h : AddSubgroup.closure (T : Set G) = ⊤ then some (ord T h) else none

/-- Semantic composition charging a supplied budget for the entire order
postprocessor, including its generating-set test. -/
noncomputable def composeOrder {G : Type*} [AddCommGroup G] [Fintype G]
    (Ag : CoinAlgo (Finset G)) (orderCost : ℕ)
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ) : CoinAlgo ℕ := by
  classical
  exact Ag.bindCosted (orderPostprocess ord) orderCost

/-- A Monte Carlo sampler of generating sets, composed with a routine that returns the group
cardinality on every generating set, remains Monte Carlo for that cardinality and adds
the supplied order budget. Its primitive-step implementation is an explicit
hypothesis, including the generating-set test; no implementation is constructed. -/
theorem proposition11_compose
    (G : Type*) [AddCommGroup G] [Fintype G]
    (Ag : CoinAlgo (Finset G)) (orderCost : ℕ)
    (hAg : Ag.IsMC (fun T => AddSubgroup.closure (T : Set G) = ⊤))
    (ord : (T : Finset G) → AddSubgroup.closure (T : Set G) = ⊤ → ℕ)
    (implementation : PostprocessingContract (orderPostprocess ord) orderCost)
    (hord : ∀ T hT, ord T hT = Fintype.card G) :
    (composeOrder Ag orderCost ord).IsMC (fun n => n = Fintype.card G)
      ∧ (composeOrder Ag orderCost ord).cost = Ag.cost + implementation.program.length := by
  classical
  unfold composeOrder
  constructor
  · apply CoinAlgo.isMC_bind Ag _ hAg
    intro T hT
    exact ⟨ord T hT, by simp [orderPostprocess, dif_pos hT], hord T hT⟩
  · change Ag.cost + orderCost = _
    exact congrArg (fun n => Ag.cost + n) implementation.cost_eq

/-- **Statement only — not proved in Qatlib.** Uniform class-number computation
with correctness probability and primitive-step execution contracts. The supplied
machine fixes the initialization/decoding cost convention. -/
def proposition11_class_number_statement (M : PrimitiveMachine (CurveData × ℕ) ℕ)
    (logq : CurveData → ℕ) : Prop :=
  ∃ (program : CurveData → ℕ → List M.Step) (c k : ℕ), ∀ C e,
    16 * (C.g : ℝ) < halfPower C.q e →
    (M.algorithm (C, e) (program C e)).IsMC (fun n => n = C.classNumber e) ∧
    (M.algorithm (C, e) (program C e)).cost ≤ c * (C.g + logq C + e + 1) ^ k

end Qatlib.Papers.ZetaCurves04.MainResults.Proposition11
