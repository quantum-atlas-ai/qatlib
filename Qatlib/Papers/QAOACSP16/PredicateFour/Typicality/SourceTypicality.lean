/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily.SourceCSPFamily
import Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState.SourceQaoaState

set_option backward.isDefEq.respectTransparency false

/-!
# Typicality of kXOR and kSAT constraints

Lin--Zhu, fixed arXiv:1601.01744v1, p.2 (Definition 3, equations (2.2)--(2.3))
and Corollary 5 (p.11).

The paper says that kXOR and kSAT are typical: choosing the signs in each
constraint independently at random makes every nonempty Fourier coefficient
have zero mean.  In the assignment form (2.2) used here this says

`E_ψ [ψ(z)] = E_ψ [ψ̂(∅)]` for every assignment `z`.

* For kXOR, `ψ(z) = 1/2 ± 1/2 ∏ x_i`, so `E_ψ[ψ(z)] = 1/2` for every `z`:
  the single random sign has zero mean.  Proved.
* For kSAT, `ψ(z) = 1 - ∏_i (1 ± x_i)/2` with an independent random sign on
  every variable of the scope.  The uniform sign law on the cube is invariant
  under the coordinate flip `σ ↦ σ ⊕ (z ⊕ z')`, which exchanges `ψ(z)` with
  `ψ(z')`; hence `E_ψ[ψ(z)]` does not depend on `z`, and its common value is
  `E_ψ E_z ψ(z) = E_ψ ψ̂(∅)`.  Proved.

Both are the finite, assignment-level form of (2.3) that the main theorem
consumes through `CSPFamily.Typical`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily
open Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.PredicateFour.Typicality

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### kXOR -/

/-- The character `χ_S(z) = ∏_{v∈S} (-1)^{z_v}` of equation (2.1). -/
def charFun (S : Finset V) (z : V → Bool) : ℝ :=
  ∏ v ∈ S, sgn (z v)

/-- Flipping a coordinate in the scope negates the character. -/
theorem charFun_flipAt (S : Finset V) (z : V → Bool) (v : V) :
    charFun S (flipAt v z) = if v ∈ S then -charFun S z else charFun S z := by
  classical
  unfold charFun
  by_cases hv : v ∈ S
  · rw [if_pos hv, Finset.prod_eq_mul_prod_diff_singleton_of_mem hv,
      Finset.prod_eq_mul_prod_diff_singleton_of_mem hv, ← neg_mul]
    congr 1
    · rw [flipAt, Function.update_self]
      cases z v <;> simp [sgn]
    · apply Finset.prod_congr rfl
      intro w hw
      have hwv : w ≠ v := by
        have := (Finset.mem_sdiff.mp hw).2
        simpa using this
      rw [flipAt, Function.update_of_ne hwv]
  · rw [if_neg hv]
    apply Finset.prod_congr rfl
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    rw [flipAt, Function.update_of_ne hwv]

/-- The character has zero sum over the cube whenever its scope is nonempty
(the pairing argument behind (2.3)). -/
theorem sum_charFun_eq_zero {S : Finset V} (hS : S.Nonempty) :
    (∑ z : V → Bool, charFun S z) = 0 := by
  classical
  obtain ⟨v, hv⟩ := hS
  have h := sum_flipAt (fun z => charFun S z) v
  have hneg : ∀ z : V → Bool, charFun S (flipAt v z) = -charFun S z := by
    intro z
    rw [charFun_flipAt]
    simp only [hv, if_true]
  rw [Finset.sum_congr rfl (fun z _ => hneg z), Finset.sum_neg_distrib] at h
  linarith

/-- The kXOR predicate with random sign `a`:
`ψ(z) = (1 + a ∏_{v∈S} z_v)/2`, i.e. the paper's `1/2 ± 1/2 ∏ x_i`. -/
def xorPredicate (S : Finset V) (a : ℝ) : Predicate V where
  scope := S
  val := fun z => (1 + a * charFun S z) / 2
  locality := by
    intro z z' h
    have hχ : charFun S z = charFun S z' := by
      unfold charFun
      apply Finset.prod_congr rfl
      intro v hv
      rw [h v hv]
    rw [hχ]

/-- The uniform mean of the kXOR predicate is `1/2` for a nonempty scope. -/
theorem constraintMean_xor {S : Finset V} (hS : S.Nonempty) (a : ℝ) :
    constraintMean (xorPredicate S a) = 1 / 2 := by
  simp only [constraintMean, uniformExpect, xorPredicate]
  have hsum : (∑ z : V → Bool, (1 + a * charFun S z))
      = (Fintype.card (V → Bool) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, sum_charFun_eq_zero hS]
    ring
  have h1 : (∑ z : V → Bool, (1 + a * charFun S z) / 2)
      = (∑ z, (1 + a * charFun S z)) / 2 := by
    rw [Finset.sum_div]
  calc (∑ z : V → Bool, (1 + a * charFun S z) / 2) / (Fintype.card (V → Bool) : ℝ)
      = ((∑ z, (1 + a * charFun S z)) / 2) / (Fintype.card (V → Bool) : ℝ) := by rw [h1]
    _ = ((Fintype.card (V → Bool) : ℝ) / 2) / (Fintype.card (V → Bool) : ℝ) := by rw [hsum]
    _ = 1 / 2 := by
      have hpos : (0 : ℝ) < (Fintype.card (V → Bool) : ℝ) := by positivity
      field_simp [hpos.ne']

/-- kXOR has typicality: the random sign has zero mean (Definition 3 / (2.2)). -/
theorem typical_xor {S : Finset V} (hS : S.Nonempty) :
    IsTypical (fun p : Bool => xorPredicate S (sgn p)) uniformBool := by
  intro z
  have hfun : (fun p : Bool =>
        (xorPredicate S (sgn p)).val z - constraintMean (xorPredicate S (sgn p)))
      = fun p : Bool => (charFun S z / 2) * sgn p := by
    funext p
    rw [constraintMean_xor hS]
    show (1 + sgn p * charFun S z) / 2 - 1 / 2 = charFun S z / 2 * sgn p
    ring
  rw [hfun, expect_const_mul, uniformBool_expect_sgn, mul_zero]

/-! ### kSAT -/

/-- The kSAT clause of the paper with independent random literal signs `σ`:
`ψ(z) = 1 - ∏_{v∈S} (1 + σ_v z_v)/2`.  Each factor is `1` exactly when the
literal at `v` is true, so the value is `1` iff the clause is satisfied. -/
def ksatVal (S : Finset V) (σ z : V → Bool) : ℝ :=
  1 - ∏ v ∈ S, ((1 + sgn (σ v) * sgn (z v)) / 2)

/-- The kSAT predicate with sign pattern `σ`. -/
def ksatPredicate (S : Finset V) (σ : V → Bool) : Predicate V where
  scope := S
  val := fun z => ksatVal S σ z
  locality := by
    intro z z' h
    unfold ksatVal
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [h v hv]

/-- `sgn` of a negated Boolean sign is the negative sign. -/
@[simp] theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> simp [sgn]

/-- The uniform law on the cube of assignments. -/
def uniformCube : FinDist (V → Bool) where
  prob _ := 1 / (Fintype.card (V → Bool) : ℝ)
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpos : (0 : ℝ) < (Fintype.card (V → Bool) : ℝ) := by positivity
    field_simp [hpos.ne']

/-- The uniform cube expectation is the normalized sum. -/
theorem uniformCube_expect (f : (V → Bool) → ℝ) :
    uniformCube.expect f = (1 / (Fintype.card (V → Bool) : ℝ)) * ∑ σ, f σ := by
  unfold FinDist.expect uniformCube
  rw [← Finset.mul_sum]

/-- Flipping the coordinates on which `z` and `z'` differ, applied to a sign
pattern.  This is the symmetry that exchanges the clause at `z` with the clause
at `z'`. -/
def pointwiseFlip (z z' : V → Bool) (σ : V → Bool) : V → Bool :=
  fun v => if z v = z' v then σ v else !(σ v)

/-- `pointwiseFlip` is an involution. -/
theorem pointwiseFlip_involutive (z z' : V → Bool) :
    Function.Involutive (pointwiseFlip z z') := by
  intro σ
  funext v
  unfold pointwiseFlip
  by_cases h : z v = z' v <;> simp [h]

/-- Sums over the cube are invariant under `pointwiseFlip`. -/
theorem sum_pointwiseFlip (f : (V → Bool) → ℝ) (z z' : V → Bool) :
    (∑ σ : V → Bool, f (pointwiseFlip z z' σ)) = ∑ σ, f σ := by
  classical
  refine Finset.sum_bij (fun σ _ => pointwiseFlip z z' σ) (fun _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro a _ b _ hab
    have h1 : pointwiseFlip z z' (pointwiseFlip z z' a) = a := pointwiseFlip_involutive z z' a
    have h2 : pointwiseFlip z z' (pointwiseFlip z z' b) = b := pointwiseFlip_involutive z z' b
    have h3 := congrArg (pointwiseFlip z z') hab
    rw [h1, h2] at h3
    exact h3
  · intro b _
    exact ⟨pointwiseFlip z z' b, Finset.mem_univ _, pointwiseFlip_involutive z z' b⟩
  · intro a _
    rfl

/-- One factor of the clause is preserved by the symmetry. -/
theorem ksat_factor_flip (z z' σ : V → Bool) (v : V) :
    sgn (pointwiseFlip z z' σ v) * sgn (z' v) = sgn (σ v) * sgn (z v) := by
  unfold pointwiseFlip
  by_cases h : z v = z' v
  · rw [if_pos h, h]
  · have h' : z' v = !(z v) := by
      cases hz : z v <;> cases hz' : z' v <;> simp_all
    rw [if_neg h, h', sgn_not, sgn_not]
    ring

/-- The clause value at `z` with signs `σ` equals the clause value at `z'` with
the flipped signs. -/
theorem ksatVal_flip (S : Finset V) (z z' σ : V → Bool) :
    ksatVal S σ z = ksatVal S (pointwiseFlip z z' σ) z' := by
  unfold ksatVal
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [ksat_factor_flip]

/-- The expectation of the clause value under the uniform sign law does not
depend on the assignment. -/
theorem expect_ksatVal_eq (S : Finset V) (z z' : V → Bool) :
    uniformCube.expect (fun σ => ksatVal S σ z)
      = uniformCube.expect (fun σ => ksatVal S σ z') := by
  rw [uniformCube_expect, uniformCube_expect]
  congr 1
  calc
    (∑ σ : V → Bool, ksatVal S σ z)
        = ∑ σ : V → Bool, ksatVal S (pointwiseFlip z z' σ) z' :=
          Finset.sum_congr rfl fun σ _ => ksatVal_flip S z z' σ
    _ = ∑ σ : V → Bool, ksatVal S σ z' := sum_pointwiseFlip (fun σ => ksatVal S σ z') z z'

/-- kSAT has typicality (Definition 3 / (2.2)) for independently chosen signs. -/
theorem typical_ksat (S : Finset V) :
    IsTypical (fun σ : V → Bool => ksatPredicate S σ) uniformCube := by
  classical
  intro z
  have hsum_eq : ∀ z' : V → Bool, (∑ σ, ksatVal S σ z') = ∑ σ, ksatVal S σ z := by
    intro z'
    have h := expect_ksatVal_eq S z' z
    rw [uniformCube_expect, uniformCube_expect] at h
    exact mul_left_cancel₀ (by positivity : (1 / (Fintype.card (V → Bool) : ℝ)) ≠ 0) h
  -- expectation of the clause value at `z`
  have hE : uniformCube.expect (fun σ => ksatVal S σ z)
      = (1 / (Fintype.card (V → Bool) : ℝ)) * (∑ σ, ksatVal S σ z) :=
    uniformCube_expect _
  -- expectation of the constraint mean
  have hmean : uniformCube.expect (fun σ => constraintMean (ksatPredicate S σ))
      = (1 / (Fintype.card (V → Bool) : ℝ)) * (∑ σ, ksatVal S σ z) := by
    rw [uniformCube_expect]
    have hstep : (∑ σ : V → Bool, constraintMean (ksatPredicate S σ))
        = (∑ σ : V → Bool, ∑ z' : V → Bool, ksatVal S σ z')
            / (Fintype.card (V → Bool) : ℝ) := by
      simp only [constraintMean, uniformExpect, ksatPredicate]
      rw [Finset.sum_div]
    rw [hstep]
    have hswap : (∑ σ : V → Bool, ∑ z' : V → Bool, ksatVal S σ z')
        = (Fintype.card (V → Bool) : ℝ) * (∑ σ, ksatVal S σ z) := by
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun z' _ => hsum_eq z')]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hswap]
    have hC : (0 : ℝ) < (Fintype.card (V → Bool) : ℝ) := by positivity
    field_simp [hC.ne']
  -- the expectation of the difference vanishes
  have hsplit : (∑ σ : V → Bool,
        uniformCube.prob σ * (ksatVal S σ z - constraintMean (ksatPredicate S σ)))
      = (∑ σ, uniformCube.prob σ * ksatVal S σ z)
        - ∑ σ, uniformCube.prob σ * constraintMean (ksatPredicate S σ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  show uniformCube.expect
      (fun σ : V → Bool => ksatVal S σ z - constraintMean (ksatPredicate S σ)) = 0
  unfold FinDist.expect
  rw [hsplit]
  have hE' : (∑ σ, uniformCube.prob σ * ksatVal S σ z)
      = (1 / (Fintype.card (V → Bool) : ℝ)) * (∑ σ, ksatVal S σ z) := by
    simp only [uniformCube]
    rw [← Finset.mul_sum]
  have hmean' : (∑ σ, uniformCube.prob σ * constraintMean (ksatPredicate S σ))
      = (1 / (Fintype.card (V → Bool) : ℝ)) * (∑ σ, ksatVal S σ z) := by
    have h := hmean
    rw [uniformCube_expect] at h
    simpa only [uniformCube, Finset.mul_sum] using h
  rw [hE', hmean', sub_self]

end Qatlib.Papers.QAOACSP16.PredicateFour.Typicality
