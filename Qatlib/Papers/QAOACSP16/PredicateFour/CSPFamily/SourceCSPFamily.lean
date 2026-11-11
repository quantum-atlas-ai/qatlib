/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel.SourceCSPModel
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

set_option backward.isDefEq.respectTransparency false

/-!
# Random CSP families

Lin--Zhu, fixed arXiv:1601.01744v1, Section 2 (pp.2--3).

A `CSPFamily` records a fixed set of scopes `S_l` together with a family of
predicates `ψ_l(·; p)` indexed by a random parameter `p` drawn from a finite
law `law`.  The `m` constraints are sampled independently, so the law on
instances is the product law `independentSampleLaw` of Frozen
`MonteCarloMean.FinDistBounds`.

This file contains the sampling model only: `Typical` (equation (2.2)),
bounded degree/arity, the Boolean-range condition, and the product instance
law.  No QAOA performance statement is asserted here.

The parameter space is required to be finite because `FinDist` is a finite
distribution.  The paper allows arbitrary real-valued random variables in the
generalized Max-XOR model (§4.1); for the discrete sign models of Theorem 2 /
Corollary 5 (which draw finitely many predicates) this is no restriction.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily

open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel

/-- The sign `±1` of a Boolean value. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The sign of `false` is `-1`. -/
@[simp] theorem sgn_false : sgn false = -1 := rfl

/-- The sign of `true` is `1`. -/
@[simp] theorem sgn_true : sgn true = 1 := rfl

/-- The uniform law on `Bool`, the law of a random sign. -/
def uniformBool : FinDist Bool where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by
    rw [Fintype.sum_bool]
    norm_num

/-- A random sign has zero mean (the elementary typicality input). -/
theorem uniformBool_expect_sgn : uniformBool.expect sgn = 0 := by
  unfold FinDist.expect uniformBool sgn
  rw [Fintype.sum_bool]
  norm_num

/-- The expectation of a function of a single independent sign. -/
theorem uniformBool_expect (f : Bool → ℝ) :
    uniformBool.expect f = (f true + f false) / 2 := by
  unfold FinDist.expect uniformBool
  rw [Fintype.sum_bool]
  ring

/-- A family of CSPs with `m` fixed scopes, each constraint's predicate drawn
independently from `law`.  `pred_scope` records that the predicate's scope is
the prescribed one (the paper fixes the scopes and randomizes only `ψ`). -/
structure CSPFamily (V : Type) (P : Type) [Fintype V] [Fintype P] [DecidableEq P] where
  /-- Number of constraints. -/
  m : ℕ
  /-- Nonempty instance. -/
  hm : 0 < m
  /-- The scope of every constraint. -/
  scope : Fin m → Finset V
  /-- The family of predicates available at every constraint. -/
  pred : Fin m → P → Predicate V
  /-- The predicate's scope is the prescribed scope. -/
  pred_scope : ∀ l p, (pred l p).scope = scope l
  /-- The law of the random parameter. -/
  law : FinDist P

variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Type} [Fintype P] [DecidableEq P]

/-- The instance sampled at the parameter tuple `ω`. -/
def CSPFamily.instance (F : CSPFamily V P) (ω : Fin F.m → P) : CSPInstance V :=
  sampledInstance F.m F.hm F.pred ω

/-- The constraints of the sampled instance are the selected predicates. -/
@[simp] theorem CSPFamily.instance_con (F : CSPFamily V P) (ω : Fin F.m → P) (l : Fin F.m) :
    (F.instance ω).con l = F.pred l (ω l) := rfl

/-- `μ` of the family: the average, over the random constraints, of the
uniform-assignment success probability `ψ̂(∅)` (equation (2.2) and Theorem 1). -/
def CSPFamily.muFamily (F : CSPFamily V P) : ℝ :=
  (∑ l : Fin F.m, F.law.expect (fun p => constraintMean (F.pred l p))) / (F.m : ℝ)

/-- Typicality, equation (2.2): at every assignment the random predicate has
mean equal to its uniform mean, i.e. all nonempty Fourier coefficients have
zero mean. -/
def CSPFamily.Typical (F : CSPFamily V P) : Prop :=
  ∀ l : Fin F.m, IsTypical (F.pred l) F.law

/-- Bounded degree `D`: every variable occurs in at most `D` constraints. -/
def CSPFamily.BoundedDegree (F : CSPFamily V P) (D : ℕ) : Prop :=
  ∀ v : V, (Finset.univ.filter fun l : Fin F.m => v ∈ F.scope l).card ≤ D

/-- Every constraint has arity at most `k`. -/
def CSPFamily.BoundedArity (F : CSPFamily V P) (k : ℕ) : Prop :=
  ∀ l : Fin F.m, (F.scope l).card ≤ k

/-- Every predicate takes values in `[0,1]` (a Max-CSP objective; the paper's
Boolean predicates and the `(1 + ψ)/2` encoding both satisfy this). -/
def CSPFamily.BooleanValues (F : CSPFamily V P) : Prop :=
  ∀ (l : Fin F.m) (p : P) (z : V → Bool), (F.pred l p).val z ∈ Set.Icc (0 : ℝ) 1

/-- The law of the sampled instance: the `m` constraint parameters are drawn
independently (Section 2: "choosing the constraint on each scope according to
some probability distribution, independently"). -/
def CSPFamily.instanceLaw (F : CSPFamily V P) : FinDist (Fin F.m → P) :=
  independentSampleLaw (fun _ => F.law)

/-- The family mean `μ` is the expectation, over the sampled instance, of the
instance mean of the random constraint means. -/
theorem CSPFamily.muFamily_eq_expect (F : CSPFamily V P) :
    F.muFamily
      = F.instanceLaw.expect
          (fun ω => (∑ l : Fin F.m, constraintMean (F.pred l (ω l))) / (F.m : ℝ)) := by
  classical
  unfold CSPFamily.muFamily
  rw [show (fun ω : Fin F.m → P =>
        (∑ l : Fin F.m, constraintMean (F.pred l (ω l))) / (F.m : ℝ))
      = fun ω => (1 / (F.m : ℝ)) *
          ∑ l : Fin F.m, constraintMean (F.pred l (ω l)) from by
    funext ω; ring]
  unfold CSPFamily.instanceLaw
  rw [expect_const_mul, expect_sum, one_div, div_eq_mul_inv]
  have h : (∑ l : Fin F.m, F.law.expect (fun p => constraintMean (F.pred l p)))
      = ∑ l : Fin F.m,
          (independentSampleLaw (fun _ : Fin F.m => F.law)).expect
            (fun ω => constraintMean (F.pred l (ω l))) := by
    apply Finset.sum_congr rfl
    intro l _
    exact (independentSampleLaw_expect_coord (fun _ : Fin F.m => F.law) l
      (fun p => constraintMean (F.pred l p))).symm
  rw [h]
  ring

/-- `μ` of the family is nonnegative for nonnegative predicates. -/
theorem CSPFamily.muFamily_nonneg (F : CSPFamily V P)
    (h : ∀ (l : Fin F.m) (p : P) (z : V → Bool), 0 ≤ (F.pred l p).val z) :
    0 ≤ F.muFamily := by
  unfold CSPFamily.muFamily
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro l _
    unfold FinDist.expect constraintMean uniformExpect
    apply Finset.sum_nonneg
    intro p _
    apply mul_nonneg
    · exact F.law.nonneg p
    · apply div_nonneg
      · exact Finset.sum_nonneg fun z _ => h l p z
      · positivity
  · positivity

end Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily
