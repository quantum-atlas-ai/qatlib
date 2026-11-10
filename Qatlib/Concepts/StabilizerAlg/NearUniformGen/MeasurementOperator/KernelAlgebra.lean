/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator

def mixtureDist {Ω G : Type*} [Fintype Ω] [Fintype G]
    (P : FinDist Ω) (k : Ω → FinDist G) : FinDist G where
  prob y := ∑ V, P.prob V * (k V).prob y
  nonneg y := Finset.sum_nonneg fun V _ => mul_nonneg (P.nonneg V) ((k V).nonneg y)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
    exact P.sum_one

theorem mixtureDist_prob {Ω G : Type*} [Fintype Ω] [Fintype G]
    (P : FinDist Ω) (k : Ω → FinDist G) (y : G) :
    (mixtureDist P k).prob y = ∑ V, P.prob V * (k V).prob y := rfl

def productKernel {Ω G H : Type*} [Fintype G] [Fintype H]
    (k : Ω → FinDist G) (h : Ω → FinDist H) : Ω → FinDist (G × H) :=
  fun V => FinDist.independentPair (k V) (h V)

theorem productKernel_prob {Ω G H : Type*} [Fintype G] [Fintype H]
    (k : Ω → FinDist G) (h : Ω → FinDist H) (V : Ω) (g : G) (z : H) :
    (productKernel k h V).prob (g, z) = (k V).prob g * (h V).prob z := rfl

theorem productKernel_swap {Ω G H : Type*} [Fintype G] [Fintype H]
    (k : Ω → FinDist G) (h : Ω → FinDist H) (V : Ω) (g : G) (z : H) :
    (productKernel k h V).prob (g, z) = (productKernel h k V).prob (z, g) := by
  exact mul_comm _ _

end Qatlib.Concepts.StabilizerAlg.NearUniformGen.MeasurementOperator
