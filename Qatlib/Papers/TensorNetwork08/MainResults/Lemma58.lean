/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Lemma56

/-!
# Normalized partition value of the delta network

Derives the partition-function normalization in Lemma 5.8 of [AradLandau2010] from an assumed
identification of the delta-network value with `consistentDeltaSum`. The connectivity and
nonempty-vertex hypotheses are those used for the difference-model partition identity.

The first result states the equality after multiplication by the color cardinality. The second
solves for the network value when that cardinality is nonzero as a complex number.

## Main statements

* `lemma5_8_delta_network_evaluates`: relates the network value to the partition function by a
  cardinality factor.
* `lemma5_8_delta_network_eq_inv`: solves for the network value using the inverse cardinality.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

namespace Qatlib.Papers.TensorNetwork08.MainResults.Lemma58

open Classical
open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
open Qatlib.Papers.TensorNetwork08.MainResults.Lemma56

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

/-- If the delta-network value equals the consistent-label sum, then under the stated
connectivity hypothesis its product with the color cardinality equals the difference-model
partition function. See [AradLandau2010]. -/
theorem lemma5_8_delta_network_evaluates
    [AddCommGroup C] [DecidableEq C] [Nonempty V]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ)
    (hconn : ∀ σ τ : V → C,
      (∀ e : E, σ (src e) - σ (dst e) = τ (src e) - τ (dst e)) →
        ∃ κ : C, ∀ v : V, τ v = σ v + κ)
    {deltaNetworkValue : ℂ}
    (hnet : deltaNetworkValue = consistentDeltaSum src dst h β) :
    (Fintype.card C : ℂ) * deltaNetworkValue = differencePartitionFunction src dst h β := by

  rw [hnet]
  exact (lemma5_6_difference_model_partition src dst h β hconn).symm

/-- Under the connectivity hypothesis and the identification with the consistent-label sum, a
nonzero complex color cardinality gives the network value as its inverse times the
difference-model partition function. See [AradLandau2010]. -/
theorem lemma5_8_delta_network_eq_inv
    [AddCommGroup C] [DecidableEq C] [Nonempty V]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ)
    (hconn : ∀ σ τ : V → C,
      (∀ e : E, σ (src e) - σ (dst e) = τ (src e) - τ (dst e)) →
        ∃ κ : C, ∀ v : V, τ v = σ v + κ)
    {deltaNetworkValue : ℂ}
    (hnet : deltaNetworkValue = consistentDeltaSum src dst h β)
    (hcard : (Fintype.card C : ℂ) ≠ 0) :
    deltaNetworkValue
      = (Fintype.card C : ℂ)⁻¹ * differencePartitionFunction src dst h β := by
  have h := lemma5_8_delta_network_evaluates src dst h β hconn hnet
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Qatlib.Papers.TensorNetwork08.MainResults.Lemma58
