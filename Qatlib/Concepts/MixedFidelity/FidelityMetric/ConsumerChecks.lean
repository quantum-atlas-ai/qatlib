/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MixedFidelity.FidelityMetric.PhyslibBridge
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ClassicalCopies
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.CalibratedMeasurement
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.QuantumCopies
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ProductMeasures

@[expose] public section


set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open Qatlib.Concepts.MixedFidelity.FidelityMetric

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.ConsumerChecks

example {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : MState d) :
    1 - MState.fidelity ρ σ ≤ TrDistance ρ σ :=
  one_sub_fidelity_le_trDistance ρ σ

example {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ σ : MState d) (Λ : CPTPMap d e) :
    MState.fidelity ρ σ ≤ MState.fidelity (Λ ρ) (Λ σ) :=
  fidelity_channel_nondecreasing ρ σ Λ

example {D : ℕ} (ρ σ : MState (Fin D)) :
    1 - MState.fidelity ρ σ ≤ TrDistance ρ σ :=
  one_sub_fidelity_le_trDistance ρ σ

example {D : ℕ} (ρ σ : MState (Fin D)) :
    TrDistance ρ σ ≤ Real.sqrt (1 - MState.fidelity ρ σ ^ 2) :=
  trDistance_le_sqrt_one_sub_fidelity_sq ρ σ

example {D : ℕ} (ρ σ : MState (Fin D)) :
    MState.fidelity ρ σ ≤ MState.fidelity
      ((CPTPMap.id : CPTPMap (Fin D) (Fin D)) ρ)
      ((CPTPMap.id : CPTPMap (Fin D) (Fin D)) σ) :=
  fidelity_channel_nondecreasing ρ σ CPTPMap.id

example {D : ℕ} (ρ : MState (Fin D)) : TrDistance ρ ρ = 0 := by
  simp [TrDistance, Matrix.traceNorm_zero]

example {D : ℕ} (ρ : MState (Fin D)) : MState.fidelity ρ ρ = 1 :=
  MState.fidelity_self_eq_one ρ

example {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) (n : ℕ) :
    MState (Fin n → d) := ρ.npow n

example {d : Type*} [Fintype d] [DecidableEq d] (ψ : Ket d) (n : ℕ) :
    MState.pure (Ket.piProd (fun _ : Fin n => ψ)) = (MState.pure ψ).npow n :=
  MState.pure_piProd _

example {d : Type*} [Fintype d] [DecidableEq d] (p q : ProbDistribution d) (n : ℕ) :
    MState.fidelity (MState.ofClassical (seqDist p n)) (MState.ofClassical (seqDist q n)) =
      (∑ x, Real.sqrt ((p x : ℝ) * (q x : ℝ))) ^ n :=
  fidelity_ofClassical_seqDist p q n

example {d : Type*} [Fintype d] [DecidableEq d] (p q : ProbDistribution d) :
    MState.fidelity (MState.ofClassical (seqDist p 0)) (MState.ofClassical (seqDist q 0)) = 1 := by
  rw [fidelity_ofClassical_seqDist, pow_zero]

example : MState.fidelity
    (MState.ofClassical (ProbDistribution.constant (0 : Fin 2)))
    (MState.ofClassical (ProbDistribution.constant (1 : Fin 2))) = 0 := by
  simp [fidelity_ofClassical_eq_bhattacharyya,
    ProbDistribution.constant_eq, apply_ite]

example {d : Type*} [Fintype d] [DecidableEq d] (Λ : POVM d d)
    (hΛ : ∀ r : ProbDistribution d, ∀ x,
      ((Λ.measure (MState.ofClassical r)) x : ℝ) = (r x : ℝ)) :
    Λ = finiteBasisReadout d :=
  calibrated_POVM_eq_finiteBasisReadout Λ hΛ

example {d : Type*} [Fintype d] [DecidableEq d] (p : ProbDistribution d) (x : d) :
    (((finiteBasisReadout d).measure (MState.ofClassical p)) x : ℝ) = (p x : ℝ) :=
  measure_finiteBasisReadout_ofClassical_apply p x

example {d : Type} [Fintype d] [DecidableEq d] :
    finiteBasisReadout d = Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout.basisPOVM d :=
  finiteBasisReadout_eq_basisPOVM d

example {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ σ : MState d) (τ ω : MState e) :
    MState.fidelity (ρ.prod τ) (σ.prod ω) = MState.fidelity ρ σ * MState.fidelity τ ω :=
  fidelity_prod ρ σ τ ω

example {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : MState d) (n : ℕ) :
    MState.fidelity (ρ.npow n) (σ.npow n) = MState.fidelity ρ σ ^ n :=
  fidelity_npow ρ σ n

example {d : Type*} [Fintype d] [DecidableEq d] (ρ σ : MState d) :
    MState.fidelity (ρ.npow 0) (σ.npow 0) = 1 := by
  rw [fidelity_npow, pow_zero]

example {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ : POVM X d) (ρ : MState d) (n : ℕ) :
    (copyPOVM Λ n).measure (ρ.npow n) = seqDist (Λ.measure ρ) n :=
  copyPOVM_measure Λ ρ n

example {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ : POVM X d) (ρ : MState d) (x : Fin 0 → X) :
    ((copyPOVM Λ 0).measure (ρ.npow 0) x : ℝ) = 1 := by
  rw [copyPOVM_measure]
  exact seqDist_zero_apply _ x

end Qatlib.Concepts.MixedFidelity.FidelityMetric.ConsumerChecks
