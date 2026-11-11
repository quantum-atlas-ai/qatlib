/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Bundled tensor-network representation and cost claims

This module defines `Clause18Claim` and `Clause19Claim`, packaging tensor-network
representation, invariance, evaluation-cost, and sampling-approximation properties as
propositions. The MPS representation setting follows [PerezGarciaEtAl2007], while the broader
MPS and PEPS setting is described in [VerstraeteMurgCirac2008].

## Main statements

* `Clause18Claim`: contraction invariance, bounded-bond network encodings, explicit small MPS
  examples, and contraction bounds and degenerate cases.
* `Clause19Claim`: counted MPS and PEPS evaluation bounds and existence of finite-bit
  approximations to normalized MPS sampling laws.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
* [Verstraete, Murg, and Cirac, 2008][VerstraeteMurgCirac2008]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

set_option autoImplicit false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix Qatlib.Concepts.TensorNetwork.GaugeInvariance

/-- The conjunction of tensor-network isomorphism and unitary gauge invariance, bounded-bond MPS
and PEPS encodings, explicit small MPS examples, and basic contraction bounds and degenerate
cases. -/
def Clause18Claim : Prop :=
  (∀ (N₁ N₂ : TensorNet) (iso : NetIso N₁ N₂) (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val)),
    netContract N₂ ext = netContract N₁
      (fun o => (ext ⟨iso.halfMap o.val, by
        rw [iso.partner_map, o.property, Option.map_none]⟩).cast
        (iso.dims_map o.val)))
  ∧ (∀ (N : TensorNet) (U : ∀ i : InternalEdge N,
        Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ),
      (∀ i, U i ∈ Matrix.unitaryGroup (Fin (N.dims i.val)) ℂ) →
      ∀ (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)),
        netContract (gaugeNet N U) ext = netContract N ext)
  ∧ (∀ (n d D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∃ (N : TensorNet) (enc : (Fin n → Fin d) → ∀ o : OpenLeg N, Fin (N.dims o.val)),
        netBondDimension N ≤ D ∧ ∀ x : Fin n → Fin d,
          netContract N (enc x) = @mpsAmplitude n d D hD A x)
  ∧ (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
        (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∃ (N : TensorNet) (enc : (Fin n → Fin d) → ∀ o : OpenLeg N, Fin (N.dims o.val)),
        netBondDimension N ≤ D ∧ ∀ x : Fin n → Fin d,
          netContract N (enc x) = @periodicMpsAmplitude n d D hn hD A x)
  ∧ (∀ (a b d D : ℕ) (hD : NeZero D)
        (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ),
      ∃ (N : TensorNet) (enc : (Fin a → Fin b → Fin d) → ∀ o : OpenLeg N, Fin (N.dims o.val)),
        netBondDimension N ≤ D ∧ ∀ x : Fin a → Fin b → Fin d,
          netContract N (enc x) = @pepsAmplitude a b d D hD T x)
  ∧ (∀ (n d : ℕ) (g : Fin n → Fin d → ℂ) (x : Fin n → Fin d),
      @mpsAmplitude n d 1 _ (fun i y => Matrix.of fun _ _ => g i y) x = ∏ i, g i (x i))
  ∧ (∀ x : Fin 2 → Fin 2,
      @mpsAmplitude 2 2 2 _
          (fun (i : Fin 2) (y : Fin 2) => Matrix.of fun a b =>
            if i = 0 then (if (y : ℕ) = (b : ℕ) then Complex.ofReal (1 / Real.sqrt 2) else 0)
            else if (y : ℕ) = (a : ℕ) then 1 else 0) x
        = if x 0 = x 1 then Complex.ofReal (1 / Real.sqrt 2) else 0)
  ∧ (∀ x : Fin 3 → Fin 2,
      @mpsAmplitude 3 2 2 _
          (fun (i : Fin 3) (y : Fin 2) => Matrix.of fun a b =>
            if (i : ℕ) = 0 then
              (if (a : ℕ) = 0 then
                (if (y : ℕ) = 0 then (if (b : ℕ) = 0 then 1 else 0) else 1)
              else 0)
            else if (i : ℕ) = 1 then
              (if (y : ℕ) = 0 ∧ a = b then 1 else 0)
            else
              (if (b : ℕ) = 0 then
                (if (y : ℕ) = 0 then (if (a : ℕ) = 1 then 1 else 0) else 1)
              else 0)) x
        = if (x 1 : ℕ) = 0 then
            (if (x 0 : ℕ) = 1 then (1 : ℂ) else 0) + (if (x 2 : ℕ) = 1 then (1 : ℂ) else 0)
          else 0)
  ∧ (∀ (N : TensorNet) (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)),
      ‖netContract N ext‖ ≤ ∏ v : Fin N.nv, tensorSumNorm N v)
  ∧ (∀ N : TensorNet, (∃ i : InternalEdge N, N.dims i.val = 0) →
      ∀ (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)), netContract N ext = 0)
  ∧ (∀ N : TensorNet, N.nv = 0 → N.nh = 0 →
      ∀ (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)), netContract N ext = 1)

/-- The conjunction of operation-count bounds for MPS and PEPS evaluators and the existence of
finite-bit samplers approximating normalized MPS laws in total variation. -/
def Clause19Claim : Prop :=
  (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D) {R : Type} [CommRing R]
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d),
    (@mpsEvalWithCount n d D R _ hn hD A x).2 ≤ mpsEvalOpCount n D)
  ∧ (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (@mpsInnerEvalWithCount n d D hn hD A B).2 ≤ mpsInnerOpCount n d D)
  ∧ (∀ (n d D : ℕ) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      (∑ x, Complex.normSq (@mpsAmplitude n d D hD A x) = 1) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (k : ℕ) (S : (Fin k → Bool) → (Fin n → Fin d)),
          tvDist (uniformPushForward S) (@mpsSampleLaw n d D hD A) ≤ ε
            ∧ k ≤ Nat.log2 (Fintype.card (Fin n → Fin d))
                + Nat.log2 (Nat.ceil (1 / ε)) + 2)
  ∧ (∀ (a b d D : ℕ) (hD : NeZero D)
      (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
      (x : Fin a → Fin b → Fin d),
    (@pepsStripEvalWithCount a b d D hD T x).2 ≤ pepsStripOpCount a b D)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
