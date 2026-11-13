/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTauScaledIsometryStat
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyLemma10PairingQuan

/-!
# Scaled isometry of the signed τ maps

This module proves `SzegedyTauScaledIsometry` using the component pairing identities. For two
vectors in a common discriminant eigenspace with `0 < lam < 1`, either signed τ map multiplies
their inner product by `1 - lam^2`.

The result gives the precise scaling of the interior source correspondence in the bipartite walk
spectral analysis [Szegedy2004].

## Main statements

* `szegedyTauScaledIsometry`: inner-product scaling on each interior source eigenspace.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.WalkSearch.TauEmbedding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

/-- The state inner product preserves addition in its first argument. -/
private theorem inner_add_left {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (u + v) w = Qatlib.Foundations.PureStateMath.Inner u w + Qatlib.Foundations.PureStateMath.Inner v w := by
  simp [Qatlib.Foundations.PureStateMath.Inner, star_add, add_dotProduct]

/-- The state inner product preserves addition in its second argument. -/
private theorem inner_add_right {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner u (v + w) = Qatlib.Foundations.PureStateMath.Inner u v + Qatlib.Foundations.PureStateMath.Inner u w := by
  simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct_add]

/-- Reversing the state inner-product arguments complex-conjugates the result. -/
private theorem inner_reverse {K : Type} [Fintype K] (u v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner v u = (starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner u v) :=
  star_dotProduct (v := v) (w := u)

/-- Establish that either signed τ map multiplies inner products by `1 - lam^2` on a
discriminant eigenspace with `0 < lam < 1` [Szegedy2004]. -/
theorem szegedyTauScaledIsometry : SzegedyTauScaledIsometry := by
  intro H I J _ _ _ _ _ _ A B lam hA hB hl hh u v hu hv s
  obtain ⟨hpair, hcross⟩ := szegedyLemma10Pairing H I J A B lam hA hB hl hh u v hu hv
  have hreverse : Qatlib.Foundations.PureStateMath.Inner (B *ᵥ fun j => u (.inr j)) (A *ᵥ fun i => v (.inl i)) =
      (lam : ℂ) * Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => v (.inl i)) := by
    rw [inner_reverse]
    rw [(szegedyLemma10Pairing H I J A B lam hA hB hl hh v u hv hu).2]
    simp only [map_mul, Complex.conj_ofReal, ← inner_reverse]
  have hcoord : Qatlib.Foundations.PureStateMath.Inner u v =
      2 * Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => v (.inl i)) := by
    have hAi : Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => v (.inl i)) =
        Qatlib.Foundations.PureStateMath.Inner (fun i => u (.inl i)) (fun i => v (.inl i)) := by
      rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec,
        show Aᴴ * A = 1 from hA, Matrix.one_mulVec]
    have hBi : Qatlib.Foundations.PureStateMath.Inner (B *ᵥ fun j => u (.inr j)) (B *ᵥ fun j => v (.inr j)) =
        Qatlib.Foundations.PureStateMath.Inner (fun j => u (.inr j)) (fun j => v (.inr j)) := by
      rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec,
        show Bᴴ * B = 1 from hB, Matrix.one_mulVec]
    have hsplit : Qatlib.Foundations.PureStateMath.Inner u v =
        Qatlib.Foundations.PureStateMath.Inner (fun i => u (.inl i)) (fun i => v (.inl i)) +
        Qatlib.Foundations.PureStateMath.Inner (fun j => u (.inr j)) (fun j => v (.inr j)) := by
      simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Fintype.sum_sum_type]
    rw [hsplit, ← hAi, ← hBi, ← hpair]
    ring
  let c : ℂ := -(lam : ℂ) +
    (if s then Complex.I else -Complex.I) * (Real.sqrt (1 - lam^2) : ℂ)
  have hc : 1 + c * (lam : ℂ) + (starRingEnd ℂ) c * (lam : ℂ) +
      (starRingEnd ℂ) c * c = 2 * ((1 - lam^2 : ℝ) : ℂ) := by
    have hr := Real.sq_sqrt (by nlinarith : 0 ≤ 1 - lam^2)
    simp only [pow_two] at hr
    cases s <;> apply Complex.ext <;>
      simp [c, Complex.mul_re, Complex.mul_im, pow_two] <;>
      nlinarith only [hr]
  change Qatlib.Foundations.PureStateMath.Inner
    ((A *ᵥ fun i => u (.inl i)) + c • (B *ᵥ fun j => u (.inr j)))
    ((A *ᵥ fun i => v (.inl i)) + c • (B *ᵥ fun j => v (.inr j))) = _
  rw [inner_add_left, inner_add_right, inner_add_right,
    Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
    hcross, hreverse, ← hpair, hcoord]
  calc
    _ = (1 + c * (lam : ℂ) + (starRingEnd ℂ) c * (lam : ℂ) +
        (starRingEnd ℂ) c * c) *
        Qatlib.Foundations.PureStateMath.Inner (A *ᵥ fun i => u (.inl i)) (A *ᵥ fun i => v (.inl i)) := by ring
    _ = _ := by rw [hc]; ring

end Qatlib.Concepts.WalkSearch.TauEmbedding
