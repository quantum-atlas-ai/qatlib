/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicOverlap.ArithLedger.TensorNetworkDefs

/-!
# Integer tensor-network contractions and sampling laws

This module relates integer tensor-network contractions to their dyadic complex decodings and
proves exact matrix product state contraction and inner-product formulas. It also bounds the
arithmetic ledgers and their associated bit-time expressions. The tensor-network and MPS
background is described in [Schollwock2011] and [PerezGarciaEtAl2007].

Further results identify normalized sampling probabilities, local-observable expressions, and
prefix-conditioned weights. They quantify the effect of relative error in a normalization
denominator and retain the multiplicity factor arising from prefix-fixed physical
configurations.

## Main statements

* `netContract_decode`: integer contraction agrees with dyadic decoding up to the global scale.
* `bitMpsContract_eq_bondSum`: explicit bond-sum contraction for nonempty chains.
* `bitInner_eq_math`: transfer contraction equals the amplitude inner product.
* `bitSampleProb_sum`: probabilities sum to one for nonzero norm.
* `bitSampleProbApprox_error`: normalization error controls probability error.
* `bitCondWeight_eq`: conditional weights equal scaled tail masses.
* `clause3_endpoint`: the combined guarantees in `clause2StatementNext`.

## References

* [Schollwock, 2011][Schollwock2011]
* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

set_option autoImplicit false

namespace Qatlib.Concepts.DyadicOverlap.ArithLedger.TensorNetwork

open Matrix
open scoped BigOperators
open Qatlib.Concepts.DyadicOverlap.ArithLedger

/-- The absolute value of an integer equals its natural absolute value cast back to the
integers. -/
theorem abs_eq_natAbs (z : ℤ) : |z| = (z.natAbs : ℤ) := by
  rcases Int.natAbs_eq z with h | h
  · calc |z| = |(z.natAbs : ℤ)| := congrArg abs h
        _ = (z.natAbs : ℤ) := abs_of_nonneg (Int.natCast_nonneg z.natAbs)
  · calc |z| = |-(z.natAbs : ℤ)| := congrArg abs h
        _ = (z.natAbs : ℤ) :=
          by rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg z.natAbs)]

/-- The real norm of an integer cast to the reals is its natural absolute value. -/
theorem norm_intCast_real (z : ℤ) : ‖((z : ℤ) : ℝ)‖ = (z.natAbs : ℝ) := by
  rw [Real.norm_eq_abs, ← Int.cast_abs, abs_eq_natAbs, Int.cast_natCast]

/-- The complex norm of an integer cast to the complexes is its natural absolute value. -/
theorem norm_intCast_complex (z : ℤ) : ‖((z : ℤ) : ℂ)‖ = (z.natAbs : ℝ) := by
  calc ‖((z : ℤ) : ℂ)‖ = ‖((z : ℤ) : ℝ)‖ := by
        have h : ((z : ℤ) : ℂ) = (((z : ℤ) : ℝ) : ℂ) := rfl
        rw [h, Complex.norm_real]
    _ = (z.natAbs : ℝ) := norm_intCast_real z

/-- Decoding dyadic tensor entries preserves the network's port-index assignment. -/
theorem decodeNet_portValue (N : TensorNet) (T : BitTensorNet N)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (j : Fin N.nh) :
    portValue (decodeNet N T) ext e j = portValue N ext e j := by
  cases hj : N.partner j with
  | none =>
    rw [portValue_of_partner_none (N := decodeNet N T) ext e j hj]
    rw [portValue_of_partner_none ext e j hj]
  | some k =>
    by_cases hlt : j < k
    · rw [portValue_of_partner_eq (N := decodeNet N T) ext e j k hj hlt]
      rw [portValue_of_partner_eq ext e j k hj hlt]
    · have hkj : k < j := (lt_or_gt_of_ne (N.no_self_loop j k hj)).resolve_left hlt
      rw [portValue_of_partner_eq_rev (N := decodeNet N T) ext e j k hj hkj
        (N.involution j k hj) (N.dims_match k j (N.involution j k hj))]
      rw [portValue_of_partner_eq_rev ext e j k hj hkj
        (N.involution j k hj) (N.dims_match k j (N.involution j k hj))]

/-- A decoded tensor entry is its integer numerator divided by `2 ^ T.precision`. -/
theorem decodeNet_tensor (N : TensorNet) (T : BitTensorNet N) (v : Fin N.nv)
    (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    (decodeNet N T).tensor v a = (T.num v a : ℂ) / (2 : ℂ) ^ T.precision := rfl

/-- Decoding tensor entries leaves the type of internal edges unchanged. -/
theorem decodeNet_index (N : TensorNet) (T : BitTensorNet N) :
    InternalEdge (decodeNet N T) = InternalEdge N := rfl

/-- The decoded network contraction is the integer contraction scaled by `2 ^ (T.precision *
N.nv)` in the denominator. -/
theorem netContract_decode (N : TensorNet) (T : BitTensorNet N)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) :
    netContract (decodeNet N T) ext
      = ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ * (netContractInt N T ext : ℂ) := by

  show (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ∏ v : Fin N.nv,
            (decodeNet N T).tensor v (fun h => portValue (decodeNet N T) ext e h.val))
      = ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ * (netContractInt N T ext : ℂ)

  have hport : ∀ (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (v : Fin N.nv)
      (h : {h : Fin N.nh // N.site h = v}),
      portValue (decodeNet N T) ext e h.val = portValue N ext e h.val := by
    intro e v h
    exact decodeNet_portValue N T ext e h.val

  have htensor : ∀ (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (v : Fin N.nv),
      (decodeNet N T).tensor v (fun h => portValue (decodeNet N T) ext e h.val)
        = (T.num v (fun h => portValue N ext e h.val) : ℂ) / (2 : ℂ) ^ T.precision := by
    intro e v
    rw [decodeNet_tensor]
    apply congrArg (fun z : ℂ => z / (2 : ℂ) ^ T.precision)
    apply congrArg (fun z : ℤ => (z : ℂ))
    apply congrArg (fun f : ∀ h : {h : Fin N.nh // N.site h = v},
        Fin (N.dims h.val) => T.num v f)
    funext h
    exact hport e v h

  have hsplit : ∀ (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (v : Fin N.nv),
      (T.num v (fun h => portValue N ext e h.val) : ℂ) / (2 : ℂ) ^ T.precision
        = (T.num v (fun h => portValue N ext e h.val) : ℂ)
          * ((2 : ℂ) ^ T.precision)⁻¹ := by
    intro e v
    rw [div_eq_mul_inv]

  have hprod : ∀ (e : ∀ i : InternalEdge N, Fin (N.dims i.val)),
      (∏ v : Fin N.nv,
          (decodeNet N T).tensor v (fun h => portValue (decodeNet N T) ext e h.val))
        = (∏ v : Fin N.nv,
            (T.num v (fun h => portValue N ext e h.val) : ℂ))
          * ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ := by
    intro e
    calc (∏ v : Fin N.nv,
          (decodeNet N T).tensor v (fun h => portValue (decodeNet N T) ext e h.val))
        = ∏ v : Fin N.nv,
            (T.num v (fun h => portValue N ext e h.val) : ℂ)
              * ((2 : ℂ) ^ T.precision)⁻¹ := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [htensor e v, hsplit e v]
      _ = (∏ v : Fin N.nv,
            (T.num v (fun h => portValue N ext e h.val) : ℂ))
          * ∏ _v : Fin N.nv, ((2 : ℂ) ^ T.precision)⁻¹ := Finset.prod_mul_distrib
      _ = (∏ v : Fin N.nv,
            (T.num v (fun h => portValue N ext e h.val) : ℂ))
          * ((2 : ℂ) ^ T.precision)⁻¹ ^ (N.nv : ℕ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (∏ v : Fin N.nv,
            (T.num v (fun h => portValue N ext e h.val) : ℂ))
          * ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ := by
        simp only [inv_pow, pow_mul]

  have hsum : (netContractInt N T ext : ℂ)
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ∏ v : Fin N.nv, (T.num v (fun h => portValue N ext e h.val) : ℂ) := by
    rw [netContractInt, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Int.cast_prod]

  calc (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ∏ v : Fin N.nv,
            (decodeNet N T).tensor v (fun h => portValue (decodeNet N T) ext e h.val))
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          (∏ v : Fin N.nv, (T.num v (fun h => portValue N ext e h.val) : ℂ))
            * ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ := by
          apply Finset.sum_congr rfl
          intro e he
          exact hprod e
      _ = ((2 : ℂ) ^ (T.precision * N.nv))⁻¹
            * ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
              ∏ v : Fin N.nv, (T.num v (fun h => portValue N ext e h.val) : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          exact mul_comm _ _
      _ = ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ * (netContractInt N T ext : ℂ) := by
          rw [← hsum]

/-- The sum norm of a decoded site tensor is its integer sum norm divided by `2 ^ T.precision`. -/
theorem tensorSumNorm_decodeNet (N : TensorNet) (T : BitTensorNet N) (v : Fin N.nv) :
    tensorSumNorm (decodeNet N T) v
      = ((2 : ℝ) ^ T.precision)⁻¹ * bitTensorSumNorm N T v := by
  have hitem : ∀ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      ‖((T.num v a : ℤ) : ℂ) / (2 : ℂ) ^ T.precision‖
        = ‖((T.num v a : ℤ) : ℝ)‖ * ((2 : ℝ) ^ T.precision)⁻¹ := by
    intro a
    calc ‖((T.num v a : ℤ) : ℂ) / (2 : ℂ) ^ T.precision‖
        = ‖((T.num v a : ℤ) : ℂ)‖ / ‖(2 : ℂ) ^ T.precision‖ := Complex.norm_div _ _
      _ = ((T.num v a).natAbs : ℝ) / ((2 : ℝ) ^ T.precision) := by
          rw [norm_intCast_complex, Complex.norm_pow, Complex.norm_two]
      _ = ‖((T.num v a : ℤ) : ℝ)‖ * ((2 : ℝ) ^ T.precision)⁻¹ := by
          rw [norm_intCast_real, div_eq_mul_inv]
  show (∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
        ‖(decodeNet N T).tensor v a‖)
      = ((2 : ℝ) ^ T.precision)⁻¹ * bitTensorSumNorm N T v
  calc (∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
        ‖(decodeNet N T).tensor v a‖)
      = ∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
          ‖((T.num v a : ℤ) : ℂ) / (2 : ℂ) ^ T.precision‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [decodeNet_tensor]
    _ = ∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
          ‖((T.num v a : ℤ) : ℝ)‖ * ((2 : ℝ) ^ T.precision)⁻¹ := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hitem a
    _ = ((2 : ℝ) ^ T.precision)⁻¹
          * ∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
            ‖((T.num v a : ℤ) : ℝ)‖ := by
        rw [← Finset.sum_mul, mul_comm]
    _ = ((2 : ℝ) ^ T.precision)⁻¹ * bitTensorSumNorm N T v := rfl

/-- The decoded contraction norm is bounded by the product of integer site sum norms divided by
`2 ^ (T.precision * N.nv)`. -/
theorem netContract_decode_norm (N : TensorNet) (T : BitTensorNet N)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) :
    ‖netContract (decodeNet N T) ext‖
      ≤ ((2 : ℝ) ^ (T.precision * N.nv))⁻¹
        * ∏ v : Fin N.nv, bitTensorSumNorm N T v := by
  have hbase : ‖netContract (decodeNet N T) ext‖
      ≤ ∏ v : Fin N.nv, tensorSumNorm (decodeNet N T) v :=
    netContract_norm_bound (decodeNet N T) ext
  calc ‖netContract (decodeNet N T) ext‖
      ≤ ∏ v : Fin N.nv, tensorSumNorm (decodeNet N T) v := hbase
    _ = ∏ v : Fin N.nv, ((2 : ℝ) ^ T.precision)⁻¹ * bitTensorSumNorm N T v := by
        rw [Finset.prod_congr rfl (fun v _ => tensorSumNorm_decodeNet N T v)]
    _ = ((2 : ℝ) ^ T.precision)⁻¹ ^ (N.nv : ℕ)
        * ∏ v : Fin N.nv, bitTensorSumNorm N T v := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
    _ = ((2 : ℝ) ^ (T.precision * N.nv))⁻¹
        * ∏ v : Fin N.nv, bitTensorSumNorm N T v := by
        simp only [inv_pow, pow_mul]

/-- A network with an internal edge of dimension zero has integer contraction zero for every
external assignment. -/
theorem netContractInt_zeroDim (N : TensorNet) (T : BitTensorNet N)
    (hd : ∃ i : InternalEdge N, N.dims i.val = 0) :
    ∀ ext : ∀ o : OpenLeg N, Fin (N.dims o.val), netContractInt N T ext = 0 := by
  obtain ⟨i, hi⟩ := hd
  have hempty : IsEmpty (∀ k : InternalEdge N, Fin (N.dims k.val)) := by
    refine ⟨fun f => ?_⟩
    have h0 : Fin (N.dims i.val) → False := by rw [hi]; exact Fin.elim0
    exact h0 (f i)
  intro ext
  have huv : (Finset.univ : Finset (∀ i : InternalEdge N, Fin (N.dims i.val))) = ∅ :=
    @Finset.univ_eq_empty _ _ hempty
  show (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
      (∏ v : Fin N.nv, T.num v (fun h => portValue N ext e h.val)) : ℤ) = 0
  rw [huv]
  exact Finset.sum_empty

/-- A network with no vertices and no half-edges has integer contraction one. -/
theorem netContractInt_empty (N : TensorNet) (T : BitTensorNet N)
    (hnv : N.nv = 0) (hnh : N.nh = 0) :
    ∀ ext : ∀ o : OpenLeg N, Fin (N.dims o.val), netContractInt N T ext = 1 := by
  have hnv' : IsEmpty (Fin N.nv) := by rw [hnv]; infer_instance
  have hnh' : IsEmpty (Fin N.nh) := by rw [hnh]; infer_instance
  have hIE : IsEmpty (InternalEdge N) := ⟨fun i => hnh'.false i.val⟩
  have huniq : Unique (∀ i : InternalEdge N, Fin (N.dims i.val)) :=
    ⟨⟨fun i => hIE.elim i⟩, fun a => funext fun i => hIE.elim i⟩
  intro ext
  have hconst : ∀ e : (∀ i : InternalEdge N, Fin (N.dims i.val)),
      (∏ v : Fin N.nv, T.num v (fun h => portValue N ext e h.val)) = 1 := by
    intro e
    have huv : (Finset.univ : Finset (Fin N.nv)) = ∅ := @Finset.univ_eq_empty _ _ hnv'
    rw [huv]
    exact Finset.prod_empty
  show (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
      (∏ v : Fin N.nv, T.num v (fun h => portValue N ext e h.val)) : ℤ) = 1
  calc (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
      (∏ v : Fin N.nv, T.num v (fun h => portValue N ext e h.val)) : ℤ)
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val), (1 : ℤ) :=
        Finset.sum_congr rfl fun e _ => hconst e
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_unique]
        simp

/-- The amplitude of a length-zero integer matrix product state is one. -/
theorem bitMpsAmplitude_zero_length {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) (hn : n = 0) : bitMpsAmplitude A x = 1 := by
  subst hn
  have key : ∀ b : Fin (0 - 1) → Fin D,
      b = (fun _ => (0 : Fin D) : Fin (0 - 1) → Fin D) := by
    intro b
    funext i
    exact Fin.elim0 i
  rw [bitMpsAmplitude,
    Finset.sum_eq_single ((fun _ => (0 : Fin D)) : Fin (0 - 1) → Fin D)]
  · exact Fin.prod_univ_zero _
  · intro b _ hb
    exact absurd (key b) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A bond-dimension-one matrix product state's amplitude is the product of its scalar site
entries. -/
theorem bitMpsAmplitude_product {n d : ℕ} (g : Fin n → Fin d → ℤ) (x : Fin n → Fin d) :
    @bitMpsAmplitude n d 1 inferInstance
        ((fun (i : Fin n) (y : Fin d) => Matrix.of (fun _ _ => g i y))
          : Fin n → Fin d → Matrix (Fin 1) (Fin 1) ℤ) x
      = ∏ i, g i (x i) := by
  have key : ∀ b : Fin (n - 1) → Fin 1,
      b = (fun _ => (0 : Fin 1) : Fin (n - 1) → Fin 1) :=
    fun b => funext fun i => Subsingleton.elim _ _
  rw [bitMpsAmplitude,
    Finset.sum_eq_single ((fun _ => (0 : Fin 1)) : Fin (n - 1) → Fin 1)]
  · rfl
  · intro b _ hb
    exact absurd (key b) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The designated three-site binary example has the stated amplitude formula in terms of its
three physical indices. -/
theorem bitMpsAmplitude_short_chain (x : Fin 3 → Fin 2) :
    bitMpsAmplitude bitShortChainTensors x
      = if (x 1 : ℕ) = 0 then
          (if (x 0 : ℕ) = 1 then (1 : ℤ) else 0) + (if (x 2 : ℕ) = 1 then (1 : ℤ) else 0)
        else 0 := by
  have hbody : ∀ α : Fin (3 - 1) → Fin 2,
      (∏ i : Fin 3, bitShortChainTensors i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = (fun p : Fin 2 × Fin 2 =>
            bitShortChainTensors 0 (x 0) 0 p.1
          * bitShortChainTensors 1 (x 1) p.1 p.2
          * bitShortChainTensors 2 (x 2) p.2 0) (equivBond22 α) := by
    intro α
    rw [Fin.prod_univ_three]
    show _ * _ * _ = _
    congr 2
  rw [bitMpsAmplitude, Fintype.sum_equiv equivBond22 _
    (fun p : Fin 2 × Fin 2 =>
      bitShortChainTensors 0 (x 0) 0 p.1 * bitShortChainTensors 1 (x 1) p.1 p.2
        * bitShortChainTensors 2 (x 2) p.2 0) hbody,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two]
  have hx0 : (x 0 : ℕ) = 0 ∨ (x 0 : ℕ) = 1 := by have := (x 0).isLt; omega
  have hx1 : (x 1 : ℕ) = 0 ∨ (x 1 : ℕ) = 1 := by have := (x 1).isLt; omega
  have hx2 : (x 2 : ℕ) = 0 ∨ (x 2 : ℕ) = 1 := by have := (x 2).isLt; omega
  rcases hx0 with v0 | v0 <;> rcases hx1 with v1 | v1 <;> rcases hx2 with v2 | v2 <;>
    simp [v0, v1, v2, Matrix.of_apply, bitShortChainTensors]

/-- The absolute value of each integer tensor entry is at most the network-wide maximum absolute
entry. -/
theorem num_le_bitTensorMaxAbs (N : TensorNet) (T : BitTensorNet N) (v : Fin N.nv)
    (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    (T.num v a).natAbs ≤ bitTensorMaxAbs N T := by
  have h1 : (T.num v a).natAbs
      ≤ (Finset.univ.sup fun a : (∀ h : {h : Fin N.nh // N.site h = v},
          Fin (N.dims h.val)) => (T.num v a).natAbs) :=
    Finset.le_sup (f := fun a : (∀ h : {h : Fin N.nh // N.site h = v},
      Fin (N.dims h.val)) => (T.num v a).natAbs) (Finset.mem_univ a)
  have h2 : (Finset.univ.sup fun a : (∀ h : {h : Fin N.nh // N.site h = v},
      Fin (N.dims h.val)) => (T.num v a).natAbs)
      ≤ (Finset.univ.sup fun v : Fin N.nv =>
        (Finset.univ.sup fun a : (∀ h : {h : Fin N.nh // N.site h = v},
          Fin (N.dims h.val)) => (T.num v a).natAbs)) :=
    Finset.le_sup (f := fun v : Fin N.nv =>
      (Finset.univ.sup fun a : (∀ h : {h : Fin N.nh // N.site h = v},
        Fin (N.dims h.val)) => (T.num v a).natAbs)) (Finset.mem_univ v)
  exact h1.trans h2

/-- If every integer tensor entry has absolute value at most `2 ^ w`, each site sum norm is
bounded by its number of entries times `2 ^ w`. -/
theorem bitTensorSumNorm_le (N : TensorNet) (T : BitTensorNet N) (w : ℕ)
    (hw : ∀ (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      (T.num v a).natAbs ≤ 2 ^ w)
    (v : Fin N.nv) :
    bitTensorSumNorm N T v
      ≤ (Fintype.card (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val))) * 2 ^ w := by
  have hitem : ∀ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      ‖((T.num v a : ℤ) : ℝ)‖ ≤ (2 : ℝ) ^ w := by
    intro a
    rw [norm_intCast_real]
    exact_mod_cast hw v a
  show (∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      ‖((T.num v a : ℤ) : ℝ)‖)
    ≤ (Fintype.card (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val))) * 2 ^ w
  have hsum : (∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      ‖((T.num v a : ℤ) : ℝ)‖)
      ≤ ∑ _a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
        ((2 : ℝ) ^ w) :=
    Finset.sum_le_sum fun a ha => hitem a
  rw [Finset.sum_const, Finset.card_univ] at hsum
  simpa [nsmul_eq_mul] using! hsum

/-- The tensor-network decoding, contraction bounds, degenerate cases, and explicit MPS examples
collected in `clause1StatementNext` hold. -/
theorem clause1_endpoint : clause1StatementNext := by
  refine ⟨Qatlib.Concepts.MpsAdaptation.MpsTransfer.g1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun N T ext => netContract_decode N T ext
  · exact fun N T ext => netContract_decode_norm N T ext
  · exact fun N T hd => netContractInt_zeroDim N T hd
  · exact fun N T hnv hnh => netContractInt_empty N T hnv hnh
  · exact fun A x hn => bitMpsAmplitude_zero_length A x hn
  · exact fun g x => bitMpsAmplitude_product g x
  · exact fun x => bitMpsAmplitude_short_chain x
  · exact fun N T v a => num_le_bitTensorMaxAbs N T v a
  · exact fun N T w hw v => bitTensorSumNorm_le N T w hw v

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- A finite sum over length-`m + 1` configurations splits into a sum over the head and a sum
over the remaining coordinates. -/
theorem sum_split_head {m : ℕ} {X : Type*} [Fintype X] {M : Type*} [AddCommMonoid M]
    (g : X → (Fin m → X) → M) :
    (∑ β : Fin (m + 1) → X, g (β 0) (fun j => β ⟨(j : ℕ) + 1, by omega⟩))
      = ∑ t : X, ∑ α : Fin m → X, g t α := by
  have h := Fintype.sum_equiv (finConsEquiv (X := X))
    (fun β : Fin (m + 1) → X => g (β 0) (fun j => β ⟨(j : ℕ) + 1, by omega⟩))
    (fun p : X × (Fin m → X) => g p.1 p.2) (fun β => rfl)
  rw [h]
  exact Fintype.sum_prod_type (fun p => g p.1 p.2)

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The first key of a chain assignment is its specified left boundary. -/
theorem chainKeys_left {D : ℕ} {k : ℕ} (b c : Fin D) (γ : Fin (k - 1) → Fin D) :
    chainKeys k b c γ 0 = b := by
  simp [chainKeys]

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- For a positive-length chain, the final key is its specified right boundary. -/
theorem chainKeys_right {D : ℕ} {k : ℕ} (b c : Fin D) (γ : Fin (k - 1) → Fin D)
    (h : (0 : ℕ) < k) : chainKeys k b c γ ⟨k, by omega⟩ = c := by
  have hk0 : (k : ℕ) ≠ 0 := by omega
  simp only [chainKeys]
  split
  · omega
  · split
    · rfl
    · simp_all

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- An interior chain key is the corresponding entry of the internal assignment. -/
theorem chainKeys_inner {D : ℕ} {k : ℕ} (b c : Fin D) (γ : Fin (k - 1) → Fin D)
    {j : Fin (k + 1)} (h0 : (j : ℕ) ≠ 0) (hk : (j : ℕ) ≠ k) :
    chainKeys k b c γ j = γ ⟨(j : ℕ) - 1, by omega⟩ := by
  simp only [chainKeys, dif_neg h0, dif_neg hk]

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- Removing the initial key of a chain gives the shorter chain with left boundary equal to the
first internal key. -/
theorem chainKeys_tail {D : ℕ} {k : ℕ} (b c : Fin D) (γ : Fin k → Fin D)
    (hk : (1 : ℕ) ≤ k) :
    ∀ (j : Fin (k + 1)),
      chainKeys k (γ ⟨0, by omega⟩) c (fun i => γ ⟨(i : ℕ) + 1, by omega⟩) j
        = chainKeys (k + 1) b c γ ⟨(j : ℕ) + 1, by omega⟩ := by
  intro j
  have hk0 : (k : ℕ) ≠ 0 := by omega
  by_cases hj0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hj]
    simp [chainKeys, hk0]
  · by_cases hj1 : (j : ℕ) = k
    · have hj : j = ⟨k, by omega⟩ := Fin.ext (by omega)
      rw [hj]
      simp [chainKeys, hk0]
    · have hjn : (j : ℕ) + 1 ≠ 0 := by omega
      have hjn2 : (j : ℕ) + 1 ≠ k + 1 := by omega
      have hL : chainKeys k (γ ⟨0, by omega⟩) c (fun i => γ ⟨(i : ℕ) + 1, by omega⟩) j
          = γ ⟨(j : ℕ) - 1 + 1, by omega⟩ := by
        simp only [chainKeys, dif_neg hj0, dif_neg hj1]
      have hR : chainKeys (k + 1) b c γ ⟨(j : ℕ) + 1, by omega⟩
          = γ ⟨(j : ℕ) + 1 - 1, by omega⟩ := by
        simp only [chainKeys, dif_neg hjn, dif_neg hjn2]
      rw [hL, hR]
      congr 1
      apply Fin.ext
      simp only [Fin.mk.injEq]
      omega

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The weight of a nonempty matrix chain factors into its first matrix entry and the weight of
the remaining chain. -/
theorem chainSum_cons {D : ℕ} (M : Fin D → Fin D → ℤ) (rest : BitSiteList D)
    (β : Fin (rest.length + 2) → Fin D) :
    chainSum (M :: rest) β
      = M (β 0) (β 1) * chainSum rest (fun j => β ⟨(j : ℕ) + 1, by omega⟩) := by
  have hprod :
      (∏ p : Fin (rest.length + 1), ((M :: rest))[p]
          (β ⟨p.val, by omega⟩) (β ⟨p.val + 1, by omega⟩))
        = ((M :: rest))[0] (β 0) (β 1)
          * (∏ p : Fin rest.length, rest[p]
              (β ⟨p.val + 1, by omega⟩) (β ⟨p.val + 2, by omega⟩)) :=
    Fin.prod_univ_succ _
  unfold chainSum
  exact hprod.trans (by congr 1)

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The total chain contraction equals the value obtained by the backward-vector recurrence. -/
theorem chainTotal_eq_chainBackVec {D : ℕ} :
    ∀ (Ms : BitSiteList D) (b c : Fin D), chainTotal Ms b c = chainBackVec Ms c b := by
  intro Ms
  induction Ms with
  | nil =>
    intro b c
    rfl
  | cons M Ms ih =>
    intro b c
    cases Ms with
    | nil =>

      have hsum : (∑ γ : Fin 0 → Fin D, chainSum [M] (chainKeys 1 b c γ)) = M b c := by
        have h1 : ∀ γ : Fin 0 → Fin D,
            chainSum [M] (chainKeys 1 b c γ) = M b c := by
          intro γ
          simp [chainSum, chainKeys]
        rw [Finset.sum_congr rfl (fun γ _ => h1 γ)]
        exact sum_fin_zero_pi (M b c)
      have hback : chainBackVec [M] c b = M b c := by
        simp only [chainBackVec]
        rw [Finset.sum_eq_single c (fun k _ hk => by
          have hkc : k ≠ c := fun h => hk (by rw [h])
          simp [hkc]) (by simp)]
        simp
      simp only [chainTotal, List.length_nil]
      rw [hsum, hback]
    | cons M' rest =>

      have hsplit : chainTotal (M :: M' :: rest) b c
          = ∑ t : Fin D, M b t * chainTotal (M' :: rest) t c := by
        have hct : chainTotal (M :: M' :: rest) b c
            = ∑ γ : Fin (rest.length + 1) → Fin D,
                chainSum (M :: M' :: rest) (chainKeys (rest.length + 2) b c γ) := by
          rfl
        have hct' : ∀ t : Fin D,
            chainTotal (M' :: rest) t c
              = ∑ α : Fin rest.length → Fin D,
                  chainSum (M' :: rest) (chainKeys (rest.length + 1) t c α) := by
          intro t
          rfl

        have hpeel : ∀ γ : Fin (rest.length + 1) → Fin D,
            chainSum (M :: M' :: rest) (chainKeys (rest.length + 2) b c γ)
              = M b (γ 0)
                * chainSum (M' :: rest) (chainKeys (rest.length + 1) (γ 0) c
                    (fun i => γ ⟨(i : ℕ) + 1, by omega⟩)) := by
          intro γ
          have hcons := chainSum_cons (M : Fin D → Fin D → ℤ) (M' :: rest)
            (chainKeys (rest.length + 2) b c γ)
          rw [hcons]
          have hβ0 : chainKeys (rest.length + 2) b c γ 0 = b := by
            simp [chainKeys]
          have hβ1 : chainKeys (rest.length + 2) b c γ 1 = γ 0 := by
            have hk0 : (1 : ℕ) ≠ 0 := by omega
            have hk1 : (1 : ℕ) ≠ rest.length + 2 := by omega
            simp only [chainKeys]
            rfl
          rw [hβ0, hβ1]
          have hshift : ∀ j : Fin (rest.length + 2),
              chainKeys (rest.length + 2) b c γ ⟨(j : ℕ) + 1, by omega⟩
                = chainKeys (rest.length + 1) (γ 0) c
                    (fun i => γ ⟨(i : ℕ) + 1, by omega⟩) j := by
            intro j
            exact (chainKeys_tail (k := rest.length + 1) b c γ (by omega) j).symm
          congr 1
          apply congrArg (fun ψ => chainSum (M' :: rest) ψ)
          funext j
          exact hshift j
        rw [hct]
        rw [Finset.sum_congr rfl (fun γ _ => hpeel γ)]
        have hsplit' := sum_split_head (M := ℤ)
          (fun t : Fin D => fun α : Fin rest.length → Fin D =>
            M b t * chainSum (M' :: rest) (chainKeys (rest.length + 1) t c α))
        calc (∑ γ : Fin (rest.length + 1) → Fin D,
                M b (γ 0) * chainSum (M' :: rest)
                  (chainKeys (rest.length + 1) (γ 0) c (fun i => γ ⟨(i : ℕ) + 1, by omega⟩)))
            = ∑ t : Fin D, ∑ α : Fin rest.length → Fin D,
                M b t * chainSum (M' :: rest) (chainKeys (rest.length + 1) t c α) := hsplit'
          _ = ∑ t : Fin D, M b t * chainTotal (M' :: rest) t c := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [hct' t, Finset.mul_sum]
      rw [hsplit]
      have ih' := ih
      simp only [chainBackVec]
      rw [Finset.sum_congr rfl (fun k _ => by rw [ih' k c])]
      rfl

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The chain key at a site equals the matrix product state's left bond index. -/
theorem chainKeys_mpsLeft {D : ℕ} {n : ℕ} [NeZero D] (γ : Fin (n - 1) → Fin D) (p : Fin n) :
    chainKeys n 0 0 γ ⟨(p : ℕ), by omega⟩ = mpsLeftIdx γ p := by
  by_cases hp0 : (p : ℕ) = 0
  · have hp : p = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hp]
    simp [chainKeys, mpsLeftIdx]
  · have hne : (p : ℕ) ≠ n := by omega
    have hlt : (p : ℕ) - 1 < n - 1 := by omega
    simp only [chainKeys, dif_neg hp0, dif_neg hne]
    simp only [mpsLeftIdx, if_neg hp0, dif_pos hlt]

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The chain key following a site equals the matrix product state's right bond index. -/
theorem chainKeys_mpsRight {D : ℕ} {n : ℕ} [NeZero D] (γ : Fin (n - 1) → Fin D) (p : Fin n) :
    chainKeys n 0 0 γ ⟨(p : ℕ) + 1, by omega⟩ = mpsRightIdx γ p := by
  have hne0 : ((p : ℕ) + 1 : ℕ) ≠ 0 := by omega
  by_cases hlt : (p : ℕ) < n - 1
  · have hne : ((p : ℕ) + 1 : ℕ) ≠ n := by omega
    simp only [chainKeys, dif_neg hne0, dif_neg hne]
    simp only [mpsRightIdx, dif_pos hlt]
    congr 1
  · have hpn : ((p : ℕ) + 1 : ℕ) = n := by omega
    simp only [chainKeys, dif_neg hne0, dif_pos hpn]
    simp only [mpsRightIdx, dif_neg hlt]

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- For a nonempty chain with zero boundary indices, the total contraction is the sum over
internal bonds of the products of site entries. -/
theorem chainTotal_zero_eq_bondSum {D : ℕ} [NeZero D] (Ms : BitSiteList D) (hne : Ms ≠ []) :
    chainTotal Ms 0 0
      = ∑ γ : Fin (Ms.length - 1) → Fin D,
          ∏ p : Fin Ms.length, Ms[p] (mpsLeftIdx γ p) (mpsRightIdx γ p) := by
  cases Ms with
  | nil => exact absurd rfl hne
  | cons M rest =>
    have hct : chainTotal (M :: rest) 0 0
        = ∑ γ : Fin rest.length → Fin D,
            chainSum (M :: rest) (chainKeys (rest.length + 1) 0 0 γ) := by
      rfl
    rw [hct]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    unfold chainSum
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [chainKeys_mpsLeft (n := rest.length + 1) γ p,
      chainKeys_mpsRight (n := rest.length + 1) γ p]

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The vector component of the counted backward contraction equals the uncounted backward
vector. -/
theorem chainBackCount_vec {D : ℕ} (Ms : BitSiteList D) (c : Fin D) :
    (chainBackCount Ms c).vec = chainBackVec Ms c := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    simp only [chainBackCount, chainBackVec]
    rw [ih]

open Qatlib.Concepts.DyadicOverlap.ArithLedger in

/-- The integer MPS contraction equals the total contraction of its selected site matrices with
zero boundary indices. -/
theorem bitMpsContract_eq_chainTotal {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) :
    bitMpsContract A x = chainTotal (bitMpsSiteList A x) 0 0 := by
  have hvec : (chainBackCount (bitMpsSiteList A x) 0).vec
      = chainBackVec (bitMpsSiteList A x) 0 :=
    chainBackCount_vec _ _
  have hback : chainBackVec (bitMpsSiteList A x) 0 0
      = chainTotal (bitMpsSiteList A x) 0 0 :=
    (chainTotal_eq_chainBackVec _ _ _).symm
  show (chainBackCount (bitMpsSiteList A x) 0).vec 0 = chainTotal (bitMpsSiteList A x) 0 0
  rw [hvec, hback]

/-- For a nonempty MPS, its integer contraction is the explicit sum over internal bond
assignments of products of site entries. -/
theorem bitMpsContract_eq_bondSum {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) (hn : n ≠ 0) :
    bitMpsContract A x
      = ∑ γ : Fin ((bitMpsSiteList A x).length - 1) → Fin D,
          ∏ p : Fin ((bitMpsSiteList A x).length),
            (bitMpsSiteList A x)[p] (mpsLeftIdx γ p) (mpsRightIdx γ p) := by
  have hne : (bitMpsSiteList A x) ≠ [] := by
    intro hh
    have hlen := congrArg List.length hh
    simp only [bitMpsSiteList, List.length_ofFn, List.length_nil] at hlen
    exact hn hlen
  have hbridge := chainTotal_zero_eq_bondSum (bitMpsSiteList A x) hne
  have hback : chainBackVec (bitMpsSiteList A x) 0 0
      = chainTotal (bitMpsSiteList A x) 0 0 :=
    (chainTotal_eq_chainBackVec _ _ _).symm
  have hvec : (chainBackCount (bitMpsSiteList A x) 0).vec
      = chainBackVec (bitMpsSiteList A x) 0 :=
    chainBackCount_vec _ _
  show (chainBackCount (bitMpsSiteList A x) 0).vec 0 = _
  rw [hvec, hback, hbridge]

/-- The backward-chain ledger uses at most `Ms.length * (D * D)` multiplications and additions
and no subtractions. -/
theorem chainBackCount_ledger {D : ℕ} (Ms : BitSiteList D) (c : Fin D) :
    (chainBackCount Ms c).ledger.muls ≤ Ms.length * (D * D)
    ∧ (chainBackCount Ms c).ledger.adds ≤ Ms.length * (D * D)
    ∧ (chainBackCount Ms c).ledger.subs = 0 := by
  induction Ms with
  | nil => simp [chainBackCount]
  | cons M Ms ih =>
    obtain ⟨hm, ha, hs⟩ := ih
    simp only [chainBackCount]
    refine ⟨?_, ?_, ?_⟩
    · calc (chainBackCount Ms c).ledger.muls + D * D
          ≤ Ms.length * (D * D) + D * D := Nat.add_le_add_right hm _
        _ = (Ms.length + 1) * (D * D) := by rw [Nat.succ_mul]
    · calc (chainBackCount Ms c).ledger.adds + D * D
          ≤ Ms.length * (D * D) + D * D := Nat.add_le_add_right ha _
        _ = (Ms.length + 1) * (D * D) := by rw [Nat.succ_mul]
    · exact hs

/-- The MPS contraction ledger bounds multiplications and additions by `bitContractOpBound n D`
and records no subtractions. -/
theorem bitMpsContractWithCount_ledger {n d D : ℕ} [NeZero D]
    (A : BitMps n d D) (x : Fin n → Fin d) :
    (bitMpsContractWithCount A x).2.muls ≤ bitContractOpBound n D
    ∧ (bitMpsContractWithCount A x).2.adds ≤ bitContractOpBound n D
    ∧ (bitMpsContractWithCount A x).2.subs = 0 := by
  have h := chainBackCount_ledger
    (List.ofFn fun i : Fin n => fun l r => A i (x i) l r) 0
  simpa [bitMpsContractWithCount, bitContractOpBound] using! h

/-- The ledger-based bit-time expression for MPS contraction is bounded by twice the operation
bound times the ring-operation bit cost at the specified width. -/
theorem bitMpsContract_bitTime {n d D w : ℕ} [NeZero D]
    (A : BitMps n d D) (x : Fin n → Fin d) :
    bitTimeOf (bitContractWidthBound n d D w) (bitMpsContractWithCount A x).2
      ≤ 2 * bitContractOpBound n D
        * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitContractWidthBound n d D w) := by
  have h := bitMpsContractWithCount_ledger A x
  simp only [bitTimeOf]
  have hsum : (bitMpsContractWithCount A x).2.muls
      + (bitMpsContractWithCount A x).2.adds
      + (bitMpsContractWithCount A x).2.subs
      ≤ 2 * bitContractOpBound n D := by omega
  exact Nat.mul_le_mul hsum (Nat.le_refl _)

/-- The designated MPS contraction workspace size is exactly the bond dimension `D`. -/
theorem bitMpsContract_workspace (D : ℕ) :
    bitContractSpace D = D := rfl

/-- Scaled integer floor rounding has nonnegative error strictly below `2 ^ p`. -/
theorem bitRoundScaled_error (p : ℕ) (z : ℤ) :
    0 ≤ z - bitRoundScaled p z ∧ z - bitRoundScaled p z < (2 : ℤ) ^ p := by
  have hpos : 0 < (2 : ℤ) ^ p := by positivity
  have hne : (2 : ℤ) ^ p ≠ 0 := by omega
  have hdecomp : (2 : ℤ) ^ p * (z / (2 : ℤ) ^ p) + z % (2 : ℤ) ^ p = z :=
    Int.mul_ediv_add_emod z _
  have hmod : 0 ≤ z % (2 : ℤ) ^ p := Int.emod_nonneg z hne
  have hmod' : z % (2 : ℤ) ^ p < (2 : ℤ) ^ p := Int.emod_lt_of_pos (a := z) hpos
  have hkey : z - (z / (2 : ℤ) ^ p) * ((2 : ℤ) ^ p) = z % (2 : ℤ) ^ p := by
    have h := hdecomp
    rw [show (z / (2 : ℤ) ^ p) * ((2 : ℤ) ^ p) = (2 : ℤ) ^ p * (z / (2 : ℤ) ^ p) by ring]
    linarith
  constructor
  · rw [bitRoundScaled, bitRoundInt, hkey]
    exact hmod
  · rw [bitRoundScaled, bitRoundInt, hkey]
    exact hmod'

/-- For positive `D`, the specified PEPS treewidth cost is at most `bitPepsTreewidthBound a b
D`. -/
theorem bitPepsTreewidthCost_le (a b D : ℕ) (_hD : 0 < D) :
    bitPepsTreewidthCost a b D ≤ bitPepsTreewidthBound a b D := by
  have h1 : D ≤ 2 ^ Nat.clog 2 D := Nat.le_pow_clog (by decide : 1 < 2) D
  have h2 : D ^ a ≤ (2 ^ Nat.clog 2 D) ^ a := Nat.pow_le_pow_left h1 a
  have h4 : ((2 ^ Nat.clog 2 D) ^ a) ^ 3 = 2 ^ (3 * a * Nat.clog 2 D) := by
    calc ((2 ^ Nat.clog 2 D) ^ a) ^ 3 = (2 ^ Nat.clog 2 D) ^ (a * 3) := by rw [← pow_mul]
      _ = 2 ^ (Nat.clog 2 D * (a * 3)) := by rw [← pow_mul]
      _ = 2 ^ (3 * a * Nat.clog 2 D) := by congr 1; ring
  have h3 : (D ^ a) ^ 3 ≤ 2 ^ (3 * a * Nat.clog 2 D) := by
    calc (D ^ a) ^ 3 ≤ ((2 ^ Nat.clog 2 D) ^ a) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = 2 ^ (3 * a * Nat.clog 2 D) := h4
  unfold bitPepsTreewidthCost bitPepsTreewidthBound
  calc b * (D ^ a) ^ 3 * (a + 2) ≤ b * (2 ^ (3 * a * Nat.clog 2 D)) * (a + 2) := by
        gcongr
      _ = 2 ^ (3 * a * Nat.clog 2 D) * (b * (a + 2)) := by ring
      _ ≤ 2 ^ (3 * a * Nat.clog 2 D) * ((a + 2) * b + 1) := by
        gcongr
        calc b * (a + 2) = (a + 2) * b := Nat.mul_comm _ _
          _ ≤ (a + 2) * b + 1 := Nat.le_add_right _ _

/-- Left MPS bond indices are preserved by the stated casts between equal chain lengths. -/
theorem mpsLeftIdx_cast {m m' D : ℕ} [NeZero D] (hc : m' - 1 = m - 1) (hs : m' = m)
    (α : Fin (m - 1) → Fin D) (p : Fin m') :
    mpsLeftIdx (fun j => α (Fin.cast hc j)) p
      = mpsLeftIdx (fun j => α j) (Fin.cast hs p) := by
  by_cases hp0 : (p : ℕ) = 0
  · have hp : p = ⟨0, by omega⟩ := Fin.ext (by omega)
    simp [mpsLeftIdx, hp, Fin.cast]
  · have hlt : (p : ℕ) - 1 < m' - 1 := by omega
    have hlt2 : (p : ℕ) - 1 < m - 1 := by omega
    simp [mpsLeftIdx, hlt, hlt2, Fin.cast]

/-- Right MPS bond indices are preserved by the stated casts between equal chain lengths. -/
theorem mpsRightIdx_cast {m m' D : ℕ} [NeZero D] (hc : m' - 1 = m - 1) (hs : m' = m)
    (α : Fin (m - 1) → Fin D) (p : Fin m') :
    mpsRightIdx (fun j => α (Fin.cast hc j)) p
      = mpsRightIdx (fun j => α j) (Fin.cast hs p) := by
  by_cases hlt : (p : ℕ) < m' - 1
  · have hlt2 : (p : ℕ) < m - 1 := by omega
    simp [mpsRightIdx, hlt, hlt2, Fin.cast]
  · have hlt2 : ¬ (p : ℕ) < m - 1 := by omega
    simp [mpsRightIdx, hlt, hlt2, Fin.cast]

/-- Left mixed-bond indices are preserved by the stated casts between equal chain lengths. -/
theorem mixedLeftIdx_cast {m m' DA DB : ℕ} [NeZero DA] [NeZero DB]
    (hc : m' - 1 = m - 1) (hs : m' = m)
    (γ : Fin (m - 1) → MixedKey DA DB) (p : Fin m') :
    mixedLeftIdx (fun j => γ (Fin.cast hc j)) p
      = mixedLeftIdx γ (Fin.cast hs p) := by
  simp only [mixedLeftIdx]
  exact Prod.ext (mpsLeftIdx_cast hc hs (fun j => (γ j).1) p)
    (mpsLeftIdx_cast hc hs (fun j => (γ j).2) p)

/-- Right mixed-bond indices are preserved by the stated casts between equal chain lengths. -/
theorem mixedRightIdx_cast {m m' DA DB : ℕ} [NeZero DA] [NeZero DB]
    (hc : m' - 1 = m - 1) (hs : m' = m)
    (γ : Fin (m - 1) → MixedKey DA DB) (p : Fin m') :
    mixedRightIdx (fun j => γ (Fin.cast hc j)) p
      = mixedRightIdx γ (Fin.cast hs p) := by
  simp only [mixedRightIdx]
  exact Prod.ext (mpsRightIdx_cast hc hs (fun j => (γ j).1) p)
    (mpsRightIdx_cast hc hs (fun j => (γ j).2) p)

/-- Decoding an encoded mixed bond key returns the original pair. -/
theorem mixedKeyEnc_dec {DA DB : ℕ} (x : MixedKey DA DB) :
    mixedKeyDec DA DB (mixedKeyEnc DA DB x) = x :=
  (mixedKeyEnc DA DB).left_inv x

/-- Encoding a decoded mixed bond index returns the original index. -/
theorem mixedKeyDec_enc {DA DB : ℕ} (x : Fin (DA * DB)) :
    mixedKeyEnc DA DB (mixedKeyDec DA DB x) = x :=
  (mixedKeyEnc DA DB).right_inv x

/-- Encoding the pair of zero bond indices gives zero. -/
theorem mixedKeyEnc_zero {DA DB : ℕ} [NeZero DA] [NeZero DB] :
    mixedKeyEnc DA DB (0, 0) = 0 := by
  show finProdFinEquiv (0, 0) = 0
  simp [finProdFinEquiv]

/-- Decoding zero gives the pair of zero bond indices. -/
theorem mixedKeyDec_zero {DA DB : ℕ} [NeZero DA] [NeZero DB] :
    mixedKeyDec DA DB 0 = (0, 0) := by
  rw [← mixedKeyEnc_zero, mixedKeyEnc_dec]

/-- Decoding an MPS left bond index gives the left mixed-bond index of the decoded assignment. -/
theorem dec_mpsLeftIdx {m DA DB : ℕ} [NeZero DA] [NeZero DB]
    (γ : Fin (m - 1) → Fin (DA * DB)) (p : Fin m) :
    mixedKeyDec DA DB (mpsLeftIdx γ p)
      = mixedLeftIdx (fun j => mixedKeyDec DA DB (γ j)) p := by
  by_cases hp0 : (p : ℕ) = 0
  · have hp : p = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [hp]
    simp [mpsLeftIdx, mixedLeftIdx, mixedKeyDec_zero]
  · have hlt : (p : ℕ) - 1 < m - 1 := by omega
    simp [mpsLeftIdx, mixedLeftIdx, hp0, hlt]

/-- Decoding an MPS right bond index gives the right mixed-bond index of the decoded assignment. -/
theorem dec_mpsRightIdx {m DA DB : ℕ} [NeZero DA] [NeZero DB]
    (γ : Fin (m - 1) → Fin (DA * DB)) (p : Fin m) :
    mixedKeyDec DA DB (mpsRightIdx γ p)
      = mixedRightIdx (fun j => mixedKeyDec DA DB (γ j)) p := by
  by_cases hlt : (p : ℕ) < m - 1
  · simp [mpsRightIdx, mixedRightIdx, hlt]
  · simp [mpsRightIdx, mixedRightIdx, hlt, mixedKeyDec_zero]

/-- The transfer-matrix list used for an MPS inner product has length `n`. -/
theorem bitInnerList_length {n d DA DB : ℕ} (A : BitMps n d DA) (B : BitMps n d DB) :
    (bitInnerList A B).length = n := by
  simp [bitInnerList, List.length_ofFn]

/-- Each entry of the inner-product transfer list equals the corresponding site transfer entry
with decoded mixed-bond indices. -/
theorem bitInnerList_get {n d DA DB : ℕ} (A : BitMps n d DA) (B : BitMps n d DB)
    (i : Fin (bitInnerList A B).length) (p q : Fin (DA * DB)) :
    (bitInnerList A B).get i p q
      = bitInnerSite A B ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by rw [bitInnerList_length])⟩
          (mixedKeyDec DA DB p) (mixedKeyDec DA DB q) := by
  unfold bitInnerList
  rw [List.get_ofFn]
  congr 1

/-- The equivalence transporting finite indices along the equality `n = m`. -/
def finCastEquiv {n m : ℕ} (hs : n = m) : Fin m ≃ Fin n where
  toFun i := Fin.cast hs.symm i
  invFun j := Fin.cast hs j
  left_inv := by intro i; apply Fin.ext; rfl
  right_inv := by intro j; apply Fin.ext; rfl

/-- The equivalence between flattened mixed-bond assignments and pair-valued assignments,
transporting the internal-chain length along `hc`. -/
def mixedChainEquiv {n L : ℕ} (hc : n - 1 = L - 1) {DA DB : ℕ} :
    (Fin (L - 1) → Fin (DA * DB)) ≃ (Fin (n - 1) → MixedKey DA DB) where
  toFun γ j := mixedKeyDec DA DB (γ (Fin.cast hc j))
  invFun γm j := mixedKeyEnc DA DB (γm (Fin.cast hc.symm j))
  left_inv := by
    intro γ
    funext j
    show mixedKeyEnc DA DB (mixedKeyDec DA DB (γ (Fin.cast hc (Fin.cast hc.symm j)))) = γ j
    rw [mixedKeyDec_enc]
    have hj : (Fin.cast hc (Fin.cast hc.symm j) : Fin (L - 1)) = j := by
      apply Fin.ext
      rfl
    rw [hj]
  right_inv := by
    intro γm
    funext j
    show mixedKeyDec DA DB (mixedKeyEnc DA DB (γm (Fin.cast hc.symm (Fin.cast hc j)))) = γm j
    rw [mixedKeyEnc_dec]
    have hj : (Fin.cast hc.symm (Fin.cast hc j) : Fin (n - 1)) = j := by
      apply Fin.ext
      rfl
    rw [hj]

/-- For a nonempty chain, the computed MPS inner product equals its mixed-chain sum. -/
theorem bitInner_eq_chain {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) (hn : n ≠ 0) :
    bitInner A B = bitInnerChainSum A B := by
  have hprog : bitInner A B = chainTotal (bitInnerList A B) 0 0 := by
    have hvec : (chainBackCount (bitInnerList A B) 0).vec = chainBackVec (bitInnerList A B) 0 :=
      chainBackCount_vec _ _
    have hback : chainBackVec (bitInnerList A B) 0 0 = chainTotal (bitInnerList A B) 0 0 :=
      (chainTotal_eq_chainBackVec _ _ _).symm
    show (chainBackCount (bitInnerList A B) 0).vec 0 = chainTotal (bitInnerList A B) 0 0
    rw [hvec, hback]
  have hne : bitInnerList A B ≠ [] := by
    intro hh
    have hlen := congrArg List.length hh
    rw [bitInnerList_length] at hlen
    simp at hlen
    exact hn hlen
  have hbond := chainTotal_zero_eq_bondSum (bitInnerList A B) hne
  rw [hprog, hbond]
  show (∑ γ' : Fin ((bitInnerList A B).length - 1) → Fin (DA * DB),
      ∏ p : Fin ((bitInnerList A B).length),
        (bitInnerList A B).get p (mpsLeftIdx γ' p) (mpsRightIdx γ' p))
    = ∑ γ : Fin (n - 1) → MixedKey DA DB,
        ∏ i : Fin n, bitInnerSite A B i (mixedLeftIdx γ i) (mixedRightIdx γ i)
  have hL : (bitInnerList A B).length = n := bitInnerList_length A B
  have hc : n - 1 = (bitInnerList A B).length - 1 := by omega
  have hs : n = (bitInnerList A B).length := hL.symm
  have hitem : ∀ (γ' : Fin ((bitInnerList A B).length - 1) → Fin (DA * DB)),
      (∏ p : Fin ((bitInnerList A B).length),
        (bitInnerList A B).get p (mpsLeftIdx γ' p) (mpsRightIdx γ' p))
        = ∏ i : Fin n, bitInnerSite A B i
            (mixedLeftIdx ((mixedChainEquiv hc) γ') i)
            (mixedRightIdx ((mixedChainEquiv hc) γ') i) := by
    intro γ'
    have hprod : (∏ p : Fin ((bitInnerList A B).length),
          (bitInnerList A B).get p (mpsLeftIdx γ' p) (mpsRightIdx γ' p))
        = ∏ i : Fin n, (bitInnerList A B).get ((finCastEquiv hs).symm i)
            (mpsLeftIdx γ' ((finCastEquiv hs).symm i))
            (mpsRightIdx γ' ((finCastEquiv hs).symm i)) :=
      Fintype.prod_equiv (finCastEquiv hs) _ _
        (fun p => by rw [Equiv.symm_apply_apply])
    rw [hprod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [bitInnerList_get, dec_mpsLeftIdx, dec_mpsRightIdx]
    have hL1 : mixedLeftIdx (fun j => mixedKeyDec DA DB (γ' j)) ((finCastEquiv hs).symm i)
        = mixedLeftIdx ((mixedChainEquiv hc) γ') i :=
      (mixedLeftIdx_cast hc hs (fun j => mixedKeyDec DA DB (γ' j)) i).symm
    have hL2 : mixedRightIdx (fun j => mixedKeyDec DA DB (γ' j)) ((finCastEquiv hs).symm i)
        = mixedRightIdx ((mixedChainEquiv hc) γ') i :=
      (mixedRightIdx_cast hc hs (fun j => mixedKeyDec DA DB (γ' j)) i).symm
    rw [hL1, hL2]
    rfl
  exact Fintype.sum_equiv (mixedChainEquiv hc)
    (fun γ' => ∏ p : Fin ((bitInnerList A B).length),
      (bitInnerList A B).get p (mpsLeftIdx γ' p) (mpsRightIdx γ' p))
    (fun γm => ∏ i : Fin n,
      bitInnerSite A B i (mixedLeftIdx γm i) (mixedRightIdx γm i))
    hitem

/-- The equivalence between a function into a product and a pair of component functions. -/
def piProdEquiv {m : ℕ} {X Y : Type} :
    (Fin m → X × Y) ≃ ((Fin m → X) × (Fin m → Y)) where
  toFun f := (fun j => (f j).1, fun j => (f j).2)
  invFun p j := (p.1 j, p.2 j)
  left_inv := by
    intro f
    funext j
    rfl
  right_inv := by
    intro p
    apply Prod.ext <;> funext j <;> rfl

/-- The mixed-chain sum equals the sum over physical configurations of the products of the two
MPS amplitudes. -/
theorem bitInnerChainSum_eq_math {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) :
    bitInnerChainSum A B = ∑ x : Fin n → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x) := by
  have hAmpA : ∀ x : Fin n → Fin d, bitMpsAmplitude A x
      = ∑ α : Fin (n - 1) → Fin DA, ∏ j : Fin n,
          A j (x j) (mpsLeftIdx α j) (mpsRightIdx α j) := by
    intro x; rfl
  have hAmpB : ∀ x : Fin n → Fin d, bitMpsAmplitude B x
      = ∑ β : Fin (n - 1) → Fin DB, ∏ j : Fin n,
          B j (x j) (mpsLeftIdx β j) (mpsRightIdx β j) := by
    intro x; rfl
  have hdistrib : ∀ (x : Fin n → Fin d) (α : Fin (n - 1) → Fin DA)
      (β : Fin (n - 1) → Fin DB),
      (∑ α' : Fin (n - 1) → Fin DA, ∏ j : Fin n,
          A j (x j) (mpsLeftIdx α' j) (mpsRightIdx α' j))
        * (∑ β' : Fin (n - 1) → Fin DB, ∏ j : Fin n,
            B j (x j) (mpsLeftIdx β' j) (mpsRightIdx β' j))
        = ∑ α' : Fin (n - 1) → Fin DA, ∑ β' : Fin (n - 1) → Fin DB,
            ∏ j : Fin n, bitInnerPair A B x α' β' j := by
    intro x α β
    calc (∑ α' : Fin (n - 1) → Fin DA, ∏ j : Fin n,
            A j (x j) (mpsLeftIdx α' j) (mpsRightIdx α' j))
          * (∑ β' : Fin (n - 1) → Fin DB, ∏ j : Fin n,
            B j (x j) (mpsLeftIdx β' j) (mpsRightIdx β' j))
        = ∑ α' : Fin (n - 1) → Fin DA,
            (∏ j : Fin n, A j (x j) (mpsLeftIdx α' j) (mpsRightIdx α' j))
              * (∑ β' : Fin (n - 1) → Fin DB, ∏ j : Fin n,
                  B j (x j) (mpsLeftIdx β' j) (mpsRightIdx β' j)) :=
          Finset.sum_mul (Finset.univ : Finset (Fin (n - 1) → Fin DA))
            (fun α' => ∏ j : Fin n, A j (x j) (mpsLeftIdx α' j) (mpsRightIdx α' j))
            (∑ β' : Fin (n - 1) → Fin DB, ∏ j : Fin n,
              B j (x j) (mpsLeftIdx β' j) (mpsRightIdx β' j))
        _ = ∑ α' : Fin (n - 1) → Fin DA, ∑ β' : Fin (n - 1) → Fin DB,
            (∏ j : Fin n, A j (x j) (mpsLeftIdx α' j) (mpsRightIdx α' j))
              * (∏ j : Fin n, B j (x j) (mpsLeftIdx β' j) (mpsRightIdx β' j)) := by
          refine Finset.sum_congr rfl (fun α' _ => ?_)
          rw [Finset.mul_sum Finset.univ]
        _ = ∑ α' : Fin (n - 1) → Fin DA, ∑ β' : Fin (n - 1) → Fin DB,
            ∏ j : Fin n, bitInnerPair A B x α' β' j := by
          refine Finset.sum_congr rfl (fun α' _ => ?_)
          refine Finset.sum_congr rfl (fun β' _ => ?_)
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun j _ => ?_)
          rfl
  have hR : (∑ x : Fin n → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x))
      = ∑ x : Fin n → Fin d, ∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
          ∏ i : Fin n, bitInnerPair A B x α β i := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hAmpA, hAmpB]
    exact hdistrib x (fun _ => ⟨0, NeZero.pos DA⟩) (fun _ => ⟨0, NeZero.pos DB⟩)
  have hsite : ∀ (α : Fin (n - 1) → Fin DA) (β : Fin (n - 1) → Fin DB) (i : Fin n),
      (∑ s : Fin d, bitInnerSiteProd A B α β i s)
        = bitInnerSite A B i
            (mixedLeftIdx (fun j => (α j, β j)) i)
            (mixedRightIdx (fun j => (α j, β j)) i) := by
    intro α β i
    rfl
  have hS : (∑ x : Fin n → Fin d, ∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
        ∏ i : Fin n, bitInnerPair A B x α β i)
      = ∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
        ∏ i : Fin n, (∑ s : Fin d, bitInnerSiteProd A B α β i s) := by
    have h1 : (∑ x : Fin n → Fin d, ∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
          ∏ i : Fin n, bitInnerPair A B x α β i)
        = ∑ α : Fin (n - 1) → Fin DA, ∑ x : Fin n → Fin d, ∑ β : Fin (n - 1) → Fin DB,
          ∏ i : Fin n, bitInnerPair A B x α β i := Finset.sum_comm
    have h2 : (∑ α : Fin (n - 1) → Fin DA, ∑ x : Fin n → Fin d, ∑ β : Fin (n - 1) → Fin DB,
          ∏ i : Fin n, bitInnerPair A B x α β i)
        = ∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
          ∑ x : Fin n → Fin d, ∏ i : Fin n, bitInnerPair A B x α β i := by
      refine Finset.sum_congr rfl (fun α _ => ?_)
      exact Finset.sum_comm
    rw [h1, h2]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rfl
  rw [hR, hS]
  have hmix : (∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
        ∏ i : Fin n, (∑ s : Fin d, bitInnerSiteProd A B α β i s))
      = ∑ γ : Fin (n - 1) → MixedKey DA DB,
        ∏ i : Fin n, bitInnerSite A B i (mixedLeftIdx γ i) (mixedRightIdx γ i) := by
    have hcomb : (∑ α : Fin (n - 1) → Fin DA, ∑ β : Fin (n - 1) → Fin DB,
          ∏ i : Fin n, (∑ s : Fin d, bitInnerSiteProd A B α β i s))
        = ∑ p : (Fin (n - 1) → Fin DA) × (Fin (n - 1) → Fin DB),
          ∏ i : Fin n, (∑ s : Fin d, bitInnerSiteProd A B p.1 p.2 i s) :=
      (Fintype.sum_prod_type (fun p : (Fin (n - 1) → Fin DA) × (Fin (n - 1) → Fin DB) =>
        ∏ i : Fin n, (∑ s : Fin d, bitInnerSiteProd A B p.1 p.2 i s))).symm
    rw [hcomb]
    refine Fintype.sum_equiv (piProdEquiv (m := n - 1)).symm
      (fun p : (Fin (n - 1) → Fin DA) × (Fin (n - 1) → Fin DB) =>
        ∏ i : Fin n, (∑ s : Fin d, bitInnerSiteProd A B p.1 p.2 i s))
      (fun γ : Fin (n - 1) → MixedKey DA DB =>
        ∏ i : Fin n, bitInnerSite A B i (mixedLeftIdx γ i) (mixedRightIdx γ i))
      (fun p => ?_)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hsite]
    rfl
  rw [hmix]
  rfl

/-- The inner-product transfer list is empty when the chain length is zero. -/
theorem bitInnerList_nil {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) (hn : n = 0) : bitInnerList A B = [] := by
  subst hn
  have hlen : (bitInnerList A B).length = 0 := by
    simp [bitInnerList]
  exact List.eq_nil_of_length_eq_zero hlen

/-- The computed MPS inner product is one when the chain length is zero. -/
theorem bitInner_nil {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) (hn : n = 0) : bitInner A B = 1 := by
  subst hn
  have hlist : bitInnerList A B = [] := bitInnerList_nil A B rfl
  show (chainBackCount (bitInnerList A B) 0).vec 0 = 1
  rw [hlist]
  rfl

/-- The computed inner product agrees with the mathematical amplitude pairing in the length-zero
case. -/
theorem bitInner_eq_math_zero {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) (hn : n = 0) :
    bitInner A B = bitInnerMath A B := by
  subst hn
  have h1 : bitInner A B = 1 := bitInner_nil A B rfl
  have h2 : ∀ x : Fin 0 → Fin d, bitMpsAmplitude A x = 1 :=
    fun x => bitMpsAmplitude_zero_length A x rfl
  have h3 : ∀ x : Fin 0 → Fin d, bitMpsAmplitude B x = 1 :=
    fun x => bitMpsAmplitude_zero_length B x rfl
  show bitInner A B = (∑ x : Fin 0 → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x))
  have hsum : (∑ x : Fin 0 → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x)) = 1 := by
    have h : ∀ x : Fin 0 → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x) = 1 := by
      intro x
      rw [h2 x, h3 x]
      norm_num
    calc (∑ x : Fin 0 → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x))
        = ∑ _ : Fin 0 → Fin d, 1 := Finset.sum_congr rfl (fun x _ => h x)
      _ = 1 := sum_fin_zero_pi (1 : ℤ)
  rw [h1, hsum]

/-- The MPS inner-product ledger bounds multiplications and additions by `bitInnerOpBound n d DA
DB` and records no subtractions. -/
theorem bitInnerWithCount_ledger {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) :
    (bitInnerWithCount A B).2.muls ≤ bitInnerOpBound n d DA DB
    ∧ (bitInnerWithCount A B).2.adds ≤ bitInnerOpBound n d DA DB
    ∧ (bitInnerWithCount A B).2.subs = 0 := by
  have hfold := chainBackCount_ledger (bitInnerList A B) 0
  have h1 : (chainBackCount (bitInnerList A B) 0).ledger.muls ≤ n * (DA * DB) ^ 2 := by
    simpa only [bitInnerList_length, Nat.pow_two] using! hfold.1
  have h2 : (chainBackCount (bitInnerList A B) 0).ledger.adds ≤ n * (DA * DB) ^ 2 := by
    simpa only [bitInnerList_length, Nat.pow_two] using! hfold.2.1
  have hm : (bitInnerWithCount A B).2.muls
      = (chainBackCount (bitInnerList A B) 0).ledger.muls + n * ((DA * DB) ^ 2 * d) := rfl
  have ha : (bitInnerWithCount A B).2.adds
      = (chainBackCount (bitInnerList A B) 0).ledger.adds + n * ((DA * DB) ^ 2 * d) := rfl
  have hs : (bitInnerWithCount A B).2.subs
      = (chainBackCount (bitInnerList A B) 0).ledger.subs := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    unfold bitInnerOpBound
    calc (chainBackCount (bitInnerList A B) 0).ledger.muls + n * ((DA * DB) ^ 2 * d)
        ≤ n * (DA * DB) ^ 2 + n * ((DA * DB) ^ 2 * d) := Nat.add_le_add_right h1 _
      _ = n * (DA * DB) ^ 2 * (d + 1) := by ring
  · rw [ha]
    unfold bitInnerOpBound
    calc (chainBackCount (bitInnerList A B) 0).ledger.adds + n * ((DA * DB) ^ 2 * d)
        ≤ n * (DA * DB) ^ 2 + n * ((DA * DB) ^ 2 * d) := Nat.add_le_add_right h2 _
      _ = n * (DA * DB) ^ 2 * (d + 1) := by ring
  · rw [hs]
    exact hfold.2.2

/-- The ledger-based inner-product bit-time expression is bounded by twice the operation bound
times the ring-operation bit cost at the specified width. -/
theorem bitInner_bitTime {n d DA DB w : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) :
    bitTimeOf (bitInnerWidthBound n d DA DB w) (bitInnerWithCount A B).2
      ≤ 2 * bitInnerOpBound n d DA DB
        * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitInnerWidthBound n d DA DB w) := by
  have h := bitInnerWithCount_ledger A B
  simp only [bitTimeOf]
  have hsum : (bitInnerWithCount A B).2.muls
      + (bitInnerWithCount A B).2.adds
      + (bitInnerWithCount A B).2.subs
      ≤ 2 * bitInnerOpBound n d DA DB := by
    have h1 := h.1
    have h2 := h.2.1
    have h3 := h.2.2
    omega
  exact Nat.mul_le_mul hsum (Nat.le_refl _)

/-- The designated MPS inner-product workspace size is the product of the two bond dimensions. -/
theorem bitInner_workspace (DA DB : ℕ) : bitInnerSpace DA DB = DA * DB := rfl

/-- The computed integer MPS inner product equals its mathematical amplitude pairing. -/
theorem bitInner_eq_math {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) :
    bitInner A B = bitInnerMath A B := by
  by_cases hn : n = 0
  · exact bitInner_eq_math_zero A B hn
  · rw [bitInner_eq_chain A B hn, bitInnerChainSum_eq_math A B]
    rfl

/-- The computed squared norm equals the total sampling mass. -/
theorem bitNormSq_eq_mass {n d D : ℕ} [NeZero D] (A : BitMps n d D) :
    bitNormSq A = bitSampleMass A := by
  have h := bitInner_eq_math A A
  unfold bitNormSq bitSampleMass
  rw [h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact (pow_two (bitMpsAmplitude A x)).symm

/-- The computed sampling probability equals the normalized squared-amplitude law. -/
theorem bitSampleProb_eq_law {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) : bitSampleProb A x = bitSampleLaw A x := by
  have hden : (bitNormSq A : ℚ) = ∑ y : Fin n → Fin d, (bitMpsAmplitude A y) ^ 2 := by
    rw [bitNormSq_eq_mass]
    norm_cast
  unfold bitSampleProb bitSampleLaw
  rw [hden]

/-- If the computed squared norm is nonzero, the sampling probabilities sum to one. -/
theorem bitSampleProb_sum {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (hA : bitNormSq A ≠ 0) : (∑ x : Fin n → Fin d, bitSampleProb A x) = 1 := by
  have hsum : (∑ x : Fin n → Fin d, (bitMpsAmplitude A x : ℚ) ^ 2) = (bitNormSq A : ℚ) := by
    rw [bitNormSq_eq_mass]
    norm_cast
  have hN : (bitNormSq A : ℚ) ≠ 0 := by exact_mod_cast hA
  unfold bitSampleProb
  rw [← Finset.sum_div (Finset.univ : Finset (Fin n → Fin d))
    (fun x => (bitMpsAmplitude A x : ℚ) ^ 2) (bitNormSq A : ℚ)]
  rw [hsum]
  exact div_self hN

/-- If the computed squared norm is nonzero, every sampling probability is nonnegative. -/
theorem bitSampleProb_nonneg {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (hA : bitNormSq A ≠ 0) (x : Fin n → Fin d) : 0 ≤ bitSampleProb A x := by
  have hN : (0 : ℚ) < (bitNormSq A : ℚ) := by
    have h1 : (0 : ℚ) ≤ (bitNormSq A : ℚ) := by
      rw [bitNormSq_eq_mass]
      unfold bitSampleMass
      rw [Int.cast_sum]
      exact Finset.sum_nonneg fun x _ => by positivity
    have h2 : (bitNormSq A : ℚ) ≠ 0 := by
      intro hz
      exact hA (by exact_mod_cast hz)
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  unfold bitSampleProb
  have hsq : (0 : ℚ) ≤ (bitMpsAmplitude A x : ℚ) ^ 2 := by positivity
  exact div_nonneg hsq hN.le

/-- At the selected site, the observable-modified MPS tensor is the physical-index contraction
of `O` with the original tensor. -/
theorem bitObsMps_site_z {n d D : ℕ} (A : BitMps n d D) (z : Fin n) (O : BitLocalObs d)
    (s : Fin d) (a b : Fin D) :
    (bitObsMps A z O) z s a b = ∑ y : Fin d, O s y * A z y a b := by
  simp [bitObsMps]

/-- The observable-modified MPS agrees with the original tensors at every other site. -/
theorem bitObsMps_site_ne {n d D : ℕ} (A : BitMps n d D) (z : Fin n) (O : BitLocalObs d)
    (i : Fin n) (h : i ≠ z) (s : Fin d) (a b : Fin D) :
    (bitObsMps A z O) i s a b = A i s a b := by
  simp [bitObsMps, h]

/-- The amplitude after applying a local observable is the sum of original amplitudes with the
selected physical coordinate replaced, weighted by the observable entries. -/
theorem bitObsMps_amplitude {n d D : ℕ} [NeZero D] (A : BitMps n d D) (z : Fin n)
    (O : BitLocalObs d) (x : Fin n → Fin d) :
    bitMpsAmplitude (bitObsMps A z O) x
      = ∑ y : Fin d, O (x z) y * bitMpsAmplitude A (Function.update x z y) := by

  have hsplit : ∀ (α : Fin (n - 1) → Fin D),
      (∏ i : Fin n, (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = (∑ y : Fin d, O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z))
          * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
              A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)) := by
    intro α
    have hz : (bitObsMps A z O) z (x z) (mpsLeftIdx α z) (mpsRightIdx α z)
        = ∑ y : Fin d, O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z) :=
      bitObsMps_site_z A z O (x z) (mpsLeftIdx α z) (mpsRightIdx α z)
    have hnotz : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase z,
        (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)
          = A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i) := by
      intro i hi
      have hne : i ≠ z := (Finset.mem_erase.mp hi).1
      exact bitObsMps_site_ne A z O i hne (x i) (mpsLeftIdx α i) (mpsRightIdx α i)
    have hprod : (∏ i : Fin n, (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = (bitObsMps A z O) z (x z) (mpsLeftIdx α z) (mpsRightIdx α z)
          * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
              (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)) :=
      (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun i => (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        (Finset.mem_univ z)).symm
    rw [hprod, hz]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => hnotz i hi)

  have hamp : ∀ (y : Fin d),
      (∑ α : Fin (n - 1) → Fin D,
          (A z y (mpsLeftIdx α z) (mpsRightIdx α z))
            * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)))
        = bitMpsAmplitude A (Function.update x z y) := by
    intro y
    have hz : ∀ (α : Fin (n - 1) → Fin D),
        A z ((Function.update x z y) z) (mpsLeftIdx α z) (mpsRightIdx α z)
          = A z y (mpsLeftIdx α z) (mpsRightIdx α z) := by
      intro α
      simp
    have hnotz : ∀ (α : Fin (n - 1) → Fin D) (i : Fin n)
        (hi : i ∈ (Finset.univ : Finset (Fin n)).erase z),
        A i ((Function.update x z y) i) (mpsLeftIdx α i) (mpsRightIdx α i)
          = A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i) := by
      intro α i hi
      have hne : i ≠ z := (Finset.mem_erase.mp hi).1
      rw [Function.update_of_ne hne y x]
    have hprod : ∀ (α : Fin (n - 1) → Fin D),
        (∏ i : Fin n, A i ((Function.update x z y) i) (mpsLeftIdx α i) (mpsRightIdx α i))
          = A z ((Function.update x z y) z) (mpsLeftIdx α z) (mpsRightIdx α z)
            * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                A i ((Function.update x z y) i) (mpsLeftIdx α i) (mpsRightIdx α i)) :=
      fun α => (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun i => A i ((Function.update x z y) i) (mpsLeftIdx α i) (mpsRightIdx α i))
        (Finset.mem_univ z)).symm
    have hexp2 : bitMpsAmplitude A (Function.update x z y)
        = ∑ α : Fin (n - 1) → Fin D,
            ∏ i : Fin n, A i ((Function.update x z y) i) (mpsLeftIdx α i) (mpsRightIdx α i) := rfl
    rw [hexp2]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hprod α, hz α]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => (hnotz α i hi).symm)

  have hmain :
      (∑ α : Fin (n - 1) → Fin D,
          ∏ i : Fin n, (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = ∑ y : Fin d, O (x z) y * bitMpsAmplitude A (Function.update x z y) := by
    calc (∑ α : Fin (n - 1) → Fin D,
          ∏ i : Fin n, (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = ∑ α : Fin (n - 1) → Fin D,
            ((∑ y : Fin d, O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z))
              * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                  A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))) := by
            exact Finset.sum_congr rfl (fun α _ => hsplit α)
      _ = ∑ α : Fin (n - 1) → Fin D, ∑ y : Fin d,
            (O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z))
              * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                  A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)) := by
            refine Finset.sum_congr rfl (fun α _ => ?_)
            exact (Finset.sum_mul (Finset.univ : Finset (Fin d))
              (fun y => O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z))
              (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)))
      _ = ∑ y : Fin d, ∑ α : Fin (n - 1) → Fin D,
            (O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z))
              * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                  A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)) := Finset.sum_comm
      _ = ∑ y : Fin d, O (x z) y * (∑ α : Fin (n - 1) → Fin D,
            (A z y (mpsLeftIdx α z) (mpsRightIdx α z))
              * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                  A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))) := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            calc (∑ α : Fin (n - 1) → Fin D,
                (O (x z) y * A z y (mpsLeftIdx α z) (mpsRightIdx α z))
                  * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                      A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)))
                = ∑ α : Fin (n - 1) → Fin D, (O (x z) y
                    * ((A z y (mpsLeftIdx α z) (mpsRightIdx α z))
                      * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                          A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)))) := by
                  refine Finset.sum_congr rfl (fun α _ => ?_)
                  simp [mul_assoc]
              _ = O (x z) y * (∑ α : Fin (n - 1) → Fin D,
                    (A z y (mpsLeftIdx α z) (mpsRightIdx α z))
                      * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                          A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))) :=
                  (Finset.mul_sum (Finset.univ : Finset (Fin (n - 1) → Fin D))
                    (fun α => (A z y (mpsLeftIdx α z) (mpsRightIdx α z))
                      * (∏ i ∈ (Finset.univ : Finset (Fin n)).erase z,
                          A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)))
                    (O (x z) y)).symm
      _ = ∑ y : Fin d, O (x z) y * bitMpsAmplitude A (Function.update x z y) := by
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [hamp y]
  show (∑ α : Fin (n - 1) → Fin D,
      ∏ i : Fin n, (bitObsMps A z O) i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)) = _
  exact hmain

/-- The computed local-observable quantity equals its mathematical amplitude expression. -/
theorem bitLocalObs_eq_math {n d D : ℕ} [NeZero D] (A : BitMps n d D) (z : Fin n)
    (O : BitLocalObs d) : bitLocalObs A z O = bitLocalObsMath A z O := by
  have hinter : bitInner A (bitObsMps A z O) = bitInnerMath A (bitObsMps A z O) :=
    bitInner_eq_math A (bitObsMps A z O)
  have hamp : ∀ x : Fin n → Fin d,
      bitMpsAmplitude (bitObsMps A z O) x
        = ∑ y : Fin d, O (x z) y * bitMpsAmplitude A (Function.update x z y) :=
    bitObsMps_amplitude A z O
  show bitInner A (bitObsMps A z O) = ∑ x : Fin n → Fin d,
    (bitMpsAmplitude A x) * (∑ y : Fin d, O (x z) y * bitMpsAmplitude A (Function.update x z y))
  rw [hinter]
  show (∑ x : Fin n → Fin d,
      (bitMpsAmplitude A x) * (bitMpsAmplitude (bitObsMps A z O) x)) = _
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hamp x]

/-- The ledger-based bit-time expression for the local-observable inner product obeys the stated
inner-product operation and width bound. -/
theorem bitLocalObs_bitTime {n d D w : ℕ} [NeZero D] (A : BitMps n d D) (z : Fin n)
    (O : BitLocalObs d) :
    bitTimeOf (bitInnerWidthBound n d D D w) (bitInnerWithCount A (bitObsMps A z O)).2
      ≤ 2 * bitInnerOpBound n d D D
        * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitInnerWidthBound n d D D w) :=
  bitInner_bitTime A (bitObsMps A z O)

/-- If `0 ≤ M ≤ N` and the positive denominator `N'` approximates `N` with relative error at
most `eps < 1`, the ratio error is at most `2 * eps / (1 - eps)`. -/
theorem rat_norm_error {M N N' eps : ℚ}
    (hM0 : 0 ≤ M) (hMN : M ≤ N) (hN : 0 < N) (hN' : 0 < N')
    (heps0 : 0 ≤ eps) (heps1 : eps < 1)
    (hrel : |N' - N| ≤ eps * N) :
    |M / N' - M / N| ≤ 2 * eps / (1 - eps) := by
  have hrel' : |N - N'| ≤ eps * N := by rw [abs_sub_comm]; exact hrel
  have h1m : (0 : ℚ) < 1 - eps := by linarith

  have hN'' : (1 - eps) * N ≤ N' := by
    have h := (abs_le.mp hrel').2
    linarith

  have hMp : M / N' ≤ 1 / (1 - eps) := by
    have hN'pos : (0 : ℚ) < (1 - eps) * N := mul_pos h1m hN
    have h1 : M / N' ≤ M / ((1 - eps) * N) :=
      div_le_div_of_nonneg_left hM0 hN'pos hN''
    have h2 : M / ((1 - eps) * N) = (M / N) / (1 - eps) := by
      field_simp
    have h3 : M / N ≤ 1 := (div_le_iff₀ hN).2 (by simpa using! hMN)
    have h4 : (M / N) / (1 - eps) ≤ 1 / (1 - eps) :=
      div_le_div_of_nonneg_right h3 (le_of_lt h1m)
    calc M / N' ≤ M / ((1 - eps) * N) := h1
      _ = (M / N) / (1 - eps) := h2
      _ ≤ 1 / (1 - eps) := h4

  have habs : |M / N' - M / N| = M * |N - N'| / (N' * N) := by
    have hfield : M / N' - M / N = M * (N - N') / (N' * N) := by
      field_simp
    rw [hfield, abs_div, abs_mul, abs_of_nonneg hM0, abs_of_pos (mul_pos hN' hN)]

  have h1 : M * |N - N'| / (N' * N) ≤ M * (eps * N) / (N' * N) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrel' hM0)
      (mul_nonneg (le_of_lt hN') (le_of_lt hN))
  have h2 : M * (eps * N) / (N' * N) = eps * (M / N') := by
    field_simp
  have h3 : eps * (M / N') ≤ eps * (1 / (1 - eps)) :=
    mul_le_mul_of_nonneg_left hMp heps0
  have h4 : eps * (1 / (1 - eps)) = eps / (1 - eps) := by
    field_simp
  have h5 : eps / (1 - eps) ≤ 2 * eps / (1 - eps) :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt h1m)
  calc |M / N' - M / N| = M * |N - N'| / (N' * N) := habs
    _ ≤ M * (eps * N) / (N' * N) := h1
    _ = eps * (M / N') := h2
    _ ≤ eps * (1 / (1 - eps)) := h3
    _ = eps / (1 - eps) := h4
    _ ≤ 2 * eps / (1 - eps) := h5

/-- A positive approximate squared norm with the stated relative error changes each sampling
probability by at most `bitSampleProbError eps`. -/
theorem bitSampleProbApprox_error {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) (N' eps : ℚ)
    (hN : (0 : ℚ) < (bitNormSq A : ℚ)) (hN' : (0 : ℚ) < N')
    (heps0 : (0 : ℚ) ≤ eps) (heps1 : eps < 1)
    (hrel : |N' - (bitNormSq A : ℚ)| ≤ eps * (bitNormSq A : ℚ)) :
    |bitSampleProbApprox A x N' - bitSampleProb A x| ≤ bitSampleProbError eps := by

  have hM0 : (0 : ℚ) ≤ (bitMpsAmplitude A x) ^ 2 := by positivity

  have hMN : ((bitMpsAmplitude A x) ^ 2 : ℚ) ≤ (bitNormSq A : ℚ) := by
    have h : (bitMpsAmplitude A x) ^ 2 ≤ ∑ y : Fin n → Fin d, (bitMpsAmplitude A y) ^ 2 := by
      refine Finset.single_le_sum (fun y _ => sq_nonneg _) (Finset.mem_univ x)
    rw [bitNormSq_eq_mass]
    exact_mod_cast h
  have h := rat_norm_error hM0 hMN hN hN' heps0 heps1 hrel
  show |((bitMpsAmplitude A x) ^ 2 : ℚ) / N'
      - (bitMpsAmplitude A x) ^ 2 / (bitNormSq A : ℚ)| ≤ bitSampleProbError eps
  simpa [bitSampleProbApprox, bitSampleProb, bitSampleProbError] using! h

/-- The amplitude of the prefix-fixed MPS equals the original amplitude at the configuration
with that prefix and next symbol fixed. -/
theorem bitMpsAmplitude_prefixFixed {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (k : ℕ) (hk : k < n) (lo : Fin k → Fin d) (s : Fin d) (t : Fin n → Fin d) :
    bitMpsAmplitude (bitPrefixFixedMps A k lo s) t
      = bitMpsAmplitude A (prefixFixedConfig lo s t) := by
  have hAmp : ∀ (α : Fin (n - 1) → Fin D),
      (∏ j : Fin n, (bitPrefixFixedMps A k lo s) j (t j) (mpsLeftIdx α j) (mpsRightIdx α j))
        = ∏ j : Fin n, A j ((prefixFixedConfig lo s t) j) (mpsLeftIdx α j) (mpsRightIdx α j) := by
    intro α
    refine Finset.prod_congr rfl (fun j _ => ?_)
    by_cases hj : j.val < k
    · simp [bitPrefixFixedMps, prefixFixedConfig, hj]
    · by_cases hj2 : j.val = k
      · simp [bitPrefixFixedMps, prefixFixedConfig, hj, hj2]
      · simp [bitPrefixFixedMps, prefixFixedConfig, hj, hj2]
  show (∑ α : Fin (n - 1) → Fin D,
      ∏ j : Fin n, (bitPrefixFixedMps A k lo s) j (t j) (mpsLeftIdx α j) (mpsRightIdx α j))
      = ∑ α : Fin (n - 1) → Fin D,
      ∏ j : Fin n, A j ((prefixFixedConfig lo s t) j) (mpsLeftIdx α j) (mpsRightIdx α j)
  exact Finset.sum_congr rfl (fun α _ => hAmp α)

/-- Fixing the prefix of a split configuration replaces its first block by `prefixSnoc lo s` and
preserves the remaining block. -/
theorem prefixFixedConfig_split {n d k : ℕ} (hk : k < n) (lo : Fin k → Fin d) (s : Fin d)
    (lo' : Fin (k + 1) → Fin d) (hi' : Fin (n - k - 1) → Fin d) :
    prefixFixedConfig lo s (splitInv (n := n) (d := d) (k := k + 1) (by omega) (lo', hi'))
      = splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, hi') := by
  funext j
  by_cases hj : j.val < k
  · have hj' : j.val < k + 1 := by omega
    simp only [prefixFixedConfig, dif_pos hj, splitInv, dif_pos hj', prefixSnoc, dif_pos hj]
  · by_cases hj2 : j.val = k
    · have hj' : j.val < k + 1 := by omega
      simp only [prefixFixedConfig, dif_neg hj, dif_pos hj2, splitInv, dif_pos hj',
        prefixSnoc, dif_neg hj]
    · have hj' : ¬ j.val < k + 1 := by omega
      simp only [prefixFixedConfig, dif_neg hj, dif_neg hj2, splitInv, dif_neg hj']

/-- The self-inner-product of the prefix-fixed MPS equals `d ^ (k + 1)` times the corresponding
tail mass. -/
theorem bitInner_prefixFixed {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (k : ℕ) (hk : k < n) (lo : Fin k → Fin d) (s : Fin d) :
    bitInner (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)
      = d ^ (k + 1) * bitTailMass A k hk lo s := by
  have h1 : bitInner (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)
      = ∑ t : Fin n → Fin d, (bitMpsAmplitude (bitPrefixFixedMps A k lo s) t) ^ 2 := by
    rw [bitInner_eq_math]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [pow_two]
  have h2 : (∑ t : Fin n → Fin d, (bitMpsAmplitude (bitPrefixFixedMps A k lo s) t) ^ 2)
      = ∑ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d),
          (bitMpsAmplitude (bitPrefixFixedMps A k lo s)
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) p)) ^ 2 := by
    refine (Fintype.sum_equiv ((splitEquiv (n := n) (d := d) (k + 1) (by omega)).symm)
      (fun p => (bitMpsAmplitude (bitPrefixFixedMps A k lo s)
        (splitInv (n := n) (d := d) (k := k + 1) (by omega) p)) ^ 2)
      (fun t => (bitMpsAmplitude (bitPrefixFixedMps A k lo s) t) ^ 2)
      (fun p => rfl)).symm
  have h3 : ∀ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d),
      (bitMpsAmplitude (bitPrefixFixedMps A k lo s)
        (splitInv (n := n) (d := d) (k := k + 1) (by omega) p)) ^ 2
        = (bitMpsAmplitude A
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p.2))) ^ 2 := by
    intro p
    rcases p with ⟨p1, p2⟩
    rw [bitMpsAmplitude_prefixFixed A k hk lo s]
    rw [prefixFixedConfig_split (hk := hk) (lo := lo) (s := s) (lo' := p1) (hi' := p2)]
  have h4 : (∑ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d),
          (bitMpsAmplitude A
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p.2))) ^ 2)
      = Fintype.card (Fin (k + 1) → Fin d) * bitTailMass A k hk lo s := by
    let g : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d) → ℤ :=
      fun p => (bitMpsAmplitude A
        (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p.2))) ^ 2
    calc (∑ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d),
          (bitMpsAmplitude A
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p.2))) ^ 2)
        = ∑ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d), g p := rfl
      _ = ∑ p1 : Fin (k + 1) → Fin d, ∑ p2 : Fin (n - k - 1) → Fin d, g (p1, p2) :=
          Fintype.sum_prod_type g
      _ = ∑ p2 : Fin (n - k - 1) → Fin d, ∑ p1 : Fin (k + 1) → Fin d, g (p1, p2) :=
          Finset.sum_comm
      _ = ∑ p2 : Fin (n - k - 1) → Fin d, (Fintype.card (Fin (k + 1) → Fin d))
          * (bitMpsAmplitude A
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p2))) ^ 2 := by
            refine Finset.sum_congr rfl (fun p2 _ => ?_)
            calc (∑ p1 : Fin (k + 1) → Fin d, g (p1, p2))
                = ∑ p1 : Fin (k + 1) → Fin d, (bitMpsAmplitude A
                  (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p2))) ^ 2 := by
                    refine Finset.sum_congr rfl (fun p1 _ => rfl)
                _ = Fintype.card (Fin (k + 1) → Fin d) * (bitMpsAmplitude A
                  (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p2))) ^ 2 :=
                    Finset.sum_const _
      _ = Fintype.card (Fin (k + 1) → Fin d)
          * (∑ p2 : Fin (n - k - 1) → Fin d, (bitMpsAmplitude A
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p2))) ^ 2) := by
            rw [Finset.mul_sum]
      _ = Fintype.card (Fin (k + 1) → Fin d) * bitTailMass A k hk lo s := by
            unfold bitTailMass
            rfl
  rw [h1, h2]
  have h6 : (∑ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d),
      (bitMpsAmplitude (bitPrefixFixedMps A k lo s)
        (splitInv (n := n) (d := d) (k := k + 1) (by omega) p)) ^ 2)
      = (∑ p : (Fin (k + 1) → Fin d) × (Fin (n - k - 1) → Fin d),
          (bitMpsAmplitude A
            (splitInv (n := n) (d := d) (k := k + 1) (by omega) (prefixSnoc lo s, p.2))) ^ 2) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h3 p]
  rw [h6, h4]
  simp [Fintype.card_fin]

/-- The conditional weight equals `d ^ (k + 1)` times the corresponding tail mass. -/
theorem bitCondWeight_eq {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ) (hk : k < n)
    (lo : Fin k → Fin d) (s : Fin d) :
    bitCondWeight A k lo s = d ^ (k + 1) * bitTailMass A k hk lo s :=
  bitInner_prefixFixed A k hk lo s

/-- Every tail mass at a valid prefix position is nonnegative. -/
theorem bitTailMass_nonneg {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ) (hk : k < n)
    (lo : Fin k → Fin d) (s : Fin d) : 0 ≤ bitTailMass A k hk lo s := by
  unfold bitTailMass
  exact Finset.sum_nonneg fun hi _ => sq_nonneg _

/-- Every conditional weight at a valid prefix position is nonnegative. -/
theorem bitCondWeight_nonneg {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ) (hk : k < n)
    (lo : Fin k → Fin d) (s : Fin d) : 0 ≤ bitCondWeight A k lo s := by
  rw [bitCondWeight_eq A k hk lo s]
  exact mul_nonneg (pow_nonneg (by omega) _) (bitTailMass_nonneg A k hk lo s)

/-- Conditional weights and tail masses satisfy the stated cross-multiplied normalization
identity. -/
theorem bitCondProb_eq {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ) (hk : k < n)
    (lo : Fin k → Fin d) (s : Fin d) :
    bitCondWeight A k lo s * (∑ s' : Fin d, bitTailMass A k hk lo s')
      = bitTailMass A k hk lo s * (∑ s' : Fin d, bitCondWeight A k lo s') := by
  rw [bitCondWeight_eq A k hk lo s]
  simp only [bitCondWeight_eq A k hk lo]
  rw [← Finset.mul_sum]
  ring

/-- The prefix-fixed self-inner-product ledger obeys the inner-product multiplication and
addition bounds and uses no subtractions. -/
theorem bitCondWeight_cost {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ)
    (lo : Fin k → Fin d) (s : Fin d) :
    (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2.muls
      ≤ bitInnerOpBound n d D D
    ∧ (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2.adds
        ≤ bitInnerOpBound n d D D
    ∧ (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2.subs
        = 0 :=
  bitInnerWithCount_ledger _ _

/-- The ledger-based conditional-weight bit-time expression obeys the specified inner-product
operation and width bound. -/
theorem bitCondWeight_bitTime {n d D w : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ)
    (lo : Fin k → Fin d) (s : Fin d) :
    bitTimeOf (bitInnerWidthBound n d D D w)
        (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2
      ≤ 2 * bitInnerOpBound n d D D
        * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitInnerWidthBound n d D D w) :=
  bitInner_bitTime _ _

/-- The contraction, operation-count, sampling, local-observable, and conditional-weight
guarantees collected in `clause2StatementNext` hold. -/
theorem clause3_endpoint : clause2StatementNext := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n d D _ A x => bitMpsContract_eq_chainTotal A x
  · exact fun Ms hne => chainTotal_zero_eq_bondSum Ms hne
  · exact fun n d D w _ A x => bitMpsContractWithCount_ledger A x
  · exact fun n d D w _ A x => bitMpsContract_bitTime A x
  · exact fun D => bitMpsContract_workspace D
  · exact fun p z => bitRoundScaled_error p z
  · exact fun a b D hD => bitPepsTreewidthCost_le a b D hD
  · exact fun n d DA DB _ _ A B => bitInner_eq_math A B
  · exact fun n d DA DB _ _ A B => bitInnerWithCount_ledger A B
  · exact fun n d DA DB w _ _ A B => bitInner_bitTime A B
  · exact fun DA DB => bitInner_workspace DA DB
  · exact fun n d D _ A x => bitSampleProb_eq_law A x
  · exact fun n d D _ A hA => bitSampleProb_sum A hA
  · exact fun n d D _ A hA x => bitSampleProb_nonneg A hA x
  · exact fun n d D _ A z O => bitLocalObs_eq_math A z O
  · exact fun n d D w _ A z O => bitLocalObs_bitTime A z O
  · exact fun n d D _ A x N' eps hN hN' heps0 heps1 hrel =>
      bitSampleProbApprox_error A x N' eps hN hN' heps0 heps1 hrel
  · exact fun n d D _ A k hk lo s => bitCondProb_eq A k hk lo s
  · exact fun n d D _ A k lo s => bitCondWeight_cost A k lo s
  · exact fun n d D w _ A k lo s => bitCondWeight_bitTime A k lo s

end Qatlib.Concepts.DyadicOverlap.ArithLedger.TensorNetwork
