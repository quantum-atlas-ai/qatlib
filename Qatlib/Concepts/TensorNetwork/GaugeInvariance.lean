/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkCoreDefs
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Gauge invariance and matrix product representations

This module proves invariance of `netContract` under network isomorphisms and unitary gauges on
internal edges. The constructions `mpsNet`, `perNet`, and `pepsNet` encode open-boundary matrix
product states, periodic matrix product states, and rectangular projected entangled pair states
as tensor networks, with matching contraction formulas. These constructions use the
tensor-network framework discussed in [Schollwock2011].

The module also relates `cutRank` to MPS bond dimension and uses singular-value decompositions
to construct left-canonical representations and approximations controlled by `schmidtTailSq`,
following [PerezGarciaEtAl2007]. Explicit examples and counterexamples record the behavior of
the evaluation procedures and their proposed resource bounds.

## Main statements

* `clause1_clause1`: contraction is invariant under a network isomorphism.
* `clause1_clause2`: contraction is invariant under unitary gauges on internal edges.
* `netContract_mpsNet_eq_mpsAmplitude`: the capped MPS network contracts to its zero-boundary
  amplitude.
* `clause1_clause4` and `clause1_clause5`: periodic MPS and PEPS amplitudes have tensor-network
  representations with the prescribed bond-dimension bound.
* `clause2_clause1`: MPS bond dimension bounds every cut rank below the site count.
* `clause2_clause2`: a normalized state on at least one site has a left-canonical MPS
  representation with bond dimension equal to the maximum of one and its cut-rank supremum.
* `clause2_clause3`: a normalized state on at least one site has a bond-dimension-`D` MPS
  approximation, for positive `D`, with squared error bounded by twice the sum of squared
  Schmidt tails.
* `clause3_counter`: the displayed conjunction of universal evaluation and resource claims
  fails.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
* [Schollwock, 2011][Schollwock2011]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.TensorNetwork.GaugeInvariance
open Matrix
open scoped BigOperators Nat ComplexConjugate

section Aux

variable {n d D : ℕ}

instance : Subsingleton (Fin (n - 1) → Fin 1) :=
  ⟨fun _a _b => funext fun _i => Subsingleton.elim _ _⟩

/-- For bond dimension one, the MPS amplitude is the product of the scalar entries at the
selected physical indices. -/
@[simp]
theorem sum_single_bond_prod (A : Fin n → Fin d → Matrix (Fin 1) (Fin 1) ℂ)
    (x : Fin n → Fin d) :
    mpsAmplitude A x = ∏ i, A i (x i) 0 0 := by
  rw [mpsAmplitude]
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp [mpsLeftIdx, mpsRightIdx]
  · intro b _ hb
    exact absurd (funext fun i => Subsingleton.elim (b i) 0) hb
  · simp

/-- A tensor network contracts to zero if some internal edge has dimension zero. -/
theorem netContract_of_isEmpty_internal {N : TensorNet}
    (hd : ∃ i : InternalEdge N, N.dims i.val = 0)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) : netContract N ext = 0 := by
  obtain ⟨i, hi⟩ := hd
  have _hempty : IsEmpty (∀ k : InternalEdge N, Fin (N.dims k.val)) := by
    refine ⟨fun f => ?_⟩
    have _h0 : Fin (N.dims i.val) → False := by rw [hi]; exact Fin.elim0
    exact _h0 (f i)
  simp [netContract]

/-- The contraction of a tensor network with no vertices and no half-edges is one. -/
theorem netContract_of_empty_net {N : TensorNet} (hnv : N.nv = 0) (hnh : N.nh = 0)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) : netContract N ext = 1 := by
  have hnv' : IsEmpty (Fin N.nv) := by rw [hnv]; infer_instance
  have hnh' : IsEmpty (Fin N.nh) := by rw [hnh]; infer_instance
  have hIE : IsEmpty (InternalEdge N) := ⟨fun i => hnh'.false i.val⟩
  have huniq : Unique (∀ i : InternalEdge N, Fin (N.dims i.val)) :=
    ⟨⟨fun i => hIE.elim i⟩, fun a => funext fun i => hIE.elim i⟩
  have hconst : ∀ e : (∀ i : InternalEdge N, Fin (N.dims i.val)),
      (∏ v : Fin N.nv, N.tensor v (fun h => portValue N ext e h.val)) = 1 := by
    intro e
    have huv : (Finset.univ : Finset (Fin N.nv)) = ∅ := @Finset.univ_eq_empty _ _ hnv'
    rw [huv]
    exact Finset.prod_empty
  calc netContract N ext
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          (∏ v : Fin N.nv, N.tensor v (fun h => portValue N ext e h.val) : ℂ) := rfl
    _ = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val), (1 : ℂ) :=
          Finset.sum_congr rfl fun e _ => hconst e
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_unique]
        simp

/-- Identifies a function from `Fin 1` to `Fin 2` with its value at the unique input. -/
def equivSingle21 : (Fin 1 → Fin 2) ≃ Fin 2 :=
  ⟨fun f => f 0, fun k _ => k, fun f => funext fun i => congrArg f (Subsingleton.elim 0 i),
    fun _ => rfl⟩

/-- The MPS with bond dimension one and site scalars `g` has amplitude `∏ i, g i (x i)`. -/
theorem mpsAmplitude_product (n d : ℕ) (g : Fin n → Fin d → ℂ) (x : Fin n → Fin d) :
    @mpsAmplitude n d 1 _ (fun i y => Matrix.of fun _ _ => g i y) x = ∏ i, g i (x i) := by
  have key : ∀ b : Fin (n - 1) → Fin 1, b = (fun _ => (0 : Fin 1) : Fin (n - 1) → Fin 1) :=
    fun b => funext fun i => Subsingleton.elim _ _
  rw [mpsAmplitude, Finset.sum_eq_single
    ((fun _ => (0 : Fin 1)) : Fin (n - 1) → Fin 1)]
  · rfl
  · intro b _ hb
    exact absurd (key b) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Identifies assignments to the single bond of a two-site chain with elements of `Fin D`. -/
def equivSingleBond (D : ℕ) : (Fin (2 - 1) → Fin D) ≃ Fin D :=
  ⟨fun f => f ⟨0, by omega⟩, fun k _ => k,
    fun f => funext fun i => congrArg f (Fin.eq_of_val_eq (by have := i.isLt; omega)),
    fun _ => rfl⟩

/-- The amplitude of a two-site MPS is the sum over its common bond index, with both outer
indices fixed to zero. -/
theorem mpsAmplitude_two_site {d D : ℕ} [NeZero D]
    (A : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin 2 → Fin d) :
    mpsAmplitude A x = ∑ k : Fin D, A 0 (x 0) 0 k * A 1 (x 1) k 0 := by
  have hbody : ∀ α : Fin (2 - 1) → Fin D,
      (∏ i : Fin 2, A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = A 0 (x 0) 0 (α ⟨0, by omega⟩)
            * A 1 (x 1) (α ⟨0, by omega⟩) 0 := by
    intro α
    rw [Fin.prod_univ_two]
    congr 2
  rw [mpsAmplitude, Fintype.sum_equiv (equivSingleBond D) _
    (fun k => A 0 (x 0) 0 k * A 1 (x 1) k 0) hbody]

/-- Identifies the two binary bond indices of a three-site chain with a pair of elements of `Fin
2`. -/
def equivBond22 : (Fin (3 - 1) → Fin 2) ≃ Fin 2 × Fin 2 :=
  ⟨fun f => (f ⟨0, by omega⟩, f ⟨1, by omega⟩),
    fun p i => if (i : ℕ) = 0 then p.1 else p.2,
    fun f => by
      funext i
      fin_cases i <;> simp,
    fun _ => rfl⟩

/-- The displayed two-site tensors have amplitude `1 / √2` when the two physical indices agree
and zero otherwise. -/
theorem bell_consumer :
    ∀ x : Fin 2 → Fin 2,
      @mpsAmplitude 2 2 2 _
          (fun (i : Fin 2) (y : Fin 2) => Matrix.of fun a b =>
            if i = 0 then (if (y : ℕ) = (b : ℕ) then Complex.ofReal (1 / Real.sqrt 2) else 0)
            else if (y : ℕ) = (a : ℕ) then 1 else 0) x
        = if x 0 = x 1 then Complex.ofReal (1 / Real.sqrt 2) else 0 := by
  intro x
  rw [mpsAmplitude_two_site, Fin.sum_univ_two]
  have hx0 : (x 0 : ℕ) = 0 ∨ (x 0 : ℕ) = 1 := by have := (x 0).isLt; omega
  have hx1 : (x 1 : ℕ) = 0 ∨ (x 1 : ℕ) = 1 := by have := (x 1).isLt; omega
  rcases hx0 with a0 | a0 <;> rcases hx1 with a1 | a1 <;>
    simp [a0, a1, ← Fin.val_eq_val, Matrix.of_apply]

/-- The explicit three-site binary tensors used in `short_chain_consumer`, with bond dimension
two. -/
def shortChainTensors : Fin 3 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun (i : Fin 3) (y : Fin 2) => Matrix.of fun a b =>
    if (i : ℕ) = 0 then
      (if (a : ℕ) = 0 then
        (if (y : ℕ) = 0 then (if (b : ℕ) = 0 then 1 else 0) else 1)
      else 0)
    else if (i : ℕ) = 1 then
      (if (y : ℕ) = 0 ∧ a = b then 1 else 0)
    else
      (if (b : ℕ) = 0 then
        (if (y : ℕ) = 0 then (if (a : ℕ) = 1 then 1 else 0) else 1)
      else 0)

/-- The amplitude of `shortChainTensors` vanishes unless the middle index is zero; otherwise it
counts the end indices equal to one. -/
theorem short_chain_consumer :
    ∀ x : Fin 3 → Fin 2,
      @mpsAmplitude 3 2 2 _ shortChainTensors x
        = if (x 1 : ℕ) = 0 then
            (if (x 0 : ℕ) = 1 then (1 : ℂ) else 0) + (if (x 2 : ℕ) = 1 then (1 : ℂ) else 0)
          else 0 := by
  intro x
  have hbody : ∀ α : Fin (3 - 1) → Fin 2,
      (∏ i : Fin 3, shortChainTensors i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
        = (fun p : Fin 2 × Fin 2 =>
            shortChainTensors 0 (x 0) 0 p.1
          * shortChainTensors 1 (x 1) p.1 p.2
          * shortChainTensors 2 (x 2) p.2 0) (equivBond22 α) := by
    intro α
    rw [Fin.prod_univ_three]
    show _ * _ * _ = _
    congr 2
  rw [mpsAmplitude, Fintype.sum_equiv equivBond22 _
    (fun p : Fin 2 × Fin 2 =>
      shortChainTensors 0 (x 0) 0 p.1 * shortChainTensors 1 (x 1) p.1 p.2
        * shortChainTensors 2 (x 2) p.2 0) hbody,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two]
  have hx0 : (x 0 : ℕ) = 0 ∨ (x 0 : ℕ) = 1 := by have := (x 0).isLt; omega
  have hx1 : (x 1 : ℕ) = 0 ∨ (x 1 : ℕ) = 1 := by have := (x 1).isLt; omega
  have hx2 : (x 2 : ℕ) = 0 ∨ (x 2 : ℕ) = 1 := by have := (x 2).isLt; omega
  rcases hx0 with v0 | v0 <;> rcases hx1 with v1 | v1 <;> rcases hx2 with v2 | v2 <;>
    simp [v0, v1, v2, Matrix.of_apply, shortChainTensors]

/-- The norm of a tensor-network contraction is bounded by the product of the local
`tensorSumNorm` values. -/
theorem netContract_norm_bound (N : TensorNet) (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) :
    ‖netContract N ext‖ ≤ ∏ v : Fin N.nv, tensorSumNorm N v := by

  set Φ : (∀ i : InternalEdge N, Fin (N.dims i.val)) →
      (∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :=
    fun e v h => portValue N ext e h.val with hΦ
  have hinj : Function.Injective Φ := by
    intro e e' heq
    funext i
    obtain ⟨j, k, hk, hlt⟩ := i
    have h1 : portValue N ext e j = e ⟨j, ⟨k, hk, hlt⟩⟩ := by
      unfold portValue
      split
      · next hj => exact absurd hj (by rw [hk]; simp)
      · next k' hk' =>
        have hkke : k' = k := by
          rw [hk] at hk'; exact (Option.some.inj hk').symm
        subst hkke
        rw [dite_eq_left hlt]
    have h2 : portValue N ext e' j = e' ⟨j, ⟨k, hk, hlt⟩⟩ := by
      unfold portValue
      split
      · next hj => exact absurd hj (by rw [hk]; simp)
      · next k' hk' =>
        have hkke : k' = k := by
          rw [hk] at hk'; exact (Option.some.inj hk').symm
        subst hkke
        rw [dite_eq_left hlt]
    have hval := congrFun (congrFun heq (N.site j)) ⟨j, rfl⟩
    simp only [hΦ] at hval
    rw [h1, h2] at hval
    exact hval
  calc ‖netContract N ext‖
      ≤ ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ‖∏ v : Fin N.nv, N.tensor v (Φ e v)‖ := by
          simp only [netContract]
          exact norm_sum_le _ _
    _ ≤ ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ∏ v : Fin N.nv, ‖N.tensor v (Φ e v)‖ :=
          Finset.sum_le_sum fun e _ => Finset.norm_prod_le _ _
    _ = ∑ y ∈ (Finset.univ.image Φ),
          ∏ v : Fin N.nv, ‖N.tensor v (y v)‖ :=
          (Finset.sum_image (g := Φ)
            (f := fun y : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v},
                Fin (N.dims h.val) => ∏ v : Fin N.nv, ‖N.tensor v (y v)‖)
            (fun e _ e' _ he => hinj he)).symm
    _ ≤ ∑ y : (∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
          ∏ v : Fin N.nv, ‖N.tensor v (y v)‖ := by
          have hnn : (0 : ℝ) ≤ ∑ y ∈ Finset.univ \ Finset.univ.image Φ,
              ∏ v : Fin N.nv, ‖N.tensor v (y v)‖ :=
            Finset.sum_nonneg fun y _ => Finset.prod_nonneg fun v _ => norm_nonneg _
          have hsplit : Finset.univ \ Finset.univ.image Φ ∪ Finset.univ.image Φ
              = Finset.univ :=
            Finset.sdiff_union_of_subset
              (Finset.subset_univ (Finset.univ.image Φ))
          rw [← hsplit, Finset.sum_union Finset.sdiff_disjoint]
          linarith
    _ = ∏ v : Fin N.nv, tensorSumNorm N v := by
          have h1 : ∏ v : Fin N.nv, tensorSumNorm N v
              = ∑ y ∈ Fintype.piFinset (fun _ => Finset.univ),
                  ∏ v, ‖N.tensor v (y v)‖ := by
            simp only [tensorSumNorm]
            rw [Finset.prod_univ_sum]
          rw [← Fintype.piFinset_univ, ← h1]

section Encoding

/-- Assigns dimension `D` to the bond half-edges and dimension `d` to the physical legs in the
capped MPS encoding. -/
def mpsDim (n d D : ℕ) (j : ℕ) : ℕ := if j < 2 * (n + 1) then D else d

/-- Pairs consecutive bond half-edges in the capped MPS encoding and leaves physical legs
unpaired. -/
def mpsPartner (n : ℕ) (j : Fin (3 * n + 2)) : Option (Fin (3 * n + 2)) :=
  if h : (j : ℕ) < 2 * (n + 1) then
    some ⟨if (j : ℕ) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1, by
      have := h
      split_ifs <;> omega⟩
  else none

/-- Assigns each half-edge of the capped MPS encoding to a physical site or one of the two
boundary vertices. -/
def mpsSite (n : ℕ) (j : Fin (3 * n + 2)) : Fin (n + 2) :=
  if (j : ℕ) = 1 then ⟨n, by omega⟩
  else if (j : ℕ) = 2 * n then ⟨n + 1, by omega⟩
  else if h : (j : ℕ) < 2 * (n + 1) then
    if h2 : (j : ℕ) % 2 = 0 then ⟨(j : ℕ) / 2, by have := h; omega⟩
    else ⟨((j : ℕ) - 3) / 2, by have := h; have := h2; omega⟩
  else ⟨(j : ℕ) - (2 * (n + 1)), by have := j.isLt; omega⟩

/-- A bond half-edge in the capped MPS encoding has dimension `D`. -/
theorem mpsDim_bond (n d D : ℕ) {j : ℕ} (h : j < 2 * (n + 1)) : mpsDim n d D j = D := by
  rw [mpsDim, ite_eq_left h]

/-- A physical half-edge in the capped MPS encoding has dimension `d`. -/
theorem mpsDim_phys (n d D : ℕ) (i : ℕ) (h : ¬(2 * (n + 1) + i < 2 * (n + 1))) :
    mpsDim n d D (2 * (n + 1) + i) = d := by
  rw [mpsDim, ite_eq_right h]

/-- The physical half-edge indexed by `i` belongs to site `i`. -/
theorem mpsSite_phys (n : ℕ) (i : ℕ) (hi : i < n) :
    mpsSite n ⟨2 * (n + 1) + i, by omega⟩ = ⟨i, by omega⟩ := by
  simp only [mpsSite]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega)]
  refine Fin.ext ?_
  show 2 * (n + 1) + i - 2 * (n + 1) = i
  omega

/-- The bond half-edge numbered `2 * i` belongs to physical site `i` when `i < n`. -/
theorem mpsSite_left (n : ℕ) (i : ℕ) (hi : i < n) :
    mpsSite n ⟨2 * i, by omega⟩ = ⟨i, by omega⟩ := by
  simp only [mpsSite]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega), dite_eq_left (by omega)]
  refine Fin.ext ?_
  show 2 * i / 2 = i
  omega

/-- The bond half-edge numbered `2 * i + 3` belongs to physical site `i` when `i < n`. -/
theorem mpsSite_right (n : ℕ) (i : ℕ) (hi : i < n) :
    mpsSite n ⟨2 * i + 3, by omega⟩ = ⟨i, by omega⟩ := by
  simp only [mpsSite]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right (by omega)]
  refine Fin.ext ?_
  show (2 * i + 3 - 3) / 2 = i
  omega

/-- Half-edge one belongs to the left boundary vertex of the capped MPS encoding. -/
theorem mpsSite_capL (n : ℕ) : mpsSite n ⟨1, by omega⟩ = ⟨n, by omega⟩ := by
  simp [mpsSite]

/-- Half-edge `2 * n` belongs to the right boundary vertex of the capped MPS encoding. -/
theorem mpsSite_capR (n : ℕ) : mpsSite n ⟨2 * n, by omega⟩ = ⟨n + 1, by omega⟩ := by
  simp [mpsSite]

/-- The local tensor for the capped MPS network, using `A` at physical vertices and zero-index
boundary constraints at the two caps. -/
noncomputable def mpsTensor (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (v : Fin (n + 2))
    (a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = v}, Fin (mpsDim n d D h.val.val)) : ℂ :=
  if hv : (v : ℕ) < n then
    A ⟨v, hv⟩
      (Fin.cast (mpsDim_phys n d D (v : ℕ) (by omega))
        (show Fin (mpsDim n d D (2 * (n + 1) + (v : ℕ))) from
          a (Subtype.mk ⟨2 * (n + 1) + (v : ℕ), by omega⟩ (by
            rw [mpsSite_phys n (v : ℕ) hv]))))
      (Fin.cast (mpsDim_bond n d D (by omega))
        (show Fin (mpsDim n d D (2 * (v : ℕ))) from
          a (Subtype.mk ⟨2 * (v : ℕ), by omega⟩ (by
            rw [mpsSite_left n (v : ℕ) hv]))))
      (Fin.cast (mpsDim_bond n d D (by omega))
        (show Fin (mpsDim n d D (2 * (v : ℕ) + 3)) from
          a (Subtype.mk ⟨2 * (v : ℕ) + 3, by omega⟩ (by
            rw [mpsSite_right n (v : ℕ) hv]))))
  else if hv2 : (v : ℕ) = n then
    if ((show Fin (mpsDim n d D 1) from
          a (Subtype.mk ⟨1, by omega⟩ (by
            rw [mpsSite_capL n]
            exact Fin.ext (by omega : (n : ℕ) = v.val))))).val = 0 then (1 : ℂ) else 0
  else
    if ((show Fin (mpsDim n d D (2 * n)) from
          a (Subtype.mk ⟨2 * n, by omega⟩ (by
            rw [mpsSite_capR n]
            exact Fin.ext (by omega : (n + 1 : ℕ) = v.val))))).val = 0 then (1 : ℂ) else 0

/-- Encodes the MPS tensors `A` as a tensor network with `n` physical vertices and two boundary
caps. -/
noncomputable def mpsNet (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    TensorNet where
  nv := n + 2
  nh := 3 * n + 2
  dims := fun j => mpsDim n d D (j : ℕ)
  site := fun j => mpsSite n j
  partner := fun j => mpsPartner n j
  involution := by
    intro j k hj
    simp only [mpsPartner] at hj ⊢
    by_cases h : (j : ℕ) < 2 * (n + 1)
    · rw [dite_eq_left h] at hj
      simp only [Option.some.injEq] at hj
      have hkv : (k : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) % 2 = 0 ∨
          (k : ℕ) = (j : ℕ) - 1 ∧ ¬((j : ℕ) % 2 = 0) := by
        have hv := congrArg Fin.val hj
        by_cases h2 : (j : ℕ) % 2 = 0
        · left
          simp only [ite_eq_left h2] at hv
          exact ⟨by simpa using! hv.symm, h2⟩
        · right
          simp only [ite_eq_right h2] at hv
          exact ⟨by simpa using! hv.symm, h2⟩
      rcases hkv with ⟨hkv, h2⟩ | ⟨hkv, h2⟩
      · simp only [hkv]
        rw [dite_eq_left (by omega : (j : ℕ) + 1 < 2 * (n + 1))]
        simp only [ite_eq_right (by omega : ¬(((j : ℕ) + 1) % 2 = 0))]
        cases j
        rfl
      · simp only [hkv]
        rw [dite_eq_left (by omega : (j : ℕ) - 1 < 2 * (n + 1))]
        simp only [ite_eq_left (by omega : ((j : ℕ) - 1) % 2 = 0), Option.some.injEq]
        cases j
        case _ val isLt =>
          have hodd : (val : ℕ) % 2 ≠ 0 := by simpa using! h2
          exact Fin.ext (by show val - 1 + 1 = val; omega)
    · rw [dite_eq_right h] at hj
      exact absurd hj (by simp)
  no_self_loop := by
    intro j k hj
    simp only [mpsPartner] at hj
    by_cases h : (j : ℕ) < 2 * (n + 1)
    · rw [dite_eq_left h] at hj
      simp only [Option.some.injEq] at hj
      have hv := congrArg Fin.val hj
      by_cases h2 : (j : ℕ) % 2 = 0
      · simp only [ite_eq_left h2] at hv
        intro hcon
        have hval := congrArg Fin.val hcon
        omega
      · simp only [ite_eq_right h2] at hv
        intro hcon
        have hval := congrArg Fin.val hcon
        omega
    · rw [dite_eq_right h] at hj
      exact absurd hj (by simp)
  dims_match := by
    intro j k hj
    simp only [mpsPartner] at hj
    by_cases h : (j : ℕ) < 2 * (n + 1)
    · rw [dite_eq_left h] at hj
      simp only [Option.some.injEq] at hj
      have hv := congrArg Fin.val hj
      have hk : (k : ℕ) < 2 * (n + 1) := by
        by_cases h2 : (j : ℕ) % 2 = 0
        · simp only [ite_eq_left h2] at hv
          omega
        · simp only [ite_eq_right h2] at hv
          omega
      show mpsDim n d D (j : ℕ) = mpsDim n d D (k : ℕ)
      rw [mpsDim, mpsDim, ite_eq_left h, ite_eq_left hk]
    · rw [dite_eq_right h] at hj
      exact absurd hj (by simp)
  tensor := fun v a =>
    mpsTensor n d D A v (fun h => a h)

end Encoding

end Aux

section MainThm

/-- A half-edge with a partner in the capped MPS encoding lies in the bond range. -/
theorem mpsPartner_isSome {n : ℕ} {j k : Fin (3 * n + 2)}
    (h : mpsPartner n j = some k) : (j : ℕ) < 2 * (n + 1) := by
  by_cases hlt : (j : ℕ) < 2 * (n + 1)
  · exact hlt
  · rw [mpsPartner, dite_eq_right hlt] at h
    exact absurd h (by simp)

/-- An unpaired half-edge in the capped MPS encoding lies beyond the bond range. -/
theorem mpsPartner_none_ge {n : ℕ} {j : Fin (3 * n + 2)} (h : mpsPartner n j = none) :
    2 * (n + 1) ≤ (j : ℕ) := by
  by_cases hlt : (j : ℕ) < 2 * (n + 1)
  · rw [mpsPartner, dite_eq_left hlt] at h
    exact absurd h (by simp)
  · omega

/-- The partner of bond half-edge `2 * j` is half-edge `2 * j + 1`. -/
theorem mpsPartner_even (n : ℕ) (j : Fin (n + 1)) :
    mpsPartner n ⟨2 * (j : ℕ), by have := j.isLt; omega⟩
      = some ⟨2 * (j : ℕ) + 1, by have := j.isLt; omega⟩ := by
  rw [mpsPartner, dite_eq_left (by have := j.isLt; omega : (2 * (j : ℕ)) < 2 * (n + 1))]
  refine congrArg some (Fin.ext ?_)
  show (if (2 * (j : ℕ)) % 2 = 0 then (2 * (j : ℕ)) + 1 else (2 * (j : ℕ)) - 1)
      = (2 * (j : ℕ)) + 1
  rw [ite_eq_left (by omega : 2 * (j : ℕ) % 2 = 0)]

/-- The partner of bond half-edge `2 * j + 1` is half-edge `2 * j`. -/
theorem mpsPartner_odd (n : ℕ) (j : Fin (n + 1)) :
    mpsPartner n ⟨2 * (j : ℕ) + 1, by have := j.isLt; omega⟩
      = some ⟨2 * (j : ℕ), by have := j.isLt; omega⟩ := by
  rw [mpsPartner, dite_eq_left (by have := j.isLt; omega : (2 * (j : ℕ) + 1) < 2 * (n + 1))]
  refine congrArg some (Fin.ext ?_)
  show (if (2 * (j : ℕ) + 1) % 2 = 0 then (2 * (j : ℕ) + 1) + 1 else (2 * (j : ℕ) + 1) - 1)
      = (2 * (j : ℕ))
  rw [ite_eq_right (by omega : ¬(2 * (j : ℕ) + 1) % 2 = 0)]
  omega

/-- The network bond dimension of `mpsNet n d D A` is at most `D`. -/
theorem netBondDimension_mpsNet_le (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    netBondDimension (mpsNet n d D A) ≤ D := by
  rw [netBondDimension]
  refine Finset.sup_le fun i _ => ?_
  obtain ⟨j, k, hk, _⟩ := i
  have hb : (j : ℕ) < 2 * (n + 1) := mpsPartner_isSome hk
  show mpsDim n d D (j : ℕ) ≤ D
  rw [mpsDim, ite_eq_left hb]

/-- Encodes the physical configuration `x` as an assignment to the open legs of `mpsNet`. -/
noncomputable def mpsEnc (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (o : OpenLeg (mpsNet n d D A)) :
    Fin ((mpsNet n d D A).dims o.val) :=
  Fin.cast (by
      show d = mpsDim n d D (o.val : ℕ)
      have hge := mpsPartner_none_ge (n := n) o.property
      rw [mpsDim, ite_eq_right (by omega)])
    (x ⟨(o.val : ℕ) - 2 * (n + 1), by
      have hge := mpsPartner_none_ge (n := n) o.property
      have := o.val.isLt
      omega⟩)

/-- The internal edge of the capped MPS network corresponding to bond position `j`. -/
def bondEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (j : Fin (n + 1)) : InternalEdge (mpsNet n d D A) :=
  ⟨⟨2 * (j : ℕ), by show 2 * (j : ℕ) < 3 * n + 2; have := j.isLt; omega⟩,
    ⟨⟨2 * (j : ℕ) + 1, by show 2 * (j : ℕ) + 1 < 3 * n + 2; have := j.isLt; omega⟩,
      mpsPartner_even n j,
      Fin.mk_lt_mk.mpr (by omega)⟩⟩

/-- Recovers the bond position represented by an internal edge of the capped MPS network. -/
def halfEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : InternalEdge (mpsNet n d D A)) : Fin (n + 1) :=
  ⟨(i.val.val) / 2, by
    obtain ⟨k, hk, -⟩ := i.property
    have := mpsPartner_isSome (n := n) hk
    omega⟩

/-- Recovering the position of `bondEdge j` returns `j`. -/
theorem halfEdge_bondEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (j : Fin (n + 1)) : halfEdge n d D A (bondEdge n d D A j) = j := by
  apply Fin.ext
  show (2 * (j : ℕ)) / 2 = (j : ℕ)
  omega

/-- Reconstructing an internal edge from its bond position returns the original edge. -/
theorem bondEdge_halfEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : InternalEdge (mpsNet n d D A)) : bondEdge n d D A (halfEdge n d D A i) = i := by
  obtain ⟨k, hk, hlt⟩ := i.property
  have hb : (i.val : ℕ) < 2 * (n + 1) := mpsPartner_isSome (n := n) hk
  have hk' : mpsPartner n i.val = some k := hk
  rw [mpsPartner, dite_eq_left hb] at hk'
  have hvk : (if (i.val : ℕ) % 2 = 0 then (i.val : ℕ) + 1 else (i.val : ℕ) - 1) = (k : ℕ) :=
    congrArg Fin.val (Option.some.inj hk')
  by_cases h2 : ((i.val : ℕ)) % 2 = 0
  · rw [ite_eq_left h2] at hvk
    refine Subtype.ext (Fin.ext ?_)
    show 2 * ((i.val.val) / 2) = (i.val : ℕ)
    omega
  · rw [ite_eq_right h2] at hvk
    exact absurd hlt (by omega)

/-- Identifies internal-edge assignments of the capped MPS network with functions `Fin (n + 1) →
Fin D`. -/
noncomputable def edgeIdxEquiv (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (∀ i : InternalEdge (mpsNet n d D A), Fin ((mpsNet n d D A).dims i.val)) ≃
      (Fin (n + 1) → Fin D) where
  toFun e j :=
    (e (bondEdge n d D A j)).cast
      (mpsDim_bond n d D (by show 2 * (j : ℕ) < 2 * (n + 1); have := j.isLt; omega))
  invFun β i :=
    (β (halfEdge n d D A i)).cast
      ((mpsDim_bond n d D (by
          show (i.val.val) < 2 * (n + 1)
          obtain ⟨k, hk, -⟩ := i.property
          exact mpsPartner_isSome (n := n) hk)).symm)
  left_inv := by
    intro e
    funext i
    have hb : bondEdge n d D A (halfEdge n d D A i) = i := bondEdge_halfEdge n d D A i
    exact Fin.ext (congrArg (fun j => (e j).val) hb)
  right_inv := by
    intro β
    funext j
    have hb : halfEdge n d D A (bondEdge n d D A j) = j := halfEdge_bondEdge n d D A j
    refine Fin.ext ?_
    show (β (halfEdge n d D A (bondEdge n d D A j))).val = (β j).val
    rw [hb]

/-- At the smaller endpoint of an internal edge, `portValue` equals the assigned edge index. -/
theorem portValue_of_partner_eq {N : TensorNet}
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val))
    (j k : Fin N.nh) (hj : N.partner j = some k) (hjk : j < k) :
    portValue N ext e j = e ⟨j, ⟨k, hj, hjk⟩⟩ := by
  unfold portValue
  split
  · next hnone => exact absurd (hnone.symm.trans hj) (by simp)
  · next k' hk' =>
    have hkk : k' = k := Option.some.inj (hk'.symm.trans hj)
    subst k'
    rw [dite_eq_left hjk]

/-- At the larger endpoint of an internal edge, `portValue` equals the assigned edge index
transported across the dimension equality. -/
theorem portValue_of_partner_eq_rev {N : TensorNet}
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val))
    (j k : Fin N.nh) (hj : N.partner j = some k) (hkj : k < j)
    (hinv : N.partner k = some j) (hdim : N.dims k = N.dims j) :
    portValue N ext e j = (e ⟨k, ⟨j, hinv, hkj⟩⟩).cast (by rw [← hdim]) := by
  unfold portValue
  split
  · next hnone => exact absurd (hnone.symm.trans hj) (by simp)
  · next k' hk' =>
    have hkk : k' = k := Option.some.inj (hk'.symm.trans hj)
    subst k'
    have hnlt : ¬(j < k) := by omega
    rw [dite_eq_right hnlt]

/-- At an unpaired half-edge, `portValue` equals the supplied open-leg assignment. -/
theorem portValue_of_partner_none {N : TensorNet}
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val))
    (j : Fin N.nh) (hj : N.partner j = none) :
    portValue N ext e j = ext ⟨j, hj⟩ := by
  unfold portValue
  split
  · next hnone => rfl
  · next k' hk' => exact absurd (hj.symm.trans hk') (by simp)

/-- The natural value of the port at half-edge `2 * j` is the value of the encoded bond
assignment `β j`. -/
theorem portValue_bond_even (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (ext : ∀ o : OpenLeg (mpsNet n d D A), Fin ((mpsNet n d D A).dims o.val))
    (β : Fin (n + 1) → Fin D) (j : Fin (n + 1)) :
    (portValue (mpsNet n d D A) ext ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * (j : ℕ), by show 2 * (j : ℕ) < 3 * n + 2; have := j.isLt; omega⟩).val
      = (β j).val := by
  rw [portValue_of_partner_eq (N := mpsNet n d D A) ext ((edgeIdxEquiv n d D A).symm β)
      ⟨2 * (j : ℕ), by show 2 * (j : ℕ) < 3 * n + 2; have := j.isLt; omega⟩
      ⟨2 * (j : ℕ) + 1, by show 2 * (j : ℕ) + 1 < 3 * n + 2; have := j.isLt; omega⟩
      (mpsPartner_even n j) (Fin.mk_lt_mk.mpr (by omega))]
  show (β ⟨(2 * (j : ℕ)) / 2, by have := j.isLt; omega⟩).val = (β j).val
  have hij : (⟨(2 * (j : ℕ)) / 2, by have := j.isLt; omega⟩ : Fin (n + 1)) = j := by
    apply Fin.ext
    show (2 * (j : ℕ)) / 2 = (j : ℕ)
    omega
  rw [hij]

/-- The natural value of the port at half-edge `2 * j + 1` is the value of the encoded bond
assignment `β j`. -/
theorem portValue_bond_odd (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (ext : ∀ o : OpenLeg (mpsNet n d D A), Fin ((mpsNet n d D A).dims o.val))
    (β : Fin (n + 1) → Fin D) (j : Fin (n + 1)) :
    (portValue (mpsNet n d D A) ext ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * (j : ℕ) + 1, by show 2 * (j : ℕ) + 1 < 3 * n + 2; have := j.isLt; omega⟩).val
      = (β j).val := by
  rw [portValue_of_partner_eq_rev (N := mpsNet n d D A) ext ((edgeIdxEquiv n d D A).symm β)
      ⟨2 * (j : ℕ) + 1, by show 2 * (j : ℕ) + 1 < 3 * n + 2; have := j.isLt; omega⟩
      ⟨2 * (j : ℕ), by show 2 * (j : ℕ) < 3 * n + 2; have := j.isLt; omega⟩
      (mpsPartner_odd n j) (Fin.mk_lt_mk.mpr (by omega)) (mpsPartner_even n j)
      ((mpsNet n d D A).dims_match ⟨2 * (j : ℕ), by show 2 * (j : ℕ) < 3 * n + 2; have := j.isLt; omega⟩ ⟨2 * (j : ℕ) + 1, by show 2 * (j : ℕ) + 1 < 3 * n + 2; have := j.isLt; omega⟩ (mpsPartner_even n j))]
  show (β ⟨(2 * (j : ℕ)) / 2, by have := j.isLt; omega⟩).val = (β j).val
  have hij : (⟨(2 * (j : ℕ)) / 2, by have := j.isLt; omega⟩ : Fin (n + 1)) = j := by
    apply Fin.ext
    show (2 * (j : ℕ)) / 2 = (j : ℕ)
    omega
  rw [hij]

/-- The physical port at site `i` has the natural value of `x i` under `mpsEnc`. -/
theorem portValue_phys (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d)
    (e : ∀ i : InternalEdge (mpsNet n d D A), Fin ((mpsNet n d D A).dims i.val))
    (i : ℕ) (hi : i < n) :
    (portValue (mpsNet n d D A) (mpsEnc n d D A x) e
        ⟨2 * (n + 1) + i, by show 2 * (n + 1) + i < 3 * n + 2; omega⟩).val
      = (x ⟨i, hi⟩).val := by
  rw [portValue_of_partner_none (N := mpsNet n d D A) (mpsEnc n d D A x) e
      ⟨2 * (n + 1) + i, by show 2 * (n + 1) + i < 3 * n + 2; omega⟩
      (by show mpsPartner n ⟨2 * (n + 1) + i, by omega⟩ = none
          rw [mpsPartner, dite_eq_right (by show ¬(2 * (n + 1) + i < 2 * (n + 1)); omega)])]
  show (x ⟨2 * (n + 1) + i - 2 * (n + 1), by omega⟩).val = (x ⟨i, hi⟩).val
  have hij : (⟨2 * (n + 1) + i - 2 * (n + 1), by omega⟩ : Fin n) = ⟨i, hi⟩ := by
    apply Fin.ext
    show 2 * (n + 1) + i - 2 * (n + 1) = i
    omega
  rw [hij]

/-- Evaluating a physical vertex tensor of `mpsNet` gives the corresponding entry of `A` with
adjacent bond indices from `β`. -/
theorem siteTensor_eq (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (β : Fin (n + 1) → Fin D) (v : Fin (n + 2)) (hv : (v : ℕ) < n) :
    (mpsNet n d D A).tensor v
        (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
          ((edgeIdxEquiv n d D A).symm β) h.val)
      = A ⟨(v : ℕ), hv⟩ (x ⟨(v : ℕ), hv⟩) (β ⟨(v : ℕ), by omega⟩) (β ⟨(v : ℕ) + 1, by omega⟩) := by
  show mpsTensor n d D A v
      (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
        ((edgeIdxEquiv n d D A).symm β) h.val) = _
  simp only [mpsTensor, dite_eq_left hv]
  have hphys : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
      ⟨2 * (n + 1) + (v : ℕ), by show 2 * (n + 1) + (v : ℕ) < 3 * n + 2; omega⟩).val
      = (x ⟨(v : ℕ), hv⟩).val := portValue_phys n d D A x _ (v : ℕ) hv
  have hleft : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
      ⟨2 * (v : ℕ), by show 2 * (v : ℕ) < 3 * n + 2; omega⟩).val
      = (β ⟨(v : ℕ), by omega⟩).val :=
    portValue_bond_even n d D A _ β ⟨(v : ℕ), by omega⟩
  have hright : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
      ⟨2 * (v : ℕ) + 3, by show 2 * (v : ℕ) + 3 < 3 * n + 2; omega⟩).val
      = (β ⟨(v : ℕ) + 1, by omega⟩).val :=
    portValue_bond_odd n d D A _ β ⟨(v : ℕ) + 1, by omega⟩
  have e1 : Fin.cast (mpsDim_phys n d D (v : ℕ) (by omega))
      (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * (n + 1) + (v : ℕ), by show 2 * (n + 1) + (v : ℕ) < 3 * n + 2; omega⟩)
      = x ⟨(v : ℕ), hv⟩ := Fin.ext hphys
  have e2 : Fin.cast (mpsDim_bond n d D (by omega : 2 * (v : ℕ) < 2 * (n + 1)))
      (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * (v : ℕ), by show 2 * (v : ℕ) < 3 * n + 2; omega⟩)
      = β ⟨(v : ℕ), by omega⟩ := Fin.ext hleft
  have e3 : Fin.cast (mpsDim_bond n d D (by omega : 2 * (v : ℕ) + 3 < 2 * (n + 1)))
      (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * (v : ℕ) + 3, by show 2 * (v : ℕ) + 3 < 3 * n + 2; omega⟩)
      = β ⟨(v : ℕ) + 1, by omega⟩ := Fin.ext hright
  show A ⟨(v : ℕ), hv⟩
      (Fin.cast (mpsDim_phys n d D (v : ℕ) (by omega))
        (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
          ⟨2 * (n + 1) + (v : ℕ), by show 2 * (n + 1) + (v : ℕ) < 3 * n + 2; omega⟩))
      (Fin.cast (mpsDim_bond n d D (by omega : 2 * (v : ℕ) < 2 * (n + 1)))
        (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
          ⟨2 * (v : ℕ), by show 2 * (v : ℕ) < 3 * n + 2; omega⟩))
      (Fin.cast (mpsDim_bond n d D (by omega : 2 * (v : ℕ) + 3 < 2 * (n + 1)))
        (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
          ⟨2 * (v : ℕ) + 3, by show 2 * (v : ℕ) + 3 < 3 * n + 2; omega⟩))
      = A ⟨(v : ℕ), hv⟩ (x ⟨(v : ℕ), hv⟩) (β ⟨(v : ℕ), by omega⟩) (β ⟨(v : ℕ) + 1, by omega⟩)
  rw [e1, e2, e3]

/-- The left boundary tensor equals one precisely when the leftmost bond index is zero, and
equals zero otherwise. -/
theorem capLTensor_eq (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (β : Fin (n + 1) → Fin D) :
    (mpsNet n d D A).tensor (Fin.castSucc (Fin.last n))
        (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
          ((edgeIdxEquiv n d D A).symm β) h.val)
      = if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0 := by
  show mpsTensor n d D A (Fin.castSucc (Fin.last n))
      (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
        ((edgeIdxEquiv n d D A).symm β) h.val) = _
  rw [mpsTensor, dite_eq_right (by simp only [Fin.val_castSucc, Fin.val_last]; omega :
      ¬(((Fin.castSucc (Fin.last n) : Fin (n + 2)) : ℕ) < n)),
    dite_eq_left (by simp only [Fin.val_castSucc, Fin.val_last] :
      ((Fin.castSucc (Fin.last n) : Fin (n + 2)) : ℕ) = n)]
  show (if (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨1, by show 1 < 3 * n + 2; omega⟩).val = 0 then (1 : ℂ) else 0)
      = if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0
  have hval : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
      ⟨1, by show 1 < 3 * n + 2; omega⟩).val = (β ⟨0, by omega⟩).val :=
    portValue_bond_odd n d D A _ β ⟨0, by omega⟩
  by_cases h0 : (β ⟨0, by omega⟩ : Fin D).val = 0
  · have h1 : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨1, by show 1 < 3 * n + 2; omega⟩).val = 0 := by rw [hval]; exact h0
    rw [ite_eq_left h0, ite_eq_left h1]
  · have h1 : ¬((portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨1, by show 1 < 3 * n + 2; omega⟩).val = 0) := by rw [hval]; exact h0
    rw [ite_eq_right h0, ite_eq_right h1]

/-- The right boundary tensor equals one precisely when the rightmost bond index is zero, and
equals zero otherwise. -/
theorem capRTensor_eq (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (β : Fin (n + 1) → Fin D) :
    (mpsNet n d D A).tensor (Fin.last (n + 1))
        (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
          ((edgeIdxEquiv n d D A).symm β) h.val)
      = if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0 := by
  show mpsTensor n d D A (Fin.last (n + 1))
      (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
        ((edgeIdxEquiv n d D A).symm β) h.val) = _
  rw [mpsTensor, dite_eq_right (by simp only [Fin.val_last]; omega :
      ¬(((Fin.last (n + 1) : Fin (n + 2)) : ℕ) < n)),
    dite_eq_right (by simp only [Fin.val_last]; omega :
      ¬(((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = n))]
  show (if (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * n, by show 2 * n < 3 * n + 2; omega⟩).val = 0 then (1 : ℂ) else 0)
      = if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0
  have hval : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
      ⟨2 * n, by show 2 * n < 3 * n + 2; omega⟩).val = (β ⟨(n : ℕ), by omega⟩).val :=
    portValue_bond_even n d D A _ β ⟨(n : ℕ), by omega⟩
  by_cases h0 : (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0
  · have h1 : (portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * n, by show 2 * n < 3 * n + 2; omega⟩).val = 0 := by rw [hval]; exact h0
    rw [ite_eq_left h0, ite_eq_left h1]
  · have h1 : ¬((portValue (mpsNet n d D A) (mpsEnc n d D A x) ((edgeIdxEquiv n d D A).symm β)
        ⟨2 * n, by show 2 * n < 3 * n + 2; omega⟩).val = 0) := by rw [hval]; exact h0
    rw [ite_eq_right h0, ite_eq_right h1]

/-- Expands the capped MPS network contraction as a sum over all bond assignments, with
zero-index constraints on both boundary bonds. -/
theorem netContract_mps_eq (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) :
    netContract (mpsNet n d D A) (mpsEnc n d D A x)
      = ∑ β : Fin (n + 1) → Fin D,
          ((∏ i : Fin n, A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0) := by
  have hprod : ∀ β : Fin (n + 1) → Fin D,
      ((∏ i : Fin n, A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0)
      = ∏ v : Fin (n + 2), (mpsNet n d D A).tensor v
          (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
            ((edgeIdxEquiv n d D A).symm β) h.val) := by
    intro β
    set T : Fin (n + 2) → ℂ := fun v => (mpsNet n d D A).tensor v
      (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x)
        ((edgeIdxEquiv n d D A).symm β) h.val)
    have h1 : (∏ v : Fin (n + 2), T v)
        = (∏ v : Fin (n + 1), T (Fin.castSucc v)) * T (Fin.last (n + 1)) :=
      Fin.prod_univ_castSucc T
    have h2 : (∏ v : Fin (n + 1), T (Fin.castSucc v))
        = (∏ i : Fin n, T (Fin.castSucc (Fin.castSucc i)))
          * T (Fin.castSucc (Fin.last n)) :=
      Fin.prod_univ_castSucc (fun v => T (Fin.castSucc v))
    rw [h1, h2]
    have hs : ∀ i : Fin n, T (Fin.castSucc (Fin.castSucc i))
        = A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
            (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩) := fun i =>
      siteTensor_eq n d D A x β (Fin.castSucc (Fin.castSucc i)) i.isLt
    have hcL : T (Fin.castSucc (Fin.last n))
        = if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0 :=
      capLTensor_eq n d D A x β
    have hcR : T (Fin.last (n + 1))
        = if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0 :=
      capRTensor_eq n d D A x β
    rw [Finset.prod_congr rfl (fun i _ => hs i), hcL, hcR]
  rw [netContract]
  rw [← Fintype.sum_equiv (edgeIdxEquiv n d D A).symm
      (fun β : Fin (n + 1) → Fin D =>
        ((∏ i : Fin n, A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
            (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
          * (if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0))
        * (if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0))
      (fun e : ∀ i : InternalEdge (mpsNet n d D A), Fin ((mpsNet n d D A).dims i.val) =>
        ∏ v : Fin (mpsNet n d D A).nv, (mpsNet n d D A).tensor v
          (fun h => portValue (mpsNet n d D A) (mpsEnc n d D A x) e h.val))
      hprod]

/-- Extends the internal bond assignment by fixing both outer bond indices to zero. -/
def capPin (n D : ℕ) [NeZero D] (α : Fin (n - 1) → Fin D) : Fin (n + 1) → Fin D :=
  fun j => dite ((j : ℕ) = 0) (fun _ => 0) (fun h1 =>
    dite ((j : ℕ) = n) (fun _ => 0) (fun h2 =>
      α ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩))

/-- Restricts a full capped-chain bond assignment to its internal bond indices. -/
def capUnpin (n D : ℕ) (β : Fin (n + 1) → Fin D) : Fin (n - 1) → Fin D :=
  fun j => β ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩

/-- Restricting an assignment extended by `capPin` recovers each original internal bond index. -/
theorem capUnpin_pin (n D : ℕ) [NeZero D] (α : Fin (n - 1) → Fin D)
    (j : Fin (n - 1)) : capUnpin n D (capPin n D α) j = α j := by
  show capPin n D α ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ = α j
  simp only [capPin]
  rw [dite_eq_right (by have := j.isLt; omega : ¬((j : ℕ) + 1 = 0)),
    dite_eq_right (by have := j.isLt; omega : ¬((j : ℕ) + 1 = n))]
  rfl

/-- A bond assignment with both boundary indices zero is recovered by restricting it and then
applying `capPin`. -/
theorem capPin_unpin {n D : ℕ} [NeZero D] (β : Fin (n + 1) → Fin D)
    (h0 : (β ⟨0, by omega⟩ : Fin D).val = 0) (hn : (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0) :
    capPin n D (capUnpin n D β) = β := by
  funext j
  rcases Nat.lt_trichotomy (j : ℕ) 0 with hlt | heq | hgt
  · exact absurd hlt (by omega)
  · have hj0 : j = (0 : Fin (n + 1)) := Fin.ext heq
    rw [hj0]
    have h0' : β ((0 : Fin (n + 1))) = (0 : Fin D) :=
      Fin.ext (by simp only [Fin.val_zero]; exact h0)
    simp only [capPin]
    exact h0'.symm
  · rcases Nat.lt_trichotomy (j : ℕ) n with hlt | heq | hgt
    · simp only [capPin]
      rw [dite_eq_right (by omega : ¬((j : ℕ) = 0)),
        dite_eq_right (by omega : ¬((j : ℕ) = n))]
      exact congrArg β (Fin.ext (by show ((j : ℕ) - 1) + 1 = (j : ℕ); omega))
    · have hjn : j = ⟨(n : ℕ), by omega⟩ := Fin.ext heq
      rw [hjn]
      have hn' : β ⟨(n : ℕ), by omega⟩ = (0 : Fin D) :=
        Fin.ext (by simp only [Fin.val_zero]; exact hn)
      simp only [capPin]
      rw [dite_eq_right (by omega : ¬((n : ℕ) = 0)), dite_eq_left trivial]
      exact hn'.symm
    · exact absurd hgt (by have := j.isLt; omega)

/-- Equality of two capped bond assignments implies equality of their internal assignments. -/
theorem capPin_inj {n D : ℕ} [NeZero D] (α α' : Fin (n - 1) → Fin D)
    (h : capPin n D α = capPin n D α') : α = α' := by
  funext j
  have h1 : capPin n D α ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
      = capPin n D α' ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ :=
    congrFun h ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
  simp only [capPin,
    dite_eq_right (by have := j.isLt; omega : ¬((j : ℕ) + 1 = 0)),
    dite_eq_right (by have := j.isLt; omega : ¬((j : ℕ) + 1 = n))] at h1
  have hl : α j = α ⟨(j : ℕ) + 1 - 1, by have := j.isLt; omega⟩ :=
    congrArg α (Fin.ext (by show (j : ℕ) = (j : ℕ) + 1 - 1; omega))
  have hr : α' ⟨(j : ℕ) + 1 - 1, by have := j.isLt; omega⟩ = α' j :=
    congrArg α' (Fin.ext (by show (j : ℕ) + 1 - 1 = (j : ℕ); omega))
  exact hl.trans (h1.trans hr)

/-- The image of `capPin` consists exactly of bond assignments whose two boundary indices are
zero. -/
theorem capPin_image_eq (n D : ℕ) [NeZero D] :
    (Finset.univ.image (capPin n D) : Finset (Fin (n + 1) → Fin D))
      = Finset.univ.filter (fun β : Fin (n + 1) → Fin D =>
          (β ⟨0, by omega⟩ : Fin D).val = 0 ∧ (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0) := by
  ext β
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨α, hα⟩
    subst hα
    refine ⟨?_, ?_⟩
    · show (capPin n D α ⟨0, by omega⟩ : Fin D).val = 0
      simp only [capPin]
      simp only [dite_eq_left trivial, Fin.val_zero]
    · show (capPin n D α ⟨(n : ℕ), by omega⟩ : Fin D).val = 0
      simp only [capPin]
      by_cases hn0 : (n : ℕ) = 0
      · simp only [dite_eq_left hn0, Fin.val_zero]
      · simp only [dite_eq_right hn0, dite_eq_left trivial, Fin.val_zero]
  · rintro ⟨h0, hn⟩
    exact ⟨capUnpin n D β, capPin_unpin β h0 hn⟩

/-- The capped bond index immediately left of site `i` equals `mpsLeftIdx` of the internal
assignment. -/
theorem capPin_left {n D : ℕ} [NeZero D] (α : Fin (n - 1) → Fin D) {i : ℕ} (hi : i < n) :
    capPin n D α ⟨i, by omega⟩ = mpsLeftIdx α ⟨i, hi⟩ := by
  simp only [capPin, mpsLeftIdx]
  by_cases h0 : i = 0
  · rw [dite_eq_left h0, ite_eq_left h0]
  · rw [dite_eq_right h0, ite_eq_right h0, dite_eq_right (by omega : ¬(i = n)),
      dite_eq_left (by omega : i - 1 < n - 1)]

/-- The capped bond index immediately right of site `i` equals `mpsRightIdx` of the internal
assignment. -/
theorem capPin_right {n D : ℕ} [NeZero D] (α : Fin (n - 1) → Fin D) {i : ℕ} (hi : i < n) :
    capPin n D α ⟨i + 1, by omega⟩ = mpsRightIdx α ⟨i, hi⟩ := by
  simp only [capPin, mpsRightIdx]
  rw [dite_eq_right (by omega : ¬(i + 1 = 0))]
  by_cases hn : i + 1 = n
  · rw [dite_eq_left hn, dite_eq_right (by omega : ¬(i < n - 1))]
  · rw [dite_eq_right hn, dite_eq_left (by omega : i < n - 1)]
    rfl

/-- The sum over full bond assignments with both boundary indices constrained to zero equals the
MPS amplitude. -/
theorem normalForm_eq_amplitude {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    ∑ β : Fin (n + 1) → Fin D,
          ((∏ i : Fin n, A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0)
      = mpsAmplitude A x := by
  have hite : ∀ β : Fin (n + 1) → Fin D,
      (((∏ i : Fin n, A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(n : ℕ), by omega⟩).val = 0 then (1 : ℂ) else 0))
      = if (β ⟨0, by omega⟩ : Fin D).val = 0 ∧ (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0
          then (∏ i : Fin n, A ⟨(i : ℕ), i.isLt⟩ (x ⟨(i : ℕ), i.isLt⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
          else 0 := by
    intro β
    by_cases h0 : (β ⟨0, by omega⟩ : Fin D).val = 0
    · by_cases hn : (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0
      · rw [ite_eq_left h0, ite_eq_left hn, ite_eq_left ⟨h0, hn⟩, mul_one, mul_one]
      · rw [ite_eq_left h0, ite_eq_right hn, mul_one, mul_zero,
          ite_eq_right (fun hc => hn hc.2)]
    · by_cases hn : (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0
      · rw [ite_eq_right h0, ite_eq_left hn, mul_zero, zero_mul,
          ite_eq_right (fun hc => h0 hc.1)]
      · rw [ite_eq_right h0, ite_eq_right hn, mul_zero,
          ite_eq_right (fun hc => h0 hc.1)]
  rw [Finset.sum_congr rfl (fun β _ => hite β), ← Finset.sum_filter,
    ← capPin_image_eq, Finset.sum_image (fun α _ α' _ h => capPin_inj α α' h)]
  rw [mpsAmplitude]
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  have hl : capPin n D α ⟨(i : ℕ), by omega⟩ = mpsLeftIdx α ⟨(i : ℕ), i.isLt⟩ :=
    capPin_left α i.isLt
  have hr : capPin n D α ⟨(i : ℕ) + 1, by omega⟩ = mpsRightIdx α ⟨(i : ℕ), i.isLt⟩ :=
    capPin_right α i.isLt
  rw [hl, hr]

/-- Contracting the capped MPS network at the encoded physical configuration gives `mpsAmplitude
A x`. -/
theorem netContract_mpsNet_eq_mpsAmplitude (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    netContract (mpsNet n d D A) (mpsEnc n d D A x) = mpsAmplitude A x :=
  (netContract_mps_eq n d D A x).trans (normalForm_eq_amplitude A x)

end MainThm

section Clause14Counterexample

open scoped BigOperators

/-- The all-ones `2 × 2` tensor family for a one-site system with physical dimension one and
bond dimension two. -/
def clause14BadA : Fin 1 → Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ _ => Matrix.of fun _ _ => 1

/-- The zero-boundary MPS amplitude of `clause14BadA` at the unique physical configuration is
one. -/
theorem clause14Amplitude_eq_one :
    mpsAmplitude (n := 1) (d := 1) (D := 2) clause14BadA (fun _ => 0) = 1 := by
  simp [mpsAmplitude, mpsLeftIdx, mpsRightIdx, clause14BadA]

/-- The value of `mpsEval` on `clause14BadA` at the unique physical configuration is two. -/
theorem clause14Eval_eq_two :
    mpsEval (n := 1) (d := 1) (D := 2) clause14BadA (fun _ => 0) = 2 := by
  have hv : mpsEvalVector clause14BadA (fun _ => 0) (⟨0, by omega⟩ : Fin 1)
      = fun _ => (1 : ℂ) := by
    simp only [mpsEvalVector.eq_def, clause14BadA, Matrix.of_apply]
  show (∑ j : Fin 2, mpsEvalVector clause14BadA (fun _ => 0) (⟨0, by omega⟩ : Fin 1) j) = 2
  rw [hv]
  simp

/-- For `clause14BadA`, `mpsEval` differs from the zero-boundary MPS amplitude. -/
theorem clause14Eval_ne_amplitude :
    mpsEval (n := 1) (d := 1) (D := 2) clause14BadA (fun _ => 0)
      ≠ mpsAmplitude (n := 1) (d := 1) (D := 2) clause14BadA (fun _ => 0) := by
  rw [clause14Eval_eq_two, clause14Amplitude_eq_one]
  norm_num

/-- The displayed conjunction of universal evaluation, resource, inner-product, sampling, and
PEPS claims is false, since its first evaluation identity fails. -/
theorem clause3_counter : ¬ (

  (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d),
      @mpsEval n d D ℂ _ hn hD A x = @mpsAmplitude n d D hD A x)

  ∧ (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d),
      (@mpsEvalWithCount n d D ℂ _ hn hD A x).1 = @mpsAmplitude n d D hD A x ∧
        (@mpsEvalWithCount n d D ℂ _ hn hD A x).2 ≤ mpsEvalOpCount n D)

  ∧ (∀ (n d D B : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℚ) (x : Fin n → Fin d),
      (∀ i y a b, ratEntryWidth (A i y a b) ≤ B) →
      (∀ i j, ratEntryWidth (@mpsEvalVector n d D ℚ _ hD A x i j)
          ≤ n * (B + Nat.log2 D + 2))
        ∧ (@mpsEvalWithCount n d D ℚ _ hn hD A x).2
            * ringOpBitCost (n * (B + Nat.log2 D + 2))
          ≤ mpsEvalOpCount n D
            * ringOpBitCost (n * B + n * (Nat.log2 D + 2) + 2)
        ∧ D * (n * (B + Nat.log2 D + 2) + 1)
          ≤ D * (n * B + n * (Nat.log2 D + 2) + 2))

  ∧ (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      (@mpsInnerEvalWithCount n d D hn hD A B).1
        = ∑ x, conj (@mpsAmplitude n d D hD A x) * @mpsAmplitude n d D hD B x
        ∧ (@mpsInnerEvalWithCount n d D hn hD A B).2 ≤ mpsInnerOpCount n d D)

  ∧ (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
      (O : Matrix (Fin d) (Fin d) ℂ),
      @mpsInnerEval n d D hn hD A (@obsTensors n d D hD A z O)
        = ∑ x, conj (@mpsAmplitude n d D hD A x)
            * ∑ y : Fin d, O (x z) y * @mpsAmplitude n d D hD A (Function.update x z y))

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
      (@pepsStripEvalWithCount a b d D hD T x).1 = @pepsAmplitude a b d D hD T x
        ∧ (@pepsStripEvalWithCount a b d D hD T x).2 ≤ pepsStripOpCount a b D)
  ) :=
  fun H => clause14Eval_ne_amplitude (H.1 1 1 2 (⟨by decide⟩ : NeZero 1) (⟨by decide⟩ : NeZero 2) clause14BadA (fun _ => 0))

end Clause14Counterexample

section ThresholdClause1

variable {n d D : ℕ}

/-- Packages an internal bond position `k ≥ c` as an index in the right-bond subtype. -/
def thresholdGoalRB (n c : ℕ) (k : ℕ) (h1 : k < n - 1) (h2 : c ≤ k) :
    {j : Fin (n - 1) // c ≤ (j : ℕ)} := ⟨⟨k, h1⟩, h2⟩

/-- The underlying finite index of `thresholdGoalRB` is the original index `k`. -/
theorem thresholdGoalRB_val (n c : ℕ) (k : ℕ) (h1 : k < n - 1) (h2 : c ≤ k) :
    (thresholdGoalRB n c k h1 h2 : Fin (n - 1)) = ⟨k, h1⟩ := rfl

/-- At a nontrivial cut `1 ≤ c < n`, combines left internal bonds, the cut bond, and right
internal bonds into a full internal bond assignment. -/
def thresholdGoalBondEnc (c : ℕ) (h1 : 1 ≤ c) (_hn : c < n)
    (p : (Fin (c - 1) → Fin D) × Fin D × ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D)) :
    Fin (n - 1) → Fin D := fun j =>
  if h : (j : ℕ) < c - 1 then p.1 ⟨(j : ℕ), h⟩
  else if h2 : (j : ℕ) = c - 1 then p.2.1
  else p.2.2 (thresholdGoalRB n c (j : ℕ) (by have hj := j.isLt; omega) (by omega))

/-- At a nontrivial cut `1 ≤ c < n`, splits an internal bond assignment into its left portion,
cut index, and right portion. -/
def thresholdGoalBondDec (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) (α : Fin (n - 1) → Fin D) :
    (Fin (c - 1) → Fin D) × Fin D × ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D) :=
  (fun j => α ⟨(j : ℕ), by have hj := j.isLt; omega⟩,
    α ⟨c - 1, by omega⟩,
    fun j => α j)

/-- Encoding the three parts obtained from a bond assignment recovers that assignment. -/
theorem thresholdGoalBondEnc_dec (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) (α : Fin (n - 1) → Fin D) :
    thresholdGoalBondEnc c h1 hn (thresholdGoalBondDec c h1 hn α) = α := by
  funext j
  by_cases h : (j : ℕ) < c - 1
  · simp only [thresholdGoalBondEnc, thresholdGoalBondDec, dite_eq_left h]
  · by_cases h2 : (j : ℕ) = c - 1
    · simp only [thresholdGoalBondEnc, thresholdGoalBondDec, dite_eq_right h, dite_eq_left h2]
      exact congrArg α (Fin.ext h2.symm)
    · simp only [thresholdGoalBondEnc, thresholdGoalBondDec, dite_eq_right h, dite_eq_right h2,
        thresholdGoalRB_val]

/-- Decoding an encoded triple of bond data recovers the triple. -/
theorem thresholdGoalBondDec_enc (c : ℕ) (h1 : 1 ≤ c) (hn : c < n)
    (p : (Fin (c - 1) → Fin D) × Fin D × ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D)) :
    thresholdGoalBondDec c h1 hn (thresholdGoalBondEnc c h1 hn p) = p := by
  obtain ⟨σ, β, τ⟩ := p
  have hσ : (fun (j : Fin (c - 1)) => (thresholdGoalBondEnc c h1 hn (σ, β, τ)) ⟨(j : ℕ),
      by have hj := j.isLt; omega⟩) = σ := by
    funext j
    by_cases h : (j : ℕ) < c - 1
    · simp only [thresholdGoalBondEnc, dite_eq_left h]
    · exact absurd j.isLt h
  have hβ : (thresholdGoalBondEnc c h1 hn (σ, β, τ)) ⟨c - 1, by omega⟩ = β := by
    simp [thresholdGoalBondEnc]
  have hτ : (fun (j : {j : Fin (n - 1) // c ≤ (j : ℕ)}) =>
      (thresholdGoalBondEnc c h1 hn (σ, β, τ)) j) = τ := by
    funext j
    have h : ¬((j : ℕ) < c - 1) := by omega
    have h2 : ¬((j : ℕ) = c - 1) := by omega
    simp only [thresholdGoalBondEnc, dite_eq_right h, dite_eq_right h2]
    exact congrArg τ (Subtype.ext (Fin.ext rfl))
  simp only [thresholdGoalBondDec]
  exact Prod.ext hσ (Prod.ext hβ hτ)

/-- At a nontrivial cut `1 ≤ c < n`, the equivalence between full internal bond assignments and
left bonds, a cut index, and right bonds. -/
def thresholdGoalBondSplit (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) :
    (Fin (c - 1) → Fin D) × Fin D × ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D) ≃
      (Fin (n - 1) → Fin D) :=
  ⟨thresholdGoalBondEnc c h1 hn, thresholdGoalBondDec c h1 hn,
    thresholdGoalBondDec_enc c h1 hn, thresholdGoalBondEnc_dec c h1 hn⟩

/-- The forward map of `thresholdGoalBondSplit` is `thresholdGoalBondEnc` at every bond
position. -/
theorem thresholdGoalBondSplit_apply (c : ℕ) (h1 : 1 ≤ c) (hn : c < n)
    (p : (Fin (c - 1) → Fin D) × Fin D × ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D))
    (j : Fin (n - 1)) : thresholdGoalBondSplit c h1 hn p j = thresholdGoalBondEnc c h1 hn p j := rfl

/-- The left partial contraction matrix at a nontrivial cut `1 ≤ c < n`, indexed by left
physical configurations and the cut bond. -/
noncomputable def thresholdGoalLeft [NeZero D] (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (c : ℕ)
    (h1 : 1 ≤ c) (hn : c < n) : Matrix (Fin (d ^ c)) (Fin D) ℂ :=
  Matrix.of fun u β =>
    ∑ σ : Fin (c - 1) → Fin D,
      ∏ i : Fin c,
        A ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩
          ((finPowEnc d c).symm u ⟨(i : ℕ), i.isLt⟩)
          (if h0 : (i : ℕ) = 0 then 0
            else σ ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩)
          (if h1' : (i : ℕ) < c - 1 then σ ⟨(i : ℕ), h1'⟩ else β)

/-- The right partial contraction matrix at a nontrivial cut `1 ≤ c < n`, indexed by the cut
bond and right physical configurations. -/
noncomputable def thresholdGoalRight [NeZero D] (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (c : ℕ)
    (h1 : 1 ≤ c) (hn : c < n) : Matrix (Fin D) (Fin (d ^ (n - c))) ℂ :=
  Matrix.of fun β w =>
    ∑ τ : {j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D,
      ∏ j : Fin (n - c),
        A ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩
          ((finPowEnc d (n - c)).symm w ⟨(j : ℕ), j.isLt⟩)
          (if h0 : (j : ℕ) = 0 then β
            else τ (thresholdGoalRB n c (c + (j : ℕ) - 1) (by have hj := j.isLt; omega)
              (by have hj := j.isLt; omega)))
          (if hlt : (j : ℕ) < n - c - 1 then
            τ (thresholdGoalRB n c (c + (j : ℕ)) (by have hj := j.isLt; omega) (by omega))
          else 0)

/-- Splits a product over `Fin n` into the product over the first `c` positions and the
remaining positions, for `c ≤ n`. -/
theorem prod_split_fin (F : Fin n → ℂ) (c : ℕ) (hcn : c ≤ n) :
    (∏ i : Fin n, F i) =
      (∏ i : Fin c, F ⟨(i : ℕ), by have hi := i.isLt; omega⟩) *
        (∏ j : Fin (n - c), F ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩) := by
  set g : ℕ → ℂ := fun k => if hk : k < n then F ⟨k, hk⟩ else 1 with hg
  have h1 : (∏ i : Fin n, F i) = ∏ k ∈ Finset.range n, g k := by
    rw [← Fin.prod_univ_eq_prod_range g]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hg, dite_eq_left i.isLt]
  have hsplit : (Finset.range n : Finset ℕ) =
      Finset.range c ∪ (Finset.range (n - c)).image (fun k => c + k) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hk
      by_cases h : k < c
      · exact Or.inl h
      · exact Or.inr ⟨k - c, by omega, by omega⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · omega
      · omega
  have hdisj : Disjoint (Finset.range c)
      ((Finset.range (n - c)).image (fun k => c + k)) := by
    refine Finset.disjoint_left.mpr (fun a ha hat => ?_)
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_image, Finset.mem_range] at hat
    obtain ⟨j, hj, rfl⟩ := hat
    omega
  have hinj : Set.InjOn (fun k : ℕ => c + k) (↑(Finset.range (n - c))) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    simp only at hab
    omega
  rw [h1, hsplit, Finset.prod_union hdisj, Finset.prod_image hinj]
  have hA : ∏ k ∈ Finset.range c, g k =
      ∏ i : Fin c, F ⟨(i : ℕ), by have hi := i.isLt; omega⟩ := by
    rw [← Fin.prod_univ_eq_prod_range g]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hkn : (i : ℕ) < n := by have hi := i.isLt; omega
    simp only [hg, dite_eq_left hkn]
  have hB : ∏ k ∈ Finset.range (n - c), g (c + k) =
      ∏ j : Fin (n - c), F ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩ := by
    rw [← Fin.prod_univ_eq_prod_range (fun k => g (c + k))]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have hkn : c + (j : ℕ) < n := by have hj := j.isLt; omega
    simp only [hg, dite_eq_left hkn]
  rw [hA, hB]

/-- Reading a position before the cut from `splitJoin` recovers the corresponding left
configuration entry. -/
theorem splitJoin_left (c : ℕ) (_h1 : 1 ≤ c) (hn : c < n) (u : Fin c → Fin d) (w : Fin (n - c) → Fin d) (i : Fin c) :
    splitJoin n c d u w ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩ = u ⟨(i : ℕ), i.isLt⟩ := by
  simp only [splitJoin, dite_eq_left i.isLt]

/-- Reading a position after the cut from `splitJoin` recovers the corresponding right
configuration entry. -/
theorem splitJoin_right (c : ℕ) (_h1 : 1 ≤ c) (_hn : c < n) (u : Fin c → Fin d) (w : Fin (n - c) → Fin d) (j : Fin (n - c)) :
    splitJoin n c d u w ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩ = w ⟨(j : ℕ), j.isLt⟩ := by
  have h : ¬(c + (j : ℕ) < c) := by omega
  simp only [splitJoin, dite_eq_right h]
  exact congrArg w (Fin.ext (show (c : ℕ) + (j : ℕ) - c = (j : ℕ) from by omega))

/-- On the left block, the encoded left bond index is zero at the boundary and otherwise comes
from the left internal assignment. -/
theorem mpsLeftIdx_left [NeZero D] (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) (p : (Fin (c - 1) → Fin D) × Fin D ×
      ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D)) (i : Fin c) :
    mpsLeftIdx (thresholdGoalBondEnc c h1 hn p) ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩ =
      (if h0 : (i : ℕ) = 0 then 0
        else p.1 ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩) := by
  simp only [mpsLeftIdx, thresholdGoalBondEnc]
  by_cases hi : (i : ℕ) = 0
  · simp [hi]
  · have hi2 : (i : ℕ) - 1 < n - 1 := by have hk := i.isLt; omega
    have hi3 : (i : ℕ) - 1 < c - 1 := by have hk := i.isLt; omega
    simp [hi, hi2, hi3]

/-- On the left block, the encoded right bond index comes from the left assignment except at the
cut, where it is the cut index. -/
theorem mpsRightIdx_left [NeZero D] (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) (p : (Fin (c - 1) → Fin D) × Fin D ×
      ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D)) (i : Fin c) :
    mpsRightIdx (thresholdGoalBondEnc c h1 hn p) ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩ =
      (if h1' : (i : ℕ) < c - 1 then p.1 ⟨(i : ℕ), h1'⟩ else p.2.1) := by
  simp only [mpsRightIdx, thresholdGoalBondEnc]
  have hi : (i : ℕ) < n - 1 := by have hk := i.isLt; omega
  simp only [dite_eq_left hi]
  by_cases h : (i : ℕ) < c - 1
  · simp [h]
  · have h2 : (i : ℕ) = c - 1 := by have hk := i.isLt; omega
    simp [h2]

/-- On the right block, the encoded left bond index is the cut index at the first site and
otherwise comes from the right assignment. -/
theorem mpsLeftIdx_right [NeZero D] (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) (p : (Fin (c - 1) → Fin D) × Fin D ×
      ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D)) (j : Fin (n - c)) :
    mpsLeftIdx (thresholdGoalBondEnc c h1 hn p) ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩ =
      (if h0 : (j : ℕ) = 0 then p.2.1
        else p.2.2 (thresholdGoalRB n c (c + (j : ℕ) - 1) (by have hj := j.isLt; omega)
          (by omega))) := by
  simp only [mpsLeftIdx, thresholdGoalBondEnc]
  have hi : (c : ℕ) + (j : ℕ) ≠ 0 := by omega
  have hi2 : (c : ℕ) + (j : ℕ) - 1 < n - 1 := by have hj := j.isLt; omega
  have hc0 : c ≠ 0 := by omega
  simp only [dite_eq_left hi2]
  by_cases h : (j : ℕ) = 0
  · have h2 : (c : ℕ) + (j : ℕ) - 1 = c - 1 := by omega
    have h3 : ¬((c : ℕ) + (j : ℕ) - 1 < c - 1) := by omega
    simp [h, hc0]
  · have h2 : ¬((c : ℕ) + (j : ℕ) - 1 < c - 1) := by omega
    have h3 : ¬((c : ℕ) + (j : ℕ) - 1 = c - 1) := by omega
    simp [h2, h3, h, hc0]

/-- On the right block, the encoded right bond index comes from the right assignment except at
the outer boundary, where it is zero. -/
theorem mpsRightIdx_right [NeZero D] (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) (p : (Fin (c - 1) → Fin D) × Fin D ×
      ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D)) (j : Fin (n - c)) :
    mpsRightIdx (thresholdGoalBondEnc c h1 hn p) ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩ =
      (if hlt : (j : ℕ) < n - c - 1 then
        p.2.2 (thresholdGoalRB n c (c + (j : ℕ)) (by omega) (by omega))
      else 0) := by
  simp only [mpsRightIdx, thresholdGoalBondEnc]
  by_cases h : (c : ℕ) + (j : ℕ) < n - 1
  · have h2 : ¬((c : ℕ) + (j : ℕ) < c - 1) := by omega
    have h3 : ¬((c : ℕ) + (j : ℕ) = c - 1) := by omega
    have hlt : (j : ℕ) < n - c - 1 := by omega
    simp [h, h2, h3, hlt]
  · have hlt : ¬((j : ℕ) < n - c - 1) := by omega
    simp [h, hlt]

/-- At a nontrivial cut, the cut matrix of an MPS factors as `thresholdGoalLeft *
thresholdGoalRight`. -/
theorem cutMatrix_eq [NeZero D] (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (ψ : (Fin n → Fin d) → ℂ) (hψ : IsMpsRepresentation A ψ)
    (c : ℕ) (h1 : 1 ≤ c) (hn : c < n) :
    cutMatrix n d ψ c = thresholdGoalLeft A c h1 hn * thresholdGoalRight A c h1 hn := by
  ext u w
  simp only [Matrix.mul_apply, cutMatrix, Matrix.of_apply]
  rw [← hψ (splitJoin n c d ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w))]
  simp only [mpsAmplitude]
  rw [← Fintype.sum_equiv (thresholdGoalBondSplit c h1 hn)
    (fun p => ∏ i : Fin n,
      A i (splitJoin n c d ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w) i)
        (mpsLeftIdx (thresholdGoalBondEnc c h1 hn p) i) (mpsRightIdx (thresholdGoalBondEnc c h1 hn p) i))
    (fun α => ∏ i : Fin n,
      A i (splitJoin n c d ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w) i)
        (mpsLeftIdx α i) (mpsRightIdx α i)) (fun p => rfl)]
  have hprod : ∀ p : (Fin (c - 1) → Fin D) × Fin D × ({j : Fin (n - 1) // c ≤ (j : ℕ)} → Fin D),
      (∏ i : Fin n,
        A i (splitJoin n c d ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w) i)
          (mpsLeftIdx (thresholdGoalBondEnc c h1 hn p) i) (mpsRightIdx (thresholdGoalBondEnc c h1 hn p) i))
      = (∏ i : Fin c,
          A ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩
            ((finPowEnc d c).symm u ⟨(i : ℕ), i.isLt⟩)
            (if h0 : (i : ℕ) = 0 then 0
              else p.1 ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩)
            (if h1' : (i : ℕ) < c - 1 then p.1 ⟨(i : ℕ), h1'⟩ else p.2.1))
        * (∏ j : Fin (n - c),
          A ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩
            ((finPowEnc d (n - c)).symm w ⟨(j : ℕ), j.isLt⟩)
            (if h0 : (j : ℕ) = 0 then p.2.1
              else p.2.2 (thresholdGoalRB n c (c + (j : ℕ) - 1) (by omega) (by omega)))
            (if hlt : (j : ℕ) < n - c - 1 then
              p.2.2 (thresholdGoalRB n c (c + (j : ℕ)) (by omega) (by omega))
            else 0)) := by
    intro p
    rw [prod_split_fin _ c (by omega)]
    congr 1
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      show A ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩
          (splitJoin n c d ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w)
            ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩)
          (mpsLeftIdx (thresholdGoalBondEnc c h1 hn p) ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩)
          (mpsRightIdx (thresholdGoalBondEnc c h1 hn p) ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩)
        = A ⟨(i : ℕ), Nat.lt_trans i.isLt hn⟩
          ((finPowEnc d c).symm u ⟨(i : ℕ), i.isLt⟩)
          (if h0 : (i : ℕ) = 0 then 0
            else p.1 ⟨(i : ℕ) - 1, by have hi := i.isLt; omega⟩)
          (if h1' : (i : ℕ) < c - 1 then p.1 ⟨(i : ℕ), h1'⟩ else p.2.1)
      rw [splitJoin_left c h1 hn ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w) i,
        mpsLeftIdx_left c h1 hn p i,
        mpsRightIdx_left c h1 hn p i]
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      show A ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩
          (splitJoin n c d ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w)
            ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩)
          (mpsLeftIdx (thresholdGoalBondEnc c h1 hn p) ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩)
          (mpsRightIdx (thresholdGoalBondEnc c h1 hn p) ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩)
        = A ⟨c + (j : ℕ), by have hj := j.isLt; omega⟩
          ((finPowEnc d (n - c)).symm w ⟨(j : ℕ), j.isLt⟩)
          (if h0 : (j : ℕ) = 0 then p.2.1
            else p.2.2 (thresholdGoalRB n c (c + (j : ℕ) - 1) (by omega) (by omega)))
          (if hlt : (j : ℕ) < n - c - 1 then
            p.2.2 (thresholdGoalRB n c (c + (j : ℕ)) (by omega) (by omega))
          else 0)
      rw [splitJoin_right c h1 hn ((finPowEnc d c).symm u) ((finPowEnc d (n - c)).symm w) j,
        mpsLeftIdx_right c h1 hn p j,
        mpsRightIdx_right c h1 hn p j]
  simp only [hprod, thresholdGoalLeft, thresholdGoalRight, Matrix.of_apply]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul_sum]

/-- Every cut `c < n` of a state represented by bond-dimension-`D` MPS tensors has cut rank at
most `D`. -/
theorem cutRank_le_of_isMps [NeZero D] (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (ψ : (Fin n → Fin d) → ℂ) (hψ : IsMpsRepresentation A ψ)
    (c : ℕ) (hc : c < n) : cutRank n d ψ c ≤ D := by
  by_cases hc0 : c = 0
  · subst hc0
    have hrank : cutRank n d ψ 0 = Matrix.rank (cutMatrix n d ψ 0) := rfl
    rw [hrank]
    refine le_trans (Matrix.rank_le_height _) ?_
    simp only [Nat.pow_zero]
    exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  · have h1 : 1 ≤ c := by omega
    have hfact := cutMatrix_eq A ψ hψ c h1 hc
    have hrank : cutRank n d ψ c = Matrix.rank (cutMatrix n d ψ c) := rfl
    rw [hrank, hfact]
    exact le_trans (Matrix.rank_mul_le_right _ _)
      (le_trans (Matrix.rank_le_height _) le_rfl)

/-- For a normalized state with an MPS representation of bond dimension `D`, every cut `c < n`
has rank at most `D`. -/
theorem clause2_clause1 (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ)
    (_hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∀ (D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation n d D hD A ψ → ∀ c : ℕ, c < n → cutRank n d ψ c ≤ D := by
  intro D hD A hψ c hc
  exact @cutRank_le_of_isMps n d D hD A ψ hψ c hc

end ThresholdClause1

section Clause1Periodic

variable {n d D : ℕ}

/-- Assigns dimension `D` to periodic bond half-edges and dimension `d` to physical legs. -/
def perDim (n d D : ℕ) (j : ℕ) : ℕ := if j < 2 * n then D else d

/-- A periodic bond half-edge has dimension `D`. -/
theorem perDim_bond (n d D : ℕ) {j : ℕ} (h : j < 2 * n) : perDim n d D j = D := by
  rw [perDim, ite_eq_left h]

/-- A half-edge beyond the periodic bond range has dimension `d`. -/
theorem perDim_phys (n d D : ℕ) {j : ℕ} (h : ¬(j < 2 * n)) : perDim n d D j = d := by
  rw [perDim, ite_eq_right h]

/-- Pairs consecutive bond half-edges in the periodic encoding and leaves physical legs
unpaired. -/
def perPartner (n : ℕ) (j : Fin (3 * n)) : Option (Fin (3 * n)) :=
  if h : (j : ℕ) < 2 * n then
    some ⟨if (j : ℕ) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1, by
      have := h
      split_ifs <;> omega⟩
  else none

/-- Assigns half-edges to the sites of the periodic chain, using cyclic predecessor indexing for
odd bond half-edges. -/
def perSite (n : ℕ) (j : Fin (3 * n)) : Fin n :=
  if h : (j : ℕ) < 2 * n then
    if (j : ℕ) % 2 = 0 then ⟨(j : ℕ) / 2, by have := h; omega⟩
    else ⟨((j : ℕ) / 2 + n - 1) % n, by
      by_cases hn0 : n = 0
      · subst hn0; simp at h
      · exact Nat.mod_lt _ (by omega)⟩
  else ⟨(j : ℕ) - 2 * n, by have := j.isLt; omega⟩

/-- In the periodic encoding, half-edge `2 * j` is paired with half-edge `2 * j + 1`. -/
theorem perPartner_even (n : ℕ) (j : Fin n) :
    perPartner n ⟨2 * (j : ℕ), by have := j.isLt; omega⟩
      = some ⟨2 * (j : ℕ) + 1, by have := j.isLt; omega⟩ := by
  have h : (2 * (j : ℕ) : ℕ) < 2 * n := by have := j.isLt; omega
  simp only [perPartner, dite_eq_left h]
  simp

/-- In the periodic encoding, half-edge `2 * j + 1` is paired with half-edge `2 * j`. -/
theorem perPartner_odd (n : ℕ) (j : Fin n) :
    perPartner n ⟨2 * (j : ℕ) + 1, by have := j.isLt; omega⟩
      = some ⟨2 * (j : ℕ), by have := j.isLt; omega⟩ := by
  have h : (2 * (j : ℕ) + 1 : ℕ) < 2 * n := by have := j.isLt; omega
  simp only [perPartner, dite_eq_left h]
  simp

/-- The even periodic bond half-edge `2 * i` belongs to site `i`. -/
theorem perSite_left (n : ℕ) (i : ℕ) (hi : i < n) :
    perSite n ⟨2 * i, by omega⟩ = ⟨i, by omega⟩ := by
  simp only [perSite]
  rw [dite_eq_left (by omega : (2 * i : ℕ) < 2 * n)]
  have h2 : (2 * i) % 2 = 0 := by omega
  rw [ite_eq_left h2]
  refine Fin.ext ?_
  show 2 * i / 2 = i
  omega

/-- The odd periodic bond half-edge `2 * i + 1` belongs to the cyclic predecessor of site `i`. -/
theorem perSite_right (n : ℕ) (i : ℕ) (hi : i < n) :
    perSite n ⟨2 * i + 1, by omega⟩ = ⟨(i + n - 1) % n, by
      by_cases hn0 : n = 0
      · subst hn0; exact absurd hi (by omega)
      · exact Nat.mod_lt _ (by omega)⟩ := by
  simp only [perSite]
  rw [dite_eq_left (by omega : (2 * i + 1 : ℕ) < 2 * n)]
  have h2 : (2 * i + 1) % 2 ≠ 0 := by omega
  rw [ite_eq_right h2]
  refine Fin.ext ?_
  show ((2 * i + 1) / 2 + n - 1) % n = (i + n - 1) % n
  have : (2 * i + 1) / 2 = i := by omega
  rw [this]

/-- The periodic physical leg numbered `2 * n + i` belongs to site `i`. -/
theorem perSite_phys (n : ℕ) (i : ℕ) (hi : i < n) :
    perSite n ⟨2 * n + i, by omega⟩ = ⟨i, by omega⟩ := by
  simp only [perSite]
  rw [dite_eq_right (by omega : ¬((2 * n + i : ℕ) < 2 * n))]
  refine Fin.ext ?_
  show 2 * n + i - 2 * n = i
  omega

/-- For `i < n` and positive `n`, taking a cyclic successor followed by a cyclic predecessor
returns `i`. -/
theorem add_mod_pred_eq (i n : ℕ) (hi : i < n) (hn : 0 < n) :
    (((i + 1) % n) + n - 1) % n = i := by
  have hlt : i + 1 < n ∨ i + 1 = n := by omega
  rcases hlt with hlt | heq
  · have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    have hcalc : (i + 1 + n - 1) = i + n := by omega
    rw [hcalc, Nat.add_mod, Nat.mod_self, Nat.add_zero]
    have h1 : i % n = i := Nat.mod_eq_of_lt hi
    simp only [h1]
  · have hmod : (i + 1) % n = 0 := by rw [heq, Nat.mod_self]
    rw [hmod, Nat.zero_add]
    have h1 : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    omega

/-- The odd bond half-edge at the cyclic successor of `i` belongs to site `i`. -/
theorem perSite_right' (n : ℕ) (i : ℕ) (hi : i < n) (hn : 0 < n) :
    perSite n ⟨2 * ((i + 1) % n) + 1, by
      have := Nat.mod_lt (i + 1) hn; omega⟩ = ⟨i, by omega⟩ := by
  rw [perSite_right n ((i + 1) % n) (Nat.mod_lt _ hn)]
  exact Fin.ext (add_mod_pred_eq i n hi hn)

/-- The odd half-edge at the cyclic successor of a site lies below `3 * n`. -/
theorem perLeg_bound (n : ℕ) (v : Fin n) :
    2 * (((v : ℕ) + 1) % n) + 1 < 3 * n := by
  by_cases hn0 : n = 0
  · subst hn0; exact absurd v.isLt (Nat.not_lt_zero _)
  · have h1 : ((v : ℕ) + 1) % n < n := Nat.mod_lt _ (by omega)
    have h2 : (v : ℕ) < n := v.isLt
    omega

/-- The odd half-edge at the cyclic successor of a site lies in the bond range below `2 * n`. -/
theorem perLeg_bound2 (n : ℕ) (v : Fin n) :
    2 * (((v : ℕ) + 1) % n) + 1 < 2 * n := by
  by_cases hn0 : n = 0
  · subst hn0; exact absurd v.isLt (Nat.not_lt_zero _)
  · have h1 : ((v : ℕ) + 1) % n < n := Nat.mod_lt _ (by omega)
    have h2 : (v : ℕ) < n := v.isLt
    omega

/-- The successor of a periodic bond half-edge index lies below `3 * n`. -/
theorem perJ_succ_bound (n : ℕ) (j : Fin (3 * n)) (h : (j : ℕ) < 2 * n) :
    (j : ℕ) + 1 < 3 * n := by
  by_cases hn0 : n = 0
  · subst hn0; exact absurd h (by omega)
  · have := j.isLt; omega

/-- The truncated predecessor of a periodic bond half-edge index lies below `3 * n`. -/
theorem perJ_pred_bound (n : ℕ) (j : Fin (3 * n)) (h : (j : ℕ) < 2 * n) :
    (j : ℕ) - 1 < 3 * n := by
  by_cases hn0 : n = 0
  · subst hn0; exact absurd h (by omega)
  · have := j.isLt; omega

/-- The local tensor of the periodic network, obtained from `A` using the site's physical leg
and two cyclic bond legs. -/
noncomputable def perTensor (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (v : Fin n)
    (a : ∀ h : {h : Fin (3 * n) // perSite n h = v}, Fin (perDim n d D h.val.val)) : ℂ :=
  A v
    (Fin.cast (perDim_phys n d D (by have := v.isLt; omega))
      (show Fin (perDim n d D (2 * n + (v : ℕ))) from
        a (Subtype.mk ⟨2 * n + (v : ℕ), by omega⟩ (by
          rw [perSite_phys n (v : ℕ) v.isLt]))))
    (Fin.cast (perDim_bond n d D (by show (2 * (v : ℕ) : ℕ) < 2 * n; have := v.isLt; omega))
      (show Fin (perDim n d D (2 * (v : ℕ))) from
        a (Subtype.mk ⟨2 * (v : ℕ), by omega⟩ (by
          rw [perSite_left n (v : ℕ) v.isLt]))))
    (Fin.cast (perDim_bond n d D (perLeg_bound2 n v))
      (show Fin (perDim n d D (2 * (((v : ℕ) + 1) % n) + 1)) from
        a (Subtype.mk ⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩
          (perSite_right' n (v : ℕ) v.isLt (by have := v.isLt; omega : 0 < n)))))

/-- If a periodic half-edge is paired with another, the latter is paired back with the former. -/
theorem perPartner_involution_aux (n : ℕ) (j k : Fin (3 * n))
    (hj : perPartner n j = some k) : perPartner n k = some j := by
  simp only [perPartner] at hj
  by_cases h : (j : ℕ) < 2 * n
  · rw [dite_eq_left h] at hj
    have hkval : (k : ℕ) = if (j : ℕ) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1 :=
      (congrArg Fin.val (Option.some.inj hj)).symm
    have hkbound : (k : ℕ) < 2 * n := by
      by_cases h2 : (j : ℕ) % 2 = 0
      · rw [hkval, ite_eq_left h2]; omega
      · rw [hkval, ite_eq_right h2]; omega
    simp only [perPartner, dite_eq_left hkbound]
    by_cases h2 : (j : ℕ) % 2 = 0
    · rw [ite_eq_left h2] at hkval
      have hkj : k = ⟨(j : ℕ) + 1, perJ_succ_bound n j h⟩ := by
        refine Fin.ext ?_
        rw [hkval]
      subst hkj
      have h3 : ((j : ℕ) + 1) % 2 ≠ 0 := by omega
      simp [h3]
    · rw [ite_eq_right h2] at hkval
      have hkj : k = ⟨(j : ℕ) - 1, perJ_pred_bound n j h⟩ := by
        refine Fin.ext ?_
        rw [hkval]
      subst hkj
      have h3 : ((j : ℕ) - 1) % 2 = 0 := by omega
      simp [h3]
      refine Fin.ext ?_
      show (j : ℕ) - 1 + 1 = (j : ℕ)
      have hj1 : 0 < (j : ℕ) := by
        rcases Nat.eq_zero_or_pos (j : ℕ) with hz | hp
        · rw [hz] at h2
          exact absurd (by decide : (0 : ℕ) % 2 = 0) h2
        · exact hp
      omega
  · rw [dite_eq_right h] at hj
    exact absurd hj (by simp)

/-- A paired periodic half-edge is distinct from its partner. -/
theorem perPartner_no_self (n : ℕ) (j k : Fin (3 * n))
    (hj : perPartner n j = some k) : j ≠ k := by
  intro heq
  subst heq
  simp only [perPartner] at hj
  by_cases h : (j : ℕ) < 2 * n
  · rw [dite_eq_left h] at hj
    have hkval : (j : ℕ) = if (j : ℕ) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1 :=
      (congrArg Fin.val (Option.some.inj hj)).symm
    by_cases h2 : (j : ℕ) % 2 = 0
    · rw [ite_eq_left h2] at hkval; omega
    · rw [ite_eq_right h2] at hkval; omega
  · rw [dite_eq_right h] at hj
    exact absurd hj (by simp)

/-- Paired half-edges in the periodic encoding have equal dimensions. -/
theorem perPartner_dims (n d D : ℕ) (j k : Fin (3 * n))
    (hj : perPartner n j = some k) :
    perDim n d D (j : ℕ) = perDim n d D (k : ℕ) := by
  simp only [perPartner] at hj
  by_cases h : (j : ℕ) < 2 * n
  · rw [dite_eq_left h] at hj
    have hkval : (k : ℕ) = if (j : ℕ) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1 :=
      (congrArg Fin.val (Option.some.inj hj)).symm
    have hkbound : (k : ℕ) < 2 * n := by
      by_cases h2 : (j : ℕ) % 2 = 0
      · rw [hkval, ite_eq_left h2]; omega
      · rw [hkval, ite_eq_right h2]; omega
    rw [perDim, perDim, ite_eq_left h, ite_eq_left hkbound]
  · rw [dite_eq_right h] at hj
    exact absurd hj (by simp)

/-- Encodes the tensor family `A` as a periodic tensor network with one physical leg and two
bond half-edges at each site. -/
noncomputable def perNet (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    TensorNet where
  nv := n
  nh := 3 * n
  dims := fun j => perDim n d D (j : ℕ)
  site := fun j => perSite n j
  partner := fun j => perPartner n j
  involution := by
    intro j k hj
    exact perPartner_involution_aux n j k hj
  no_self_loop := by
    intro j k hj
    exact perPartner_no_self n j k hj
  dims_match := by
    intro j k hj
    exact perPartner_dims n d D j k hj
  tensor := perTensor n d D A

/-- A half-edge with a partner in the periodic encoding lies below `2 * n`. -/
theorem perPartner_isSome (n : ℕ) {j k : Fin (3 * n)} (h : perPartner n j = some k) :
    (j : ℕ) < 2 * n := by
  simp only [perPartner] at h
  by_cases h' : (j : ℕ) < 2 * n
  · exact h'
  · rw [dite_eq_right h'] at h
    exact absurd h (by simp)

/-- An unpaired half-edge in the periodic encoding does not lie below `2 * n`. -/
theorem perPartner_none_lt (n : ℕ) {j : Fin (3 * n)} (h : perPartner n j = none) :
    ¬((j : ℕ) < 2 * n) := by
  intro hj
  simp only [perPartner, dite_eq_left hj] at h
  exact absurd h (by simp)

/-- The internal edge at bond position `b` in the periodic network. -/
def perBondEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (b : Fin n) : InternalEdge (perNet n d D A) :=
  ⟨⟨2 * (b : ℕ), by show 2 * (b : ℕ) < 3 * n; have := b.isLt; omega⟩,
    ⟨⟨2 * (b : ℕ) + 1, by show 2 * (b : ℕ) + 1 < 3 * n; have := b.isLt; omega⟩,
      perPartner_even n b,
      Fin.mk_lt_mk.mpr (by omega)⟩⟩

/-- Recovers the bond position of an internal edge in the periodic network. -/
def perHalfEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : InternalEdge (perNet n d D A)) : Fin n :=
  ⟨(i.val.val) / 2, by
    obtain ⟨k, hk, -⟩ := i.property
    have hb := perPartner_isSome n hk
    omega⟩

/-- Recovering the position of `perBondEdge b` returns `b`. -/
theorem perHalfEdge_bondEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (b : Fin n) : perHalfEdge n d D A (perBondEdge n d D A b) = b := by
  apply Fin.ext
  show (2 * (b : ℕ)) / 2 = (b : ℕ)
  omega

/-- Reconstructing a periodic internal edge from its bond position returns that edge. -/
theorem perBondEdge_halfEdge (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : InternalEdge (perNet n d D A)) : perBondEdge n d D A (perHalfEdge n d D A i) = i := by
  obtain ⟨k, hk, hlt⟩ := i.property
  have hb : (i.val : ℕ) < 2 * n := perPartner_isSome n hk
  have hk' : perPartner n i.val = some k := hk
  rw [perPartner, dite_eq_left hb] at hk'
  have hvk : (if (i.val : ℕ) % 2 = 0 then (i.val : ℕ) + 1 else (i.val : ℕ) - 1) = (k : ℕ) :=
    congrArg Fin.val (Option.some.inj hk')
  by_cases h2 : ((i.val : ℕ)) % 2 = 0
  · rw [ite_eq_left h2] at hvk
    refine Subtype.ext (Fin.ext ?_)
    show 2 * ((i.val.val) / 2) = (i.val : ℕ)
    omega
  · rw [ite_eq_right h2] at hvk
    exact absurd hlt (by omega)

/-- Encodes a physical configuration as an open-leg assignment of the periodic network. -/
noncomputable def perEnc (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (o : OpenLeg (perNet n d D A)) : Fin ((perNet n d D A).dims o.val) :=
  (x ⟨(o.val.val) - 2 * n, by
    have h := perPartner_none_lt n o.property
    have := o.val.isLt
    omega⟩).cast ((perDim_phys n d D (by
      have h := perPartner_none_lt n o.property
      omega)).symm)

/-- Identifies internal-edge assignments of the periodic network with functions `Fin n → Fin D`. -/
noncomputable def perEdgeIdxEquiv (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (∀ i : InternalEdge (perNet n d D A), Fin ((perNet n d D A).dims i.val)) ≃
      (Fin n → Fin D) where
  toFun e b :=
    (e (perBondEdge n d D A b)).cast
      (perDim_bond n d D (by show 2 * (b : ℕ) < 2 * n; have := b.isLt; omega))
  invFun β i :=
    (β (perHalfEdge n d D A i)).cast
      ((perDim_bond n d D (by
          show (i.val.val) < 2 * n
          obtain ⟨k, hk, -⟩ := i.property
          exact perPartner_isSome n hk)).symm)
  left_inv := by
    intro e
    funext i
    have hb : perBondEdge n d D A (perHalfEdge n d D A i) = i :=
      perBondEdge_halfEdge n d D A i
    exact Fin.ext (congrArg (fun j => (e j).val) hb)
  right_inv := by
    intro β
    funext b
    have hb : perHalfEdge n d D A (perBondEdge n d D A b) = b :=
      perHalfEdge_bondEdge n d D A b
    refine Fin.ext ?_
    show (β (perHalfEdge n d D A (perBondEdge n d D A b))).val = (β b).val
    rw [hb]

/-- The even half-edge at the cyclic successor of a bond position lies below `3 * n`. -/
theorem perM_bound (n : ℕ) (b : Fin n) : 2 * (((b : ℕ) + 1) % n) < 3 * n := by
  by_cases hn0 : n = 0
  · subst hn0; exact absurd b.isLt (Nat.not_lt_zero _)
  · have h1 : ((b : ℕ) + 1) % n < n := Nat.mod_lt _ (by omega)
    have h2 := b.isLt
    omega

/-- The even half-edge at the cyclic successor of a bond position lies below `2 * n`. -/
theorem perM_bound2 (n : ℕ) (b : Fin n) : 2 * (((b : ℕ) + 1) % n) < 2 * n := by
  by_cases hn0 : n = 0
  · subst hn0; exact absurd b.isLt (Nat.not_lt_zero _)
  · have h1 : ((b : ℕ) + 1) % n < n := Nat.mod_lt _ (by omega)
    have h2 := b.isLt
    omega

/-- The even half-edge at a periodic bond position lies below `3 * n`. -/
theorem perLeg2_bound (n : ℕ) (b : Fin n) : 2 * (b : ℕ) < 3 * n := by
  have := b.isLt; omega

/-- The odd half-edge at a periodic bond position lies below `3 * n`. -/
theorem perLeg2_bound1 (n : ℕ) (b : Fin n) : 2 * (b : ℕ) + 1 < 3 * n := by
  have := b.isLt; omega

/-- The left port at a periodic site equals the index assigned to its bond edge, after
transporting dimensions. -/
theorem perPort_left [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (e : ∀ i : InternalEdge (perNet n d D A), Fin ((perNet n d D A).dims i.val))
    (b : Fin n) :
    (portValue (perNet n d D A) (perEnc n d D A x) e
        ⟨2 * (b : ℕ), perLeg2_bound n b⟩).cast
        (perDim_bond n d D (by show (2 * (b : ℕ) : ℕ) < 2 * n; have := b.isLt; omega))
      = (e (perBondEdge n d D A b)).cast
          (perDim_bond n d D (by show (2 * (b : ℕ) : ℕ) < 2 * n; have := b.isLt; omega)) := by
  have hjk : (⟨2 * (b : ℕ), perLeg2_bound n b⟩ : Fin ((perNet n d D A).nh))
      < ⟨2 * (b : ℕ) + 1, perLeg2_bound1 n b⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have h1 : perPartner n ⟨2 * (b : ℕ), perLeg2_bound n b⟩
      = some ⟨2 * (b : ℕ) + 1, perLeg2_bound1 n b⟩ :=
    perPartner_even n b
  refine Fin.ext ?_
  simp only [Fin.val_cast]
  unfold portValue
  split
  · next hnone => exact absurd (hnone.symm.trans h1) (by simp)
  · next k' hk' =>
    have hkk : k' = ⟨2 * (b : ℕ) + 1, perLeg2_bound1 n b⟩ :=
      Option.some.inj (hk'.symm.trans h1)
    subst k'
    rw [dite_eq_left hjk]
    rfl

/-- The right port at a periodic site equals the index assigned to the cyclic successor bond,
after transporting dimensions. -/
theorem perPort_right [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (e : ∀ i : InternalEdge (perNet n d D A), Fin ((perNet n d D A).dims i.val))
    (b : Fin n) :
    (portValue (perNet n d D A) (perEnc n d D A x) e
        ⟨2 * (((b : ℕ) + 1) % n) + 1, perLeg_bound n b⟩).cast
        (perDim_bond n d D (perLeg_bound2 n b))
      = (e (perBondEdge n d D A ⟨((b : ℕ) + 1) % n, Nat.mod_lt _ (by have := b.isLt; omega)⟩)).cast
          (perDim_bond n d D (perM_bound2 n b)) := by
  refine Fin.ext ?_
  simp only [Fin.val_cast]
  have h1 : perPartner n ⟨2 * (((b : ℕ) + 1) % n) + 1, perLeg_bound n b⟩
      = some ⟨2 * (((b : ℕ) + 1) % n), perM_bound n b⟩ := by
    have hb : (2 * (((b : ℕ) + 1) % n) + 1 : ℕ) < 2 * n := perLeg_bound2 n b
    simp only [perPartner, dite_eq_left hb]
    simp
  have hkj : (2 * (((b : ℕ) + 1) % n) : ℕ) < 2 * (((b : ℕ) + 1) % n) + 1 := by omega
  unfold portValue
  split
  · next hnone => exact absurd (hnone.symm.trans h1) (by simp)
  · next k' hk' =>
    have hkk : k' = ⟨2 * (((b : ℕ) + 1) % n), perM_bound n b⟩ :=
      Option.some.inj (hk'.symm.trans h1)
    subst k'
    have hnlt : ¬((⟨2 * (((b : ℕ) + 1) % n) + 1, perLeg_bound n b⟩ : Fin ((perNet n d D A).nh))
        < ⟨2 * (((b : ℕ) + 1) % n), perM_bound n b⟩) :=
      fun h => absurd (Fin.mk_lt_mk.mp h) (by omega)
    rw [dite_eq_right hnlt]
    rfl

/-- The physical port of the periodic network at site `v` equals `x v`, after transporting
dimensions. -/
theorem perPort_phys [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (e : ∀ i : InternalEdge (perNet n d D A), Fin ((perNet n d D A).dims i.val))
    (v : Fin n) :
    (portValue (perNet n d D A) (perEnc n d D A x) e
        ⟨2 * n + (v : ℕ), by show 2 * n + (v : ℕ) < 3 * n; have := v.isLt; omega⟩).cast
        (perDim_phys n d D (by show ¬(2 * n + (v : ℕ) < 2 * n); have := v.isLt; omega))
      = x v := by
  refine Fin.ext ?_
  simp only [Fin.val_cast]
  have h1 : perPartner n ⟨2 * n + (v : ℕ), by show 2 * n + (v : ℕ) < 3 * n; have := v.isLt; omega⟩ = none := by
    simp only [perPartner]
    rw [dite_eq_right (by omega : ¬((2 * n + (v : ℕ) : ℕ) < 2 * n))]
  unfold portValue
  split
  · next hnone =>
    simp only [perEnc, Fin.val_cast, Nat.add_sub_cancel_left]
  · next k' hk' => exact absurd (h1.symm.trans hk') (by simp)

/-- Evaluating the periodic local tensor gives the entry of `A` selected by the physical index
and the two adjacent cyclic bond indices. -/
theorem perTensor_at [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (e : ∀ i : InternalEdge (perNet n d D A), Fin ((perNet n d D A).dims i.val))
    (v : Fin n) :
    perTensor n d D A v (fun h => portValue (perNet n d D A) (perEnc n d D A x) e h.val)
      = A v (x v)
          ((e (perBondEdge n d D A v)).cast
            (perDim_bond n d D (by show (2 * (v : ℕ) : ℕ) < 2 * n; have := v.isLt; omega)))
          ((e (perBondEdge n d D A ⟨((v : ℕ) + 1) % n,
            Nat.mod_lt _ (by have := v.isLt; omega)⟩)).cast
            (perDim_bond n d D (perM_bound2 n v))) := by
  have hphys := perPort_phys A x e v
  have hleft := perPort_left A x e v
  have hright := perPort_right A x e v
  show A v
      ((portValue (perNet n d D A) (perEnc n d D A x) e
        ⟨2 * n + (v : ℕ), by show 2 * n + (v : ℕ) < 3 * n; have := v.isLt; omega⟩).cast
        (perDim_phys n d D (by show ¬(2 * n + (v : ℕ) < 2 * n); have := v.isLt; omega)))
      ((portValue (perNet n d D A) (perEnc n d D A x) e
        ⟨2 * (v : ℕ), perLeg2_bound n v⟩).cast
        (perDim_bond n d D (by show (2 * (v : ℕ) : ℕ) < 2 * n; have := v.isLt; omega)))
      ((portValue (perNet n d D A) (perEnc n d D A x) e
        ⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩).cast
        (perDim_bond n d D (perLeg_bound2 n v)))
    = A v (x v)
      ((e (perBondEdge n d D A v)).cast
        (perDim_bond n d D (by show (2 * (v : ℕ) : ℕ) < 2 * n; have := v.isLt; omega)))
      ((e (perBondEdge n d D A ⟨((v : ℕ) + 1) % n,
        Nat.mod_lt _ (by have := v.isLt; omega)⟩)).cast
        (perDim_bond n d D (perM_bound2 n v)))
  rw [hphys, hleft, hright]

/-- The bond dimension of the periodic tensor network is at most `D`. -/
theorem netBondDimension_perNet_le [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    netBondDimension (perNet n d D A) ≤ D := by
  apply Finset.sup_le
  intro i _
  obtain ⟨k, hk, -⟩ := i.property
  have hb := perPartner_isSome n hk
  have hd : ((perNet n d D A).dims i.val) = D := perDim_bond n d D hb
  rw [hd]

/-- Contracting the periodic network at the encoded physical configuration gives
`periodicMpsAmplitude A x`. -/
theorem netContract_perNet_eq [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    netContract (perNet n d D A) (perEnc n d D A x) = periodicMpsAmplitude A x := by
  show (∑ e : ∀ i : InternalEdge (perNet n d D A), Fin ((perNet n d D A).dims i.val),
      ∏ v : Fin (perNet n d D A).nv,
        (perNet n d D A).tensor v (fun h =>
          portValue (perNet n d D A) (perEnc n d D A x) e h.val))
    = periodicMpsAmplitude A x
  simp only [periodicMpsAmplitude]
  rw [Fintype.sum_equiv (perEdgeIdxEquiv n d D A) (fun e =>
      ∏ v : Fin (perNet n d D A).nv,
        (perNet n d D A).tensor v (fun h =>
          portValue (perNet n d D A) (perEnc n d D A x) e h.val))
    (fun α => ∏ v : Fin n, A v (x v) (α v)
      (α ⟨((v : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)) (fun e => ?eq)]
  case eq =>
    refine Finset.prod_congr rfl (fun v _ => ?_)
    show perTensor n d D A v (fun h =>
        portValue (perNet n d D A) (perEnc n d D A x) e h.val)
      = A v (x v) ((perEdgeIdxEquiv n d D A e) v)
        ((perEdgeIdxEquiv n d D A e) ⟨((v : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
    rw [perTensor_at A x e v]
    rfl

/-- Every periodic MPS with positive site count and nonzero bond dimension is represented by a
tensor network of bond dimension at most `D`. -/
theorem clause1_clause4 :
    ∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∃ (N : TensorNet) (enc : (Fin n → Fin d) → ∀ o : OpenLeg N, Fin (N.dims o.val)),
        netBondDimension N ≤ D ∧ ∀ x : Fin n → Fin d,
          netContract N (enc x) = @periodicMpsAmplitude n d D hn hD A x := by
  intro n d D hn hD A
  have := hn
  have := hD
  exact ⟨perNet n d D A, perEnc n d D A,
    netBondDimension_perNet_le A, fun x => netContract_perNet_eq A x⟩

end Clause1Periodic

section Clause1NetIso

variable {N₁ N₂ : TensorNet}

/-- Two partners of the same half-edge are equal. -/
theorem partner_unique {N : TensorNet} {h k₁ k₂ : Fin N.nh}
    (h1 : N.partner h = some k₁) (h2 : N.partner h = some k₂) : k₁ = k₂ :=
  Option.some.inj (h1.symm.trans h2)

/-- Maps two half-edges through a network isomorphism and orders their images increasingly. -/
def isoEndMap (iso : NetIso N₁ N₂) (h k : Fin N₁.nh) : Fin N₂.nh × Fin N₂.nh :=
  if iso.halfMap h < iso.halfMap k then (iso.halfMap h, iso.halfMap k)
  else (iso.halfMap k, iso.halfMap h)

/-- Maps two half-edges through the inverse half-edge equivalence and orders their preimages
increasingly. -/
def isoEndMapInv (iso : NetIso N₁ N₂) (h k : Fin N₂.nh) : Fin N₁.nh × Fin N₁.nh :=
  if iso.halfMap.symm h < iso.halfMap.symm k then (iso.halfMap.symm h, iso.halfMap.symm k)
  else (iso.halfMap.symm k, iso.halfMap.symm h)

/-- The ordered images of paired half-edges under a network isomorphism remain paired. -/
theorem isoEndMap_partner (iso : NetIso N₁ N₂) {h k : Fin N₁.nh}
    (hpk : N₁.partner h = some k) :
    N₂.partner (isoEndMap iso h k).1 = some (isoEndMap iso h k).2 := by
  unfold isoEndMap
  by_cases hlt : iso.halfMap h < iso.halfMap k
  · rw [ite_eq_left hlt]
    show N₂.partner (iso.halfMap h) = some (iso.halfMap k)
    rw [iso.partner_map, hpk]
    rfl
  · rw [ite_eq_right hlt]
    show N₂.partner (iso.halfMap k) = some (iso.halfMap h)
    have hpk' : N₂.partner (iso.halfMap h) = some (iso.halfMap k) := by
      rw [iso.partner_map, hpk]
      rfl
    exact N₂.involution _ _ hpk'

/-- The ordered images of distinct half-edges under a network isomorphism are strictly
increasing. -/
theorem isoEndMap_lt (iso : NetIso N₁ N₂) {h k : Fin N₁.nh} (hne : h ≠ k) :
    (isoEndMap iso h k).1 < (isoEndMap iso h k).2 := by
  unfold isoEndMap
  by_cases hlt : iso.halfMap h < iso.halfMap k
  · rw [ite_eq_left hlt]
    exact hlt
  · rw [ite_eq_right hlt]
    show iso.halfMap k < iso.halfMap h
    have hne' : iso.halfMap h ≠ iso.halfMap k :=
      fun he => hne (iso.halfMap.injective he)
    omega

/-- The inverse half-edge map of a network isomorphism preserves the partner relation. -/
theorem isoEndMapInv_partner_core (iso : NetIso N₁ N₂) {h k : Fin N₂.nh}
    (hpk : N₂.partner h = some k) :
    N₁.partner (iso.halfMap.symm h) = some (iso.halfMap.symm k) := by
  have h2 : N₂.partner h = (N₁.partner (iso.halfMap.symm h)).map iso.halfMap := by
    have := iso.partner_map (iso.halfMap.symm h)
    rwa [Equiv.apply_symm_apply] at this
  have h3 : (N₁.partner (iso.halfMap.symm h)).map iso.halfMap = some k :=
    h2.symm.trans hpk
  cases hc : N₁.partner (iso.halfMap.symm h) with
  | none => rw [hc, Option.map_none] at h3; exact absurd h3 (by simp)
  | some m =>
    rw [hc, Option.map_some] at h3
    have hmk : iso.halfMap m = k := Option.some.inj h3
    congr 1
    exact iso.halfMap.injective (hmk.trans (iso.halfMap.apply_symm_apply k).symm)

/-- The ordered preimages of paired half-edges remain paired. -/
theorem isoEndMapInv_partner (iso : NetIso N₁ N₂) {h k : Fin N₂.nh}
    (hpk : N₂.partner h = some k) :
    N₁.partner (isoEndMapInv iso h k).1 = some (isoEndMapInv iso h k).2 := by
  unfold isoEndMapInv
  by_cases hlt : iso.halfMap.symm h < iso.halfMap.symm k
  · rw [ite_eq_left hlt]
    show N₁.partner (iso.halfMap.symm h) = some (iso.halfMap.symm k)
    exact isoEndMapInv_partner_core iso hpk
  · rw [ite_eq_right hlt]
    show N₁.partner (iso.halfMap.symm k) = some (iso.halfMap.symm h)
    exact N₁.involution _ _ (isoEndMapInv_partner_core iso hpk)

/-- The ordered preimages of distinct half-edges are strictly increasing. -/
theorem isoEndMapInv_lt (iso : NetIso N₁ N₂) {h k : Fin N₂.nh} (hne : h ≠ k) :
    (isoEndMapInv iso h k).1 < (isoEndMapInv iso h k).2 := by
  unfold isoEndMapInv
  by_cases hlt : iso.halfMap.symm h < iso.halfMap.symm k
  · rw [ite_eq_left hlt]
    exact hlt
  · rw [ite_eq_right hlt]
    show iso.halfMap.symm k < iso.halfMap.symm h
    have hne' : iso.halfMap.symm h ≠ iso.halfMap.symm k :=
      fun he => hne (iso.halfMap.symm.injective he)
    omega

/-- Mapping an increasing pair forward and then backward recovers the pair. -/
theorem isoEndMapInv_isoEndMap (iso : NetIso N₁ N₂) {h k : Fin N₁.nh} (hlt : h < k) :
    isoEndMapInv iso (isoEndMap iso h k).1 (isoEndMap iso h k).2 = (h, k) := by
  unfold isoEndMap isoEndMapInv
  by_cases hlt' : iso.halfMap h < iso.halfMap k
  · rw [ite_eq_left hlt']
    have hs : iso.halfMap.symm (iso.halfMap h) < iso.halfMap.symm (iso.halfMap k) := by
      simp only [Equiv.symm_apply_apply]
      exact hlt
    rw [ite_eq_left hs]
    simp only [Equiv.symm_apply_apply]
  · rw [ite_eq_right hlt']
    have hs : ¬(iso.halfMap.symm (iso.halfMap k) < iso.halfMap.symm (iso.halfMap h)) := by
      simp only [Equiv.symm_apply_apply]
      exact fun hlt'' => absurd hlt'' (by omega)
    rw [ite_eq_right hs]
    simp only [Equiv.symm_apply_apply]

/-- Mapping an increasing pair backward and then forward recovers the pair. -/
theorem isoEndMap_isoEndMapInv (iso : NetIso N₁ N₂) {h k : Fin N₂.nh} (hlt : h < k) :
    isoEndMap iso (isoEndMapInv iso h k).1 (isoEndMapInv iso h k).2 = (h, k) := by
  unfold isoEndMap isoEndMapInv
  by_cases hlt' : iso.halfMap.symm h < iso.halfMap.symm k
  · rw [ite_eq_left hlt']
    have hs : iso.halfMap (iso.halfMap.symm h) < iso.halfMap (iso.halfMap.symm k) := by
      simp only [Equiv.apply_symm_apply]
      exact hlt
    rw [ite_eq_left hs]
    simp only [Equiv.apply_symm_apply]
  · rw [ite_eq_right hlt']
    have hs : ¬(iso.halfMap (iso.halfMap.symm k) < iso.halfMap (iso.halfMap.symm h)) := by
      simp only [Equiv.apply_symm_apply]
      exact fun hlt'' => absurd hlt'' (by omega)
    rw [ite_eq_right hs]
    simp only [Equiv.apply_symm_apply]

/-- The internal edge induced by a network isomorphism, represented by its smaller image
endpoint. -/
noncomputable def isoEdgeMap (iso : NetIso N₁ N₂) (i : InternalEdge N₁) : InternalEdge N₂ :=
  let k := Classical.choose i.property
  have hpk : N₁.partner i.val = some k := (Classical.choose_spec i.property).1
  have hne : i.val ≠ k := Fin.ne_of_lt (Classical.choose_spec i.property).2
  ⟨(isoEndMap iso i.val k).1,
    ⟨(isoEndMap iso i.val k).2, isoEndMap_partner iso hpk, isoEndMap_lt iso hne⟩⟩

/-- The internal edge induced by the inverse half-edge equivalence of a network isomorphism. -/
noncomputable def isoEdgeMapInv (iso : NetIso N₁ N₂) (j : InternalEdge N₂) : InternalEdge N₁ :=
  let k := Classical.choose j.property
  have hpk : N₂.partner j.val = some k := (Classical.choose_spec j.property).1
  have hne : j.val ≠ k := Fin.ne_of_lt (Classical.choose_spec j.property).2
  ⟨(isoEndMapInv iso j.val k).1,
    ⟨(isoEndMapInv iso j.val k).2, isoEndMapInv_partner iso hpk, isoEndMapInv_lt iso hne⟩⟩

/-- The representative of an image edge is the first endpoint returned by `isoEndMap`. -/
theorem isoEdgeMap_val (iso : NetIso N₁ N₂) (i : InternalEdge N₁) :
    (isoEdgeMap iso i).val = (isoEndMap iso i.val (Classical.choose i.property)).1 :=
  rfl

/-- The partner of an image edge's representative is the second endpoint returned by
`isoEndMap`. -/
theorem isoEdgeMap_partner' (iso : NetIso N₁ N₂) (i : InternalEdge N₁) :
    N₂.partner (isoEdgeMap iso i).val =
      some (isoEndMap iso i.val (Classical.choose i.property)).2 :=
  isoEndMap_partner iso (Classical.choose_spec i.property).1

/-- The representative of an inverse image edge is the first endpoint returned by
`isoEndMapInv`. -/
theorem isoEdgeMapInv_val (iso : NetIso N₁ N₂) (j : InternalEdge N₂) :
    (isoEdgeMapInv iso j).val = (isoEndMapInv iso j.val (Classical.choose j.property)).1 :=
  rfl

/-- The chosen partner of an image edge is the second endpoint returned by `isoEndMap`. -/
theorem isoEdgeMap_choose (iso : NetIso N₁ N₂) (i : InternalEdge N₁) :
    Classical.choose (isoEdgeMap iso i).property =
      (isoEndMap iso i.val (Classical.choose i.property)).2 :=
  partner_unique (Classical.choose_spec (isoEdgeMap iso i).property).1
    (isoEdgeMap_partner' iso i)

/-- The chosen partner of an inverse image edge is the second endpoint returned by
`isoEndMapInv`. -/
theorem isoEdgeMapInv_choose (iso : NetIso N₁ N₂) (j : InternalEdge N₂) :
    Classical.choose (isoEdgeMapInv iso j).property =
      (isoEndMapInv iso j.val (Classical.choose j.property)).2 :=
  partner_unique (Classical.choose_spec (isoEdgeMapInv iso j).property).1
    (isoEndMapInv_partner iso (Classical.choose_spec j.property).1)

/-- The inverse edge map recovers an internal edge from its image. -/
theorem isoEdgeMapInv_isoEdgeMap (iso : NetIso N₁ N₂) (i : InternalEdge N₁) :
    isoEdgeMapInv iso (isoEdgeMap iso i) = i := by
  apply Subtype.ext

  rw [isoEdgeMapInv_val, isoEdgeMap_choose, isoEdgeMap_val]
  have hlt : i.val < Classical.choose i.property := (Classical.choose_spec i.property).2
  have h := isoEndMapInv_isoEndMap iso hlt
  exact congrArg Prod.fst h

/-- The forward edge map recovers an internal edge from its inverse image. -/
theorem isoEdgeMap_isoEdgeMapInv (iso : NetIso N₁ N₂) (j : InternalEdge N₂) :
    isoEdgeMap iso (isoEdgeMapInv iso j) = j := by
  apply Subtype.ext
  rw [isoEdgeMap_val, isoEdgeMapInv_choose, isoEdgeMapInv_val]
  have hlt : j.val < Classical.choose j.property := (Classical.choose_spec j.property).2
  have h := isoEndMap_isoEndMapInv iso hlt
  exact congrArg Prod.fst h

/-- The equivalence of internal edges induced by a network isomorphism. -/
noncomputable def edgeEquiv (iso : NetIso N₁ N₂) : InternalEdge N₁ ≃ InternalEdge N₂ where
  toFun := isoEdgeMap iso
  invFun := isoEdgeMapInv iso
  left_inv := isoEdgeMapInv_isoEdgeMap iso
  right_inv := isoEdgeMap_isoEdgeMapInv iso

/-- A network isomorphism preserves the dimension of every internal edge. -/
theorem isoEdgeMap_dims (iso : NetIso N₁ N₂) (i : InternalEdge N₁) :
    N₂.dims (isoEdgeMap iso i).val = N₁.dims i.val := by
  rw [isoEdgeMap_val]
  unfold isoEndMap
  by_cases hlt : iso.halfMap i.val < iso.halfMap (Classical.choose i.property)
  · rw [ite_eq_left hlt]
    exact iso.dims_map i.val
  · rw [ite_eq_right hlt]
    have hpk : N₁.partner i.val = some (Classical.choose i.property) :=
      (Classical.choose_spec i.property).1
    rw [iso.dims_map]
    exact (N₁.dims_match i.val _ hpk).symm

/-- Pulls an open-leg assignment back along a network isomorphism, transporting each finite
index across the dimension equality. -/
noncomputable def ext₁ (iso : NetIso N₁ N₂) (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val)) :
    ∀ o : OpenLeg N₁, Fin (N₁.dims o.val) :=
  fun o => (ext ⟨iso.halfMap o.val, by
    rw [iso.partner_map, o.property, Option.map_none]⟩).cast (iso.dims_map o.val)

/-- Transporting a finite index along an equality of bounds preserves its natural value. -/
theorem fin_cast_val {n m : ℕ} (h : n = m) (x : Fin n) : (x.cast h).val = x.val := by
  simp

/-- Pulls an internal-edge assignment back along the induced edge map of a network isomorphism. -/
noncomputable def edgeValMap (iso : NetIso N₁ N₂)
    (e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val)) (i : InternalEdge N₁) :
    Fin (N₁.dims i.val) :=
  (e₂ (isoEdgeMap iso i)).cast (isoEdgeMap_dims iso i)

/-- The equivalence between internal-edge assignments induced contravariantly by a network
isomorphism. -/
noncomputable def edgeValEquiv (iso : NetIso N₁ N₂) :
    (∀ i : InternalEdge N₂, Fin (N₂.dims i.val)) ≃
      (∀ i : InternalEdge N₁, Fin (N₁.dims i.val)) where
  toFun := edgeValMap iso
  invFun := fun e₁ j => (e₁ (isoEdgeMapInv iso j)).cast (by
    have h := isoEdgeMap_dims iso (isoEdgeMapInv iso j)
    rw [isoEdgeMap_isoEdgeMapInv] at h
    exact h.symm)
  left_inv := by
    intro e₂
    funext j

    apply Fin.ext
    simp only [fin_cast_val]
    exact congrArg (fun z => (e₂ z).val) (isoEdgeMap_isoEdgeMapInv iso j)
  right_inv := by
    intro e₁
    funext i
    apply Fin.ext
    exact congrArg (fun z => (e₁ z).val) (isoEdgeMapInv_isoEdgeMap iso i)

/-- The chosen partner in an internal edge's witness equals any specified partner of its
representative. -/
theorem choose_eq_of_partner {N : TensorNet} (i : InternalEdge N) {k : Fin N.nh}
    (hpk : N.partner i.val = some k) : Classical.choose i.property = k :=
  partner_unique (Classical.choose_spec i.property).1 hpk

/-- For an explicitly presented internal edge, the representative of its image is the first
ordered image endpoint. -/
theorem isoEdgeMap_val_fst (iso : NetIso N₁ N₂) {h k : Fin N₁.nh}
    (hpk : N₁.partner h = some k) (hlt : h < k) :
    (isoEdgeMap iso (⟨h, ⟨k, hpk, hlt⟩⟩ : InternalEdge N₁)).val = (isoEndMap iso h k).1 := by
  rw [isoEdgeMap_val]
  refine congrArg (fun z => (isoEndMap iso h z).1) ?_
  exact choose_eq_of_partner (⟨h, ⟨k, hpk, hlt⟩⟩ : InternalEdge N₁) hpk

/-- Pulling back an edge assignment preserves the natural value at the corresponding image edge. -/
theorem edgeValMap_val (iso : NetIso N₁ N₂)
    (e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val)) (i : InternalEdge N₁) :
    (edgeValMap iso e₂ i).val = (e₂ (isoEdgeMap iso i)).val :=
  fin_cast_val (isoEdgeMap_dims iso i) (e₂ (isoEdgeMap iso i))

/-- Corresponding ports under a network isomorphism have the same natural value when external
and internal assignments are pulled back. -/
theorem portValue_iso_val (iso : NetIso N₁ N₂)
    (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val))
    (e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val))
    (h : Fin N₁.nh) :
    (portValue N₂ ext e₂ (iso.halfMap h)).val
      = (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) h).val := by
  cases hc : N₁.partner h with
  | none =>

    have hp' : N₂.partner (iso.halfMap h) = none := by
      rw [iso.partner_map, hc, Option.map_none]
    rw [portValue_of_partner_none ext e₂ (iso.halfMap h) hp',
      portValue_of_partner_none (ext₁ iso ext) (edgeValMap iso e₂) h hc]
    show (ext ⟨iso.halfMap h, hp'⟩).val
      = ((ext ⟨iso.halfMap h, _⟩).cast (iso.dims_map h)).val
    rw [fin_cast_val]
  | some k =>

    have hpk : N₁.partner h = some k := hc
    have hp' : N₂.partner (iso.halfMap h) = some (iso.halfMap k) := by
      rw [iso.partner_map, hc, Option.map_some]
    have hne : h ≠ k := N₁.no_self_loop h k hpk
    have hne' : iso.halfMap h ≠ iso.halfMap k :=
      fun he => hne (iso.halfMap.injective he)
    have hinv : N₁.partner k = some h := N₁.involution h k hpk
    have hinv' : N₂.partner (iso.halfMap k) = some (iso.halfMap h) :=
      N₂.involution _ _ hp'
    have hdim' : N₂.dims (iso.halfMap k) = N₂.dims (iso.halfMap h) :=
      N₂.dims_match _ _ hinv'
    rcases lt_or_gt_of_ne hne with hlth | hklt
    · have hR : (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) h).val
          = (e₂ (isoEdgeMap iso (⟨h, ⟨k, hpk, hlth⟩⟩ : InternalEdge N₁))).val := by
        rw [portValue_of_partner_eq (ext₁ iso ext) (edgeValMap iso e₂) h k hpk hlth]
        exact edgeValMap_val iso e₂ ⟨h, ⟨k, hpk, hlth⟩⟩
      by_cases hlt' : iso.halfMap h < iso.halfMap k
      · have hL : (portValue N₂ ext e₂ (iso.halfMap h)).val
            = (e₂ (⟨iso.halfMap h, ⟨iso.halfMap k, hp', hlt'⟩⟩ : InternalEdge N₂)).val := by
          rw [portValue_of_partner_eq ext e₂ (iso.halfMap h) (iso.halfMap k) hp' hlt']
        have hval : (isoEdgeMap iso (⟨h, ⟨k, hpk, hlth⟩⟩ : InternalEdge N₁)).val
            = (⟨iso.halfMap h, ⟨iso.halfMap k, hp', hlt'⟩⟩ : InternalEdge N₂).val := by
          rw [isoEdgeMap_val_fst iso hpk hlth]
          show (isoEndMap iso h k).1 = iso.halfMap h
          unfold isoEndMap
          rw [ite_eq_left hlt']
        have key : isoEdgeMap iso (⟨h, ⟨k, hpk, hlth⟩⟩ : InternalEdge N₁)
            = (⟨iso.halfMap h, ⟨iso.halfMap k, hp', hlt'⟩⟩ : InternalEdge N₂) :=
          Subtype.ext hval
        rw [hL, hR]
        exact (congrArg (fun z => (e₂ z).val) key).symm
      · have hlt₂ : iso.halfMap k < iso.halfMap h :=
          (lt_or_gt_of_ne hne').resolve_left hlt'
        have hL : (portValue N₂ ext e₂ (iso.halfMap h)).val
            = (e₂ (⟨iso.halfMap k, ⟨iso.halfMap h, hinv', hlt₂⟩⟩ : InternalEdge N₂)).val := by
          rw [portValue_of_partner_eq_rev ext e₂ (iso.halfMap h) (iso.halfMap k) hp' hlt₂
            hinv' hdim']
          exact fin_cast_val _ _
        have hval : (isoEdgeMap iso (⟨h, ⟨k, hpk, hlth⟩⟩ : InternalEdge N₁)).val
            = (⟨iso.halfMap k, ⟨iso.halfMap h, hinv', hlt₂⟩⟩ : InternalEdge N₂).val := by
          rw [isoEdgeMap_val_fst iso hpk hlth]
          show (isoEndMap iso h k).1 = iso.halfMap k
          unfold isoEndMap
          rw [ite_eq_right hlt']
        have key : isoEdgeMap iso (⟨h, ⟨k, hpk, hlth⟩⟩ : InternalEdge N₁)
            = (⟨iso.halfMap k, ⟨iso.halfMap h, hinv', hlt₂⟩⟩ : InternalEdge N₂) :=
          Subtype.ext hval
        rw [hL, hR]
        exact (congrArg (fun z => (e₂ z).val) key).symm
    · have hR : (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) h).val
          = (e₂ (isoEdgeMap iso (⟨k, ⟨h, hinv, hklt⟩⟩ : InternalEdge N₁))).val := by
        rw [portValue_of_partner_eq_rev (ext₁ iso ext) (edgeValMap iso e₂) h k hpk hklt hinv
          (N₁.dims_match h k hpk).symm]
        rw [fin_cast_val]
        exact edgeValMap_val iso e₂ ⟨k, ⟨h, hinv, hklt⟩⟩
      by_cases hlt' : iso.halfMap h < iso.halfMap k
      · have hL : (portValue N₂ ext e₂ (iso.halfMap h)).val
            = (e₂ (⟨iso.halfMap h, ⟨iso.halfMap k, hp', hlt'⟩⟩ : InternalEdge N₂)).val := by
          rw [portValue_of_partner_eq ext e₂ (iso.halfMap h) (iso.halfMap k) hp' hlt']
        have hval : (isoEdgeMap iso (⟨k, ⟨h, hinv, hklt⟩⟩ : InternalEdge N₁)).val
            = (⟨iso.halfMap h, ⟨iso.halfMap k, hp', hlt'⟩⟩ : InternalEdge N₂).val := by
          rw [isoEdgeMap_val_fst iso hinv hklt]
          show (isoEndMap iso k h).1 = iso.halfMap h
          unfold isoEndMap
          rw [ite_eq_right (lt_asymm hlt')]
        have key : isoEdgeMap iso (⟨k, ⟨h, hinv, hklt⟩⟩ : InternalEdge N₁)
            = (⟨iso.halfMap h, ⟨iso.halfMap k, hp', hlt'⟩⟩ : InternalEdge N₂) :=
          Subtype.ext hval
        rw [hL, hR]
        exact (congrArg (fun z => (e₂ z).val) key).symm
      · have hlt₂ : iso.halfMap k < iso.halfMap h :=
          (lt_or_gt_of_ne hne').resolve_left hlt'
        have hL : (portValue N₂ ext e₂ (iso.halfMap h)).val
            = (e₂ (⟨iso.halfMap k, ⟨iso.halfMap h, hinv', hlt₂⟩⟩ : InternalEdge N₂)).val := by
          rw [portValue_of_partner_eq_rev ext e₂ (iso.halfMap h) (iso.halfMap k) hp' hlt₂
            hinv' hdim']
          exact fin_cast_val _ _
        have hval : (isoEdgeMap iso (⟨k, ⟨h, hinv, hklt⟩⟩ : InternalEdge N₁)).val
            = (⟨iso.halfMap k, ⟨iso.halfMap h, hinv', hlt₂⟩⟩ : InternalEdge N₂).val := by
          rw [isoEdgeMap_val_fst iso hinv hklt]
          show (isoEndMap iso k h).1 = iso.halfMap k
          unfold isoEndMap
          rw [ite_eq_left hlt₂]
        have key : isoEdgeMap iso (⟨k, ⟨h, hinv, hklt⟩⟩ : InternalEdge N₁)
            = (⟨iso.halfMap k, ⟨iso.halfMap h, hinv', hlt₂⟩⟩ : InternalEdge N₂) :=
          Subtype.ext hval
        rw [hL, hR]
        exact (congrArg (fun z => (e₂ z).val) key).symm

/-- A port value is preserved by a network isomorphism after transporting it across the
dimension equality. -/
theorem portValue_iso_fin (iso : NetIso N₁ N₂)
    (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val))
    (e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val))
    (h : Fin N₁.nh) :
    portValue N₂ ext e₂ (iso.halfMap h) =
      (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) h).cast (iso.dims_map h).symm := by
  apply Fin.ext
  show (portValue N₂ ext e₂ (iso.halfMap h)).val
    = ((portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) h).cast (iso.dims_map h).symm).val
  rw [fin_cast_val]
  exact portValue_iso_val iso ext e₂ h

/-- Expresses a target port value using the inverse half-edge map and the pulled-back
assignments. -/
theorem portValue_iso_fin' (iso : NetIso N₁ N₂)
    (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val))
    (e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val))
    (h' : Fin N₂.nh) :
    portValue N₂ ext e₂ h' =
      (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) (iso.halfMap.symm h')).cast
        ((iso.dims_map (iso.halfMap.symm h')).symm.trans
          (congrArg N₂.dims (iso.halfMap.apply_symm_apply h'))) := by
  apply Fin.ext
  show (portValue N₂ ext e₂ h').val
    = ((portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) (iso.halfMap.symm h')).cast _).val
  rw [fin_cast_val]
  have hval := portValue_iso_val iso ext e₂ (iso.halfMap.symm h')
  have hpp : iso.halfMap (iso.halfMap.symm h') = h' := iso.halfMap.apply_symm_apply h'
  have hcong : (portValue N₂ ext e₂ h').val
      = (portValue N₂ ext e₂ (iso.halfMap (iso.halfMap.symm h'))).val := by
    rw [hpp]
  exact hcong.trans hval

/-- Corresponding vertex tensors evaluate equally under a network isomorphism and the induced
pullback of port assignments. -/
theorem vertexTensor_eq (iso : NetIso N₁ N₂)
    (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val))
    (e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val))
    (v : Fin N₁.nv) :
    N₂.tensor (iso.vertexMap v)
        (fun hh => portValue N₂ ext e₂ hh.val) =
      N₁.tensor v
        (fun hh => portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) hh.val) := by
  have hten := iso.tensor_map v
    (fun hh => portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) hh.val)
  have hfun : (fun hh : {h : Fin N₂.nh // N₂.site h = iso.vertexMap v} =>
        portValue N₂ ext e₂ hh.val)
      = fun h' => (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂)
          (iso.halfMap.symm h'.val)).cast
        ((iso.dims_map (iso.halfMap.symm h'.val)).symm.trans
          (congrArg N₂.dims (iso.halfMap.apply_symm_apply h'.val))) := by
    funext hh
    exact portValue_iso_fin' iso ext e₂ hh.val
  refine (congrArg (N₂.tensor (iso.vertexMap v)) hfun).trans ?_
  show N₂.tensor (iso.vertexMap v)
      (fun h' => (portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂)
          (iso.halfMap.symm h'.val)).cast
        ((iso.dims_map (iso.halfMap.symm h'.val)).symm.trans
          (congrArg N₂.dims (iso.halfMap.apply_symm_apply h'.val))))
    = N₁.tensor v
      (fun hh => portValue N₁ (ext₁ iso ext) (edgeValMap iso e₂) hh.val)
  exact hten

/-- Tensor-network contraction is invariant under network isomorphism when the open-leg
assignment is pulled back. -/
theorem clause1_clause1 :
    ∀ (N₁ N₂ : TensorNet) (iso : NetIso N₁ N₂)
        (ext : ∀ o : OpenLeg N₂, Fin (N₂.dims o.val)),
      netContract N₂ ext = netContract N₁
        (fun o => (ext ⟨iso.halfMap o.val, by
          rw [iso.partner_map, o.property, Option.map_none]⟩).cast
          (iso.dims_map o.val)) := by
  intro N₁ N₂ iso ext
  show netContract N₂ ext = netContract N₁ (ext₁ iso ext)
  have hsum : (∑ e₂ : ∀ i : InternalEdge N₂, Fin (N₂.dims i.val),
        ∏ v : Fin N₂.nv, N₂.tensor v (fun h => portValue N₂ ext e₂ h.val))
      = ∑ e₁ : ∀ i : InternalEdge N₁, Fin (N₁.dims i.val),
        ∏ v : Fin N₁.nv, N₁.tensor v (fun h => portValue N₁ (ext₁ iso ext) e₁ h.val) := by

    have hre := (Equiv.sum_comp (edgeValEquiv iso).symm
      (fun e₂ => ∏ v : Fin N₂.nv,
        N₂.tensor v (fun h => portValue N₂ ext e₂ h.val))).symm
    rw [hre]
    refine Finset.sum_congr rfl fun e₁ _ => ?_

    have hprod : (∏ v : Fin N₂.nv,
          N₂.tensor v (fun h => portValue N₂ ext ((edgeValEquiv iso).symm e₁) h.val))
        = ∏ v : Fin N₁.nv, N₁.tensor v (fun h => portValue N₁ (ext₁ iso ext) e₁ h.val) := by
      have hpre := (Equiv.prod_comp iso.vertexMap
        (fun v => N₂.tensor v
          (fun h => portValue N₂ ext ((edgeValEquiv iso).symm e₁) h.val))).symm
      rw [hpre]
      refine Finset.prod_congr rfl fun v₁ _ => ?_
      have hvt := vertexTensor_eq iso ext ((edgeValEquiv iso).symm e₁) v₁
      have hkey : edgeValMap iso ((edgeValEquiv iso).symm e₁) = e₁ :=
        (edgeValEquiv iso).apply_symm_apply e₁
      rw [hkey] at hvt
      exact hvt
    exact hprod
  exact hsum

end Clause1NetIso

set_option autoImplicit false

open scoped ComplexConjugate

/-- An assignment of a finite index of the appropriate dimension to every half-edge of a tensor
network. -/
abbrev HalfAssign (N : TensorNet) : Type := ∀ h : Fin N.nh, Fin (N.dims h)

/-- The partner endpoint of the representative of an internal edge. -/
def edgeOther {N : TensorNet} (i : InternalEdge N) : Fin N.nh :=
  (N.partner i.val).getD i.val

/-- A specified partner of an internal edge's representative equals its `edgeOther` endpoint. -/
lemma edgeOther_of_partner {N : TensorNet} {i : InternalEdge N} {k : Fin N.nh}
    (hk : N.partner i.val = some k) : edgeOther i = k := by
  show (N.partner i.val).getD i.val = k
  rw [hk]
  rfl

/-- The representative of an internal edge is paired with its `edgeOther` endpoint. -/
lemma partner_edgeOther {N : TensorNet} (i : InternalEdge N) :
    N.partner i.val = some (edgeOther i) := by
  obtain ⟨k, hk, _hlt⟩ := i.property
  rw [edgeOther_of_partner hk]
  exact hk

/-- The `edgeOther` endpoint is paired back with the representative of the internal edge. -/
lemma partner_edgeOther_inv {N : TensorNet} (i : InternalEdge N) :
    N.partner (edgeOther i) = some i.val :=
  N.involution i.val (edgeOther i) (partner_edgeOther i)

/-- The representative endpoint of an internal edge is strictly smaller than its other endpoint. -/
lemma edgeOther_lt {N : TensorNet} (i : InternalEdge N) : i.val < edgeOther i := by
  obtain ⟨k, hk, hlt⟩ := i.property
  rw [edgeOther_of_partner hk]
  exact hlt

/-- The two endpoints of an internal edge have equal dimensions. -/
lemma dims_edgeOther {N : TensorNet} (i : InternalEdge N) :
    N.dims i.val = N.dims (edgeOther i) :=
  N.dims_match i.val (edgeOther i) (partner_edgeOther i)

/-- The dimension at the other endpoint of an internal edge equals that at its representative. -/
lemma dims_edgeOther' {N : TensorNet} (i : InternalEdge N) :
    N.dims (edgeOther i) = N.dims i.val :=
  (dims_edgeOther i).symm

/-- The local gauge kernel on a half-edge, using the identity kernel on open legs and
`gaugeKernel` on paired legs. -/
noncomputable def legK {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (j : Fin N.nh) (a x : Fin (N.dims j)) : ℂ :=
  match hk : N.partner j with
  | none => if a = x then (1 : ℂ) else 0
  | some _k => gaugeKernel N U hk a x

/-- Expands a gauge-transformed vertex tensor as a sum over local half-edge indices weighted by
the product of `legK` kernels. -/
lemma gaugeTensor_eq {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    gaugeTensor N U v a =
      ∑ x : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
        (∏ h : {h : Fin N.nh // N.site h = v}, legK U h.val (a h) (x h)) * N.tensor v x :=
  rfl

/-- The port at the representative of an internal edge equals its assigned edge index. -/
lemma portValue_rep {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (i : InternalEdge N) :
    portValue N ext e i.val = e i :=
  portValue_of_partner_eq ext e i.val (edgeOther i) (partner_edgeOther i) (edgeOther_lt i)

/-- The port at the other endpoint equals the assigned edge index transported across the
endpoint dimension equality. -/
lemma portValue_other {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (i : InternalEdge N) :
    portValue N ext e (edgeOther i) = (e i).cast (dims_edgeOther i) :=
  portValue_of_partner_eq_rev ext e (edgeOther i) i.val
    (partner_edgeOther_inv i) (edgeOther_lt i) (partner_edgeOther i) (dims_edgeOther i)

/-- Gauge transformation preserves port values for fixed external and internal assignments. -/
lemma portValue_gaugeNet {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (j : Fin N.nh) :
    portValue (gaugeNet N U) ext e j = portValue N ext e j := by
  cases hj : N.partner j with
  | none =>
    rw [portValue_of_partner_none (N := gaugeNet N U) ext e j hj]
    rw [portValue_of_partner_none ext e j hj]
  | some k =>
    by_cases hlt : j < k
    · rw [portValue_of_partner_eq (N := gaugeNet N U) ext e j k hj hlt]
      rw [portValue_of_partner_eq ext e j k hj hlt]
    · have hkj : k < j := (lt_or_gt_of_ne (N.no_self_loop j k hj)).resolve_left hlt
      rw [portValue_of_partner_eq_rev (N := gaugeNet N U) ext e j k hj hkj
        (N.involution j k hj) (N.dims_match k j (N.involution j k hj))]
      rw [portValue_of_partner_eq_rev ext e j k hj hkj
        (N.involution j k hj) (N.dims_match k j (N.involution j k hj))]

/-- On an open leg, `legK` is the Kronecker delta kernel. -/
lemma legK_none {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    {j : Fin N.nh} (hj : N.partner j = none) (a x : Fin (N.dims j)) :
    legK U j a x = if a = x then (1 : ℂ) else 0 := by
  simp only [legK]
  split
  · next hnone => rfl
  · next k hk => exact absurd (hj.symm.trans hk) (by simp)

/-- On the representative of an internal edge, `legK` is the corresponding gauge matrix entry. -/
lemma legK_rep {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (i : InternalEdge N) (a x : Fin (N.dims i.val)) :
    legK U i.val a x = U i a x := by
  simp only [legK]
  split
  · next hnone => exact absurd (hnone.symm.trans (partner_edgeOther i)) (by simp)
  · next k hk =>
    have hk' : k = edgeOther i := Option.some.inj (hk.symm.trans (partner_edgeOther i))
    subst hk'
    have hlt : i.val < edgeOther i := edgeOther_lt i
    simp only [gaugeKernel, dite_eq_left hlt]
    rfl

/-- On the other endpoint of an internal edge, `legK` is the conjugate gauge matrix entry after
transporting indices. -/
lemma legK_other {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (i : InternalEdge N) (a x : Fin (N.dims (edgeOther i))) :
    legK U (edgeOther i) a x
      = conj (U i (a.cast (dims_edgeOther' i)) (x.cast (dims_edgeOther' i))) := by
  simp only [legK]
  split
  · next hnone => exact absurd (hnone.symm.trans (partner_edgeOther_inv i)) (by simp)
  · next k hk =>
    have hk' : k = i.val := Option.some.inj (hk.symm.trans (partner_edgeOther_inv i))
    subst hk'
    have hnlt : ¬ (edgeOther i < i.val) := lt_asymm (edgeOther_lt i)
    simp only [gaugeKernel, dite_eq_right hnlt]
    rfl

/-- Maps an open leg or one of the two endpoints of an internal edge to its half-edge index. -/
def halfEdgeDecFun (N : TensorNet) (z : OpenLeg N ⊕ InternalEdge N ⊕ InternalEdge N) : Fin N.nh :=
  match z with
  | Sum.inl o => o.val
  | Sum.inr (Sum.inl i) => i.val
  | Sum.inr (Sum.inr i) => edgeOther i

/-- Classifies a half-edge as an open leg, an internal edge representative, or the other
endpoint of an internal edge. -/
def halfEdgeDecInv (N : TensorNet) (j : Fin N.nh) :
    OpenLeg N ⊕ InternalEdge N ⊕ InternalEdge N :=
  match hj : N.partner j with
  | none => Sum.inl ⟨j, hj⟩
  | some k =>
      if hlt : j < k then Sum.inr (Sum.inl ⟨j, ⟨k, hj, hlt⟩⟩)
      else
        Sum.inr (Sum.inr ⟨k, ⟨j, N.involution j k hj,
          (lt_or_gt_of_ne (N.no_self_loop j k hj)).resolve_left hlt⟩⟩)

/-- Reconstructing a half-edge from its classification returns the original half-edge. -/
lemma halfEdgeDecFun_inv (N : TensorNet) (j : Fin N.nh) :
    halfEdgeDecFun N (halfEdgeDecInv N j) = j := by
  simp only [halfEdgeDecInv]
  split
  · next hj => rfl
  · next k hk =>
    split
    · next hlt => rfl
    · next hnlt =>
      exact edgeOther_of_partner (N.involution j k hk)

/-- Classifying a half-edge constructed from open-leg or internal-edge endpoint data recovers
those data. -/
lemma halfEdgeDecInv_fun (N : TensorNet)
    (z : OpenLeg N ⊕ InternalEdge N ⊕ InternalEdge N) :
    halfEdgeDecInv N (halfEdgeDecFun N z) = z := by
  cases z with
  | inl o =>
    simp only [halfEdgeDecFun]
    simp only [halfEdgeDecInv]
    split
    · next hj => rfl
    · next k hk => exact absurd (o.property.symm.trans hk) (by simp)
  | inr s =>
    cases s with
    | inl i =>
      simp only [halfEdgeDecFun]
      simp only [halfEdgeDecInv]
      split
      · next hj => exact absurd (hj.symm.trans (partner_edgeOther i)) (by simp)
      · next k hk =>
        have hk' : k = edgeOther i := Option.some.inj (hk.symm.trans (partner_edgeOther i))
        subst hk'
        split
        · next hlt => rfl
        · next hnlt => exact absurd (edgeOther_lt i) hnlt
    | inr i =>
      simp only [halfEdgeDecFun]
      simp only [halfEdgeDecInv]
      split
      · next hj => exact absurd (hj.symm.trans (partner_edgeOther_inv i)) (by simp)
      · next k hk =>
        have hk' : k = i.val := Option.some.inj (hk.symm.trans (partner_edgeOther_inv i))
        subst hk'
        split
        · next hlt => exact absurd hlt (lt_asymm (edgeOther_lt i))
        · next hnlt => rfl

/-- Decomposes all half-edges into open legs and two copies of the internal edges. -/
def halfEdgeDec (N : TensorNet) :
    (OpenLeg N ⊕ InternalEdge N ⊕ InternalEdge N) ≃ Fin N.nh where
  toFun := halfEdgeDecFun N
  invFun := halfEdgeDecInv N
  left_inv := halfEdgeDecInv_fun N
  right_inv := halfEdgeDecFun_inv N

/-- A product over a finite sum type factors into the products over its two summands. -/
lemma prod_sum_elim {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι ⊕ κ → ℂ) :
    (∏ z : ι ⊕ κ, f z) = (∏ i : ι, f (Sum.inl i)) * ∏ k : κ, f (Sum.inr k) := by
  have h1 : (Finset.univ : Finset (ι ⊕ κ)) = Finset.univ.disjSum Finset.univ := by
    ext z
    cases z <;> simp
  have h2 : f = Sum.elim (fun i => f (Sum.inl i)) (fun k => f (Sum.inr k)) := by
    funext z
    cases z <;> rfl
  rw [h2, h1]
  exact Finset.prod_sumElim Finset.univ Finset.univ
    (fun i => f (Sum.inl i)) (fun k => f (Sum.inr k))

/-- A product over all half-edges factors into open-leg factors and paired endpoint factors for
each internal edge. -/
lemma prod_halfEdge_eq {N : TensorNet} (f : Fin N.nh → ℂ) :
    (∏ h : Fin N.nh, f h)
      = (∏ o : OpenLeg N, f o.val) * ∏ i : InternalEdge N, (f i.val * f (edgeOther i)) := by
  rw [(Fintype.prod_equiv (halfEdgeDec N)
      (fun z => f (halfEdgeDecFun N z)) f (fun _ => rfl)).symm]
  rw [prod_sum_elim]
  rw [prod_sum_elim]
  simp only [halfEdgeDecFun]
  rw [← Finset.prod_mul_distrib]

/-- Identifies a vertex together with an incident half-edge with the corresponding global
half-edge. -/
def siteFiber (N : TensorNet) :
    (Σ v : Fin N.nv, {h : Fin N.nh // N.site h = v}) ≃ Fin N.nh where
  toFun x := x.2.val
  invFun j := ⟨N.site j, ⟨j, rfl⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk v h =>
      cases h with
      | mk j hj =>
        subst hj
        rfl
  right_inv := by
    intro j
    rfl

/-- A product over vertices and their incident half-edges equals the product over all
half-edges. -/
lemma prod_local_eq_prod_global {N : TensorNet}
    (g : (v : Fin N.nv) → {h : Fin N.nh // N.site h = v} → ℂ) :
    (∏ v : Fin N.nv, ∏ h : {h : Fin N.nh // N.site h = v}, g v h)
      = ∏ j : Fin N.nh, g (N.site j) ⟨j, rfl⟩ := by
  rw [← Fintype.prod_sigma
    (fun x : Σ v : Fin N.nv, {h : Fin N.nh // N.site h = v} => g x.1 x.2)]
  exact Fintype.prod_equiv (siteFiber N) _ _
    (fun x => by
      cases x with
      | mk v h =>
        cases h with
        | mk j hj =>
          subst hj
          rfl)

/-- Identifies collections of local vertex assignments with a global half-edge assignment. -/
def localAssignEquiv (N : TensorNet) :
    (∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val))
      ≃ HalfAssign N where
  toFun F := fun j => F (N.site j) ⟨j, rfl⟩
  invFun σ := fun v h => σ h.val
  left_inv := by
    intro F
    funext v h
    cases h with
    | mk j hj =>
      subst hj
      rfl
  right_inv := by
    intro σ
    funext j
    rfl

/-- The product of all vertex tensor entries evaluated at a global half-edge assignment. -/
noncomputable def netTheta (N : TensorNet) (σ : HalfAssign N) : ℂ :=
  ∏ v : Fin N.nv, N.tensor v (fun h => σ h.val)

/-- The global half-edge assignment determined by external leg values and internal edge values
through `portValue`. -/
noncomputable def portAssign {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) : HalfAssign N :=
  fun h => portValue N ext e h

/-- The product of vertex tensor entries at local assignments equals `netTheta` at the
corresponding global assignment. -/
lemma prod_tensor_eq_netTheta {N : TensorNet}
    (F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    (∏ v : Fin N.nv, N.tensor v (F v)) = netTheta N (localAssignEquiv N F) := by
  apply Finset.prod_congr rfl
  intro v _hv
  congr 1
  funext h
  cases h with
  | mk j hj =>
    subst hj
    rfl

/-- The complex Kronecker delta is symmetric in its two arguments. -/
lemma if_eq_comm {α : Type} [DecidableEq α] (a b : α) :
    (if a = b then (1 : ℂ) else 0) = if b = a then (1 : ℂ) else 0 := by
  by_cases h : a = b
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (fun he => h he.symm)]

/-- Transporting a finite index along an equality of bounds and then back returns the index. -/
lemma cast_cast_self {n m : ℕ} (h1 : n = m) (h2 : m = n) (x : Fin n) :
    ((x.cast h1).cast h2) = x :=
  Fin.ext (by simp [Fin.cast])

/-- Summing a unitary gauge matrix entry times a conjugate entry over the shared row gives the
Kronecker delta of the endpoint indices. -/
lemma unitary_edge_sum {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup (Fin (N.dims i.val)) ℂ)
    (i : InternalEdge N) (p : Fin (N.dims i.val)) (q : Fin (N.dims (edgeOther i))) :
    (∑ idx : Fin (N.dims i.val),
      U i idx p * conj (U i idx (q.cast (dims_edgeOther' i))))
      = if p.val = q.val then (1 : ℂ) else 0 := by
  have hval : (q.cast (dims_edgeOther' i)).val = q.val := rfl
  have hcross : ∀ idx : Fin (N.dims i.val),
      U i idx p * conj (U i idx (q.cast (dims_edgeOther' i)))
        = (U i)ᴴ (q.cast (dims_edgeOther' i)) idx * U i idx p := by
    intro idx
    rw [mul_comm, starRingEnd_apply]
    simp only [Matrix.conjTranspose_apply]
  have hu := (Matrix.mem_unitaryGroup_iff' (A := U i)).mp (hU i)
  rw [Matrix.star_eq_conjTranspose] at hu
  calc (∑ idx : Fin (N.dims i.val),
        U i idx p * conj (U i idx (q.cast (dims_edgeOther' i))))
      = ∑ idx : Fin (N.dims i.val),
          (U i)ᴴ (q.cast (dims_edgeOther' i)) idx * U i idx p :=
        Finset.sum_congr rfl (fun idx _ => hcross idx)
    _ = ((U i)ᴴ * U i) (q.cast (dims_edgeOther' i)) p := (Matrix.mul_apply).symm
    _ = (1 : Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
          (q.cast (dims_edgeOther' i)) p := by rw [hu]
    _ = if (q.cast (dims_edgeOther' i)) = p then (1 : ℂ) else 0 := Matrix.one_apply
    _ = if p.val = q.val then (1 : ℂ) else 0 := by
        by_cases hq : (q.cast (dims_edgeOther' i)) = p
        · rw [ite_eq_left hq]
          have hp : p.val = q.val := (congrArg Fin.val hq).symm.trans hval
          rw [ite_eq_left hp]
        · rw [ite_eq_right hq]
          have hp : ¬ p.val = q.val := by
            intro he
            apply hq
            apply Fin.ext
            rw [hval]
            exact he.symm
          rw [ite_eq_right hp]

/-- A half-edge assignment is consistent when it matches the external assignment on open legs
and has equal natural values at paired endpoints. -/
def GaugeConsistent {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (σ : HalfAssign N) : Prop :=
  (∀ o : OpenLeg N, σ o.val = ext o) ∧
    (∀ i : InternalEdge N, (σ i.val).val = (σ (edgeOther i)).val)

/-- The product of Kronecker delta factors imposing the external assignments and equality of
internal endpoint values. -/
def deltaFactor {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (σ : HalfAssign N) : ℂ :=
  (∏ o : OpenLeg N, if σ o.val = ext o then (1 : ℂ) else 0) *
    ∏ i : InternalEdge N, if (σ i.val).val = (σ (edgeOther i)).val then (1 : ℂ) else 0

/-- The delta factor of a consistent half-edge assignment is one. -/
lemma deltaFactor_of_consistent {N : TensorNet}
    {ext : ∀ o : OpenLeg N, Fin (N.dims o.val)} {σ : HalfAssign N}
    (hc : GaugeConsistent ext σ) : deltaFactor ext σ = 1 := by
  obtain ⟨ho, hi⟩ := hc
  simp only [deltaFactor]
  rw [Finset.prod_congr rfl (fun o _ => ite_eq_left (ho o))]
  rw [Finset.prod_congr rfl (fun i _ => ite_eq_left (hi i))]
  simp

/-- The delta factor of an inconsistent half-edge assignment is zero. -/
lemma deltaFactor_of_not_consistent {N : TensorNet}
    {ext : ∀ o : OpenLeg N, Fin (N.dims o.val)} {σ : HalfAssign N}
    (hc : ¬ GaugeConsistent ext σ) : deltaFactor ext σ = 0 := by
  classical
  simp only [GaugeConsistent] at hc
  rw [not_and_or] at hc
  cases hc with
  | inl ho =>
    rw [Classical.not_forall] at ho
    obtain ⟨o, ho⟩ := ho
    simp only [deltaFactor]
    rw [Finset.prod_eq_zero (Finset.mem_univ o) (ite_eq_right ho)]
    simp
  | inr hi =>
    rw [Classical.not_forall] at hi
    obtain ⟨i, hi⟩ := hi
    simp only [deltaFactor]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
    simp

/-- For unitary edge gauges, summing the product of half-edge kernels over internal assignments
gives `deltaFactor`. -/
lemma sum_e_legK {N : TensorNet}
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup (Fin (N.dims i.val)) ℂ)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) (σ : HalfAssign N) :
    (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
      ∏ h : Fin N.nh, legK U h (portValue N ext e h) (σ h))
    = deltaFactor ext σ := by
  have hfact : ∀ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
      (∏ h : Fin N.nh, legK U h (portValue N ext e h) (σ h))
        = (∏ o : OpenLeg N, if σ o.val = ext o then (1 : ℂ) else 0) *
            ∏ i : InternalEdge N,
              (U i (e i) (σ i.val) *
                conj (U i (e i) ((σ (edgeOther i)).cast (dims_edgeOther' i)))) := by
    intro e
    rw [prod_halfEdge_eq]
    have hop : ∀ o : OpenLeg N, legK U o.val (portValue N ext e o.val) (σ o.val)
        = if σ o.val = ext o then (1 : ℂ) else 0 := by
      intro o
      rw [portValue_of_partner_none ext e o.val o.property, legK_none U o.property]
      exact if_eq_comm _ _
    have hedge : ∀ i : InternalEdge N,
        legK U i.val (portValue N ext e i.val) (σ i.val) *
          legK U (edgeOther i) (portValue N ext e (edgeOther i)) (σ (edgeOther i))
        = U i (e i) (σ i.val) *
            conj (U i (e i) ((σ (edgeOther i)).cast (dims_edgeOther' i))) := by
      intro i
      rw [portValue_rep, legK_rep, portValue_other, legK_other]
      rw [cast_cast_self (dims_edgeOther i) (dims_edgeOther' i) (e i)]
    rw [Finset.prod_congr rfl (fun o _ => hop o), Finset.prod_congr rfl (fun i _ => hedge i)]
  calc (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
        ∏ h : Fin N.nh, legK U h (portValue N ext e h) (σ h))
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ((∏ o : OpenLeg N, if σ o.val = ext o then (1 : ℂ) else 0) *
            ∏ i : InternalEdge N,
              (U i (e i) (σ i.val) *
                conj (U i (e i) ((σ (edgeOther i)).cast (dims_edgeOther' i))))) :=
        Finset.sum_congr rfl (fun e _ => hfact e)
    _ = (∏ o : OpenLeg N, if σ o.val = ext o then (1 : ℂ) else 0) *
          ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
            ∏ i : InternalEdge N,
              (U i (e i) (σ i.val) *
                conj (U i (e i) ((σ (edgeOther i)).cast (dims_edgeOther' i)))) :=
        (Finset.mul_sum _ _ _).symm
    _ = (∏ o : OpenLeg N, if σ o.val = ext o then (1 : ℂ) else 0) *
          ∏ i : InternalEdge N,
            ∑ idx : Fin (N.dims i.val),
              (U i idx (σ i.val) *
                conj (U i idx ((σ (edgeOther i)).cast (dims_edgeOther' i)))) := by
        rw [(Fintype.prod_sum (fun (i : InternalEdge N) (idx : Fin (N.dims i.val)) =>
          U i idx (σ i.val) * conj (U i idx ((σ (edgeOther i)).cast (dims_edgeOther' i))))).symm]
    _ = (∏ o : OpenLeg N, if σ o.val = ext o then (1 : ℂ) else 0) *
          ∏ i : InternalEdge N, (if (σ i.val).val = (σ (edgeOther i)).val then (1 : ℂ) else 0) := by
        rw [Finset.prod_congr rfl (fun i _ =>
          unitary_edge_sum U hU i (σ i.val) (σ (edgeOther i)))]
    _ = deltaFactor ext σ := rfl

/-- The half-edge assignment induced by external and internal values is gauge consistent. -/
lemma portAssign_consistent {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) :
    GaugeConsistent ext (portAssign ext e) := by
  constructor
  · intro o
    exact portValue_of_partner_none ext e o.val o.property
  · intro i
    simp only [portAssign]
    rw [portValue_rep, portValue_other]
    simp [Fin.cast]

/-- Two internal-edge assignments inducing the same half-edge assignment are equal. -/
lemma portAssign_inj {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    {e₁ e₂ : ∀ i : InternalEdge N, Fin (N.dims i.val)}
    (h : portAssign ext e₁ = portAssign ext e₂) : e₁ = e₂ := by
  funext i
  have h1 := congrFun h i.val
  simp only [portAssign] at h1
  simp only [portValue_rep] at h1
  exact h1

/-- A consistent half-edge assignment is recovered from its values at the representative
internal endpoints and the prescribed external values. -/
lemma portAssign_of_consistent {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (σ : HalfAssign N) (hc : GaugeConsistent ext σ) :
    portAssign ext (fun i => σ i.val) = σ := by
  obtain ⟨ho, hi⟩ := hc
  funext j
  simp only [portAssign]
  by_cases hj : N.partner j = none
  · rw [portValue_of_partner_none ext (fun i => σ i.val) j hj]
    exact (ho ⟨j, hj⟩).symm
  · cases hk : N.partner j with
    | none => exact absurd hk hj
    | some k =>
      by_cases hlt : j < k
      · rw [portValue_of_partner_eq ext (fun i => σ i.val) j k hk hlt]
      · have hkj : k < j := (lt_or_gt_of_ne (N.no_self_loop j k hk)).resolve_left hlt
        rw [portValue_of_partner_eq_rev ext (fun i => σ i.val) j k hk hkj
          (N.involution j k hk) (N.dims_match k j (N.involution j k hk))]
        have hi' : (σ k).val = (σ j).val := by
          have h2 := hi ⟨k, ⟨j, N.involution j k hk, hkj⟩⟩
          rw [edgeOther_of_partner (i := ⟨k, ⟨j, N.involution j k hk, hkj⟩⟩)
            (N.involution j k hk)] at h2
          exact h2
        exact Fin.ext hi'

/-- A sum over all half-edge assignments weighted by `deltaFactor` reduces to a sum over
internal-edge assignments. -/
lemma sum_delta_collapse {N : TensorNet} (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (Θ : HalfAssign N → ℂ) :
    (∑ σ : HalfAssign N, Θ σ * deltaFactor ext σ)
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val), Θ (portAssign ext e) := by
  classical
  have hite : ∑ σ : HalfAssign N, Θ σ * deltaFactor ext σ
      = ∑ σ ∈ (Finset.univ : Finset (HalfAssign N)),
          if GaugeConsistent ext σ then Θ σ else 0 := by
    apply Finset.sum_congr rfl
    intro σ _hσ
    by_cases hc : GaugeConsistent ext σ
    · rw [ite_eq_left hc, deltaFactor_of_consistent hc]
      simp
    · rw [ite_eq_right hc, deltaFactor_of_not_consistent hc]
      simp
  have hbij : (∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val), Θ (portAssign ext e))
      = ∑ σ ∈ (Finset.univ : Finset (HalfAssign N)) with GaugeConsistent ext σ, Θ σ := by
    apply Finset.sum_bij (fun e _ => portAssign ext e)
    · intro e _he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact portAssign_consistent ext e
    · intro e₁ _he₁ e₂ _he₂ hEq
      exact portAssign_inj ext hEq
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact ⟨fun i => σ i.val, Finset.mem_univ _,
        portAssign_of_consistent ext σ hσ⟩
    · intro e _he
      rfl
  rw [hite, ← Finset.sum_filter, ← hbij]

/-- Tensor-network contraction is invariant under unitary gauge transformations on all internal
edges. -/
theorem clause1_clause2 :
    ∀ (N : TensorNet) (U : ∀ i : InternalEdge N,
      Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ),
    (∀ i, U i ∈ Matrix.unitaryGroup (Fin (N.dims i.val)) ℂ) →
    ∀ (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)),
      netContract (gaugeNet N U) ext = netContract N ext := by
  intro N U hU ext
  have hL : netContract (gaugeNet N U) ext
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
        ∏ v : Fin N.nv, gaugeTensor N U v (fun h => portValue N ext e h.val) := by
    have h1 : netContract (gaugeNet N U) ext
        = ∑ e : ∀ i : InternalEdge (gaugeNet N U), Fin ((gaugeNet N U).dims i.val),
          ∏ v : Fin (gaugeNet N U).nv, (gaugeNet N U).tensor v
            (fun h => portValue (gaugeNet N U) ext e h.val) := rfl
    rw [h1]
    have hT : (∀ i : InternalEdge (gaugeNet N U), Fin ((gaugeNet N U).dims i.val))
        = (∀ i : InternalEdge N, Fin (N.dims i.val)) := rfl
    cases hT
    apply Finset.sum_congr rfl
    intro e _he
    apply Finset.prod_congr rfl
    intro v _hv
    show gaugeTensor N U v (fun h => portValue (gaugeNet N U) ext e h.val)
      = gaugeTensor N U v (fun h => portValue N ext e h.val)
    congr 1
    funext h
    exact portValue_gaugeNet U ext e h.val
  have hR : netContract N ext
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val), netTheta N (portAssign ext e) := rfl
  have hterm : ∀ (e : ∀ i : InternalEdge N, Fin (N.dims i.val))
      (F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      (∏ v : Fin N.nv,
        ((∏ h : {h : Fin N.nh // N.site h = v},
            legK U h.val (portValue N ext e h.val) (F v h)) * N.tensor v (F v)))
        = (∏ h : Fin N.nh, legK U h (portValue N ext e h) (localAssignEquiv N F h)) *
            netTheta N (localAssignEquiv N F) := by
    intro e F
    rw [Finset.prod_mul_distrib]
    rw [prod_local_eq_prod_global (fun (v : Fin N.nv) (h : {h : Fin N.nh // N.site h = v}) =>
      legK U h.val (portValue N ext e h.val) (F v h))]
    rw [prod_tensor_eq_netTheta F]
    show (∏ j : Fin N.nh, legK U j (portValue N ext e j) ((localAssignEquiv N) F j)) *
        netTheta N (localAssignEquiv N F)
      = (∏ h : Fin N.nh, legK U h (portValue N ext e h) ((localAssignEquiv N) F h)) *
        netTheta N (localAssignEquiv N F)
    rfl
  have hexpand : ∀ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
      (∏ v : Fin N.nv, gaugeTensor N U v (fun h => portValue N ext e h.val))
        = ∑ F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
          (∏ h : Fin N.nh, legK U h (portValue N ext e h) (localAssignEquiv N F h)) *
            netTheta N (localAssignEquiv N F) := by
    intro e
    have h1 : (∏ v : Fin N.nv, gaugeTensor N U v (fun h => portValue N ext e h.val))
        = ∏ v : Fin N.nv, ∑ x : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
            (∏ h : {h : Fin N.nh // N.site h = v},
              legK U h.val (portValue N ext e h.val) (x h)) * N.tensor v x :=
      Finset.prod_congr rfl (fun v _ => gaugeTensor_eq U v (fun h => portValue N ext e h.val))
    rw [h1]
    rw [Fintype.prod_sum (fun (v : Fin N.nv)
        (x : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) =>
      (∏ h : {h : Fin N.nh // N.site h = v},
        legK U h.val (portValue N ext e h.val) (x h)) * N.tensor v x)]
    exact Finset.sum_congr rfl (fun F _ => hterm e F)
  calc netContract (gaugeNet N U) ext
      = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ∏ v : Fin N.nv, gaugeTensor N U v (fun h => portValue N ext e h.val) := hL
    _ = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
          ∑ F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
            (∏ h : Fin N.nh, legK U h (portValue N ext e h) (localAssignEquiv N F h)) *
              netTheta N (localAssignEquiv N F) :=
        Finset.sum_congr rfl (fun e _ => hexpand e)
    _ = ∑ F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
          ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
            (∏ h : Fin N.nh, legK U h (portValue N ext e h) (localAssignEquiv N F h)) *
              netTheta N (localAssignEquiv N F) := by
        rw [Finset.sum_comm]
    _ = ∑ F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
          netTheta N (localAssignEquiv N F) *
            ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
              ∏ h : Fin N.nh, legK U h (portValue N ext e h) (localAssignEquiv N F h) := by
        apply Finset.sum_congr rfl
        intro F _hF
        rw [← Finset.sum_mul, mul_comm]
    _ = ∑ F : ∀ v : Fin N.nv, ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
          netTheta N (localAssignEquiv N F) * deltaFactor ext (localAssignEquiv N F) := by
        apply Finset.sum_congr rfl
        intro F _hF
        rw [sum_e_legK U hU ext (localAssignEquiv N F)]
    _ = ∑ σ : HalfAssign N, netTheta N σ * deltaFactor ext σ := by
        rw [Fintype.sum_equiv (localAssignEquiv N)
          (fun F => netTheta N (localAssignEquiv N F) *
            deltaFactor ext (localAssignEquiv N F))
          (fun σ => netTheta N σ * deltaFactor ext σ) (fun _ => rfl)]
    _ = ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val), netTheta N (portAssign ext e) :=
        sum_delta_collapse ext (netTheta N)
    _ = netContract N ext := hR.symm

open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
section Structural

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The cut rank is the matrix rank of the corresponding cut matrix. -/
theorem cutRank_eq_matrixRank (c : ℕ) :
    cutRank n d ψ c = Matrix.rank (cutMatrix n d ψ c) := rfl

/-- The cut rank is at most the number `d ^ c` of left physical configurations. -/
theorem cutRank_le_pow_left (c : ℕ) : cutRank n d ψ c ≤ d ^ c :=
  Matrix.rank_le_height (cutMatrix n d ψ c)

/-- The cut rank is at most the number `d ^ (n - c)` of right physical configurations. -/
theorem cutRank_le_pow_right (c : ℕ) : cutRank n d ψ c ≤ d ^ (n - c) :=
  Matrix.rank_le_width (cutMatrix n d ψ c)

/-- The cut rank at the left boundary is at most one. -/
theorem cutRank_le_one_left : cutRank n d ψ 0 ≤ 1 := by
  simpa [Nat.pow_zero] using! cutRank_le_pow_left ψ 0

/-- The cut rank at the right boundary is at most one. -/
theorem cutRank_le_one_right : cutRank n d ψ n ≤ 1 := by
  simpa [Nat.sub_self, Nat.pow_zero] using! cutRank_le_pow_right ψ n

/-- A state whose squared amplitudes sum to one has a nonzero amplitude. -/
theorem exists_ne_zero_of_normSq_eq_one (hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∃ x, ψ x ≠ 0 := by
  by_contra hn
  have hzero : ∀ x, ψ x = 0 := by
    intro x
    by_contra hx
    exact hn ⟨x, hx⟩
  have hsum : (∑ x, Complex.normSq (ψ x)) = 0 :=
    Finset.sum_eq_zero (fun x _ => by simp [hzero x])
  linarith

/-- The rank of a complex matrix equals the complex dimension of the range of its associated
Euclidean linear map. -/
theorem rank_eq_finrank_range_toEuclideanLin {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    Matrix.rank M = Module.finrank ℂ (LinearMap.range M.toEuclideanLin) := by
  rw [Matrix.rank_eq_finrank_range_toLin M
      (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℂ).toBasis]
  have hM : M.toEuclideanLin = Matrix.toLin
      (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℂ).toBasis M := rfl
  rw [hM]

/-- The support of the finitely supported singular-value sequence is exactly the natural-number
range below the matrix rank. -/
theorem support_matrixSingularValues_eq_range_rank {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    (matrixSingularValues M).support = Finset.range (Matrix.rank M) := by
  rw [Qatlib.Concepts.RandCompile.ChannelBudget.support_matrixSingularValues,
    rank_eq_finrank_range_toEuclideanLin]

/-- The singular-value support of a cut matrix is exactly the range below the cut rank. -/
theorem support_matrixSingularValues_cutMatrix (c : ℕ) :
    (matrixSingularValues (cutMatrix n d ψ c)).support =
      Finset.range (cutRank n d ψ c) := by
  rw [support_matrixSingularValues_eq_range_rank, cutRank_eq_matrixRank]

/-- The squared Schmidt tail is the sum of squared singular values at supported indices at least
`D`. -/
theorem schmidtTailSq_eq_sum (c D : ℕ) :
    schmidtTailSq n d ψ c D =
      ∑ i ∈ (matrixSingularValues (cutMatrix n d ψ c)).support.filter (fun i => D ≤ i),
        (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 := rfl

/-- The squared Schmidt tail is nonnegative. -/
theorem schmidtTailSq_nonneg (c D : ℕ) : 0 ≤ schmidtTailSq n d ψ c D :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The squared Schmidt tail beyond `D` vanishes when the cut rank is at most `D`. -/
theorem schmidtTailSq_eq_zero_of_cutRank_le {c D : ℕ} (h : cutRank n d ψ c ≤ D) :
    schmidtTailSq n d ψ c D = 0 := by
  unfold schmidtTailSq
  rw [support_matrixSingularValues_cutMatrix]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  exact (by omega : False).elim

/-- The squared Schmidt tail decreases when the truncation threshold increases. -/
theorem schmidtTailSq_mono (c : ℕ) {D D' : ℕ} (h : D ≤ D') :
    schmidtTailSq n d ψ c D' ≤ schmidtTailSq n d ψ c D := by
  unfold schmidtTailSq
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i _ _ => sq_nonneg _)
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, le_trans h hi.2⟩

/-- At sites satisfying `i + 2 ≤ n`, left canonicity gives orthonormal columns after summing
over the physical and left bond indices. -/
theorem leftCanonical_entrywise {D : ℕ} {A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ}
    (hA : LeftCanonical A) {i : Fin n} (hi : (i : ℕ) + 2 ≤ n) :
    ∀ r₁ r₂ : Fin D, (∑ x : Fin d, ∑ l : Fin D, star (A i x l r₁) * A i x l r₂)
      = if r₁ = r₂ then (1 : ℂ) else 0 := by
  intro r₁ r₂
  have hentry := congrFun (congrFun (hA i hi) r₁) r₂
  rw [Matrix.sum_apply] at hentry
  have hterm : ∀ x : Fin d, ((A i x)ᴴ * A i x) r₁ r₂
      = ∑ l : Fin D, star (A i x l r₁) * A i x l r₂ := by
    intro x
    calc ((A i x)ᴴ * (A i x)) r₁ r₂
        = ∑ l : Fin D, (A i x)ᴴ r₁ l * A i x l r₂ :=
          Matrix.mul_apply (M := (A i x)ᴴ) (N := A i x) (i := r₁) (k := r₂)
      _ = ∑ l : Fin D, star (A i x l r₁) * A i x l r₂ :=
          Finset.sum_congr rfl (fun l _ => by rw [Matrix.conjTranspose_apply (A i x) l r₁])
  have hsum : (∑ x : Fin d, ((A i x)ᴴ * A i x) r₁ r₂)
      = ∑ x : Fin d, ∑ l : Fin D, star (A i x l r₁) * A i x l r₂ :=
    Finset.sum_congr rfl (fun x _ => hterm x)
  rw [hsum, Matrix.one_apply (i := r₁) (j := r₂)] at hentry
  exact hentry

/-- The maximum of one and the supremum of the cut ranks below `n` is nonzero. -/
theorem neZero_max_one_supCutRank (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) :
    NeZero (max 1 ((Finset.range n).sup fun c => cutRank n d ψ c)) :=
  ⟨Nat.pos_iff_ne_zero.mp
    (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Nat.le_max_left 1 _))⟩

/-- Every cut rank with `c < n` is bounded by the maximum of one and the supremum of those cut
ranks. -/
theorem cutRank_le_max_one_supCutRank (c : ℕ) (hc : c < n) :
    cutRank n d ψ c ≤ max 1 ((Finset.range n).sup fun c => cutRank n d ψ c) :=
  le_trans (Finset.le_sup (Finset.mem_range.mpr hc)) (Nat.le_max_right 1 _)

/-- A complex matrix has rank zero exactly when it is the zero matrix. -/
theorem matrixRank_eq_zero_iff {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    Matrix.rank M = 0 ↔ M = 0 := by
  constructor
  · intro h
    rw [Matrix.rank_eq_finrank_span_cols] at h
    have hspan : (Submodule.span ℂ (Set.range (M.col))) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      simpa using! h
    ext i j
    have hj : M.col j ∈ (Submodule.span ℂ (Set.range (M.col))) :=
      Submodule.subset_span ⟨j, rfl⟩
    rw [hspan] at hj
    simp only [Submodule.mem_bot] at hj
    have hentry := congrFun hj i
    simpa [Matrix.col] using! hentry
  · intro h
    rw [h, Matrix.rank_zero]

/-- The boundary cut matrix at cut zero recovers each amplitude in its unique row. -/
theorem cutMatrix_zero_apply (x : Fin n → Fin d) :
    cutMatrix n d ψ 0 ⟨0, by simp⟩ ((finPowEnc d n) x) = ψ x := by
  show ψ (splitJoin n 0 d ((finPowEnc d 0).symm ⟨0, by simp⟩)
      ((finPowEnc d n).symm ((finPowEnc d n) x))) = ψ x
  congr 1
  funext k
  unfold splitJoin
  have hk : ¬((k : ℕ) < 0) := Nat.not_lt_zero _
  simp only [dite_eq_right hk]
  simp

/-- A state with a nonzero amplitude has cut rank one at cut zero. -/
theorem cutRank_zero_eq_one_of_ne (hψ : ∃ x, ψ x ≠ 0) : cutRank n d ψ 0 = 1 := by
  have hle : cutRank n d ψ 0 ≤ 1 := cutRank_le_one_left ψ
  have hne : cutRank n d ψ 0 ≠ 0 := by
    intro h
    rw [cutRank_eq_matrixRank, matrixRank_eq_zero_iff] at h
    obtain ⟨x, hx⟩ := hψ
    have hentry := congrFun (congrFun h ⟨0, by simp⟩) ((finPowEnc d n) x)
    have key : ψ x = 0 := by
      rw [← cutMatrix_zero_apply ψ x]
      exact hentry
    exact hx key
  omega

/-- The squared Schmidt tail beyond `D` vanishes exactly when the cut rank is at most `D`. -/
theorem schmidtTailSq_eq_zero_iff {c D : ℕ} :
    schmidtTailSq n d ψ c D = 0 ↔ cutRank n d ψ c ≤ D := by
  constructor
  · intro h
    by_contra hn
    have hDlt : D < cutRank n d ψ c := Nat.not_le.mp hn
    unfold schmidtTailSq at h
    rw [support_matrixSingularValues_cutMatrix] at h
    have hmem : D ∈ (Finset.range (cutRank n d ψ c)).filter (fun i => D ≤ i) := by
      simp [hDlt]
    have hpos : (0 : ℝ) < (matrixSingularValues (cutMatrix n d ψ c) D) ^ 2 := by
      apply sq_pos_of_ne_zero
      intro hz
      have hpos' : 0 < matrixSingularValues (cutMatrix n d ψ c) D := by
        rw [matrixSingularValues_pos_iff_lt_finrank_range,
          ← rank_eq_finrank_range_toEuclideanLin]
        exact hDlt
      exact hpos'.ne' hz
    have hle := Finset.single_le_sum
      (f := fun i => (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2)
      (fun i _ => sq_nonneg _) hmem
    rw [h] at hle
    have hle' : (matrixSingularValues (cutMatrix n d ψ c) D) ^ 2 ≤ 0 := hle
    linarith [hpos, hle']
  · intro h
    exact schmidtTailSq_eq_zero_of_cutRank_le ψ h

end Structural

section AmplitudeSmall

/-- The amplitude of a one-site MPS is its tensor entry with both bond indices zero. -/
theorem mpsAmplitude_one {d D : ℕ} [NeZero D] (A : Fin 1 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin 1 → Fin d) : mpsAmplitude A x = A 0 (x 0) 0 0 := by
  unfold mpsAmplitude
  rw [Fintype.sum_eq_single (fun i : Fin (1 - 1) => i.elim0)]
  · rw [Fin.prod_univ_one]
    show A 0 (x 0) (mpsLeftIdx (fun i : Fin (1 - 1) => i.elim0) 0)
        (mpsRightIdx (fun i : Fin (1 - 1) => i.elim0) 0) = _
    simp only [mpsLeftIdx, mpsRightIdx]
    simp
  · intro α _hne
    exact absurd (funext (fun i => i.elim0)) _hne

end AmplitudeSmall

section Clause2One

/-- A normalized one-site state has a left-canonical MPS representation whose bond dimension is
the maximum of one and its cut-rank supremum. -/
theorem clause2_clause2_one (d : ℕ) (ψ : (Fin 1 → Fin d) → ℂ)
    (_hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∃ (D : ℕ) (hD : NeZero D) (A : Fin 1 → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation 1 d D hD A ψ ∧ LeftCanonical A ∧
        D = max 1 ((Finset.range 1).sup fun c => cutRank 1 d ψ c) := by
  refine ⟨1, inferInstance,
    fun (_i : Fin 1) (y : Fin d) => Matrix.of fun _ _ => ψ (fun _ => y), ?_, ?_, ?_⟩
  · intro x
    rw [mpsAmplitude_one]
    show (Matrix.of fun _ _ => ψ (fun _ => x 0)) (0 : Fin 1) (0 : Fin 1) = ψ x
    simp only [Matrix.of_apply]
    congr 1
    funext i
    exact (congrArg x (Fin.eq_zero i)).symm
  · intro i hi
    have hfalse : False := by have hlt := i.isLt; omega
    exact hfalse.elim
  · have hsup : (Finset.range 1).sup (fun c => cutRank 1 d ψ c) = cutRank 1 d ψ 0 := by
      simp
    rw [hsup]
    have h : cutRank 1 d ψ 0 ≤ 1 := cutRank_le_one_left ψ
    omega

end Clause2One

section Embed

/-- Embeds a square matrix into a larger square matrix by padding all entries outside its
original index range with zeros. -/
noncomputable def mpsEmbed {D₀ D : ℕ} (_h : D₀ ≤ D) (B : Matrix (Fin D₀) (Fin D₀) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < D₀ then if hj : (j : ℕ) < D₀ then B ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

/-- Inside the original row and column ranges, `mpsEmbed` agrees with the original matrix. -/
theorem mpsEmbed_apply_of_lt {D₀ D : ℕ} {h : D₀ ≤ D} {B : Matrix (Fin D₀) (Fin D₀) ℂ}
    {i j : Fin D} (hi : (i : ℕ) < D₀) (hj : (j : ℕ) < D₀) :
    mpsEmbed h B i j = B ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [mpsEmbed, hi, hj]

/-- An entry of `mpsEmbed` is zero when its row lies beyond the original matrix size. -/
theorem mpsEmbed_apply_eq_zero_of_le {D₀ D : ℕ} {h : D₀ ≤ D} {B : Matrix (Fin D₀) (Fin D₀) ℂ}
    {i j : Fin D} (hi : D₀ ≤ (i : ℕ)) : mpsEmbed h B i j = 0 := by
  have hnot : ¬((i : ℕ) < D₀) := Nat.not_lt.mpr hi
  simp [mpsEmbed, hnot]

/-- An entry of `mpsEmbed` is zero when its column lies beyond the original matrix size. -/
theorem mpsEmbed_apply_eq_zero_of_le_right {D₀ D : ℕ} {h : D₀ ≤ D}
    {B : Matrix (Fin D₀) (Fin D₀) ℂ} {i j : Fin D} (hj : D₀ ≤ (j : ℕ)) :
    mpsEmbed h B i j = 0 := by
  by_cases hi : (i : ℕ) < D₀
  · have hnot : ¬((j : ℕ) < D₀) := Nat.not_lt.mpr hj
    simp [mpsEmbed, hi, hnot]
  · exact mpsEmbed_apply_eq_zero_of_le (Nat.le_of_not_lt hi)

/-- For positive `D₀`, if every internal bond value is below `D₀`, each left bond index is also
below `D₀`. -/
theorem mpsLeftIdx_lt_of_forall_lt {n D D₀ : ℕ} [NeZero D] [NeZero D₀]
    {α : Fin (n - 1) → Fin D} (hα : ∀ j, (α j : ℕ) < D₀) (i : Fin n) :
    (mpsLeftIdx α i : ℕ) < D₀ := by
  unfold mpsLeftIdx
  by_cases h0 : (i : ℕ) = 0
  · simp [h0, NeZero.pos D₀]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : (i : ℕ) - 1 < n - 1
    · simp only [h1, ↓reduceDIte]
      exact hα _
    · simp only [h1, ↓reduceDIte]
      exact NeZero.pos D₀

/-- For positive `D₀`, if every internal bond value is below `D₀`, each right bond index is also
below `D₀`. -/
theorem mpsRightIdx_lt_of_forall_lt {n D D₀ : ℕ} [NeZero D] [NeZero D₀]
    {α : Fin (n - 1) → Fin D} (hα : ∀ j, (α j : ℕ) < D₀) (i : Fin n) :
    (mpsRightIdx α i : ℕ) < D₀ := by
  unfold mpsRightIdx
  by_cases h1 : (i : ℕ) < n - 1
  · simp only [h1, ↓reduceDIte]
    exact hα _
  · simp only [h1, ↓reduceDIte]
    exact NeZero.pos D₀

/-- Restricting bond values to `Fin D₀` commutes with forming the left bond index. -/
theorem mpsLeftIdx_trunc {n D D₀ : ℕ} [NeZero D] [NeZero D₀]
    {α : Fin (n - 1) → Fin D} (hα : ∀ j, (α j : ℕ) < D₀) (i : Fin n) :
    mpsLeftIdx (fun j => (⟨α j, hα j⟩ : Fin D₀)) i
      = ⟨mpsLeftIdx α i, mpsLeftIdx_lt_of_forall_lt hα i⟩ := by
  unfold mpsLeftIdx
  by_cases h0 : (i : ℕ) = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    by_cases h1 : (i : ℕ) - 1 < n - 1
    · simp only [h1, ↓reduceDIte]
    · simp only [h1, ↓reduceDIte]
      exact Fin.ext rfl

/-- Restricting bond values to `Fin D₀` commutes with forming the right bond index. -/
theorem mpsRightIdx_trunc {n D D₀ : ℕ} [NeZero D] [NeZero D₀]
    {α : Fin (n - 1) → Fin D} (hα : ∀ j, (α j : ℕ) < D₀) (i : Fin n) :
    mpsRightIdx (fun j => (⟨α j, hα j⟩ : Fin D₀)) i
      = ⟨mpsRightIdx α i, mpsRightIdx_lt_of_forall_lt hα i⟩ := by
  unfold mpsRightIdx
  by_cases h1 : (i : ℕ) < n - 1
  · simp only [h1, ↓reduceDIte]
  · simp only [h1, ↓reduceDIte]
    exact Fin.ext rfl

/-- When every bond value lies in the original index range, the product of embedded tensor
entries equals the product of the original entries. -/
theorem prod_embed_eq_prod_of_good {n d D₀ D : ℕ} [NeZero D₀] [NeZero D] (h : D₀ ≤ D)
    {A : Fin n → Fin d → Matrix (Fin D₀) (Fin D₀) ℂ} {x : Fin n → Fin d}
    {α : Fin (n - 1) → Fin D} (hα : ∀ j, (α j : ℕ) < D₀) :
    (∏ i : Fin n, mpsEmbed h (A i (x i)) (mpsLeftIdx α i) (mpsRightIdx α i))
      = ∏ i : Fin n, A i (x i) (mpsLeftIdx (fun j => (⟨α j, hα j⟩ : Fin D₀)) i)
          (mpsRightIdx (fun j => (⟨α j, hα j⟩ : Fin D₀)) i) := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hl : (mpsLeftIdx α i : ℕ) < D₀ := mpsLeftIdx_lt_of_forall_lt hα i
  have hr : (mpsRightIdx α i : ℕ) < D₀ := mpsRightIdx_lt_of_forall_lt hα i
  rw [mpsEmbed_apply_of_lt hl hr]
  rw [← mpsLeftIdx_trunc hα i, ← mpsRightIdx_trunc hα i]

/-- The product of embedded tensor entries vanishes if some internal bond index lies outside the
original range. -/
theorem prod_embed_eq_zero_of_exists {n d D₀ D : ℕ} [NeZero D₀] [NeZero D] (h : D₀ ≤ D)
    {A : Fin n → Fin d → Matrix (Fin D₀) (Fin D₀) ℂ} {x : Fin n → Fin d}
    {α : Fin (n - 1) → Fin D} (hα : ∃ j, D₀ ≤ (α j : ℕ)) :
    (∏ i : Fin n, mpsEmbed h (A i (x i)) (mpsLeftIdx α i) (mpsRightIdx α i)) = 0 := by
  obtain ⟨j, hj⟩ := hα
  have hjlt : (j : ℕ) < n - 1 := j.isLt
  set j' : Fin n := ⟨(j : ℕ), by have hjn := j.isLt; omega⟩ with hj'def
  have hright : mpsRightIdx α j' = α j := by
    unfold mpsRightIdx
    have hco : (j' : ℕ) < n - 1 := by
      rw [hj'def]
      exact hjlt
    rw [dite_eq_left hco]
  have hfac : mpsEmbed h (A j' (x j')) (mpsLeftIdx α j') (mpsRightIdx α j') = 0 := by
    rw [hright]
    exact mpsEmbed_apply_eq_zero_of_le_right hj
  exact Finset.prod_eq_zero (Finset.mem_univ j') hfac

/-- Padding MPS tensors with zero rows and columns preserves every MPS amplitude. -/
theorem mpsAmplitude_embed {n d D₀ D : ℕ} [NeZero D₀] [NeZero D] (h : D₀ ≤ D)
    (A : Fin n → Fin d → Matrix (Fin D₀) (Fin D₀) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude (fun i y => mpsEmbed h (A i y)) x = mpsAmplitude A x := by
  unfold mpsAmplitude
  set T : (Fin (n - 1) → Fin D) → ℂ := fun α =>
    ∏ i : Fin n, mpsEmbed h (A i (x i)) (mpsLeftIdx α i) (mpsRightIdx α i) with hT
  set T₀ : (Fin (n - 1) → Fin D₀) → ℂ := fun β =>
    ∏ i : Fin n, A i (x i) (mpsLeftIdx β i) (mpsRightIdx β i) with hT₀
  have hsplit : (∑ α : Fin (n - 1) → Fin D, T α)
      = ∑ α ∈ (Finset.univ.filter (fun α => ∀ j, (α j : ℕ) < D₀)), T α := by
    have hz : (∑ α ∈ (Finset.univ.filter (fun α => ¬∀ j, (α j : ℕ) < D₀)), T α) = 0 := by
      apply Finset.sum_eq_zero
      intro α hmem
      have hnot : ¬∀ j, (α j : ℕ) < D₀ := by
        simpa using! (Finset.mem_filter.mp hmem).2
      have hex : ∃ j, D₀ ≤ (α j : ℕ) := by
        by_contra hnone
        push Not at hnone
        exact hnot hnone
      rw [hT]
      exact prod_embed_eq_zero_of_exists h hex
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin (n - 1) → Fin D)) (fun α => ∀ j, (α j : ℕ) < D₀)]
    rw [hz, add_zero]
  have hfilter : (∑ α ∈ (Finset.univ.filter (fun α => ∀ j, (α j : ℕ) < D₀)), T α)
      = ∑ β : Fin (n - 1) → Fin D₀, T₀ β := by
    refine Finset.sum_bij
      (fun α hα => fun j => (⟨α j, (Finset.mem_filter.mp hα).2 j⟩ : Fin D₀)) ?_ ?_ ?_ ?_
    · intro α _hα
      exact Finset.mem_univ _
    · intro α₁ _h₁ α₂ _h₂ heq
      ext j
      have hval : (α₁ j : ℕ) = (α₂ j : ℕ) := by
        have hcongr := congrArg Fin.val (congrFun heq j)
        simpa using! hcongr
      exact hval
    · intro β _hβ
      refine ⟨fun j => (β j).castLE h, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
        show ((β j).castLE h : ℕ) < D₀
        rw [Fin.val_castLE]
        exact (β j).isLt
      · funext j
        exact Fin.ext rfl
    · intro α hmem
      have hα : ∀ j, (α j : ℕ) < D₀ := Finset.mem_filter.mp hmem |>.2
      exact prod_embed_eq_prod_of_good h hα
  rw [hsplit, hfilter]

/-- Padding MPS tensors with zeros preserves their representation of the state `ψ`. -/
theorem isMpsRepresentation_embed {n d D₀ D : ℕ} [NeZero D₀] [NeZero D] (h : D₀ ≤ D)
    {A : Fin n → Fin d → Matrix (Fin D₀) (Fin D₀) ℂ} {ψ : (Fin n → Fin d) → ℂ}
    (hA : IsMpsRepresentation A ψ) :
    IsMpsRepresentation (fun i y => mpsEmbed h (A i y)) ψ := by
  intro x
  rw [mpsAmplitude_embed h A x]
  exact hA x

end Embed

/-- If `ψ` has an exact MPS representation of bond dimension at most positive `D` and all its
cut ranks are at most `D`, it has a bond-dimension-`D` approximation satisfying the stated
Schmidt-tail bound. -/
theorem clause2_clause3_of_exact_le (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) {D : ℕ} (hD : 0 < D)
    (hex : ∃ (D₀ : ℕ) (h₀ : NeZero D₀) (A : Fin n → Fin d → Matrix (Fin D₀) (Fin D₀) ℂ),
      @IsMpsRepresentation n d D₀ h₀ A ψ ∧ D₀ ≤ D)
    (hrank : ∀ c ∈ Finset.range n, cutRank n d ψ c ≤ D) :
    ∃ (hD' : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∑ x, Complex.normSq (@mpsAmplitude n d D hD' A x - ψ x)
        ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  obtain ⟨D₀, h₀, A₀, hA₀, hle⟩ := hex
  have hD' : NeZero D := ⟨Nat.pos_iff_ne_zero.mp hD⟩
  refine ⟨hD', fun i y => mpsEmbed hle (A₀ i y), ?_⟩
  have heq : ∀ x, @mpsAmplitude n d D hD' (fun i y => mpsEmbed hle (A₀ i y)) x = ψ x := by
    intro x
    rw [mpsAmplitude_embed hle A₀ x]
    exact hA₀ x
  have hzero : (∑ x, Complex.normSq
        (@mpsAmplitude n d D hD' (fun i y => mpsEmbed hle (A₀ i y)) x - ψ x)) = 0 := by
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [heq x, sub_self]
    exact Complex.normSq_zero
  have htail : ∀ c ∈ Finset.range n, schmidtTailSq n d ψ c D = 0 := by
    intro c hc
    exact schmidtTailSq_eq_zero_of_cutRank_le ψ (hrank c hc)
  rw [hzero, Finset.sum_eq_zero htail, mul_zero]

/-- For any one-site state and positive `D`, there are bond-dimension-`D` MPS tensors satisfying
the squared-error bound by twice the sum of squared Schmidt tails. -/
theorem clause2_clause3_one (d : ℕ) (ψ : (Fin 1 → Fin d) → ℂ) :
    ∀ D : ℕ, 0 < D →
      ∃ (hD : NeZero D) (A : Fin 1 → Fin d → Matrix (Fin D) (Fin D) ℂ),
        ∑ x, Complex.normSq (@mpsAmplitude 1 d D hD A x - ψ x)
          ≤ 2 * ∑ c ∈ Finset.range 1, schmidtTailSq 1 d ψ c D := by
  intro D hD
  refine clause2_clause3_of_exact_le 1 d ψ hD ?_ ?_
  · refine ⟨1, inferInstance,
      fun (_i : Fin 1) (y : Fin d) => Matrix.of fun _ _ => ψ (fun _ => y), ?_, by omega⟩
    intro x
    rw [mpsAmplitude_one]
    show (Matrix.of fun _ _ => ψ (fun _ => x 0)) (0 : Fin 1) (0 : Fin 1) = ψ x
    simp only [Matrix.of_apply]
    congr 1
    funext i
    exact (congrArg x (Fin.eq_zero i)).symm
  · intro c hc
    have hc0 : c = 0 := by simp at hc; omega
    subst hc0
    exact le_trans (cutRank_le_one_left ψ) (by omega : (1 : ℕ) ≤ D)

/-- If `Mᴴ * M = 1`, the entrywise inner products of the columns of `M` are Kronecker deltas. -/
theorem gram_apply_of_eq_one {m k : ℕ} {M : Matrix (Fin m) (Fin k) ℂ} (h : Mᴴ * M = 1)
    (j₁ j₂ : Fin k) : (∑ i : Fin m, star (M i j₁) * M i j₂) = if j₁ = j₂ then (1 : ℂ) else 0 := by
  have hentry := congrFun (congrFun h j₁) j₂
  have hexp : ((Mᴴ * M : Matrix (Fin k) (Fin k) ℂ) j₁ j₂) = ∑ i : Fin m, star (M i j₁) * M i j₂ := by
    calc (Mᴴ * M) j₁ j₂
        = ∑ i : Fin m, (Mᴴ) j₁ i * M i j₂ :=
          Matrix.mul_apply (M := Mᴴ) (N := M) (i := j₁) (k := j₂)
      _ = ∑ i : Fin m, star (M i j₁) * M i j₂ :=
          Finset.sum_congr rfl (fun i _ => by rw [Matrix.conjTranspose_apply M i j₁])
  rw [hexp, Matrix.one_apply (i := j₁) (j := j₂)] at hentry
  exact hentry

/-- Kronecker delta inner products of all column pairs imply `Mᴴ * M = 1`. -/
theorem eq_one_of_gram_apply {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ)
    (h : ∀ j₁ j₂ : Fin k, (∑ i : Fin m, star (M i j₁) * M i j₂) = if j₁ = j₂ then (1 : ℂ) else 0) :
    Mᴴ * M = 1 := by
  ext j₁ j₂
  have h1 : ((Mᴴ * M : Matrix (Fin k) (Fin k) ℂ) j₁ j₂) = ∑ i : Fin m, star (M i j₁) * M i j₂ := by
    calc (Mᴴ * M) j₁ j₂
        = ∑ i : Fin m, (Mᴴ) j₁ i * M i j₂ :=
          Matrix.mul_apply (M := Mᴴ) (N := M) (i := j₁) (k := j₂)
      _ = ∑ i : Fin m, star (M i j₁) * M i j₂ :=
          Finset.sum_congr rfl (fun i _ => by rw [Matrix.conjTranspose_apply M i j₁])
  rw [h1, Matrix.one_apply (i := j₁) (j := j₂)]
  exact h j₁ j₂

/-- For positive `d` and `r ≤ D`, an isometric matrix with `r` columns in dimension `D * d`
extends to an isometric matrix with `D` columns, preserving the original columns. -/
theorem exists_isometry_extend {D r d : ℕ} (hr : r ≤ D) (hd : 0 < d)
    (V₀ : Matrix (Fin (D * d)) (Fin r) ℂ) (hV₀ : V₀ᴴ * V₀ = 1) :
    ∃ V : Matrix (Fin (D * d)) (Fin D) ℂ, Vᴴ * V = 1 ∧
      ∀ (j : Fin r) (i : Fin (D * d)),
        V i ⟨(j : ℕ), lt_of_lt_of_le j.isLt hr⟩ = V₀ i j := by
  classical
  set v : Fin (D * d) → EuclideanSpace ℂ (Fin (D * d)) := (fun k =>
    if hk : (k : ℕ) < r then WithLp.toLp 2 (fun i => V₀ i ⟨k, hk⟩) else 0) with hvdef
  have horth : Orthonormal ℂ (({k : Fin (D * d) | (k : ℕ) < r} : Set _).domRestrict v) := by
    refine ⟨?_, ?_⟩
    · intro k
      have hk : ((k : Fin (D * d)) : ℕ) < r := k.2
      show ‖v (k : Fin (D * d))‖ = 1
      simp only [hvdef, dite_eq_left hk]
      set w : EuclideanSpace ℂ (Fin (D * d)) := WithLp.toLp 2 (fun i => V₀ i ⟨k, hk⟩) with hw
      have hgram1 : (∑ i : Fin (D * d), star (V₀ i ⟨k, hk⟩) * V₀ i ⟨k, hk⟩) = (1 : ℂ) := by
        rw [gram_apply_of_eq_one hV₀ ⟨k, hk⟩ ⟨k, hk⟩]
        simp
      have hinner : inner ℂ w w = (∑ i : Fin (D * d), star (V₀ i ⟨k, hk⟩) * V₀ i ⟨k, hk⟩) := by
        rw [hw, PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [RCLike.inner_apply]
        rw [mul_comm, Complex.star_def]
      have hsq : ‖w‖ ^ 2 = 1 := by
        have h2 : inner ℂ w w = (1 : ℂ) := hinner.trans hgram1
        apply Complex.ofReal_injective
        simpa only [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K] using! h2
      exact (sq_eq_sq₀ (norm_nonneg w) (by norm_num)).mp (by rw [one_pow]; exact hsq)
    · refine fun k₁ k₂ hne => ?_
      have hk₁ : ((k₁ : Fin (D * d)) : ℕ) < r := k₁.2
      have hk₂ : ((k₂ : Fin (D * d)) : ℕ) < r := k₂.2
      show inner ℂ (v (k₁ : Fin (D * d))) (v (k₂ : Fin (D * d))) = 0
      simp only [hvdef, dite_eq_left hk₁, dite_eq_left hk₂]
      set w₁ : EuclideanSpace ℂ (Fin (D * d)) := WithLp.toLp 2 (fun i => V₀ i ⟨k₁, hk₁⟩) with hw₁
      set w₂ : EuclideanSpace ℂ (Fin (D * d)) := WithLp.toLp 2 (fun i => V₀ i ⟨k₂, hk₂⟩) with hw₂
      have hgram := gram_apply_of_eq_one hV₀ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
      have hne' : (⟨k₁, hk₁⟩ : Fin r) ≠ ⟨k₂, hk₂⟩ := by
        intro hcongr
        have hval : ((⟨k₁, hk₁⟩ : Fin r) : ℕ) = ((⟨k₂, hk₂⟩ : Fin r) : ℕ) :=
          congrArg (fun t : Fin r => (t : ℕ)) hcongr
        apply hne
        apply Subtype.ext
        apply Fin.ext
        simpa using! hval
      simp only [ite_eq_right hne'] at hgram
      have hinner : inner ℂ w₁ w₂ = (∑ i : Fin (D * d), star (V₀ i ⟨k₁, hk₁⟩) * V₀ i ⟨k₂, hk₂⟩) := by
        rw [hw₁, hw₂, PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [RCLike.inner_apply]
        rw [mul_comm, Complex.star_def]
      rw [hinner, hgram]
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin (D * d))) = Fintype.card (Fin (D * d)) := by
    simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  have hblt : ∀ k : Fin D, (k : ℕ) < D * d := by
    intro k
    have hk := k.isLt
    have hDm : D ≤ D * d := Nat.le_mul_of_pos_right D hd
    omega
  refine ⟨Matrix.of fun i k => (b ⟨(k : ℕ), hblt k⟩ : EuclideanSpace ℂ (Fin (D * d))) i, ?_, ?_⟩
  · refine eq_one_of_gram_apply _ (fun k₁ k₂ => ?_)
    have h1 : (∑ i : Fin (D * d),
          star ((b ⟨(k₁ : ℕ), hblt k₁⟩ : EuclideanSpace ℂ (Fin (D * d))) i)
            * ((b ⟨(k₂ : ℕ), hblt k₂⟩ : EuclideanSpace ℂ (Fin (D * d))) i))
        = inner ℂ (b ⟨(k₁ : ℕ), hblt k₁⟩) (b ⟨(k₂ : ℕ), hblt k₂⟩) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [RCLike.inner_apply]
      rw [mul_comm, Complex.star_def]
    simp only [Matrix.of_apply] at h1 ⊢
    rw [h1]
    by_cases hk : k₁ = k₂
    · subst hk
      rw [b.inner_eq_ite]
      simp
    · have hk' : (⟨(k₁ : ℕ), hblt k₁⟩ : Fin (D * d)) ≠ ⟨(k₂ : ℕ), hblt k₂⟩ := by
        intro hcongr
        have hval : ((⟨(k₁ : ℕ), hblt k₁⟩ : Fin (D * d)) : ℕ)
            = ((⟨(k₂ : ℕ), hblt k₂⟩ : Fin (D * d)) : ℕ) :=
          congrArg (fun t : Fin (D * d) => (t : ℕ)) hcongr
        exact hk (Fin.ext (by exact hval))
      rw [b.inner_eq_zero hk']
      simp [hk]
  · intro j i
    simp only [Matrix.of_apply]
    have hj : ((j : Fin r) : ℕ) < r := j.isLt
    have hjm : ((j : Fin r) : ℕ) < D * d := by
      have := j.isLt
      have hDm : r ≤ D * d := le_trans hr (Nat.le_mul_of_pos_right D hd)
      omega
    have hbeq : (b ⟨(j : ℕ), hjm⟩ : EuclideanSpace ℂ (Fin (D * d)))
        = v ⟨(j : ℕ), hjm⟩ := hb ⟨(j : ℕ), hjm⟩ (by rw [Set.mem_ofPred_eq]; exact hj)
    have hvv : (v ⟨(j : ℕ), hjm⟩ : EuclideanSpace ℂ (Fin (D * d)))
        = WithLp.toLp 2 (fun i => V₀ i ⟨(j : ℕ), hj⟩) := by
      simp only [hvdef, dite_eq_left hj]
    rw [hbeq, hvv, PiLp.toLp_apply]

section Clause1Peps

variable {a b d D : ℕ}

/-- The number of half-edges in the PEPS encoding: five per lattice site and, for a nonempty
grid, `2 * (a + b)` additional half-edges. -/
def pepsNh (a b : ℕ) : ℕ := 5 * a * b + (if a = 0 ∨ b = 0 then 0 else 2 * (a + b))

/-- The PEPS encoding has zero half-edges if either lattice dimension is zero. -/
theorem pepsNh_of_zero (h : a = 0 ∨ b = 0) : pepsNh a b = 0 := by
  rw [pepsNh, ite_eq_left h, Nat.add_zero]
  rcases h with h | h <;> rw [h] <;> ring

/-- For positive lattice dimensions, the PEPS encoding has `5 * a * b + 2 * (a + b)` half-edges. -/
theorem pepsNh_of_pos (ha : 0 < a) (hb : 0 < b) : pepsNh a b = 5 * a * b + 2 * (a + b) := by
  rw [pepsNh, ite_eq_right (by omega : ¬(a = 0 ∨ b = 0))]

/-- The PEPS half-edge count is at least `5 * a * b`. -/
theorem pepsNh_le (a b : ℕ) : 5 * a * b ≤ pepsNh a b := by
  rw [pepsNh]
  split_ifs <;> omega

/-- An index in the additional PEPS half-edge range has offset below `2 * (a + b)`. -/
theorem pepsNh_lt_add (a b : ℕ) (h : ¬(a = 0 ∨ b = 0)) (j : ℕ) (hj : 5 * a * b ≤ j)
    (hj2 : j < pepsNh a b) : j - 5 * a * b < 2 * (a + b) := by
  rw [pepsNh, ite_eq_right h] at hj2
  omega

/-- If neither lattice dimension is zero, both are positive. -/
theorem pepsNh_pos_of_nzero (a b : ℕ) (h : ¬(a = 0 ∨ b = 0)) :
    0 < a ∧ 0 < b := by
  constructor <;> by_contra hc <;> apply h <;> omega

/-- Assigns dimension `d` to each physical PEPS leg and dimension `D` to all other half-edges. -/
def pepsDim (a b d D : ℕ) (j : ℕ) : ℕ := if j < 5 * a * b ∧ j % 5 = 0 then d else D

/-- A regular PEPS half-edge whose index is divisible by five has physical dimension `d`. -/
theorem pepsDim_phys (a b d D : ℕ) {j : ℕ} (h : j < 5 * a * b) (h2 : j % 5 = 0) :
    pepsDim a b d D j = d := by
  rw [pepsDim, ite_eq_left ⟨h, h2⟩]

/-- A PEPS half-edge whose index is not divisible by five has bond dimension `D`. -/
theorem pepsDim_reg (a b d D : ℕ) {j : ℕ} (h2 : j % 5 ≠ 0) :
    pepsDim a b d D j = D := by
  rw [pepsDim, ite_eq_right (fun ⟨_, hc⟩ => h2 hc)]

/-- An additional half-edge beyond the five-per-site range has dimension `D`. -/
theorem pepsDim_dummy (a b d D : ℕ) {j : ℕ} (h : 5 * a * b ≤ j) :
    pepsDim a b d D j = D := by
  rw [pepsDim, ite_eq_right (fun ⟨hj, _⟩ => absurd hj (by omega))]

/-- For `r < 5`, the remainder of `5 * k + r` modulo five is `r`. -/
theorem pepsLeg_mod (k r : ℕ) (hr : r < 5) : (5 * k + r) % 5 = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- For `r < 5`, dividing `5 * k + r` by five gives `k`. -/
theorem pepsLeg_div (k r : ℕ) (hr : r < 5) : (5 * k + r) / 5 = k := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (show 0 < 5 by omega), Nat.div_eq_of_lt hr]
  omega

/-- For a site index `k < a * b` and leg offset `r < 5`, the regular half-edge index lies below
`5 * a * b`. -/
theorem pepsLeg_lt (a b k r : ℕ) (hk : k < a * b) (hr : r < 5) : 5 * k + r < 5 * a * b := by
  have h1 : 5 * k + r < 5 * (k + 1) := by omega
  have h2 : k + 1 ≤ a * b := by omega
  have h3 : 5 * (k + 1) ≤ 5 * (a * b) := Nat.mul_le_mul_left 5 h2
  have h4 : 5 * a * b = 5 * (a * b) := by ring
  omega

/-- Every regular PEPS leg index lies below the total half-edge count. -/
theorem pepsLeg_lt_nh (a b k r : ℕ) (hk : k < a * b) (hr : r < 5) :
    5 * k + r < pepsNh a b := by
  have := pepsLeg_lt a b k r hk hr
  have := pepsNh_le a b
  omega

/-- Division and remainder reconstruct a natural index as `b * (k / b) + k % b`. -/
theorem peps_divmod (k b : ℕ) : b * (k / b) + k % b = k := Nat.div_add_mod k b

/-- If incrementing the remainder does not reach `b`, incrementing an index preserves its
quotient and increments its remainder. -/
theorem peps_mod_div_succ (k b : ℕ) (hb : 0 < b) (h : k % b + 1 < b) :
    (k + 1) % b = k % b + 1 ∧ (k + 1) / b = k / b := by
  have hd := peps_divmod k b
  have h1 : (b * (k / b) + (k % b + 1)) % b = k % b + 1 := by
    rw [Nat.add_comm (b * (k / b)), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  have h2 : (b * (k / b) + (k % b + 1)) / b = k / b := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt h, Nat.add_zero]
  have he : k + 1 = b * (k / b) + (k % b + 1) := by
    have h4 : b * (k / b) + (k % b + 1) = b * (k / b) + k % b + 1 := by
      rw [Nat.add_assoc]
    omega
  exact ⟨by rw [he]; exact h1, by rw [he]; exact h2⟩

/-- For a positive divisor and nonzero remainder, decrementing an index preserves its quotient
and decrements its remainder. -/
theorem peps_mod_div_pred (k b : ℕ) (hb : 0 < b) (h : k % b ≠ 0) :
    (k - 1) % b = k % b - 1 ∧ (k - 1) / b = k / b := by
  have hd := peps_divmod k b
  have hlt : k % b - 1 < b :=
    Nat.lt_of_le_of_lt (Nat.sub_le (k % b) 1) (Nat.mod_lt k hb)
  have h1 : (b * (k / b) + (k % b - 1)) % b = k % b - 1 := by
    rw [Nat.add_comm (b * (k / b)), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have h2 : (b * (k / b) + (k % b - 1)) / b = k / b := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hlt, Nat.add_zero]
  have he : k - 1 = b * (k / b) + (k % b - 1) := by
    have h4 : b * (k / b) + (k % b - 1) + 1 = b * (k / b) + k % b := by
      rw [Nat.add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ k % b)]
    omega
  exact ⟨by rw [he]; exact h1, by rw [he]; exact h2⟩

/-- For positive `a` and `b`, the last index `a * b - 1` has remainder `b - 1` modulo `b`. -/
theorem peps_mod_last (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : (a * b - 1) % b = b - 1 := by
  have h1 : b * (a - 1) + (b - 1) = a * b - 1 := by
    have h5 : (a - 1) + 1 = a := by omega
    have h3 : b * ((a - 1) + 1) = a * b := by rw [h5, Nat.mul_comm]
    have h3'' : b * (a - 1) + b = b * ((a - 1) + 1) := by
      have := Nat.mul_add b (a - 1) 1
      rw [Nat.mul_one] at this
      exact this.symm
    have h4 : b * (a - 1) + b = a * b := by rw [h3'', h3]
    omega
  rw [← h1, Nat.add_comm (b * (a - 1)), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega : b - 1 < b)]

/-- A regular site index can be incremented within the grid when its remainder modulo `b` has
room to increase. -/
theorem peps_down_bound (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) (h : k % b + 1 < b)
    (h2 : k < a * b) : k + 1 < a * b := by
  by_contra hc
  have hk : k = a * b - 1 := by omega
  have hm := peps_mod_last a b ha hb
  rw [hk] at h
  omega

/-- Assigns regular PEPS legs to their lattice sites and additional half-edge pairs to boundary
sites. -/
def pepsSite (a b : ℕ) (j : Fin (pepsNh a b)) : Fin (a * b) :=
  if h : a = 0 ∨ b = 0 then
    (by
      have hz : pepsNh a b = 0 := pepsNh_of_zero h
      have hlt := j.isLt
      exact absurd (by omega : (j : ℕ) < 0) (Nat.not_lt_zero _))
  else
    if hreg : (j : ℕ) < 5 * a * b then
      ⟨(j : ℕ) / 5, by
        have hj : (j : ℕ) < 5 * (a * b) := by rwa [← Nat.mul_assoc]
        exact Nat.div_lt_of_lt_mul hj⟩
    else
      have hpos := pepsNh_pos_of_nzero a b h
      if hm : ((j : ℕ) - 5 * a * b) / 2 < b then
        ⟨(a - 1) * b + ((j : ℕ) - 5 * a * b) / 2, by
          have h1 : (a - 1) * b + b = a * b := by
            have : (a - 1) + 1 = a := by omega
            nlinarith [Nat.add_mul (a - 1) 1 b]
          omega⟩
      else
        ⟨(((j : ℕ) - 5 * a * b) / 2 - b) * b + (b - 1), by
          have hlt : ((j : ℕ) - 5 * a * b) / 2 < a + b := by
            have := pepsNh_lt_add a b h (j : ℕ) (by omega) j.isLt
            omega
          have h1 : (a - 1) * b + b = a * b := by
            have : (a - 1) + 1 = a := by omega
            nlinarith [Nat.add_mul (a - 1) 1 b]
          have h2 : ((j : ℕ) - 5 * a * b) / 2 - b ≤ a - 1 := by omega
          have h3 : (((j : ℕ) - 5 * a * b) / 2 - b) * b ≤ (a - 1) * b :=
            Nat.mul_le_mul_right b h2
          omega⟩

/-- Pairs neighboring PEPS bond legs and the additional half-edge pairs, leaving physical and
outer boundary legs unpaired. -/
def pepsPartner (a b : ℕ) (j : Fin (pepsNh a b)) : Option (Fin (pepsNh a b)) :=
  if h : a = 0 ∨ b = 0 then
    none
  else
    if hreg : (j : ℕ) < 5 * a * b then
      if h0 : (j : ℕ) % 5 = 0 then none
      else if h1 : (j : ℕ) % 5 = 1 then
        if hk : (j : ℕ) / 5 < b then none
        else some ⟨(j : ℕ) - 5 * b + 1, by
          have hpos := pepsNh_pos_of_nzero a b h
          have heq : (j : ℕ) = 5 * ((j : ℕ) / 5) + 1 := by
            have := peps_divmod (j : ℕ) 5
            omega
          have h5ab : 5 * a * b = 5 * (a * b) := by ring
          have hklt : (j : ℕ) / 5 < a * b := Nat.div_lt_of_lt_mul (by rwa [← h5ab])
          have := pepsNh_le a b
          omega⟩
      else if h2 : (j : ℕ) % 5 = 2 then
        if hk : (j : ℕ) / 5 + b < a * b then some ⟨(j : ℕ) + 5 * b - 1, by
          have heq : (j : ℕ) = 5 * ((j : ℕ) / 5) + 2 := by
            have := peps_divmod (j : ℕ) 5
            omega
          have h5ab : 5 * a * b = 5 * (a * b) := by ring
          have hkb : (j : ℕ) / 5 + b + 1 ≤ a * b := by omega
          have h5 : 5 * ((j : ℕ) / 5 + b + 1) ≤ 5 * (a * b) := Nat.mul_le_mul_left 5 hkb
          have := pepsNh_le a b
          omega⟩
        else none
      else if h3 : (j : ℕ) % 5 = 3 then
        if hk : (j : ℕ) / 5 % b + 1 < b then some ⟨(j : ℕ) + 6, by
          have hpos := pepsNh_pos_of_nzero a b h
          have heq : (j : ℕ) = 5 * ((j : ℕ) / 5) + 3 := by
            have := peps_divmod (j : ℕ) 5
            omega
          have h5ab : 5 * a * b = 5 * (a * b) := by ring
          have hklt : (j : ℕ) / 5 < a * b := Nat.div_lt_of_lt_mul (by rwa [← h5ab])
          have hkb : (j : ℕ) / 5 + 1 < a * b :=
            peps_down_bound a b ((j : ℕ) / 5) hpos.1 hpos.2 hk hklt
          have h5 : 5 * ((j : ℕ) / 5 + 1) ≤ 5 * (a * b) :=
            Nat.mul_le_mul_left 5 (Nat.le_of_lt hkb)
          have := pepsNh_le a b
          omega⟩
        else none
      else
        if hk : (j : ℕ) / 5 % b = 0 then none
        else some ⟨(j : ℕ) - 6, by
          have hpos := pepsNh_pos_of_nzero a b h
          have heq : (j : ℕ) = 5 * ((j : ℕ) / 5) + 4 := by
            have := peps_divmod (j : ℕ) 5
            omega
          have hkb : 0 < (j : ℕ) / 5 := by
            by_contra hc
            have : (j : ℕ) / 5 = 0 := by omega
            simp [this] at hk
          omega⟩
    else
      if hev : ((j : ℕ) - 5 * a * b) % 2 = 0 then some ⟨(j : ℕ) + 1, by
        have hpos := pepsNh_pos_of_nzero a b h
        have hnh := pepsNh_of_pos hpos.1 hpos.2
        have hle : 5 * a * b ≤ (j : ℕ) := by omega
        have hlt := pepsNh_lt_add a b h (j : ℕ) hle j.isLt
        omega⟩
      else some ⟨(j : ℕ) - 1, by
        have := pepsNh_le a b
        have := j.isLt
        omega⟩

/-- Positive lattice dimensions imply that neither lattice dimension is zero. -/
theorem peps_not_zero (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : ¬(a = 0 ∨ b = 0) := by
  omega

/-- A physical PEPS leg is unpaired. -/
theorem pepsPartner_phys (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k, pepsLeg_lt_nh a b k 0 hk (by omega)⟩ = none := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k : ℕ) < 5 * a * b := pepsLeg_lt a b k 0 hk (by omega)
  have hmod : (5 * k : ℕ) % 5 = 0 := pepsLeg_mod k 0 (by omega)
  have hdiv : (5 * k : ℕ) / 5 = k := pepsLeg_div k 0 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_left (by trivial : True)]

/-- For `b ≤ k`, the left leg at site `k` is paired with the right leg at site `k - b`. -/
theorem pepsPartner_left_bond (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : b ≤ k) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 1, pepsLeg_lt_nh a b k 1 hk (by omega)⟩
      = some ⟨5 * (k - b) + 2, by
        have := pepsLeg_lt_nh a b k 1 hk (by omega)
        have := pepsNh_le a b
        omega⟩ := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 1 : ℕ) < 5 * a * b := pepsLeg_lt a b k 1 hk (by omega)
  have hmod : (5 * k + 1 : ℕ) % 5 = 1 := pepsLeg_mod k 1 (by omega)
  have hdiv : (5 * k + 1 : ℕ) / 5 = k := pepsLeg_div k 1 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((1 : ℕ) = 0)), dite_eq_left (by trivial : True),
    dite_eq_right (by omega : ¬(k < b))]
  apply congrArg some
  apply Fin.ext
  show (5 * k + 1 : ℕ) - 5 * b + 1 = 5 * (k - b) + 2
  omega

/-- For `k < b`, the left leg at site `k` is an unpaired boundary leg. -/
theorem pepsPartner_left_open (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : k < b) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 1, pepsLeg_lt_nh a b k 1 hk (by omega)⟩ = none := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 1 : ℕ) < 5 * a * b := pepsLeg_lt a b k 1 hk (by omega)
  have hmod : (5 * k + 1 : ℕ) % 5 = 1 := pepsLeg_mod k 1 (by omega)
  have hdiv : (5 * k + 1 : ℕ) / 5 = k := pepsLeg_div k 1 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((1 : ℕ) = 0)), dite_eq_left (by trivial : True),
    dite_eq_left hkb]

/-- If `k + b < a * b`, the right leg at site `k` is paired with the left leg at site `k + b`. -/
theorem pepsPartner_right_bond (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : k + b < a * b) :
    pepsPartner a b ⟨5 * k + 2, pepsLeg_lt_nh a b k 2 (by omega) (by omega)⟩
      = some ⟨5 * (k + b) + 1, by
        have := pepsLeg_lt_nh a b (k + b) 1 (by omega : k + b < a * b) (by omega)
        exact this⟩ := by
  have hz := peps_not_zero a b ha hb
  have hk : k < a * b := by omega
  have hreg : (5 * k + 2 : ℕ) < 5 * a * b := pepsLeg_lt a b k 2 hk (by omega)
  have hmod : (5 * k + 2 : ℕ) % 5 = 2 := pepsLeg_mod k 2 (by omega)
  have hdiv : (5 * k + 2 : ℕ) / 5 = k := pepsLeg_div k 2 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((2 : ℕ) = 0)), dite_eq_right (by omega : ¬((2 : ℕ) = 1)),
    dite_eq_left (by trivial : True), dite_eq_left (by omega : k + b < a * b)]
  apply congrArg some
  apply Fin.ext
  show (5 * k + 2 : ℕ) + 5 * b - 1 = 5 * (k + b) + 1
  omega

/-- If `k + b` lies beyond the grid, the right leg at site `k` is unpaired. -/
theorem pepsPartner_right_open (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : ¬(k + b < a * b)) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 2, pepsLeg_lt_nh a b k 2 hk (by omega)⟩ = none := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 2 : ℕ) < 5 * a * b := pepsLeg_lt a b k 2 hk (by omega)
  have hmod : (5 * k + 2 : ℕ) % 5 = 2 := pepsLeg_mod k 2 (by omega)
  have hdiv : (5 * k + 2 : ℕ) / 5 = k := pepsLeg_div k 2 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((2 : ℕ) = 0)), dite_eq_right (by omega : ¬((2 : ℕ) = 1)),
    dite_eq_left (by trivial : True), dite_eq_right hkb]

/-- If `k % b + 1 < b`, the down leg at site `k` is paired with the up leg at site `k + 1`. -/
theorem pepsPartner_down_bond (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : k % b + 1 < b) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 3, pepsLeg_lt_nh a b k 3 hk (by omega)⟩
      = some ⟨5 * (k + 1) + 4, by
        have := pepsLeg_lt_nh a b (k + 1) 4
          (peps_down_bound a b k ha hb hkb hk) (by omega)
        exact this⟩ := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 3 : ℕ) < 5 * a * b := pepsLeg_lt a b k 3 hk (by omega)
  have hmod : (5 * k + 3 : ℕ) % 5 = 3 := pepsLeg_mod k 3 (by omega)
  have hdiv : (5 * k + 3 : ℕ) / 5 = k := pepsLeg_div k 3 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((3 : ℕ) = 0)), dite_eq_right (by omega : ¬((3 : ℕ) = 1)),
    dite_eq_right (by omega : ¬((3 : ℕ) = 2)), dite_eq_left (by trivial : True),
    dite_eq_left hkb]
  apply congrArg some
  apply Fin.ext
  show (5 * k + 3 : ℕ) + 6 = 5 * (k + 1) + 4
  omega

/-- If `k % b + 1` is not below `b`, the down leg at site `k` is unpaired. -/
theorem pepsPartner_down_open (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : ¬(k % b + 1 < b)) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 3, pepsLeg_lt_nh a b k 3 hk (by omega)⟩ = none := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 3 : ℕ) < 5 * a * b := pepsLeg_lt a b k 3 hk (by omega)
  have hmod : (5 * k + 3 : ℕ) % 5 = 3 := pepsLeg_mod k 3 (by omega)
  have hdiv : (5 * k + 3 : ℕ) / 5 = k := pepsLeg_div k 3 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((3 : ℕ) = 0)), dite_eq_right (by omega : ¬((3 : ℕ) = 1)),
    dite_eq_right (by omega : ¬((3 : ℕ) = 2)), dite_eq_left (by trivial : True),
    dite_eq_right hkb]

/-- If `k % b` is nonzero, the up leg at site `k` is paired with the down leg at site `k - 1`. -/
theorem pepsPartner_up_bond (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : k % b ≠ 0) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 4, pepsLeg_lt_nh a b k 4 hk (by omega)⟩
      = some ⟨5 * (k - 1) + 3, by
        have hk0 : 0 < k := by
          by_contra hc
          have : k = 0 := by omega
          subst this
          simp at hkb
        have := pepsLeg_lt_nh a b (k - 1) 3 (by omega) (by omega)
        exact this⟩ := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 4 : ℕ) < 5 * a * b := pepsLeg_lt a b k 4 hk (by omega)
  have hmod : (5 * k + 4 : ℕ) % 5 = 4 := pepsLeg_mod k 4 (by omega)
  have hdiv : (5 * k + 4 : ℕ) / 5 = k := pepsLeg_div k 4 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((4 : ℕ) = 0)), dite_eq_right (by omega : ¬((4 : ℕ) = 1)),
    dite_eq_right (by omega : ¬((4 : ℕ) = 2)), dite_eq_right (by omega : ¬((4 : ℕ) = 3)),
    dite_eq_right hkb]
  apply congrArg some
  apply Fin.ext
  have hk0 : 0 < k := by
    by_contra hc
    have : k = 0 := by omega
    subst this
    simp at hkb
  show (5 * k + 4 : ℕ) - 6 = 5 * (k - 1) + 3
  omega

/-- If `k % b = 0`, the up leg at site `k` is unpaired. -/
theorem pepsPartner_up_open (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkb : k % b = 0) (hk : k < a * b) :
    pepsPartner a b ⟨5 * k + 4, pepsLeg_lt_nh a b k 4 hk (by omega)⟩ = none := by
  have hz := peps_not_zero a b ha hb
  have hreg : (5 * k + 4 : ℕ) < 5 * a * b := pepsLeg_lt a b k 4 hk (by omega)
  have hmod : (5 * k + 4 : ℕ) % 5 = 4 := pepsLeg_mod k 4 (by omega)
  have hdiv : (5 * k + 4 : ℕ) / 5 = k := pepsLeg_div k 4 (by omega)
  simp only [pepsPartner, dite_eq_right hz, dite_eq_left hreg, hmod, hdiv,
    dite_eq_right (by omega : ¬((4 : ℕ) = 0)), dite_eq_right (by omega : ¬((4 : ℕ) = 1)),
    dite_eq_right (by omega : ¬((4 : ℕ) = 2)), dite_eq_right (by omega : ¬((4 : ℕ) = 3)),
    dite_eq_left hkb]

/-- The additional half-edge at offset `2 * m` from `5 * a * b` is paired with the one at offset
`2 * m + 1`. -/
theorem pepsPartner_dummy_even (a b m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : m < a + b) :
    pepsPartner a b ⟨5 * a * b + 2 * m, by
      have := pepsNh_of_pos ha hb
      omega⟩
      = some ⟨5 * a * b + 2 * m + 1, by
        have := pepsNh_of_pos ha hb
        omega⟩ := by
  have hz := peps_not_zero a b ha hb
  have hreg : ¬(5 * a * b + 2 * m < 5 * a * b) := by omega
  have hmod : ((5 * a * b + 2 * m) - 5 * a * b) % 2 = 0 := by omega
  simp only [pepsPartner, dite_eq_right hz, dite_eq_right hreg, dite_eq_left hmod]

/-- The additional half-edge at offset `2 * m + 1` from `5 * a * b` is paired with the one at
offset `2 * m`. -/
theorem pepsPartner_dummy_odd (a b m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : m < a + b) :
    pepsPartner a b ⟨5 * a * b + 2 * m + 1, by
      have := pepsNh_of_pos ha hb
      omega⟩
      = some ⟨5 * a * b + 2 * m, by
        have := pepsNh_of_pos ha hb
        omega⟩ := by
  have hz := peps_not_zero a b ha hb
  have hreg : ¬(5 * a * b + 2 * m + 1 < 5 * a * b) := by omega
  have hmod : ¬(((5 * a * b + 2 * m + 1) - 5 * a * b) % 2 = 0) := by omega
  simp only [pepsPartner, dite_eq_right hz, dite_eq_right hreg, dite_eq_right hmod]
  apply congrArg some
  apply Fin.ext
  show (5 * a * b + 2 * m + 1 : ℕ) - 1 = 5 * a * b + 2 * m
  omega

/-- Every paired PEPS half-edge belongs to one of the four directed lattice-bond cases or the
two directed additional-pair cases. -/
theorem pepsPartner_classify (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (j k : Fin (pepsNh a b)) (hj : pepsPartner a b j = some k) :
    (∃ m, (j : ℕ) = 5 * m + 1 ∧ (k : ℕ) = 5 * (m - b) + 2 ∧ b ≤ m ∧ m < a * b) ∨
    (∃ m, (j : ℕ) = 5 * m + 2 ∧ (k : ℕ) = 5 * (m + b) + 1 ∧ m + b < a * b ∧ m < a * b) ∨
    (∃ m, (j : ℕ) = 5 * m + 3 ∧ (k : ℕ) = 5 * (m + 1) + 4 ∧ m % b + 1 < b ∧ m < a * b) ∨
    (∃ m, (j : ℕ) = 5 * m + 4 ∧ (k : ℕ) = 5 * (m - 1) + 3 ∧ m % b ≠ 0 ∧ m < a * b) ∨
    (∃ m, (j : ℕ) = 5 * a * b + 2 * m ∧ (k : ℕ) = 5 * a * b + 2 * m + 1 ∧ m < a + b) ∨
    (∃ m, (j : ℕ) = 5 * a * b + 2 * m + 1 ∧ (k : ℕ) = 5 * a * b + 2 * m ∧ m < a + b) := by
  have hd := peps_divmod (j : ℕ) 5
  have h5ab : 5 * a * b = 5 * (a * b) := by ring
  simp only [pepsPartner] at hj
  by_cases hz : a = 0 ∨ b = 0
  · rw [dite_eq_left hz] at hj
    exact absurd hj (by simp)
  · rw [dite_eq_right hz] at hj
    by_cases hreg : (j : ℕ) < 5 * a * b
    · rw [dite_eq_left hreg] at hj
      by_cases h0 : (j : ℕ) % 5 = 0
      · rw [dite_eq_left h0] at hj
        exact absurd hj (by simp)
      · rw [dite_eq_right h0] at hj
        by_cases h1 : (j : ℕ) % 5 = 1
        · rw [dite_eq_left h1] at hj
          by_cases hk1 : (j : ℕ) / 5 < b
          · rw [dite_eq_left hk1] at hj
            exact absurd hj (by simp)
          · rw [dite_eq_right hk1] at hj
            have hkval : ((j : ℕ) - 5 * b + 1) = (k : ℕ) :=
              congrArg Fin.val (Option.some.inj hj)
            exact Or.inl ⟨(j : ℕ) / 5, by omega, by omega, by omega, by omega⟩
        · rw [dite_eq_right h1] at hj
          by_cases h2 : (j : ℕ) % 5 = 2
          · rw [dite_eq_left h2] at hj
            by_cases hk2 : (j : ℕ) / 5 + b < a * b
            · rw [dite_eq_left hk2] at hj
              have hkval : ((j : ℕ) + 5 * b - 1) = (k : ℕ) :=
                congrArg Fin.val (Option.some.inj hj)
              exact Or.inr (Or.inl ⟨(j : ℕ) / 5, by omega, by omega, by omega, by omega⟩)
            · rw [dite_eq_right hk2] at hj
              exact absurd hj (by simp)
          · rw [dite_eq_right h2] at hj
            by_cases h3 : (j : ℕ) % 5 = 3
            · rw [dite_eq_left h3] at hj
              by_cases hk3 : (j : ℕ) / 5 % b + 1 < b
              · rw [dite_eq_left hk3] at hj
                have hkval : ((j : ℕ) + 6) = (k : ℕ) :=
                  congrArg Fin.val (Option.some.inj hj)
                exact Or.inr (Or.inr (Or.inl
                  ⟨(j : ℕ) / 5, by omega, by omega, by omega, by omega⟩))
              · rw [dite_eq_right hk3] at hj
                exact absurd hj (by simp)
            · rw [dite_eq_right h3] at hj
              by_cases hk4 : (j : ℕ) / 5 % b = 0
              · rw [dite_eq_left hk4] at hj
                exact absurd hj (by simp)
              · rw [dite_eq_right hk4] at hj
                have hkval : ((j : ℕ) - 6) = (k : ℕ) :=
                  congrArg Fin.val (Option.some.inj hj)
                have hk0 : 0 < (j : ℕ) / 5 := by
                  by_contra hc
                  have : (j : ℕ) / 5 = 0 := by omega
                  rw [this] at hk4
                  simp at hk4
                exact Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨(j : ℕ) / 5, by omega, by omega, by omega, by omega⟩)))
    · rw [dite_eq_right hreg] at hj
      have hnh := pepsNh_of_pos ha hb
      by_cases hev : ((j : ℕ) - 5 * a * b) % 2 = 0
      · rw [dite_eq_left hev] at hj
        have hkval : ((j : ℕ) + 1) = (k : ℕ) :=
          congrArg Fin.val (Option.some.inj hj)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨((j : ℕ) - 5 * a * b) / 2, by omega, by omega, by omega⟩))))
      · rw [dite_eq_right hev] at hj
        have hkval : ((j : ℕ) - 1) = (k : ℕ) :=
          congrArg Fin.val (Option.some.inj hj)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨((j : ℕ) - 5 * a * b) / 2, by omega, by omega, by omega⟩))))

/-- The PEPS partner relation is involutive. -/
theorem pepsPartner_involution (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (j k : Fin (pepsNh a b)) (hj : pepsPartner a b j = some k) :
    pepsPartner a b k = some j := by
  obtain ⟨m, hjm, hkm, hmb, hmlt⟩ | ⟨m, hjm, hkm, hmk, hmlt⟩ |
      ⟨m, hjm, hkm, hmk, hmlt⟩ | ⟨m, hjm, hkm, hmk, hmlt⟩ |
      ⟨m, hjm, hkm, hmlt⟩ | ⟨m, hjm, hkm, hmlt⟩ :=
    pepsPartner_classify a b ha hb j k hj
  · have hkfin : k = ⟨5 * (m - b) + 2, by
        have := pepsLeg_lt_nh a b (m - b) 2 (by omega) (by omega)
        exact this⟩ := Fin.ext hkm
    rw [hkfin]
    have h := pepsPartner_right_bond a b (m - b) ha hb (by omega)
    rw [h]
    refine congrArg some (Fin.ext ?_)
    show (5 * (m - b + b) + 1 : ℕ) = (j : ℕ)
    omega
  · have hkfin : k = ⟨5 * (m + b) + 1, by
        have := pepsLeg_lt_nh a b (m + b) 1 (by omega) (by omega)
        exact this⟩ := Fin.ext hkm
    rw [hkfin]
    have h := pepsPartner_left_bond a b (m + b) ha hb (by omega) (by omega)
    rw [h]
    refine congrArg some (Fin.ext ?_)
    show (5 * (m + b - b) + 2 : ℕ) = (j : ℕ)
    omega
  · have hkfin : k = ⟨5 * (m + 1) + 4, by
        have hbnd : m + 1 < a * b := peps_down_bound a b m ha hb hmk hmlt
        have := pepsLeg_lt_nh a b (m + 1) 4 hbnd (by omega)
        exact this⟩ := Fin.ext hkm
    rw [hkfin]
    have hs := (peps_mod_div_succ m b hb hmk).1
    have hcond : (m + 1) % b ≠ 0 := by
      rw [hs]; omega
    have hbnd : m + 1 < a * b := peps_down_bound a b m ha hb hmk hmlt
    have h := pepsPartner_up_bond a b (m + 1) ha hb hcond hbnd
    rw [h]
    refine congrArg some (Fin.ext ?_)
    show (5 * (m + 1 - 1) + 3 : ℕ) = (j : ℕ)
    omega
  · have hm0 : 0 < m := by
      by_contra hc
      have : m = 0 := by omega
      subst this
      simp at hmk
    have hbound : m - 1 < a * b := Nat.lt_of_le_of_lt (Nat.sub_le m 1) hmlt
    have hkfin : k = ⟨5 * (m - 1) + 3, by
        have := pepsLeg_lt_nh a b (m - 1) 3 hbound (by omega)
        exact this⟩ := Fin.ext hkm
    rw [hkfin]
    have hpred := peps_mod_div_pred m b hb hmk
    have hcond : (m - 1) % b + 1 < b := by
      have hmltb : m % b < b := Nat.mod_lt m hb
      rw [hpred.1]; omega
    have h := pepsPartner_down_bond a b (m - 1) ha hb hcond hbound
    rw [h]
    refine congrArg some (Fin.ext ?_)
    show (5 * ((m - 1) + 1) + 4 : ℕ) = (j : ℕ)
    omega
  · have hkfin : k = ⟨5 * a * b + 2 * m + 1, by
        have := pepsNh_of_pos ha hb
        omega⟩ := Fin.ext hkm
    rw [hkfin]
    have h := pepsPartner_dummy_odd a b m ha hb hmlt
    rw [h]
    refine congrArg some (Fin.ext ?_)
    show (5 * a * b + 2 * m : ℕ) = (j : ℕ)
    omega
  · have hkfin : k = ⟨5 * a * b + 2 * m, by
        have := pepsNh_of_pos ha hb
        omega⟩ := Fin.ext hkm
    rw [hkfin]
    have h := pepsPartner_dummy_even a b m ha hb hmlt
    rw [h]
    refine congrArg some (Fin.ext ?_)
    show (5 * a * b + 2 * m + 1 : ℕ) = (j : ℕ)
    omega

/-- A paired PEPS half-edge is distinct from its partner. -/
theorem pepsPartner_no_self (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (j k : Fin (pepsNh a b)) (hj : pepsPartner a b j = some k) : j ≠ k := by
  intro heq
  subst heq
  obtain ⟨m, hjm, hkm, hmb, hmlt⟩ | ⟨m, hjm, hkm, hmk, hmlt⟩ |
      ⟨m, hjm, hkm, hmk, hmlt⟩ | ⟨m, hjm, hkm, hmk, hmlt⟩ |
      ⟨m, hjm, hkm, hmlt⟩ | ⟨m, hjm, hkm, hmlt⟩ :=
    pepsPartner_classify a b ha hb j j hj
  · omega
  · omega
  · omega
  · have hm0 : 0 < m := by
      by_contra hc
      have : m = 0 := by omega
      subst this
      simp at hmk
    omega
  · omega
  · omega

/-- Paired PEPS half-edges have equal dimensions. -/
theorem pepsPartner_dims (a b d D : ℕ) (ha : 0 < a) (hb : 0 < b)
    (j k : Fin (pepsNh a b)) (hj : pepsPartner a b j = some k) :
    pepsDim a b d D j = pepsDim a b d D k := by
  obtain ⟨m, hjm, hkm, hmb, hmlt⟩ | ⟨m, hjm, hkm, hmk, hmlt⟩ |
      ⟨m, hjm, hkm, hmk, hmlt⟩ | ⟨m, hjm, hkm, hmk, hmlt⟩ |
      ⟨m, hjm, hkm, hmlt⟩ | ⟨m, hjm, hkm, hmlt⟩ :=
    pepsPartner_classify a b ha hb j k hj
  · rw [pepsDim_reg a b d D (by omega), pepsDim_reg a b d D (by omega)]
  · rw [pepsDim_reg a b d D (by omega), pepsDim_reg a b d D (by omega)]
  · rw [pepsDim_reg a b d D (by omega), pepsDim_reg a b d D (by omega)]
  · rw [pepsDim_reg a b d D (by omega), pepsDim_reg a b d D (by omega)]
  · rw [pepsDim_dummy a b d D (by omega), pepsDim_dummy a b d D (by omega)]
  · rw [pepsDim_dummy a b d D (by omega), pepsDim_dummy a b d D (by omega)]

/-- Every half-edge that is not a physical PEPS leg has dimension `D`. -/
theorem pepsDim_of_not_phys (a b d D : ℕ) {j : ℕ}
    (h : ¬(j < 5 * a * b ∧ j % 5 = 0)) : pepsDim a b d D j = D := by
  rw [pepsDim, ite_eq_right h]

/-- All five regular legs at a PEPS site are assigned to that site. -/
theorem pepsSite_leg (a b : ℕ) (v : Fin (a * b)) (r : ℕ) (hr : r < 5) :
    pepsSite a b ⟨5 * (v : ℕ) + r, pepsLeg_lt_nh a b (v : ℕ) r v.isLt hr⟩ = v := by
  by_cases hz : a = 0 ∨ b = 0
  · rcases hz with h | h <;> rw [h] at v <;> exact absurd v.isLt (by omega)
  · have hreg : (5 * (v : ℕ) + r : ℕ) < 5 * a * b := pepsLeg_lt a b (v : ℕ) r v.isLt hr
    simp only [pepsSite, dite_eq_right hz, dite_eq_left hreg]
    apply Fin.ext
    show (5 * (v : ℕ) + r) / 5 = (v : ℕ)
    exact pepsLeg_div (v : ℕ) r hr

/-- A regular PEPS leg with nonzero offset below five has dimension `D`. -/
theorem pepsDim_bond_leg (a b d D v r : ℕ) (hr : r < 5) (hne : r ≠ 0) :
    pepsDim a b d D (5 * v + r) = D := by
  apply pepsDim_reg
  rw [pepsLeg_mod v r hr]
  exact hne

/-- The local PEPS tensor obtained from `T` using the physical and four directional legs, with
outer boundary bond indices fixed to zero. -/
noncomputable def pepsTensor (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (v : Fin (a * b))
    (α : ∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v},
        Fin (pepsDim a b d D h.val.val)) : ℂ :=
  let p := (finProdFinEquiv (m := a) (n := b)).symm v
  T p.1 p.2
    (Fin.cast (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
        (pepsLeg_mod (v : ℕ) 0 (by omega)))
      (α ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩,
        pepsSite_leg a b v 0 (by omega)⟩))
    (if h : (p.1 : ℕ) = 0 then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega))
        (α ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
          pepsSite_leg a b v 1 (by omega)⟩))
    (if (p.1 : ℕ) + 1 = a then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega))
        (α ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
          pepsSite_leg a b v 2 (by omega)⟩))
    (if (p.2 : ℕ) + 1 = b then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega))
        (α ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
          pepsSite_leg a b v 3 (by omega)⟩))
    (if h : (p.2 : ℕ) = 0 then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))
        (α ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
          pepsSite_leg a b v 4 (by omega)⟩))

/-- Encodes the PEPS tensors `T` as a tensor network on the rectangular grid, including the
additional paired half-edges. -/
noncomputable def pepsNet (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    TensorNet where
  nv := a * b
  nh := pepsNh a b
  dims := fun j => pepsDim a b d D (j : ℕ)
  site := fun j => pepsSite a b j
  partner := fun j => pepsPartner a b j
  involution := by
    intro j k hj
    by_cases hz : a = 0 ∨ b = 0
    · have hzz : pepsNh a b = 0 := pepsNh_of_zero hz
      have hlt := j.isLt
      exact absurd (by omega : (j : ℕ) < 0) (Nat.not_lt_zero _)
    · have ha : 0 < a := by
        by_contra hc; apply hz; left; omega
      have hb : 0 < b := by
        by_contra hc; apply hz; right; omega
      exact pepsPartner_involution a b ha hb j k hj
  no_self_loop := by
    intro j k hj
    by_cases hz : a = 0 ∨ b = 0
    · have hzz : pepsNh a b = 0 := pepsNh_of_zero hz
      have hlt := j.isLt
      exact absurd (by omega : (j : ℕ) < 0) (Nat.not_lt_zero _)
    · have ha : 0 < a := by
        by_contra hc; apply hz; left; omega
      have hb : 0 < b := by
        by_contra hc; apply hz; right; omega
      exact pepsPartner_no_self a b ha hb j k hj
  dims_match := by
    intro j k hj
    by_cases hz : a = 0 ∨ b = 0
    · have hzz : pepsNh a b = 0 := pepsNh_of_zero hz
      have hlt := j.isLt
      exact absurd (by omega : (j : ℕ) < 0) (Nat.not_lt_zero _)
    · have ha : 0 < a := by
        by_contra hc; apply hz; left; omega
      have hb : 0 < b := by
        by_contra hc; apply hz; right; omega
      exact pepsPartner_dims a b d D ha hb j k hj
  tensor := pepsTensor a b d D T

/-- Encodes the physical configuration on PEPS physical legs and assigns zero to all other open
legs. -/
noncomputable def pepsEnc (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (o : OpenLeg (pepsNet a b d D T)) : Fin ((pepsNet a b d D T).dims o.val) :=
  if h : (o.val : ℕ) < 5 * a * b ∧ (o.val : ℕ) % 5 = 0 then
    let v : Fin (a * b) := ⟨(o.val : ℕ) / 5, by
      have hj : (o.val : ℕ) < 5 * (a * b) := by
        have h1 := h.1
        rwa [Nat.mul_assoc] at h1
      exact Nat.div_lt_of_lt_mul hj⟩
    let p := (finProdFinEquiv (m := a) (n := b)).symm v
    (x p.1 p.2).cast (pepsDim_phys a b d D h.1 h.2).symm
  else
    (0 : Fin D).cast (pepsDim_of_not_phys a b d D h).symm

/-- Incrementing the first lattice coordinate increases the flattened site index by `b`. -/
theorem peps_ib_succ (i c b : ℕ) : (i + 1) * b + c = i * b + c + b := by
  ring

/-- Flattening valid coordinates `i < a` and `c < b` gives an index below `a * b`. -/
theorem peps_ib_lt (a b i c : ℕ) (hi : i < a) (hc : c < b) : i * b + c < a * b := by
  have h1 : (a - 1) * b + b = a * b := by
    have : (a - 1) + 1 = a := by omega
    nlinarith [Nat.add_mul (a - 1) 1 b]
  have h2 : i ≤ a - 1 := by omega
  have h3 : i * b ≤ (a - 1) * b := Nat.mul_le_mul_right b h2
  nlinarith

/-- If the next first-coordinate site exists, its flattened index remains below `a * b`. -/
theorem peps_ib_add_b_lt (a b i c : ℕ) (hi : i + 1 < a) (hc : c < b) :
    i * b + c + b < a * b := by
  have h1 : (a - 1) * b + b = a * b := by
    have : (a - 1) + 1 = a := by omega
    nlinarith [Nat.add_mul (a - 1) 1 b]
  have h2 : i + 1 ≤ a - 1 := by omega
  have h3 : (i + 1) * b ≤ (a - 1) * b := Nat.mul_le_mul_right b h2
  have h4 : (i + 1) * b + c = i * b + c + b := peps_ib_succ i c b
  nlinarith

/-- The flattened index `i * b + (c + 1)` remains below `a * b` when `i < a` and `c + 1 < b`. -/
theorem peps_ib_succ_col (a b i c : ℕ) (hi : i < a) (hc : c + 1 < b) :
    i * b + (c + 1) < a * b := by
  exact peps_ib_lt a b i (c + 1) hi hc

/-- The existence of a lattice coordinate in `Fin a × Fin b` forces both lattice dimensions to
be positive. -/
theorem peps_pos_of_fin (a b : ℕ) (p : Fin a × Fin b) : 0 < a ∧ 0 < b := by
  constructor
  · by_contra hc; exact absurd p.1.isLt (by omega)
  · by_contra hc; exact absurd p.2.isLt (by omega)

/-- Taking the remainder of the flattened index `i * b + c` modulo positive `b` recovers `c`
whenever `c < b`. -/
theorem peps_ib_mod (i c b : ℕ) (_hb : 0 < b) (hc : c < b) : (i * b + c) % b = c := by
  rw [Nat.add_comm (i * b), Nat.mul_comm i b, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- The half-edge index `5 * a * b + 2 * m` of a dummy pair lies below `pepsNh a b` for positive
lattice dimensions and `m < a + b`. -/
theorem pepsNh_dummy_lt (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : m < a + b) :
    5 * a * b + 2 * m < pepsNh a b := by
  have := pepsNh_of_pos ha hb
  omega

/-- The half-edge index `5 * a * b + 2 * m + 1` of a dummy pair lies below `pepsNh a b` for
positive lattice dimensions and `m < a + b`. -/
theorem pepsNh_dummy_lt1 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : m < a + b) :
    5 * a * b + 2 * m + 1 < pepsNh a b := by
  have := pepsNh_of_pos ha hb
  omega

/-- Selects the internal edge for the right-going bond at a PEPS site, using the corresponding
dummy edge when the site lies on the right boundary. -/
noncomputable def pepsEdgeR (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) : InternalEdge (pepsNet a b d D T) :=
  if h : (p.1 : ℕ) + 1 < a then
    have hpos := peps_pos_of_fin a b p
    have hk : (p.1 : ℕ) * b + (p.2 : ℕ) < a * b :=
      peps_ib_lt a b (p.1 : ℕ) (p.2 : ℕ) p.1.isLt p.2.isLt
    have hkb : (p.1 : ℕ) * b + (p.2 : ℕ) + b < a * b :=
      peps_ib_add_b_lt a b (p.1 : ℕ) (p.2 : ℕ) h p.2.isLt
    ⟨⟨5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 2,
        pepsLeg_lt_nh a b ((p.1 : ℕ) * b + (p.2 : ℕ)) 2 hk (by omega)⟩,
      ⟨⟨5 * (((p.1 : ℕ) * b + (p.2 : ℕ)) + b) + 1,
          pepsLeg_lt_nh a b (((p.1 : ℕ) * b + (p.2 : ℕ)) + b) 1 hkb (by omega)⟩,
        pepsPartner_right_bond a b ((p.1 : ℕ) * b + (p.2 : ℕ)) hpos.1 hpos.2 hkb,
        Fin.mk_lt_mk.mpr (by omega)⟩⟩
  else
    have hpos := peps_pos_of_fin a b p
    have hm : (p.2 : ℕ) < a + b := by have := p.2.isLt; omega
    ⟨⟨5 * a * b + 2 * (p.2 : ℕ), pepsNh_dummy_lt a b (p.2 : ℕ) hpos.1 hpos.2 hm⟩,
      ⟨⟨5 * a * b + 2 * (p.2 : ℕ) + 1, pepsNh_dummy_lt1 a b (p.2 : ℕ) hpos.1 hpos.2 hm⟩,
        pepsPartner_dummy_even a b (p.2 : ℕ) hpos.1 hpos.2 hm,
        Fin.mk_lt_mk.mpr (by omega)⟩⟩

/-- Selects the internal edge for the downward bond at a PEPS site, using the corresponding
dummy edge when the site lies on the bottom boundary. -/
noncomputable def pepsEdgeD (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) : InternalEdge (pepsNet a b d D T) :=
  if h : (p.2 : ℕ) + 1 < b then
    have hpos := peps_pos_of_fin a b p
    have hk : (p.1 : ℕ) * b + (p.2 : ℕ) < a * b :=
      peps_ib_lt a b (p.1 : ℕ) (p.2 : ℕ) p.1.isLt p.2.isLt
    have hk1 : (p.1 : ℕ) * b + (p.2 : ℕ) + 1 < a * b := by
      have := peps_ib_succ_col a b (p.1 : ℕ) (p.2 : ℕ) p.1.isLt h
      omega
    have hmod : ((p.1 : ℕ) * b + (p.2 : ℕ)) % b + 1 < b := by
      have := peps_ib_mod (p.1 : ℕ) (p.2 : ℕ) b hpos.2 p.2.isLt
      omega
    ⟨⟨5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 3,
        pepsLeg_lt_nh a b ((p.1 : ℕ) * b + (p.2 : ℕ)) 3 hk (by omega)⟩,
      ⟨⟨5 * (((p.1 : ℕ) * b + (p.2 : ℕ)) + 1) + 4,
          pepsLeg_lt_nh a b (((p.1 : ℕ) * b + (p.2 : ℕ)) + 1) 4 hk1 (by omega)⟩,
        pepsPartner_down_bond a b ((p.1 : ℕ) * b + (p.2 : ℕ)) hpos.1 hpos.2 hmod hk,
        Fin.mk_lt_mk.mpr (by omega)⟩⟩
  else
    have hpos := peps_pos_of_fin a b p
    have hm : b + (p.1 : ℕ) < a + b := by have := p.1.isLt; omega
    ⟨⟨5 * a * b + 2 * (b + (p.1 : ℕ)),
        pepsNh_dummy_lt a b (b + (p.1 : ℕ)) hpos.1 hpos.2 hm⟩,
      ⟨⟨5 * a * b + 2 * (b + (p.1 : ℕ)) + 1,
          pepsNh_dummy_lt1 a b (b + (p.1 : ℕ)) hpos.1 hpos.2 hm⟩,
        pepsPartner_dummy_even a b (b + (p.1 : ℕ)) hpos.1 hpos.2 hm,
        Fin.mk_lt_mk.mpr (by omega)⟩⟩

/-- Dividing the flattened index `i * b + c` by positive `b` recovers `i` whenever `c < b`. -/
theorem peps_ib_div (i c b : ℕ) (hb : 0 < b) (hc : c < b) : (i * b + c) / b = i := by
  rw [Nat.mul_comm i b, Nat.mul_add_div hb, Nat.div_eq_of_lt hc, Nat.add_zero]

/-- For an in-bounds coordinate, a right neighbor exists exactly when adding `b` to its
flattened index remains below `a * b`. -/
theorem peps_right_cond (a b i c : ℕ) (_hb : 0 < b) (hi : i < a) (hc : c < b) :
    (i + 1 < a) ↔ (i * b + c + b < a * b) := by
  constructor
  · intro h; exact peps_ib_add_b_lt a b i c h hc
  · intro h
    by_contra hn
    have hi1 : i = a - 1 := by omega
    have h1 : (a - 1) * b + b = a * b := by
      have : (a - 1) + 1 = a := by omega
      nlinarith [Nat.add_mul (a - 1) 1 b]
    have h3 : i * b ≤ (a - 1) * b := by
      have : i ≤ a - 1 := by omega
      exact Nat.mul_le_mul_right b this
    nlinarith

/-- An index below `a * b` has quotient by `b` strictly below `a`. -/
theorem peps_mb_div (a b m : ℕ) (hmb : m < a * b) : m / b < a := by
  apply Nat.div_lt_of_lt_mul
  rwa [Nat.mul_comm]

/-- The smaller half-edge of a PEPS internal edge is either a right-bond leg, a down-bond leg,
or the even half of a dummy pair. Each case includes the bounds on its underlying site or
dummy index. -/
theorem peps_rep_form (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (j k : Fin (pepsNh a b)) (hj : pepsPartner a b j = some k) (hlt : j < k) :
    (∃ m, (j : ℕ) = 5 * m + 2 ∧ m + b < a * b ∧ m < a * b) ∨
    (∃ m, (j : ℕ) = 5 * m + 3 ∧ m % b + 1 < b ∧ m < a * b) ∨
    (∃ m, (j : ℕ) = 5 * a * b + 2 * m ∧ m < a + b) := by
  obtain ⟨m, hjm, hkm, hs1, hs2⟩ | ⟨m, hjm, hkm, hs1, hs2⟩ |
      ⟨m, hjm, hkm, hs1, hs2⟩ | ⟨m, hjm, hkm, hs1, hs2⟩ |
      ⟨m, hjm, hkm, hs1⟩ | ⟨m, hjm, hkm, hs1⟩ :=
    pepsPartner_classify a b ha hb j k hj
  · exact absurd hlt (by
      simp only [Fin.lt_def]
      omega)
  · exact Or.inl ⟨m, hjm, hs1, hs2⟩
  · exact Or.inr (Or.inl ⟨m, hjm, hs1, hs2⟩)
  · exact absurd hlt (by
      simp only [Fin.lt_def]
      have hm0 : 0 < m := by
        by_contra hc
        have : m = 0 := by omega
        subst this
        simp at hs1
      omega)
  · exact Or.inr (Or.inr ⟨m, hjm, hs1⟩)
  · exact absurd hlt (by
      simp only [Fin.lt_def]
      omega)

/-- Decodes a PEPS internal edge into a lattice site and a direction flag, with `true` for
right-going edges and `false` for downward edges. Dummy edges decode to their associated
boundary sites. -/
noncomputable def pepsEdgeIdx (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (i : InternalEdge (pepsNet a b d D T)) : (Fin a × Fin b) × Bool :=
  if h : (i.val : ℕ) < 5 * a * b then
    have hpos : 0 < a ∧ 0 < b := by
      constructor
      · by_contra hc
        have h0 : a = 0 := by omega
        have h5 : 5 * a * b = 0 := by rw [h0]; ring
        omega
      · by_contra hc
        have h0 : b = 0 := by omega
        have h5 : 5 * a * b = 0 := by rw [h0]; ring
        omega
    (⟨⟨((i.val : ℕ) / 5) / b, peps_mb_div a b ((i.val : ℕ) / 5)
        (by
          have h5ab : 5 * a * b = 5 * (a * b) := by ring
          have := Nat.div_lt_of_lt_mul (by rwa [← h5ab] : (i.val : ℕ) < 5 * (a * b))
          exact this)⟩,
      ⟨((i.val : ℕ) / 5) % b, Nat.mod_lt _ hpos.2⟩⟩,
      decide ((i.val : ℕ) % 5 = 2))
  else
    have hpos : 0 < a ∧ 0 < b := by
      have hnh : (pepsNet a b d D T).nh = pepsNh a b := rfl
      constructor
      · by_contra hc
        have h0 : a = 0 := by omega
        have hzz : pepsNh a b = 0 := pepsNh_of_zero (Or.inl h0)
        omega
      · by_contra hc
        have h0 : b = 0 := by omega
        have hzz : pepsNh a b = 0 := pepsNh_of_zero (Or.inr h0)
        omega
    if hm : ((i.val : ℕ) - 5 * a * b) / 2 < b then
      (⟨⟨a - 1, by omega⟩, ⟨((i.val : ℕ) - 5 * a * b) / 2, hm⟩⟩, true)
    else
      (⟨⟨((i.val : ℕ) - 5 * a * b) / 2 - b, by
          have hlt : ((i.val : ℕ) - 5 * a * b) / 2 < a + b := by
            have := pepsNh_lt_add a b (by omega : ¬(a = 0 ∨ b = 0))
              (i.val : ℕ) (by omega) i.val.isLt
            omega
          omega⟩,
        ⟨b - 1, by omega⟩⟩, false)

/-- Away from the right boundary, the representative half-edge of `pepsEdgeR` has index `5 *
(p.1 * b + p.2) + 2`. -/
theorem pepsEdgeR_val_bond (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) (h : (p.1 : ℕ) + 1 < a) :
    ((pepsEdgeR a b d D T p).val : ℕ) = 5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 2 := by
  simp only [pepsEdgeR, dite_eq_left h]

/-- At the right boundary, the representative half-edge of `pepsEdgeR` has dummy index `5 * a *
b + 2 * p.2`. -/
theorem pepsEdgeR_val_dummy (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) (h : ¬(p.1 : ℕ) + 1 < a) :
    ((pepsEdgeR a b d D T p).val : ℕ) = 5 * a * b + 2 * (p.2 : ℕ) := by
  simp only [pepsEdgeR, dite_eq_right h]

/-- Away from the bottom boundary, the representative half-edge of `pepsEdgeD` has index `5 *
(p.1 * b + p.2) + 3`. -/
theorem pepsEdgeD_val_bond (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) (h : (p.2 : ℕ) + 1 < b) :
    ((pepsEdgeD a b d D T p).val : ℕ) = 5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 3 := by
  simp only [pepsEdgeD, dite_eq_left h]

/-- At the bottom boundary, the representative half-edge of `pepsEdgeD` has dummy index `5 * a *
b + 2 * (b + p.1)`. -/
theorem pepsEdgeD_val_dummy (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) (h : ¬(p.2 : ℕ) + 1 < b) :
    ((pepsEdgeD a b d D T p).val : ℕ) = 5 * a * b + 2 * (b + (p.1 : ℕ)) := by
  simp only [pepsEdgeD, dite_eq_right h]

/-- Decoding the right-going edge associated with `p` returns the site `p` and the direction
flag `true`. -/
theorem pepsEdgeIdx_edgeR (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) :
    pepsEdgeIdx a b d D T (pepsEdgeR a b d D T p) = (p, true) := by
  have hpos := peps_pos_of_fin a b p
  by_cases h : (p.1 : ℕ) + 1 < a
  · have hval := pepsEdgeR_val_bond a b d D T p h
    have hk : (p.1 : ℕ) * b + (p.2 : ℕ) < a * b :=
      peps_ib_lt a b (p.1 : ℕ) (p.2 : ℕ) p.1.isLt p.2.isLt
    have hreg : ((pepsEdgeR a b d D T p).val : ℕ) < 5 * a * b := by
      rw [hval]
      exact pepsLeg_lt a b ((p.1 : ℕ) * b + (p.2 : ℕ)) 2 hk (by omega)
    have hdiv : (5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 2) / 5 = (p.1 : ℕ) * b + (p.2 : ℕ) :=
      pepsLeg_div ((p.1 : ℕ) * b + (p.2 : ℕ)) 2 (by omega)
    have hmod : (5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 2) % 5 = 2 :=
      pepsLeg_mod ((p.1 : ℕ) * b + (p.2 : ℕ)) 2 (by omega)
    simp only [pepsEdgeIdx, dite_eq_left hreg]
    simp only [hval, hdiv, hmod, peps_ib_div (p.1 : ℕ) (p.2 : ℕ) b hpos.2 p.2.isLt,
      peps_ib_mod (p.1 : ℕ) (p.2 : ℕ) b hpos.2 p.2.isLt]
    rfl
  · have hval := pepsEdgeR_val_dummy a b d D T p h
    have hreg : ¬((pepsEdgeR a b d D T p).val : ℕ) < 5 * a * b := by
      rw [hval]
      omega
    have hm : (p.2 : ℕ) < b := p.2.isLt
    have heq : (5 * a * b + 2 * (p.2 : ℕ) - 5 * a * b) / 2 = (p.2 : ℕ) := by omega
    simp only [pepsEdgeIdx, dite_eq_right hreg]
    simp only [hval, heq]
    rw [dite_eq_left hm]
    have h2 : a - 1 = (p.1 : ℕ) := by have := p.1.isLt; omega
    simp only [h2]

/-- Decoding the downward edge associated with `p` returns the site `p` and the direction flag
`false`. -/
theorem pepsEdgeIdx_edgeD (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : Fin a × Fin b) :
    pepsEdgeIdx a b d D T (pepsEdgeD a b d D T p) = (p, false) := by
  have hpos := peps_pos_of_fin a b p
  by_cases h : (p.2 : ℕ) + 1 < b
  · have hval := pepsEdgeD_val_bond a b d D T p h
    have hk : (p.1 : ℕ) * b + (p.2 : ℕ) < a * b :=
      peps_ib_lt a b (p.1 : ℕ) (p.2 : ℕ) p.1.isLt p.2.isLt
    have hreg : ((pepsEdgeD a b d D T p).val : ℕ) < 5 * a * b := by
      rw [hval]
      exact pepsLeg_lt a b ((p.1 : ℕ) * b + (p.2 : ℕ)) 3 hk (by omega)
    have hdiv : (5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 3) / 5 = (p.1 : ℕ) * b + (p.2 : ℕ) :=
      pepsLeg_div ((p.1 : ℕ) * b + (p.2 : ℕ)) 3 (by omega)
    have hmod : (5 * ((p.1 : ℕ) * b + (p.2 : ℕ)) + 3) % 5 = 3 :=
      pepsLeg_mod ((p.1 : ℕ) * b + (p.2 : ℕ)) 3 (by omega)
    simp only [pepsEdgeIdx, dite_eq_left hreg]
    simp only [hval, hdiv, hmod, peps_ib_div (p.1 : ℕ) (p.2 : ℕ) b hpos.2 p.2.isLt,
      peps_ib_mod (p.1 : ℕ) (p.2 : ℕ) b hpos.2 p.2.isLt]
    rfl
  · have hval := pepsEdgeD_val_dummy a b d D T p h
    have hreg : ¬((pepsEdgeD a b d D T p).val : ℕ) < 5 * a * b := by
      rw [hval]
      omega
    have hm : ¬(b + (p.1 : ℕ) < b) := by have := p.1.isLt; omega
    have heq : (5 * a * b + 2 * (b + (p.1 : ℕ)) - 5 * a * b) / 2 = b + (p.1 : ℕ) := by omega
    have hbb : b + (p.1 : ℕ) - b = (p.1 : ℕ) := by omega
    simp only [pepsEdgeIdx, dite_eq_right hreg]
    simp only [hval, heq]
    rw [dite_eq_right hm]
    simp only [hbb]
    have h2 : b - 1 = (p.2 : ℕ) := by have := p.2.isLt; omega
    simp only [h2]

/-- The quotient and remainder reconstruct a natural number as `(m / b) * b + m % b = m`. -/
theorem peps_divmod_symm (m b : ℕ) : (m / b) * b + m % b = m := by
  rw [Nat.mul_comm, Nat.div_add_mod]

/-- Every internal edge of the encoded PEPS network has dimension `D`, including its dummy
edges. -/
theorem pepsDim_internal (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (i : InternalEdge (pepsNet a b d D T)) :
    pepsDim a b d D i.val.val = D := by
  obtain ⟨k, hk, hlt⟩ := i.property
  have hpos : 0 < a ∧ 0 < b := by
    have hnh : (pepsNet a b d D T).nh = pepsNh a b := rfl
    constructor
    · by_contra hc
      have h0 : a = 0 := by omega
      have hzz : pepsNh a b = 0 := pepsNh_of_zero (Or.inl h0)
      omega
    · by_contra hc
      have h0 : b = 0 := by omega
      have hzz : pepsNh a b = 0 := pepsNh_of_zero (Or.inr h0)
      omega
  obtain ⟨m, hjm, hmk, hmlt⟩ | ⟨m, hjm, hmk, hmlt⟩ | ⟨m, hjm, hmlt⟩ :=
    peps_rep_form a b hpos.1 hpos.2 i.val k hk hlt
  · rw [pepsDim_reg a b d D (by omega)]
  · rw [pepsDim_reg a b d D (by omega)]
  · rw [pepsDim_dummy a b d D (by omega)]

/-- Reconstructing the right-going or downward edge selected by `pepsEdgeIdx` recovers the
original PEPS internal edge. -/
theorem pepsEdge_of_idx (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (i : InternalEdge (pepsNet a b d D T)) :
    (if (pepsEdgeIdx a b d D T i).2 = true then
      pepsEdgeR a b d D T (pepsEdgeIdx a b d D T i).1
    else pepsEdgeD a b d D T (pepsEdgeIdx a b d D T i).1) = i := by
  obtain ⟨k, hk, hlt⟩ := i.property
  have hpos : 0 < a ∧ 0 < b := by
    have hnh : (pepsNet a b d D T).nh = pepsNh a b := rfl
    constructor
    · by_contra hc
      have h0 : a = 0 := by omega
      have hzz : pepsNh a b = 0 := pepsNh_of_zero (Or.inl h0)
      omega
    · by_contra hc
      have h0 : b = 0 := by omega
      have hzz : pepsNh a b = 0 := pepsNh_of_zero (Or.inr h0)
      omega
  obtain ⟨m, hjm, hmk, hmlt⟩ | ⟨m, hjm, hmk, hmlt⟩ | ⟨m, hjm, hmlt⟩ :=
    peps_rep_form a b hpos.1 hpos.2 i.val k hk hlt
  · have hreg : i.val.val < 5 * a * b := by rw [hjm]; exact pepsLeg_lt a b m 2 hmlt (by omega)
    have hdiv : (5 * m + 2) / 5 = m := pepsLeg_div m 2 (by omega)
    have hmod : (5 * m + 2) % 5 = 2 := pepsLeg_mod m 2 (by omega)
    have hidx : pepsEdgeIdx a b d D T i
        = (⟨⟨m / b, peps_mb_div a b m hmlt⟩, ⟨m % b, Nat.mod_lt _ hpos.2⟩⟩, true) := by
      simp only [pepsEdgeIdx, dite_eq_left hreg]
      simp only [hjm, hdiv, hmod]
      rfl
    simp only [hidx]
    have hp : (m / b) + 1 < a := (peps_right_cond a b (m / b) (m % b) hpos.2
      (peps_mb_div a b m hmlt) (Nat.mod_lt _ hpos.2)).2 (by
        rw [peps_divmod_symm m b]; exact hmk)
    have hval : ((pepsEdgeR a b d D T ⟨⟨m / b, peps_mb_div a b m hmlt⟩,
        ⟨m % b, Nat.mod_lt _ hpos.2⟩⟩).val : ℕ) = 5 * m + 2 := by
      rw [pepsEdgeR_val_bond a b d D T _ hp, peps_divmod_symm m b]
    apply Subtype.ext
    apply Fin.ext
    show ((pepsEdgeR a b d D T ⟨⟨m / b, peps_mb_div a b m hmlt⟩,
      ⟨m % b, Nat.mod_lt _ hpos.2⟩⟩).val : ℕ) = i.val.val
    rw [hval, hjm]
  · have hreg : i.val.val < 5 * a * b := by rw [hjm]; exact pepsLeg_lt a b m 3 hmlt (by omega)
    have hdiv : (5 * m + 3) / 5 = m := pepsLeg_div m 3 (by omega)
    have hmod : (5 * m + 3) % 5 = 3 := pepsLeg_mod m 3 (by omega)
    have hidx : pepsEdgeIdx a b d D T i
        = (⟨⟨m / b, peps_mb_div a b m hmlt⟩, ⟨m % b, Nat.mod_lt _ hpos.2⟩⟩, false) := by
      simp only [pepsEdgeIdx, dite_eq_left hreg]
      simp only [hjm, hdiv, hmod]
      rfl
    simp only [hidx]
    have hp : (m % b) + 1 < b := by
      have := peps_ib_mod (m / b) (m % b) b hpos.2 (Nat.mod_lt _ hpos.2)
      rw [peps_divmod_symm m b] at this
      omega
    have hval : ((pepsEdgeD a b d D T ⟨⟨m / b, peps_mb_div a b m hmlt⟩,
        ⟨m % b, Nat.mod_lt _ hpos.2⟩⟩).val : ℕ) = 5 * m + 3 := by
      rw [pepsEdgeD_val_bond a b d D T _ hp, peps_divmod_symm m b]
    apply Subtype.ext
    apply Fin.ext
    show ((pepsEdgeD a b d D T ⟨⟨m / b, peps_mb_div a b m hmlt⟩,
      ⟨m % b, Nat.mod_lt _ hpos.2⟩⟩).val : ℕ) = i.val.val
    rw [hval, hjm]
  · have hreg : ¬(i.val.val < 5 * a * b) := by rw [hjm]; omega
    have heq : (5 * a * b + 2 * m - 5 * a * b) / 2 = m := by omega
    by_cases hm : m < b
    · have hidx : pepsEdgeIdx a b d D T i
          = (⟨⟨a - 1, by omega⟩, ⟨m, hm⟩⟩, true) := by
        simp only [pepsEdgeIdx, dite_eq_right hreg]
        simp only [hjm, heq]
        rw [dite_eq_left hm]
      simp only [hidx]
      have hp : ¬((a - 1 : ℕ) + 1 < a) := by omega
      have hval : ((pepsEdgeR a b d D T ⟨⟨a - 1, by omega⟩, ⟨m, hm⟩⟩).val : ℕ)
          = 5 * a * b + 2 * m := by
        rw [pepsEdgeR_val_dummy a b d D T _ hp]
      apply Subtype.ext
      apply Fin.ext
      show ((pepsEdgeR a b d D T ⟨⟨a - 1, by omega⟩, ⟨m, hm⟩⟩).val : ℕ) = i.val.val
      rw [hval, hjm]
    · have hidx : pepsEdgeIdx a b d D T i
          = (⟨⟨m - b, by omega⟩, ⟨b - 1, by omega⟩⟩, false) := by
        simp only [pepsEdgeIdx, dite_eq_right hreg]
        simp only [hjm, heq]
        rw [dite_eq_right hm]
      simp only [hidx]
      have hp : ¬((b - 1 : ℕ) + 1 < b) := by have := hpos.2; omega
      have hval : ((pepsEdgeD a b d D T ⟨⟨m - b, by omega⟩, ⟨b - 1, by omega⟩⟩).val : ℕ)
          = 5 * a * b + 2 * m := by
        rw [pepsEdgeD_val_dummy a b d D T _ hp]
        have h2 : b + (m - b) = m := by omega
        rw [h2]
      apply Subtype.ext
      apply Fin.ext
      show ((pepsEdgeD a b d D T ⟨⟨m - b, by omega⟩, ⟨b - 1, by omega⟩⟩).val : ℕ) = i.val.val
      rw [hval, hjm]

/-- Identifies assignments to PEPS internal edges with a pair of `Fin D` values at every lattice
site. The two components label the site's right-going and downward edges, including boundary
dummy edges. -/
noncomputable def pepsEdgeEquiv (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    (∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val)) ≃
      (Fin a × Fin b → Fin D × Fin D) where
  toFun e p :=
    ((e (pepsEdgeR a b d D T p)).cast (pepsDim_internal a b d D T (pepsEdgeR a b d D T p)),
      (e (pepsEdgeD a b d D T p)).cast (pepsDim_internal a b d D T (pepsEdgeD a b d D T p)))
  invFun γ i :=
    if h : (pepsEdgeIdx a b d D T i).2 = true then
      ((γ (pepsEdgeIdx a b d D T i).1).1).cast
        (pepsDim_internal a b d D T i).symm
    else
      ((γ (pepsEdgeIdx a b d D T i).1).2).cast
        (pepsDim_internal a b d D T i).symm
  left_inv := by
    intro e
    funext i
    simp only []
    have hidx := pepsEdge_of_idx a b d D T i
    by_cases h : (pepsEdgeIdx a b d D T i).2 = true
    · rw [dite_eq_left h]
      have h2 : pepsEdgeR a b d D T (pepsEdgeIdx a b d D T i).1 = i :=
        (ite_eq_left h).symm.trans hidx
      rw [h2]
      exact Fin.ext (by rfl)
    · rw [dite_eq_right h]
      have h2 : pepsEdgeD a b d D T (pepsEdgeIdx a b d D T i).1 = i :=
        (ite_eq_right h).symm.trans hidx
      rw [h2]
      exact Fin.ext (by rfl)
  right_inv := by
    intro γ
    funext p
    simp only []
    rw [pepsEdgeIdx_edgeR a b d D T p, pepsEdgeIdx_edgeD a b d D T p]
    simp only [dite_eq_right (by simp : ¬((false : Bool) = true))]
    refine Prod.ext ?_ ?_
    · exact Fin.ext (by rfl)
    · exact Fin.ext (by rfl)

/-- Decodes a flattened PEPS vertex index into its pair of lattice coordinates using the
standard finite-product equivalence. -/
def pepsP (a b : ℕ) (v : Fin (a * b)) : Fin a × Fin b :=
  (finProdFinEquiv (m := a) (n := b)).symm v

/-- The first coordinate of `pepsP a b v` is the quotient of the flattened index `v` by `b`. -/
theorem pepsP_fst (a b : ℕ) (v : Fin (a * b)) : ((pepsP a b v).1 : ℕ) = (v : ℕ) / b := rfl

/-- The second coordinate of `pepsP a b v` is the remainder of the flattened index `v` modulo
`b`. -/
theorem pepsP_snd (a b : ℕ) (v : Fin (a * b)) : ((pepsP a b v).2 : ℕ) = (v : ℕ) % b := rfl

/-- The existence of a flattened vertex in `Fin (a * b)` forces both lattice dimensions to be
positive. -/
theorem peps_pos_of_v (a b : ℕ) (v : Fin (a * b)) : 0 < a ∧ 0 < b := by
  constructor
  · by_contra hc
    have ha0 : a = 0 := by omega
    have hz : a * b = 0 := by rw [ha0]; ring
    have hlt := v.isLt
    omega
  · by_contra hc
    have hb0 : b = 0 := by omega
    have hz : a * b = 0 := by rw [hb0]; ring
    have hlt := v.isLt
    omega

/-- Flattening the two coordinates decoded by `pepsP` recovers the original vertex index. -/
theorem peps_coord_right (a b : ℕ) (v : Fin (a * b)) :
    ((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ) = (v : ℕ) := by
  rw [pepsP_fst, pepsP_snd, peps_divmod_symm]

/-- Decreasing a nonzero first coordinate by one decreases the flattened PEPS vertex index by
`b`. -/
theorem peps_coord_left (a b : ℕ) (v : Fin (a * b)) (hne : ((pepsP a b v).1 : ℕ) ≠ 0) :
    (((pepsP a b v).1 : ℕ) - 1) * b + ((pepsP a b v).2 : ℕ) = (v : ℕ) - b := by
  have hne' : (v : ℕ) / b ≠ 0 := hne
  have hb : 0 < b := (peps_pos_of_v a b v).2
  have h1 : 1 ≤ (v : ℕ) / b := by
    by_contra hc
    have h0 : (v : ℕ) / b = 0 := by
      by_contra hc2
      exact hc (Nat.pos_of_ne_zero hc2)
    exact hne' h0
  have h2 : b ≤ ((v : ℕ) / b) * b := by
    have := Nat.mul_le_mul_right b h1
    simpa using! this
  have h3 := peps_divmod_symm (v : ℕ) b
  have h4 : (((v : ℕ) / b - 1) * b) = ((v : ℕ) / b) * b - b := by
    rw [Nat.sub_mul, one_mul]
  rw [pepsP_fst, pepsP_snd, h4]
  omega

/-- Decreasing a nonzero second coordinate by one decreases the flattened PEPS vertex index by
one. -/
theorem peps_coord_up (a b : ℕ) (v : Fin (a * b)) (hne : ((pepsP a b v).2 : ℕ) ≠ 0) :
    ((pepsP a b v).1 : ℕ) * b + (((pepsP a b v).2 : ℕ) - 1) = (v : ℕ) - 1 := by
  have hne' : (v : ℕ) % b ≠ 0 := hne
  have h1 : 1 ≤ (v : ℕ) % b := by
    by_contra hc
    have h0 : (v : ℕ) % b = 0 := by
      by_contra hc2
      exact hc (Nat.pos_of_ne_zero hc2)
    exact hne' h0
  have h3 := peps_divmod_symm (v : ℕ) b
  rw [pepsP_fst, pepsP_snd]
  omega

/-- Evaluates the PEPS tensor at a site using its physical label and the adjacent bond values
from `γ`. Missing boundary bonds are fixed to zero. -/
noncomputable def pepsFactor {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (γ : Fin a × Fin b → Fin D × Fin D) (p : Fin a × Fin b) : ℂ :=
  T p.1 p.2 (x p.1 p.2)
    (if h : (p.1 : ℕ) = 0 then 0
      else (γ ((⟨(p.1 : ℕ) - 1, by have := p.1.isLt; omega⟩ : Fin a), p.2)).1)
    (if (p.1 : ℕ) + 1 = a then 0 else (γ p).1)
    (if (p.2 : ℕ) + 1 = b then 0 else (γ p).2)
    (if h : (p.2 : ℕ) = 0 then 0
      else (γ (p.1, (⟨(p.2 : ℕ) - 1, by have := p.2.isLt; omega⟩ : Fin b))).2)

/-- Expresses the PEPS amplitude as the sum over sitewise bond pairs of the product of local
factors `pepsFactor`. -/
theorem pepsAmplitude_eq (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) :
    pepsAmplitude T x
      = ∑ γ : Fin a × Fin b → Fin D × Fin D,
          ∏ p : Fin a × Fin b, pepsFactor T x γ p := rfl

/-- The physical port value at an encoded PEPS vertex equals the physical configuration label at
its decoded lattice coordinates, after casting the dimension. -/
theorem pepsPort_phys (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val))
    (v : Fin (a * b)) :
    Fin.cast (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
        (pepsLeg_mod (v : ℕ) 0 (by omega)))
      (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩)
      = x (pepsP a b v).1 (pepsP a b v).2 := by
  have ha : 0 < a := (peps_pos_of_v a b v).1
  have hb : 0 < b := (peps_pos_of_v a b v).2
  have hpartner : pepsPartner a b
      ⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩ = none :=
    pepsPartner_phys a b (v : ℕ) ha hb v.isLt
  have hport : portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
      ⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩
      = pepsEnc a b d D T x
          ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩, hpartner⟩ :=
    portValue_of_partner_none (pepsEnc a b d D T x) e
      ⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩ hpartner
  have hcond : ((⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩ :
        Fin (pepsNh a b)) : ℕ) < 5 * a * b ∧
      ((⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩ :
        Fin (pepsNh a b)) : ℕ) % 5 = 0 :=
    ⟨pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega), pepsLeg_mod (v : ℕ) 0 (by omega)⟩
  have hdiv : (5 * (v : ℕ)) / 5 = (v : ℕ) := by
    have h := pepsLeg_div (v : ℕ) 0 (by omega)
    rw [Nat.add_zero] at h
    exact h
  have key : pepsEnc a b d D T x
        ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩, hpartner⟩
      = (x (pepsP a b v).1 (pepsP a b v).2).cast
          (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
            (pepsLeg_mod (v : ℕ) 0 (by omega))).symm := by
    simp only [pepsEnc, dite_eq_left hcond]
    show (x ((finProdFinEquiv (m := a) (n := b)).symm ⟨(5 * (v : ℕ)) / 5, _⟩).1
        ((finProdFinEquiv (m := a) (n := b)).symm ⟨(5 * (v : ℕ)) / 5, _⟩).2).cast _
      = (x (pepsP a b v).1 (pepsP a b v).2).cast _
    simp only [hdiv]
    rfl
  rw [hport, key]
  rfl

/-- The boundary-adjusted right port value agrees with the first component of the site's bond
assignment under `pepsEdgeEquiv`. Both expressions are zero at the right boundary. -/
theorem pepsPort_right (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val))
    (v : Fin (a * b)) :
    (if ((pepsP a b v).1 : ℕ) + 1 = a then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩))
      = (if ((pepsP a b v).1 : ℕ) + 1 = a then 0
        else ((pepsEdgeEquiv a b d D T e) (pepsP a b v)).1) := by
  by_cases h : ((pepsP a b v).1 : ℕ) + 1 = a
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    have ha : 0 < a := (peps_pos_of_v a b v).1
    have hb : 0 < b := (peps_pos_of_v a b v).2
    have hkb : (v : ℕ) + b < a * b := by
      have h1 : ((pepsP a b v).1 : ℕ) + 1 < a := by
        have := (pepsP a b v).1.isLt
        omega
      have h2 : ((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ) + b < a * b :=
        (peps_right_cond a b ((pepsP a b v).1 : ℕ) ((pepsP a b v).2 : ℕ) hb
          (pepsP a b v).1.isLt (pepsP a b v).2.isLt).1 h1
      rw [peps_coord_right a b v] at h2
      exact h2
    have hpartner : pepsPartner a b
        ⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩
        = some ⟨5 * ((v : ℕ) + b) + 1, pepsLeg_lt_nh a b ((v : ℕ) + b) 1 hkb (by omega)⟩ :=
      pepsPartner_right_bond a b (v : ℕ) ha hb hkb
    have hkj : (⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩ :
        Fin (pepsNh a b)) < ⟨5 * ((v : ℕ) + b) + 1, pepsLeg_lt_nh a b ((v : ℕ) + b) 1 hkb (by omega)⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hport : portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩
        = e ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
            ⟨⟨5 * ((v : ℕ) + b) + 1, pepsLeg_lt_nh a b ((v : ℕ) + b) 1 hkb (by omega)⟩,
              hpartner, hkj⟩⟩ :=
      portValue_of_partner_eq (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) + b) + 1, pepsLeg_lt_nh a b ((v : ℕ) + b) 1 hkb (by omega)⟩
        hpartner hkj
    have hsub : (⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
          ⟨⟨5 * ((v : ℕ) + b) + 1, pepsLeg_lt_nh a b ((v : ℕ) + b) 1 hkb (by omega)⟩,
            hpartner, hkj⟩⟩ : InternalEdge (pepsNet a b d D T))
        = pepsEdgeR a b d D T (pepsP a b v) := by
      apply Subtype.ext
      apply Fin.ext
      rw [pepsEdgeR_val_bond a b d D T (pepsP a b v)
        (by have := (pepsP a b v).1.isLt; omega)]
      rw [peps_coord_right a b v]
    show Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩)
      = (e (pepsEdgeR a b d D T (pepsP a b v))).cast
        (pepsDim_internal a b d D T (pepsEdgeR a b d D T (pepsP a b v)))
    rw [hport]
    refine Fin.ext ?_
    simp only [Fin.val_cast]
    exact congrArg (fun i : InternalEdge (pepsNet a b d D T) => (e i).val) hsub

/-- The boundary-adjusted left port value agrees with the first bond component at the preceding
first coordinate under `pepsEdgeEquiv`. Both expressions are zero when the first coordinate
is zero. -/
theorem pepsPort_left (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val))
    (v : Fin (a * b)) :
    (if h : ((pepsP a b v).1 : ℕ) = 0 then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩))
      = (if h : ((pepsP a b v).1 : ℕ) = 0 then 0
        else ((pepsEdgeEquiv a b d D T e)
          (⟨((pepsP a b v).1 : ℕ) - 1, by have := (pepsP a b v).1.isLt; omega⟩,
            (pepsP a b v).2)).1) := by
  by_cases h : ((pepsP a b v).1 : ℕ) = 0
  · simp only [dite_eq_left h]
  · simp only [dite_eq_right h]
    have ha : 0 < a := (peps_pos_of_v a b v).1
    have hb : 0 < b := (peps_pos_of_v a b v).2
    have hkb : b ≤ (v : ℕ) := by
      by_contra hc
      have h1 : (v : ℕ) < b := by omega
      have h2 : (v : ℕ) / b = 0 := Nat.div_eq_of_lt h1
      exact h h2
    have hpartner : pepsPartner a b
        ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩
        = some ⟨5 * ((v : ℕ) - b) + 2,
          pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩ :=
      pepsPartner_left_bond a b (v : ℕ) ha hb hkb v.isLt
    have hkj : (⟨5 * ((v : ℕ) - b) + 2,
        pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩ :
        Fin (pepsNh a b)) < ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hinv : pepsPartner a b
        (⟨5 * ((v : ℕ) - b) + 2,
          pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩ : Fin (pepsNh a b))
        = some ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩ :=
      pepsPartner_involution a b ha hb
        ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) - b) + 2, pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩
        hpartner
    have hdim : (pepsNet a b d D T).dims
        (⟨5 * ((v : ℕ) - b) + 2,
          pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩ : Fin (pepsNh a b))
        = (pepsNet a b d D T).dims
          ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩ :=
      (pepsPartner_dims a b d D ha hb
        ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) - b) + 2, pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩
        hpartner).symm
    have hport : portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩
        = (e ⟨⟨5 * ((v : ℕ) - b) + 2,
            pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩,
          ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
            hinv, hkj⟩⟩).cast (by rw [← hdim]) :=
      portValue_of_partner_eq_rev (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) - b) + 2, pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩
        hpartner hkj hinv hdim
    have hsub : (⟨⟨5 * ((v : ℕ) - b) + 2,
          pepsLeg_lt_nh a b ((v : ℕ) - b) 2 (by have := v.isLt; omega) (by omega)⟩,
        ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
          hinv, hkj⟩⟩ : InternalEdge (pepsNet a b d D T))
        = pepsEdgeR a b d D T
          (⟨((pepsP a b v).1 : ℕ) - 1, by have := (pepsP a b v).1.isLt; omega⟩,
            (pepsP a b v).2) := by
      apply Subtype.ext
      apply Fin.ext
      rw [pepsEdgeR_val_bond a b d D T
        (⟨((pepsP a b v).1 : ℕ) - 1, by have := (pepsP a b v).1.isLt; omega⟩, (pepsP a b v).2)
        (by
          have hlt := (pepsP a b v).1.isLt
          have hne' := h
          show (((pepsP a b v).1 : ℕ) - 1) + 1 < a
          omega)]
      rw [peps_coord_left a b v h]
    show Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩)
      = (e (pepsEdgeR a b d D T
          (⟨((pepsP a b v).1 : ℕ) - 1, by have := (pepsP a b v).1.isLt; omega⟩,
            (pepsP a b v).2))).cast
        (pepsDim_internal a b d D T (pepsEdgeR a b d D T
          (⟨((pepsP a b v).1 : ℕ) - 1, by have := (pepsP a b v).1.isLt; omega⟩,
            (pepsP a b v).2)))
    rw [hport]
    refine Fin.ext ?_
    simp only [Fin.val_cast]
    exact congrArg (fun i : InternalEdge (pepsNet a b d D T) => (e i).val) hsub

/-- The boundary-adjusted downward port value agrees with the second component of the site's
bond assignment under `pepsEdgeEquiv`. Both expressions are zero at the bottom boundary. -/
theorem pepsPort_down (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val))
    (v : Fin (a * b)) :
    (if ((pepsP a b v).2 : ℕ) + 1 = b then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩))
      = (if ((pepsP a b v).2 : ℕ) + 1 = b then 0
        else ((pepsEdgeEquiv a b d D T e) (pepsP a b v)).2) := by
  by_cases h : ((pepsP a b v).2 : ℕ) + 1 = b
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    have ha : 0 < a := (peps_pos_of_v a b v).1
    have hb : 0 < b := (peps_pos_of_v a b v).2
    have hkb : (v : ℕ) % b + 1 < b := by
      have hlt := (pepsP a b v).2.isLt
      have hne' := h
      show ((pepsP a b v).2 : ℕ) + 1 < b
      omega
    have hpartner : pepsPartner a b
        ⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩
        = some ⟨5 * ((v : ℕ) + 1) + 4,
          pepsLeg_lt_nh a b ((v : ℕ) + 1) 4 (peps_down_bound a b (v : ℕ) ha hb hkb v.isLt) (by omega)⟩ :=
      pepsPartner_down_bond a b (v : ℕ) ha hb hkb v.isLt
    have hkj : (⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩ :
        Fin (pepsNh a b))
        < ⟨5 * ((v : ℕ) + 1) + 4,
          pepsLeg_lt_nh a b ((v : ℕ) + 1) 4 (peps_down_bound a b (v : ℕ) ha hb hkb v.isLt) (by omega)⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hport : portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩
        = e ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
            ⟨⟨5 * ((v : ℕ) + 1) + 4,
              pepsLeg_lt_nh a b ((v : ℕ) + 1) 4 (peps_down_bound a b (v : ℕ) ha hb hkb v.isLt) (by omega)⟩,
              hpartner, hkj⟩⟩ :=
      portValue_of_partner_eq (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) + 1) + 4,
          pepsLeg_lt_nh a b ((v : ℕ) + 1) 4 (peps_down_bound a b (v : ℕ) ha hb hkb v.isLt) (by omega)⟩
        hpartner hkj
    have hsub : (⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
          ⟨⟨5 * ((v : ℕ) + 1) + 4,
            pepsLeg_lt_nh a b ((v : ℕ) + 1) 4 (peps_down_bound a b (v : ℕ) ha hb hkb v.isLt) (by omega)⟩,
            hpartner, hkj⟩⟩ : InternalEdge (pepsNet a b d D T))
        = pepsEdgeD a b d D T (pepsP a b v) := by
      apply Subtype.ext
      apply Fin.ext
      rw [pepsEdgeD_val_bond a b d D T (pepsP a b v)
        (by
          have hlt := (pepsP a b v).2.isLt
          have hne' := h
          show ((pepsP a b v).2 : ℕ) + 1 < b
          omega)]
      rw [peps_coord_right a b v]
    show Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩)
      = (e (pepsEdgeD a b d D T (pepsP a b v))).cast
        (pepsDim_internal a b d D T (pepsEdgeD a b d D T (pepsP a b v)))
    rw [hport]
    refine Fin.ext ?_
    simp only [Fin.val_cast]
    exact congrArg (fun i : InternalEdge (pepsNet a b d D T) => (e i).val) hsub

/-- The boundary-adjusted upward port value agrees with the second bond component at the
preceding second coordinate under `pepsEdgeEquiv`. Both expressions are zero when the second
coordinate is zero. -/
theorem pepsPort_up (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val))
    (v : Fin (a * b)) :
    (if h : ((pepsP a b v).2 : ℕ) = 0 then 0
      else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩))
      = (if h : ((pepsP a b v).2 : ℕ) = 0 then 0
        else ((pepsEdgeEquiv a b d D T e)
          ((pepsP a b v).1, ⟨((pepsP a b v).2 : ℕ) - 1, by have := (pepsP a b v).2.isLt; omega⟩)).2) := by
  by_cases h : ((pepsP a b v).2 : ℕ) = 0
  · simp only [dite_eq_left h]
  · simp only [dite_eq_right h]
    have ha : 0 < a := (peps_pos_of_v a b v).1
    have hb : 0 < b := (peps_pos_of_v a b v).2
    have hpartner : pepsPartner a b
        ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩
        = some ⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩ :=
      pepsPartner_up_bond a b (v : ℕ) ha hb h v.isLt
    have hkj : (⟨5 * ((v : ℕ) - 1) + 3,
        pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩ :
        Fin (pepsNh a b)) < ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hinv : pepsPartner a b
        (⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩ : Fin (pepsNh a b))
        = some ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩ :=
      pepsPartner_involution a b ha hb
        ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩
        hpartner
    have hdim : (pepsNet a b d D T).dims
        (⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩ : Fin (pepsNh a b))
        = (pepsNet a b d D T).dims
          ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩ :=
      (pepsPartner_dims a b d D ha hb
        ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩
        hpartner).symm
    have hport : portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩
        = (e ⟨⟨5 * ((v : ℕ) - 1) + 3,
            pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩,
          ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
            hinv, hkj⟩⟩).cast (by rw [← hdim]) :=
      portValue_of_partner_eq_rev (pepsEnc a b d D T x) e
        ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩
        ⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩
        hpartner hkj hinv hdim
    have hsub : (⟨⟨5 * ((v : ℕ) - 1) + 3,
          pepsLeg_lt_nh a b ((v : ℕ) - 1) 3 (by have := v.isLt; omega) (by omega)⟩,
        ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
          hinv, hkj⟩⟩ : InternalEdge (pepsNet a b d D T))
        = pepsEdgeD a b d D T
          ((pepsP a b v).1, ⟨((pepsP a b v).2 : ℕ) - 1, by have := (pepsP a b v).2.isLt; omega⟩) := by
      apply Subtype.ext
      apply Fin.ext
      rw [pepsEdgeD_val_bond a b d D T
        ((pepsP a b v).1, ⟨((pepsP a b v).2 : ℕ) - 1, by have := (pepsP a b v).2.isLt; omega⟩)
        (by
          have hlt := (pepsP a b v).2.isLt
          have hne' := h
          show (((pepsP a b v).2 : ℕ) - 1) + 1 < b
          omega)]
      rw [peps_coord_up a b v h]
    show Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩)
      = (e (pepsEdgeD a b d D T
          ((pepsP a b v).1, ⟨((pepsP a b v).2 : ℕ) - 1, by have := (pepsP a b v).2.isLt; omega⟩))).cast
        (pepsDim_internal a b d D T (pepsEdgeD a b d D T
          ((pepsP a b v).1, ⟨((pepsP a b v).2 : ℕ) - 1, by have := (pepsP a b v).2.isLt; omega⟩)))
    rw [hport]
    refine Fin.ext ?_
    simp only [Fin.val_cast]
    exact congrArg (fun i : InternalEdge (pepsNet a b d D T) => (e i).val) hsub

/-- Evaluating the encoded network tensor at a vertex gives `pepsFactor` at its decoded lattice
site with bond assignment `pepsEdgeEquiv e`. -/
theorem pepsTensor_at (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d)
    (e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val))
    (v : Fin (a * b)) :
    pepsTensor a b d D T v (fun h => portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e h.val)
      = pepsFactor T x (pepsEdgeEquiv a b d D T e) (pepsP a b v) := by
  have hphys := pepsPort_phys a b d D T x e v
  have hleft := pepsPort_left a b d D T x e v
  have hright := pepsPort_right a b d D T x e v
  have hdown := pepsPort_down a b d D T x e v
  have hup := pepsPort_up a b d D T x e v
  show T (pepsP a b v).1 (pepsP a b v).2
      (Fin.cast (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
          (pepsLeg_mod (v : ℕ) 0 (by omega)))
        (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
          ⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩))
      (if h : ((pepsP a b v).1 : ℕ) = 0 then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega))
          (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
            ⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩))
      (if ((pepsP a b v).1 : ℕ) + 1 = a then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega))
          (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
            ⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩))
      (if ((pepsP a b v).2 : ℕ) + 1 = b then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega))
          (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
            ⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩))
      (if h : ((pepsP a b v).2 : ℕ) = 0 then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))
          (portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e
            ⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩))
    = T (pepsP a b v).1 (pepsP a b v).2 (x (pepsP a b v).1 (pepsP a b v).2)
      (if h : ((pepsP a b v).1 : ℕ) = 0 then 0
        else ((pepsEdgeEquiv a b d D T e)
          (⟨((pepsP a b v).1 : ℕ) - 1, by have := (pepsP a b v).1.isLt; omega⟩,
            (pepsP a b v).2)).1)
      (if ((pepsP a b v).1 : ℕ) + 1 = a then 0
        else ((pepsEdgeEquiv a b d D T e) (pepsP a b v)).1)
      (if ((pepsP a b v).2 : ℕ) + 1 = b then 0
        else ((pepsEdgeEquiv a b d D T e) (pepsP a b v)).2)
      (if h : ((pepsP a b v).2 : ℕ) = 0 then 0
        else ((pepsEdgeEquiv a b d D T e)
          ((pepsP a b v).1, ⟨((pepsP a b v).2 : ℕ) - 1, by have := (pepsP a b v).2.isLt; omega⟩)).2)
  rw [hphys, hleft, hright, hdown, hup]

/-- The bond dimension of the tensor network encoding a PEPS is at most the PEPS bond dimension
`D`. -/
theorem netBondDimension_pepsNet_le (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    netBondDimension (pepsNet a b d D T) ≤ D := by
  apply Finset.sup_le
  intro i _
  exact (pepsDim_internal a b d D T i).le

/-- Contracting the encoded PEPS network with the encoded physical configuration reproduces the
PEPS amplitude. -/
theorem netContract_pepsNet_eq (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) :
    netContract (pepsNet a b d D T) (pepsEnc a b d D T x) = pepsAmplitude T x := by
  show (∑ e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val),
      ∏ v : Fin (a * b),
        pepsTensor a b d D T v (fun h =>
          portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e h.val))
    = pepsAmplitude T x
  rw [pepsAmplitude_eq]
  rw [Fintype.sum_equiv (pepsEdgeEquiv a b d D T)
    (fun e => ∏ v : Fin (a * b),
      pepsTensor a b d D T v (fun h =>
        portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e h.val))
    (fun γ => ∏ p : Fin a × Fin b, pepsFactor T x γ p)
    (fun e => ?eq)]
  case eq =>

    rw [Fintype.prod_equiv (finProdFinEquiv (m := a) (n := b)).symm
      (fun v => pepsTensor a b d D T v (fun h =>
        portValue (pepsNet a b d D T) (pepsEnc a b d D T x) e h.val))
      (fun p => pepsFactor T x (pepsEdgeEquiv a b d D T e) p)
      (fun v => pepsTensor_at a b d D T x e v)]

/-- Every PEPS with nonzero bond dimension `D` has a tensor-network realization of bond
dimension at most `D` whose contraction reproduces every physical amplitude. -/
theorem clause1_clause5 :
    ∀ (a b d D : ℕ) (hD : NeZero D)
      (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ),
      ∃ (N : TensorNet) (enc : (Fin a → Fin b → Fin d) → ∀ o : OpenLeg N, Fin (N.dims o.val)),
        netBondDimension N ≤ D ∧ ∀ x : Fin a → Fin b → Fin d,
          netContract N (enc x) = @pepsAmplitude a b d D hD T x := by
  intro a b d D hD T
  have := hD
  refine ⟨pepsNet a b d D T, pepsEnc a b d D T, ?_, ?_⟩
  · exact netBondDimension_pepsNet_le a b d D T
  · intro x
    exact netContract_pepsNet_eq a b d D T x

end Clause1Peps

/-- Collects network reindexing and unitary gauge invariance, open and periodic MPS
realizations, PEPS realizations, and the explicit product, Bell, and three-site amplitude
identities. It also records the contraction norm bound, vanishing for a zero-dimensional
internal edge, and the value one for an empty network. -/
theorem g1 :

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
      ∀ (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)), netContract N ext = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact clause1_clause1
  · exact clause1_clause2
  · intro n d D hD A
    refine ⟨mpsNet n d D A, mpsEnc n d D A, ?_, ?_⟩
    · exact netBondDimension_mpsNet_le n d D A
    · intro x
      exact @netContract_mpsNet_eq_mpsAmplitude n d D hD A x
  · exact clause1_clause4
  · exact clause1_clause5
  · exact mpsAmplitude_product
  · exact bell_consumer
  · exact short_chain_consumer
  · exact netContract_norm_bound
  · exact @netContract_of_isEmpty_internal
  · exact @netContract_of_empty_net

open Module

section FrobeniusRankOne

variable {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]

/-- The complex Euclidean inner product is the coordinate sum of the conjugated first vector
times the second vector. -/
theorem g10g_inner_eq_sum {ι : Type} [Fintype ι] (u w : EuclideanSpace ℂ ι) :
    inner ℂ u w = ∑ p : ι, star (u p) * w p := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [RCLike.inner_apply]
  rw [mul_comm, Complex.star_def]

/-- The complex embedding of `Complex.normSq z` equals `z * star z`. -/
theorem g10g_ofReal_normSq_eq_mul_star (z : ℂ) :
    ((Complex.normSq z : ℝ) : ℂ) = z * star z := by
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm]

/-- Complex conjugation fixes a real number embedded in the complex numbers. -/
theorem g10g_star_ofReal (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
  rw [Complex.star_def]
  exact Complex.conj_ofReal r

/-- An entry of the singular-value-scaled outer product equals the singular value times the
corresponding left singular-vector coordinate and conjugated right singular-vector
coordinate. -/
theorem g10g_rankOne_apply (A : Matrix O I ℂ)
    (i : Fin (Fintype.card I)) (p : O) (q : I) :
    (((matrixSingularValues A i : ℂ) •
        vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i))) : Matrix O I ℂ) p q
      = (matrixSingularValues A i : ℂ) *
        (leftSingularVector A i p * star (rightSingularBasis A i q)) := by
  simp [Matrix.smul_apply, Matrix.vecMulVec]

/-- Factors the product of a singular rank-one entry and the conjugate of another into
singular-value, left-coordinate, and right-coordinate contributions. -/
theorem g10g_rankOne_cross (A : Matrix O I ℂ) (i j : Fin (Fintype.card I)) (p : O) (q : I) :
    ((matrixSingularValues A i : ℂ) *
        (leftSingularVector A i p * star (rightSingularBasis A i q)))
      * star ((matrixSingularValues A j : ℂ) *
        (leftSingularVector A j p * star (rightSingularBasis A j q)))
      = ((matrixSingularValues A i : ℂ) * (matrixSingularValues A j : ℂ))
        * (leftSingularVector A i p * star (leftSingularVector A j p))
        * (star (rightSingularBasis A i q) * rightSingularBasis A j q) := by
  simp only [star_mul, star_star, g10g_star_ofReal]
  ring

/-- A finite double sum of `a * P p * Q q` factors as `a` times the separate sums of `P` and
`Q`. -/
theorem g10g_sum_sum_mul_split {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : ℂ) (P : ι → ℂ) (Q : κ → ℂ) :
    (∑ p : ι, ∑ q : κ, a * P p * Q q) = a * (∑ p : ι, P p) * (∑ q : κ, Q q) := by
  have h1 : ∀ p : ι, (∑ q : κ, a * P p * Q q) = (a * P p) * (∑ q : κ, Q q) := by
    intro p
    exact (Finset.mul_sum Finset.univ (fun q => Q q) (a * P p)).symm
  rw [show (∑ p : ι, ∑ q : κ, a * P p * Q q)
      = ∑ p : ι, (a * P p) * (∑ q : κ, Q q) from
      Finset.sum_congr rfl (fun p _ => h1 p)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Interchanges the two coordinate sums with the two finite-set sums in a fourfold complex sum. -/
theorem g10g_sum_swap {α β γ δ : Type} [Fintype α] [Fintype β]
    (s : Finset γ) (t : Finset δ) (G : γ → δ → α → β → ℂ) :
    (∑ p : α, ∑ q : β, ∑ i ∈ s, ∑ j ∈ t, G i j p q)
      = ∑ i ∈ s, ∑ j ∈ t, ∑ p : α, ∑ q : β, G i j p q := by
  have ha : ∀ p : α, (∑ q : β, ∑ i ∈ s, ∑ j ∈ t, G i j p q)
      = ∑ i ∈ s, ∑ q : β, ∑ j ∈ t, G i j p q := fun _ => Finset.sum_comm
  conv_lhs => simp only [ha]
  have hb : (∑ p : α, ∑ i ∈ s, ∑ q : β, ∑ j ∈ t, G i j p q)
      = ∑ i ∈ s, ∑ p : α, ∑ q : β, ∑ j ∈ t, G i j p q := Finset.sum_comm
  rw [hb]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hc : ∀ p : α, (∑ q : β, ∑ j ∈ t, G i j p q)
      = ∑ j ∈ t, ∑ q : β, G i j p q := fun _ => Finset.sum_comm
  conv_lhs => simp only [hc]
  have hd : (∑ p : α, ∑ j ∈ t, ∑ q : β, G i j p q)
      = ∑ j ∈ t, ∑ p : α, ∑ q : β, G i j p q := Finset.sum_comm
  rw [hd]

end FrobeniusRankOne

section FrobeniusSum

variable {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]

/-- The squared Frobenius norm of any finite sum of singular rank-one terms equals the sum of
the corresponding squared singular values. -/
theorem g10g_spectralFrobenius_sq_sum_singularRankOne (A : Matrix O I ℂ)
    (s : Finset (Fin (Fintype.card I))) :
    spectralFrobenius (∑ i ∈ s, (matrixSingularValues A i : ℂ) •
        vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i))) ^ 2
      = ∑ i ∈ s, (matrixSingularValues A i) ^ 2 := by
  set N : Matrix O I ℂ := (∑ i ∈ s, (matrixSingularValues A i : ℂ) •
      vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i))) with hNdef
  have hentry : ∀ (p : O) (q : I),
      N p q = ∑ i ∈ s,
        (matrixSingularValues A i : ℂ) *
          (leftSingularVector A i p * star (rightSingularBasis A i q)) := by
    intro p q
    rw [hNdef, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => g10g_rankOne_apply A i p q)
  have hG : ∀ (p : O) (q : I), N p q * star (N p q)
      = ∑ i ∈ s, ∑ j ∈ s,
          ((matrixSingularValues A i : ℂ) * (matrixSingularValues A j : ℂ))
            * (leftSingularVector A i p * star (leftSingularVector A j p))
            * (star (rightSingularBasis A i q) * rightSingularBasis A j q) := by
    intro p q
    rw [hentry p q, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact g10g_rankOne_cross A i j p q
  have hC : ((spectralFrobenius N ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s, ((matrixSingularValues A i : ℂ) ^ 2) := by
    rw [spectralFrobenius_sq]
    push_cast
    have hz : ∀ (p : O) (q : I),
        ((Complex.normSq (N p q) : ℝ) : ℂ) = N p q * star (N p q) :=
      fun p q => g10g_ofReal_normSq_eq_mul_star _
    simp only [hz, hG]
    rw [g10g_sum_swap]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.sum_eq_single i]
    · rw [g10g_sum_sum_mul_split]
      have hv : (∑ q : I, star (rightSingularBasis A i q) * rightSingularBasis A i q)
          = (1 : ℂ) := by
        rw [← g10g_inner_eq_sum, (rightSingularBasis A).inner_eq_ite]
        simp
      rw [hv, mul_one]
      by_cases hσ : matrixSingularValues A i = 0
      · rw [hσ]
        push_cast
        simp
      · have hP : (∑ p : O, leftSingularVector A i p * star (leftSingularVector A i p))
            = (1 : ℂ) := by
          rw [show (∑ p : O, leftSingularVector A i p * star (leftSingularVector A i p))
              = ∑ p : O, star (leftSingularVector A i p) * leftSingularVector A i p from
              Finset.sum_congr rfl (fun p _ => mul_comm _ _)]
          rw [← g10g_inner_eq_sum]
          have hip : (i : ℕ) < finrank ℂ A.toEuclideanLin.range :=
            (matrixSingularValues_pos_iff_lt_finrank_range A).1
              (lt_of_le_of_ne (matrixSingularValues_nonneg A i) (Ne.symm hσ))
          have hnorm : ‖leftSingularVector A i‖ = 1 := norm_leftSingularVector A i hip
          rw [inner_self_eq_norm_sq_to_K, hnorm]
          simp
        rw [hP, mul_one, ← pow_two]
    · intro j _hj hji
      rw [g10g_sum_sum_mul_split]
      have hu0 : inner ℂ (leftSingularVector A j) (leftSingularVector A i) = (0 : ℂ) :=
        inner_leftSingularVector_of_ne A hji
      have hP0 : (∑ p : O, leftSingularVector A i p * star (leftSingularVector A j p))
          = (0 : ℂ) := by
        rw [show (∑ p : O, leftSingularVector A i p * star (leftSingularVector A j p))
            = ∑ p : O, star (leftSingularVector A j p) * leftSingularVector A i p from
            Finset.sum_congr rfl (fun p _ => mul_comm _ _)]
        rw [← g10g_inner_eq_sum]
        exact hu0
      rw [hP0]
      ring
    · intro hi'
      exact absurd hi hi'
  have hconv : (∑ i ∈ s, (((matrixSingularValues A i) ^ 2 : ℝ) : ℂ))
      = ∑ i ∈ s, ((matrixSingularValues A i : ℂ) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => Complex.ofReal_pow (matrixSingularValues A i) 2)
  refine Complex.ofReal_injective ?_
  rw [Complex.ofReal_sum, hconv]
  exact hC

end FrobeniusSum

section Truncation

variable {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]

/-- Truncates the singular-value decomposition of a complex matrix to the terms with index
strictly below `D`. -/
noncomputable def g10g_svdTrunc (A : Matrix O I ℂ) (D : ℕ) : Matrix O I ℂ :=
  ∑ i : Fin (Fintype.card I), if (i : ℕ) < D then
    (matrixSingularValues A i : ℂ) •
      vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i))
  else 0

/-- Writes the SVD truncation as the sum of singular rank-one terms over the finite set of
indices below `D`. -/
theorem g10g_svdTrunc_eq_sum_filter (A : Matrix O I ℂ) (D : ℕ) :
    g10g_svdTrunc A D
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card I) => (i : ℕ) < D),
        (matrixSingularValues A i : ℂ) •
          vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i)) := by
  rw [g10g_svdTrunc, ← Finset.sum_filter]

/-- Subtracting the SVD truncation from a matrix leaves precisely the singular rank-one terms
with indices at least `D`. -/
theorem g10g_svdTrunc_sub_eq (A : Matrix O I ℂ) (D : ℕ) :
    A - g10g_svdTrunc A D
      = ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card I) => D ≤ (i : ℕ)),
        (matrixSingularValues A i : ℂ) •
          vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i)) := by
  have hp : ∀ i : Fin (Fintype.card I),
      ((matrixSingularValues A i : ℂ) •
          vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i)))
        - (if (i : ℕ) < D then
            ((matrixSingularValues A i : ℂ) •
              vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i))) else 0)
        = (if D ≤ (i : ℕ) then
            ((matrixSingularValues A i : ℂ) •
              vecMulVec (leftSingularVector A i) (star (rightSingularBasis A i))) else 0) := by
    intro i
    by_cases hi : (i : ℕ) < D
    · simp [hi]
    · have hge : D ≤ (i : ℕ) := Nat.le_of_not_gt hi
      simp [hi, hge]
  refine (congrArg (fun z : Matrix O I ℂ => z - g10g_svdTrunc A D)
    (matrix_eq_sum_singularVectors A)).trans ?_
  rw [g10g_svdTrunc, ← Finset.sum_sub_distrib]
  conv_lhs => simp only [hp]
  rw [← Finset.sum_filter]

/-- The squared Frobenius error of SVD truncation is the sum of the squared singular values at
indices at least `D`. -/
theorem g10g_svdTrunc_error_sq (A : Matrix O I ℂ) (D : ℕ) :
    spectralFrobenius (A - g10g_svdTrunc A D) ^ 2
      = ∑ i : Fin (Fintype.card I), if (i : ℕ) < D then 0
        else (matrixSingularValues A i) ^ 2 := by
  rw [g10g_svdTrunc_sub_eq]
  rw [g10g_spectralFrobenius_sq_sum_singularRankOne, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : (i : ℕ) < D
  · simp [hi]
  · simp [hi]

/-- The squared Frobenius norm of the SVD truncation is the sum of the squared singular values
at indices below `D`. -/
theorem g10g_svdTrunc_sq (A : Matrix O I ℂ) (D : ℕ) :
    spectralFrobenius (g10g_svdTrunc A D) ^ 2
      = ∑ i : Fin (Fintype.card I), if (i : ℕ) < D
        then (matrixSingularValues A i) ^ 2 else 0 := by
  rw [g10g_svdTrunc_eq_sum_filter, g10g_spectralFrobenius_sq_sum_singularRankOne,
    Finset.sum_filter]

section CutTail

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- For a cut matrix, the squared singular-value tail can be summed over indices below `d ^ (n -
c)` instead of over the support of the singular-value sequence. -/
theorem g10g_tail_support_eq_range (c D : ℕ) :
    ∑ i ∈ (matrixSingularValues (cutMatrix n d ψ c)).support.filter (fun i => D ≤ i),
        (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2
      = ∑ i ∈ (Finset.range (d ^ (n - c))).filter (fun i => D ≤ i),
        (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 := by
  have hsup : (matrixSingularValues (cutMatrix n d ψ c)).support
      = Finset.range (cutRank n d ψ c) := support_matrixSingularValues_cutMatrix ψ c
  have hle : cutRank n d ψ c ≤ d ^ (n - c) := cutRank_le_pow_right ψ c
  refine Finset.sum_subset (fun i hi => ?_) (fun i hi hnot => ?_)
  · rw [hsup] at hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨lt_of_lt_of_le hi.1 hle, hi.2⟩
  · simp only [Finset.mem_filter] at hi hnot
    rcases not_and_or.mp hnot with hns | hnd
    · have hz : matrixSingularValues (cutMatrix n d ψ c) i = 0 := by
        by_contra hne
        exact hns (Finsupp.mem_support_iff.mpr hne)
      rw [hz]
      simp
    · exact absurd hi.2 hnd

/-- Expresses the squared Schmidt tail as the sum of squared cut-matrix singular values over
indices from `D` up to `d ^ (n - c) - 1`. -/
theorem g10g_schmidtTailSq_eq_filter_sum (c D : ℕ) :
    schmidtTailSq n d ψ c D
      = ∑ i ∈ (Finset.range (d ^ (n - c))).filter (fun i => D ≤ i),
        (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 := by
  rw [schmidtTailSq_eq_sum ψ c D]
  exact g10g_tail_support_eq_range ψ c D

/-- Expresses the squared Schmidt tail as a finite sum over `Fin (d ^ (n - c))`, with zero
contributions at indices below `D`. -/
theorem g10g_schmidtTailSq_eq_ite_sum (c D : ℕ) :
    schmidtTailSq n d ψ c D
      = ∑ i : Fin (d ^ (n - c)), if (i : ℕ) < D then 0
        else (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 := by
  rw [g10g_schmidtTailSq_eq_filter_sum ψ c D, Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : (i : ℕ) < D
  · simp [hi]
  · have hge : D ≤ (i : ℕ) := Nat.le_of_not_gt hi
    simp [hi, hge]

/-- The squared Schmidt tail equals the squared Frobenius distance between the cut matrix and
its SVD truncation at `D`. -/
theorem g10g_schmidtTailSq_eq_frob_sub_trunc (c D : ℕ) :
    schmidtTailSq n d ψ c D
      = spectralFrobenius (cutMatrix n d ψ c
          - g10g_svdTrunc (cutMatrix n d ψ c) D) ^ 2 := by
  rw [g10g_svdTrunc_error_sq, g10g_schmidtTailSq_eq_ite_sum ψ c D]
  have hcard : Fintype.card (Fin (d ^ (n - c))) = d ^ (n - c) := Fintype.card_fin _
  have hR : (∑ i : Fin (Fintype.card (Fin (d ^ (n - c)))),
        if (i : ℕ) < D then 0
          else (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2)
      = ∑ i ∈ Finset.range (d ^ (n - c)), if i < D then 0
          else (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range, hcard]
  have hL : (∑ i : Fin (d ^ (n - c)), if (i : ℕ) < D then 0
        else (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2)
      = ∑ i ∈ Finset.range (d ^ (n - c)), if i < D then 0
          else (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 :=
    Fin.sum_univ_eq_sum_range
      (fun k => if k < D then 0 else (matrixSingularValues (cutMatrix n d ψ c) k) ^ 2) _
  rw [hR, hL]

/-- The sum of all squared singular values of the cut matrix equals its squared Frobenius norm. -/
theorem g10g_singularSq_sum_eq_frob (c : ℕ) :
    (∑ i : Fin (d ^ (n - c)), (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2)
      = spectralFrobenius (cutMatrix n d ψ c) ^ 2 := by
  have hcard : Fintype.card (Fin (d ^ (n - c))) = d ^ (n - c) := Fintype.card_fin _
  have h := spectralFrobenius_sq_singular (A := cutMatrix n d ψ c)
  have hconv : (∑ i : Fin (Fintype.card (Fin (d ^ (n - c)))),
        (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2)
      = ∑ i : Fin (d ^ (n - c)), (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 := by
    have h1 := Fin.sum_univ_eq_sum_range
      (fun k => (matrixSingularValues (cutMatrix n d ψ c) k) ^ 2)
      (Fintype.card (Fin (d ^ (n - c))))
    have h2 := Fin.sum_univ_eq_sum_range
      (fun k => (matrixSingularValues (cutMatrix n d ψ c) k) ^ 2) (d ^ (n - c))
    rw [h1, h2, hcard]
  rw [← hconv]
  exact h.symm

end CutTail

/-- The squared Frobenius norm of a matrix splits into the squared norm of its SVD truncation
and the squared norm of the residual. -/
theorem g10g_pythagoras_svdTrunc [DecidableEq O] (A : Matrix O I ℂ) (D : ℕ) :
    spectralFrobenius A ^ 2 = spectralFrobenius (g10g_svdTrunc A D) ^ 2
      + spectralFrobenius (A - g10g_svdTrunc A D) ^ 2 := by
  rw [spectralFrobenius_sq_singular, g10g_svdTrunc_sq, g10g_svdTrunc_error_sq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : (i : ℕ) < D
  · simp [hi]
  · simp [hi]

end Truncation

section NestedRank

/-- Appends a symbol `y` to a configuration of length `c`, placing it at the final coordinate of
the resulting configuration of length `c + 1`. -/
def g10g_snoc {c d : ℕ} (u : Fin c → Fin d) (y : Fin d) : Fin (c + 1) → Fin d :=
  fun k => if h : (k : ℕ) < c then u ⟨k, h⟩ else y

/-- Appending a symbol preserves every coordinate whose index is below the original length `c`. -/
theorem g10g_snoc_of_lt {c d : ℕ} (u : Fin c → Fin d) (y : Fin d)
    {k : Fin (c + 1)} (hk : (k : ℕ) < c) : g10g_snoc u y k = u ⟨k, hk⟩ := by
  simp [g10g_snoc, hk]

/-- The final coordinate of `g10g_snoc u y` is the appended symbol `y`. -/
theorem g10g_snoc_last {c d : ℕ} (u : Fin c → Fin d) (y : Fin d) :
    g10g_snoc u y ⟨c, by omega⟩ = y := by
  simp [g10g_snoc]

/-- Restricts a configuration of length `c + 1` to its first `c` coordinates. -/
def g10g_init {c d : ℕ} (u : Fin (c + 1) → Fin d) : Fin c → Fin d :=
  fun k => u ⟨(k : ℕ), by omega⟩

/-- Returns the final symbol of a configuration of length `c + 1`. -/
def g10g_last {c d : ℕ} (u : Fin (c + 1) → Fin d) : Fin d :=
  u ⟨c, by omega⟩

/-- Appending a configuration's last symbol to its initial segment reconstructs the
configuration. -/
theorem g10g_snoc_init_last {c d : ℕ} (u : Fin (c + 1) → Fin d) :
    g10g_snoc (g10g_init u) (g10g_last u) = u := by
  funext k
  by_cases hk : (k : ℕ) < c
  · rw [g10g_snoc_of_lt _ _ hk]
    simp [g10g_init]
  · have hkc : (k : ℕ) = c := by
      have hk' := k.isLt
      omega
    have hk2 : g10g_snoc (g10g_init u) (g10g_last u) k = g10g_last u := by
      unfold g10g_snoc
      rw [dite_eq_right hk]
    rw [hk2]
    have heq : (⟨c, by omega⟩ : Fin (c + 1)) = k := by
      ext
      simp [hkc]
    rw [← heq]
    simp [g10g_last]

/-- Taking the initial segment after appending a symbol recovers the original configuration. -/
theorem g10g_init_snoc {c d : ℕ} (u : Fin c → Fin d) (y : Fin d) :
    g10g_init (g10g_snoc u y) = u := by
  funext k
  simp [g10g_init, g10g_snoc, k.isLt]

/-- Taking the final symbol after appending `y` returns `y`. -/
theorem g10g_last_snoc {c d : ℕ} (u : Fin c → Fin d) (y : Fin d) :
    g10g_last (g10g_snoc u y) = y := by
  simp [g10g_last, g10g_snoc]

/-- An appended configuration equals `u'` exactly when its initial segment and appended symbol
equal the initial segment and final symbol of `u'`. -/
theorem g10g_snoc_eq_iff {c d : ℕ} {u' : Fin (c + 1) → Fin d} {u : Fin c → Fin d} {y : Fin d} :
    g10g_snoc u y = u' ↔ u = g10g_init u' ∧ y = g10g_last u' := by
  constructor
  · intro h
    constructor
    · rw [← h, g10g_init_snoc]
    · rw [← h, g10g_last_snoc]
  · intro h
    rw [h.1, h.2, g10g_snoc_init_last]

/-- Prepends a symbol to a suffix configuration when `c + 1 ≤ n`, increasing its length from `n
- (c + 1)` to `n - c`. -/
def g10g_cons {n c d : ℕ} (_hc : c + 1 ≤ n) (y : Fin d)
    (v : Fin (n - (c + 1)) → Fin d) : Fin (n - c) → Fin d :=
  fun k => if h : (k : ℕ) = 0 then y else v ⟨(k : ℕ) - 1, by
    have hk := k.isLt
    omega⟩

/-- The zeroth coordinate of a configuration formed by prepending `y` is `y`. -/
theorem g10g_cons_zero {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d)
    (v : Fin (n - (c + 1)) → Fin d) :
    g10g_cons hc y v ⟨0, by omega⟩ = y := by
  simp [g10g_cons]

/-- At a successor coordinate, a configuration formed by prepending a symbol returns the
corresponding coordinate of the original suffix. -/
theorem g10g_cons_succ {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d)
    (v : Fin (n - (c + 1)) → Fin d) (k : Fin (n - (c + 1))) :
    g10g_cons hc y v ⟨(k : ℕ) + 1, by have hk := k.isLt; omega⟩ = v k := by
  simp [g10g_cons]

/-- Returns the first symbol of a suffix of length `n - c`, which is nonempty under `c + 1 ≤ n`. -/
def g10g_head {n c d : ℕ} (hc : c + 1 ≤ n) (v : Fin (n - c) → Fin d) : Fin d :=
  v ⟨0, by omega⟩

/-- Removes the first symbol of a suffix of length `n - c`, producing a suffix of length `n - (c
+ 1)`. -/
def g10g_tail {n c d : ℕ} (hc : c + 1 ≤ n) (v : Fin (n - c) → Fin d) :
    Fin (n - (c + 1)) → Fin d :=
  fun k => v ⟨(k : ℕ) + 1, by have hk := k.isLt; omega⟩

/-- Prepending the head of a nonempty suffix to its tail reconstructs that suffix. -/
theorem g10g_cons_head_tail {n c d : ℕ} (hc : c + 1 ≤ n) (v : Fin (n - c) → Fin d) :
    g10g_cons hc (g10g_head hc v) (g10g_tail hc v) = v := by
  funext k
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = (⟨0, by have hk' := k.isLt; omega⟩ : Fin (n - c)) := by
      ext
      simpa using! hk
    rw [hk0, g10g_cons_zero]
    simp [g10g_head]
  · have hkk : (0 : ℕ) < (k : ℕ) := Nat.pos_of_ne_zero hk
    have hde : g10g_cons hc (g10g_head hc v) (g10g_tail hc v) k
        = g10g_tail hc v (⟨(k : ℕ) - 1, by have hk' := k.isLt; omega⟩ : Fin (n - (c + 1))) := by
      unfold g10g_cons
      rw [dite_eq_right hk]
    rw [hde, g10g_tail]
    have heq : (⟨((k : ℕ) - 1) + 1, by have hk' := k.isLt; omega⟩ : Fin (n - c)) = k := by
      ext
      simp
      omega
    rw [heq]

/-- The head of a suffix formed by prepending `y` is `y`. -/
theorem g10g_head_cons {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d)
    (v : Fin (n - (c + 1)) → Fin d) : g10g_head hc (g10g_cons hc y v) = y := by
  simp [g10g_head, g10g_cons]

/-- Taking the tail of a suffix formed by prepending a symbol recovers the original suffix. -/
theorem g10g_tail_cons {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d)
    (v : Fin (n - (c + 1)) → Fin d) : g10g_tail hc (g10g_cons hc y v) = v := by
  funext k
  simp [g10g_tail, g10g_cons]

/-- A prepended suffix equals `v` exactly when the prepended symbol is the head of `v` and the
remaining suffix is its tail. -/
theorem g10g_cons_eq_iff {n c d : ℕ} (hc : c + 1 ≤ n)
    {v : Fin (n - c) → Fin d} {y : Fin d} {v' : Fin (n - (c + 1)) → Fin d} :
    g10g_cons hc y v' = v ↔ y = g10g_head hc v ∧ v' = g10g_tail hc v := by
  constructor
  · intro h
    constructor
    · rw [← h, g10g_head_cons]
    · rw [← h, g10g_tail_cons]
  · intro h
    rw [h.1, h.2, g10g_cons_head_tail]

/-- Moving the final symbol of a prefix of length `c + 1` to the head of the suffix leaves the
joined full configuration unchanged. -/
theorem g10g_splitJoin_snoc_cons {n c d : ℕ} (hc : c + 1 ≤ n)
    (u' : Fin (c + 1) → Fin d) (v' : Fin (n - (c + 1)) → Fin d) :
    splitJoin n c d (g10g_init u') (g10g_cons hc (g10g_last u') v')
      = splitJoin n (c + 1) d u' v' := by
  funext k
  by_cases h1 : (k : ℕ) < c
  · have h1' : (k : ℕ) < c + 1 := by omega
    simp [splitJoin, h1, h1', g10g_init]
  · by_cases h2 : (k : ℕ) < c + 1
    · have hk : (k : ℕ) = c := by omega
      have hk2 : ¬((k : ℕ) < c) := h1
      rw [splitJoin, splitJoin, dite_eq_right hk2, dite_eq_left h2]
      simp [g10g_cons, hk, g10g_last]
    · have hk2 : ¬((k : ℕ) < c) := h1
      rw [splitJoin, splitJoin, dite_eq_right hk2, dite_eq_right h2]
      simp only [g10g_cons]
      rw [dite_eq_right (by have hk' := k.isLt; omega : ¬((k : ℕ) - c = 0))]
      congr 1

end NestedRank

section NestedRankFactor

/-- The zero-one matrix that appends a fixed physical symbol `y` to an encoded prefix
configuration. -/
def g10g_leftFactor {c d : ℕ} (y : Fin d) : Matrix (Fin (d ^ (c + 1))) (Fin (d ^ c)) ℂ :=
  Matrix.of fun i' w =>
    if (finPowEnc d (c + 1)).symm i' = g10g_snoc ((finPowEnc d c).symm w) y then 1 else 0

/-- The zero-one matrix that prepends a fixed physical symbol `y` to an encoded suffix
configuration. -/
def g10g_rightFactor {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d) :
    Matrix (Fin (d ^ (n - c))) (Fin (d ^ (n - (c + 1)))) ℂ :=
  Matrix.of fun w j' =>
    if (finPowEnc d (n - c)).symm w = g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')
      then 1 else 0

/-- At the column encoding a row configuration's initial segment, the left factor is one exactly
when `y` is that configuration's last symbol, and zero otherwise. -/
theorem g10g_leftFactor_self {c d : ℕ} (y : Fin d) (i' : Fin (d ^ (c + 1))) :
    g10g_leftFactor y i' (finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i')))
      = if y = g10g_last ((finPowEnc d (c + 1)).symm i') then 1 else 0 := by
  simp only [g10g_leftFactor, Matrix.of_apply, Equiv.symm_apply_apply]
  have hiff : ((finPowEnc d (c + 1)).symm i'
      = g10g_snoc (g10g_init ((finPowEnc d (c + 1)).symm i')) y)
      ↔ (y = g10g_last ((finPowEnc d (c + 1)).symm i')) := by
    rw [eq_comm, g10g_snoc_eq_iff, and_iff_right rfl]
  simp only [hiff]

/-- A left-factor entry vanishes unless its column encodes the initial segment of its decoded
row configuration. -/
theorem g10g_leftFactor_eq_zero_of_ne {c d : ℕ} (y : Fin d) (i' : Fin (d ^ (c + 1)))
    (w : Fin (d ^ c)) (hw : w ≠ finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i'))) :
    g10g_leftFactor y i' w = 0 := by
  simp only [g10g_leftFactor, Matrix.of_apply]
  rw [ite_eq_right]
  intro hcongr
  have key : w = finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i')) := by
    have := (g10g_snoc_eq_iff (u' := (finPowEnc d (c + 1)).symm i')).mp (hcongr.symm)
    rw [← this.1]
    simp
  exact hw key

/-- The right factor is one at the row encoding the configuration obtained by prepending `y` to
its decoded column configuration. -/
theorem g10g_rightFactor_self {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d)
    (j' : Fin (d ^ (n - (c + 1)))) :
    g10g_rightFactor hc y
        (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))) j' = 1 := by
  simp [g10g_rightFactor]

/-- A right-factor entry vanishes unless its row encodes `y` prepended to its decoded column
configuration. -/
theorem g10g_rightFactor_eq_zero_of_ne {n c d : ℕ} (hc : c + 1 ≤ n) (y : Fin d)
    (v : Fin (d ^ (n - c))) (j' : Fin (d ^ (n - (c + 1))))
    (hv : v ≠ finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))) :
    g10g_rightFactor hc y v j' = 0 := by
  simp only [g10g_rightFactor, Matrix.of_apply]
  rw [ite_eq_right]
  intro hcongr
  have key : v = finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')) := by
    rw [← hcongr]
    simp
  exact hv key

/-- Evaluates an entry of the cut matrix multiplied by the left and right factors for `y`. The
entry is zero unless `y` matches the decoded row's last symbol; otherwise it uses the
shortened prefix and the suffix with `y` prepended. -/
theorem g10g_factor_prod_apply {n d c : ℕ} (hc : c + 1 ≤ n) (ψ : (Fin n → Fin d) → ℂ)
    (y : Fin d) (i' : Fin (d ^ (c + 1))) (j' : Fin (d ^ (n - (c + 1)))) :
    (g10g_leftFactor (c := c) y * cutMatrix n d ψ c * g10g_rightFactor hc y) i' j'
      = if y = g10g_last ((finPowEnc d (c + 1)).symm i') then
          cutMatrix n d ψ c
            (finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i')))
            (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')))
        else 0 := by
  rw [Matrix.mul_apply]
  set v0 : Fin (d ^ (n - c)) :=
    finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')) with hv0
  set w0 : Fin (d ^ c) :=
    finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i')) with hw0
  have hcol : (∑ v : Fin (d ^ (n - c)),
        (g10g_leftFactor (c := c) y * cutMatrix n d ψ c) i' v * g10g_rightFactor hc y v j')
      = (g10g_leftFactor (c := c) y * cutMatrix n d ψ c) i' v0 := by
    rw [Finset.sum_eq_single v0]
    · rw [hv0, g10g_rightFactor_self]
      ring
    · intro b _ hne
      rw [g10g_rightFactor_eq_zero_of_ne hc y b j' (by simpa [hv0] using! hne)]
      ring
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  rw [hcol]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single w0]
  · rw [hw0, g10g_leftFactor_self]
    by_cases h : y = g10g_last ((finPowEnc d (c + 1)).symm i')
    · simp [h]
    · simp [h]
  · intro b _ hne
    rw [g10g_leftFactor_eq_zero_of_ne y i' b (by simpa [hw0] using! hne)]
    ring
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- The cut matrix at `c + 1` is the sum over physical symbols of the cut matrix at `c`
multiplied by the corresponding left and right factors. -/
theorem g10g_cutMatrix_succ_eq_sum_factor {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)
    (c : ℕ) (hc : c + 1 ≤ n) :
    cutMatrix n d ψ (c + 1)
      = ∑ y : Fin d, g10g_leftFactor (c := c) y * cutMatrix n d ψ c * g10g_rightFactor hc y := by
  ext i' j'
  have hsplit : splitJoin n c d
      (g10g_init ((finPowEnc d (c + 1)).symm i'))
      (g10g_cons hc (g10g_last ((finPowEnc d (c + 1)).symm i'))
        ((finPowEnc d (n - (c + 1))).symm j'))
      = splitJoin n (c + 1) d ((finPowEnc d (c + 1)).symm i')
        ((finPowEnc d (n - (c + 1))).symm j') :=
    g10g_splitJoin_snoc_cons hc _ _
  have hL : cutMatrix n d ψ (c + 1) i' j'
      = ψ (splitJoin n (c + 1) d ((finPowEnc d (c + 1)).symm i')
        ((finPowEnc d (n - (c + 1))).symm j')) := by
    simp [cutMatrix]
  rw [hL, ← hsplit]
  have hR : (∑ y : Fin d,
        g10g_leftFactor (c := c) y * cutMatrix n d ψ c * g10g_rightFactor hc y) i' j'
      = ∑ y : Fin d,
          (if y = g10g_last ((finPowEnc d (c + 1)).symm i') then
            cutMatrix n d ψ c
              (finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i')))
              (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')))
          else 0) := by
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun y _ => g10g_factor_prod_apply hc ψ y i' j')
  rw [hR]
  rw [Finset.sum_eq_single (g10g_last ((finPowEnc d (c + 1)).symm i'))]
  · simp
    have hM : cutMatrix n d ψ c
          (finPowEnc d c (g10g_init ((finPowEnc d (c + 1)).symm i')))
          (finPowEnc d (n - c)
            (g10g_cons hc (g10g_last ((finPowEnc d (c + 1)).symm i'))
              ((finPowEnc d (n - (c + 1))).symm j')))
        = ψ (splitJoin n c d
            (g10g_init ((finPowEnc d (c + 1)).symm i'))
            (g10g_cons hc (g10g_last ((finPowEnc d (c + 1)).symm i'))
              ((finPowEnc d (n - (c + 1))).symm j'))) := by
      simp [cutMatrix, Equiv.symm_apply_apply]
    rw [hM]
  · intro b _ hne
    rw [ite_eq_right hne]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

end NestedRankFactor

section NestedRankBound

/-- The rank of the sum of two finite complex matrices is at most the sum of their ranks. -/
theorem g10g_matrixRank_add_le {m k : ℕ} (A B : Matrix (Fin m) (Fin k) ℂ) :
    Matrix.rank (A + B) ≤ Matrix.rank A + Matrix.rank B := by
  rw [rank_eq_finrank_range_toEuclideanLin (A + B), rank_eq_finrank_range_toEuclideanLin A,
    rank_eq_finrank_range_toEuclideanLin B]
  have hadd : (A + B).toEuclideanLin = A.toEuclideanLin + B.toEuclideanLin :=
    map_add Matrix.toEuclideanLin A B
  rw [hadd]
  have hle : LinearMap.range (A.toEuclideanLin + B.toEuclideanLin)
      ≤ LinearMap.range A.toEuclideanLin ⊔ LinearMap.range B.toEuclideanLin :=
    LinearMap.range_add_le _ _
  exact le_trans (Submodule.finrank_mono hle)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a finite sum of complex matrices is at most the sum of their ranks. -/
theorem g10g_matrixRank_sum_le {m k d : ℕ} (T : Fin d → Matrix (Fin m) (Fin k) ℂ) :
    Matrix.rank (∑ y : Fin d, T y) ≤ ∑ y : Fin d, Matrix.rank (T y) := by
  have hgen : ∀ s : Finset (Fin d),
      Matrix.rank (∑ y ∈ s, T y) ≤ ∑ y ∈ s, Matrix.rank (T y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert y s hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy]
      exact le_trans (g10g_matrixRank_add_le _ _) (add_le_add le_rfl ih)
  simpa using! hgen Finset.univ

/-- Moving a valid cut one site to the right increases its rank by at most a factor of the local
dimension `d`. -/
theorem g10g_cutRank_succ_le {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c : ℕ) (hc : c + 1 ≤ n) :
    cutRank n d ψ (c + 1) ≤ d * cutRank n d ψ c := by
  have hM := g10g_cutMatrix_succ_eq_sum_factor ψ c hc
  rw [cutRank_eq_matrixRank ψ (c + 1), cutRank_eq_matrixRank ψ c, hM]
  refine le_trans (g10g_matrixRank_sum_le _) ?_
  have hle : ∀ y : Fin d,
      Matrix.rank (g10g_leftFactor (c := c) y * cutMatrix n d ψ c * g10g_rightFactor hc y)
        ≤ Matrix.rank (cutMatrix n d ψ c) := by
    intro y
    have h1 : Matrix.rank (g10g_leftFactor (c := c) y * cutMatrix n d ψ c * g10g_rightFactor hc y)
        ≤ Matrix.rank (g10g_leftFactor (c := c) y * cutMatrix n d ψ c) :=
      le_trans (Matrix.rank_mul_le _ _) (min_le_left _ _)
    have h2 : Matrix.rank (g10g_leftFactor (c := c) y * cutMatrix n d ψ c)
        ≤ Matrix.rank (cutMatrix n d ψ c) :=
      le_trans (Matrix.rank_mul_le _ _) (min_le_right _ _)
    exact le_trans h1 h2
  refine le_trans (Finset.sum_le_sum (fun y _ => hle y)) ?_
  have hconst : (∑ _y : Fin d, Matrix.rank (cutMatrix n d ψ c))
      = d * Matrix.rank (cutMatrix n d ψ c) := by
    rw [Finset.sum_const, Finset.card_fin]
    simp
  rw [hconst]

end NestedRankBound

set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix Complex
open scoped BigOperators Nat ComplexConjugate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Module

/-- Identifies a prefix of length `c` and a suffix of length `n - c` with a full configuration
of length `n`, provided `c ≤ n`. -/
def g10a_splitJoinEquiv (n c d : ℕ) (hc : c ≤ n) :
    ((Fin c → Fin d) × (Fin (n - c) → Fin d)) ≃ (Fin n → Fin d) where
  toFun := fun p => splitJoin n c d p.1 p.2
  invFun := fun x =>
    (fun k : Fin c => x ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩,
      fun k : Fin (n - c) => x ⟨c + (k : ℕ), by have hk := k.isLt; omega⟩)
  left_inv := by
    intro p
    rcases p with ⟨u, v⟩
    apply Prod.ext
    · funext k
      show (splitJoin n c d u v)
          ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩ = _
      unfold splitJoin
      simp only [Fin.is_lt]
      exact congrArg u (Fin.ext rfl)
    · funext k
      show (splitJoin n c d u v) ⟨c + (k : ℕ), by have hk := k.isLt; omega⟩ = _
      unfold splitJoin
      have hnk : ¬(c + (k : ℕ) < c) := by omega
      simp only [hnk, ↓reduceDIte]
      refine congrArg v ?_
      exact Fin.ext (Nat.add_sub_cancel_left c (k : ℕ))
  right_inv := by
    intro x
    funext k
    unfold splitJoin
    by_cases hk : (k : ℕ) < c
    · simp only [hk]
      exact congrArg x (Fin.ext rfl)
    · simp only [hk, ↓reduceDIte]
      exact congrArg x (Fin.ext (Nat.add_sub_of_le (le_of_not_gt hk)))

/-- An entry of a cut matrix is the state amplitude at the full configuration obtained by
decoding and joining its row and column indices. -/
theorem g10a_cutMatrix_apply {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c : ℕ)
    (i : Fin (d ^ c)) (j : Fin (d ^ (n - c))) :
    cutMatrix n d ψ c i j
      = ψ (splitJoin n c d ((finPowEnc d c).symm i) ((finPowEnc d (n - c)).symm j)) :=
  rfl

/-- For a cut position `c ≤ n`, the squared Frobenius norm of the cut matrix equals the sum of
squared moduli of all state amplitudes. -/
theorem g10a_parseval {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) {c : ℕ} (hc : c ≤ n) :
    spectralFrobenius (cutMatrix n d ψ c) ^ 2 = ∑ x, Complex.normSq (ψ x) := by
  rw [spectralFrobenius_sq]
  have hentry : ∀ (i : Fin (d ^ c)) (j : Fin (d ^ (n - c))),
      Complex.normSq (cutMatrix n d ψ c i j)
        = Complex.normSq (ψ (splitJoin n c d ((finPowEnc d c).symm i)
            ((finPowEnc d (n - c)).symm j))) := fun _ _ => rfl
  have hre : (∑ i : Fin (d ^ c), ∑ j : Fin (d ^ (n - c)),
        Complex.normSq (cutMatrix n d ψ c i j))
      = ∑ u : Fin c → Fin d, ∑ v : Fin (n - c) → Fin d,
        Complex.normSq (ψ (splitJoin n c d u v)) := by
    simp only [hentry]
    rw [← Equiv.sum_comp (finPowEnc d c)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Equiv.sum_comp (finPowEnc d (n - c))]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [Equiv.symm_apply_apply]
  rw [hre]
  have hprod : (∑ u : Fin c → Fin d, ∑ v : Fin (n - c) → Fin d,
        Complex.normSq (ψ (splitJoin n c d u v)))
      = ∑ p : (Fin c → Fin d) × (Fin (n - c) → Fin d),
        Complex.normSq (ψ (splitJoin n c d p.1 p.2)) :=
    (Fintype.sum_prod_type (fun p : (Fin c → Fin d) × (Fin (n - c) → Fin d) =>
      Complex.normSq (ψ (splitJoin n c d p.1 p.2)))).symm
  rw [hprod]
  exact Fintype.sum_equiv (g10a_splitJoinEquiv n c d hc)
    (fun p => Complex.normSq (ψ (splitJoin n c d p.1 p.2)))
    (fun x => Complex.normSq (ψ x)) (fun _ => rfl)

/-- When `n ≤ c`, a cut-matrix entry is the state amplitude at the restriction of its decoded
row configuration to the first `n` sites. -/
theorem g10a_cutMatrix_apply_of_le {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) {c : ℕ}
    (hc : n ≤ c) (i : Fin (d ^ c)) (j : Fin (d ^ (n - c))) :
    cutMatrix n d ψ c i j
      = ψ (fun k : Fin n => (finPowEnc d c).symm i ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩) := by
  rw [g10a_cutMatrix_apply]
  congr 1
  funext k
  unfold splitJoin
  have hk : ((k : ℕ) < c) := lt_of_lt_of_le k.isLt hc
  simp [hk]

/-- A cut at or beyond the full chain length has rank at most one. -/
theorem g10a_cutRank_le_one_of_le {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) {c : ℕ}
    (hc : n ≤ c) : cutRank n d ψ c ≤ 1 := by
  have h := cutRank_le_pow_right ψ c
  rw [Nat.sub_eq_zero_of_le hc, Nat.pow_zero] at h
  exact h

/-- Restricting a joined configuration of length `c` to its prefix of length `n` recovers that
prefix when `n ≤ c`. -/
theorem g10a_restrict_splitJoin {n c d : ℕ} (hc : n ≤ c) (x : Fin n → Fin d)
    (w : Fin (c - n) → Fin d) :
    (fun k : Fin n => splitJoin c n d x w ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩) = x := by
  funext k
  unfold splitJoin
  have hk : ((k : ℕ) < n) := k.isLt
  simp [hk]

/-- Restricting the configuration produced by the split-and-join equivalence to its first `n`
coordinates returns the pair's first component. -/
theorem g10a_restrict_splitJoinEquiv {n c d : ℕ} (hc : n ≤ c)
    (p : (Fin n → Fin d) × (Fin (c - n) → Fin d)) :
    (fun k : Fin n => g10a_splitJoinEquiv c n d hc p
      ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩) = p.1 :=
  g10a_restrict_splitJoin hc p.1 p.2

/-- Summing a real-valued function of the first `n` coordinates over configurations of length `c
≥ n` multiplies its sum over length-`n` configurations by `d ^ (c - n)`. -/
theorem g10a_sum_restrict {n c d : ℕ} (hc : n ≤ c) (F : (Fin n → Fin d) → ℝ) :
    (∑ u : Fin c → Fin d, F (fun k : Fin n => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩))
      = (d ^ (c - n) : ℝ) * ∑ x, F x := by
  have h1 : (∑ u : Fin c → Fin d,
        F (fun k : Fin n => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩))
      = ∑ p : (Fin n → Fin d) × (Fin (c - n) → Fin d), F p.1 :=
    (Equiv.sum_comp (g10a_splitJoinEquiv c n d hc)
      (fun u => F (fun k : Fin n => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩))).symm.trans
      (Finset.sum_congr rfl (fun p _ => congrArg F (g10a_restrict_splitJoinEquiv hc p)))
  rw [h1]
  have h2 : (∑ p : (Fin n → Fin d) × (Fin (c - n) → Fin d), F p.1)
      = ∑ x : Fin n → Fin d, ∑ _w : Fin (c - n) → Fin d, F x :=
    Fintype.sum_prod_type (fun p : (Fin n → Fin d) × (Fin (c - n) → Fin d) => F p.1)
  rw [h2]
  have h3 : ∀ x : Fin n → Fin d,
      (∑ _w : Fin (c - n) → Fin d, F x) = (d ^ (c - n) : ℝ) * F x := by
    intro x
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => h3 x)

/-- For a cut position `c ≥ n`, the squared Frobenius norm of the cut matrix is `d ^ (c - n)`
times the sum of squared moduli of the state amplitudes. -/
theorem g10a_parseval_of_le {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) {c : ℕ} (hc : n ≤ c) :
    spectralFrobenius (cutMatrix n d ψ c) ^ 2
      = (d ^ (c - n) : ℝ) * ∑ x, Complex.normSq (ψ x) := by
  rw [spectralFrobenius_sq]
  have hentry : ∀ (i : Fin (d ^ c)) (j : Fin (d ^ (n - c))),
      Complex.normSq (cutMatrix n d ψ c i j)
        = Complex.normSq (ψ (fun k : Fin n =>
            (finPowEnc d c).symm i ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩)) := by
    intro i j
    rw [g10a_cutMatrix_apply_of_le ψ hc]
  have hre : (∑ i : Fin (d ^ c), ∑ j : Fin (d ^ (n - c)),
        Complex.normSq (cutMatrix n d ψ c i j))
      = ∑ u : Fin c → Fin d,
        Complex.normSq (ψ (fun k : Fin n => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩)) := by
    simp only [hentry]
    rw [← Equiv.sum_comp (finPowEnc d c)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have hsumj : (∑ j : Fin (d ^ (n - c)), Complex.normSq (ψ
          (fun k : Fin n => (finPowEnc d c).symm (finPowEnc d c u)
            ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩)))
        = Complex.normSq (ψ
          (fun k : Fin n => (finPowEnc d c).symm (finPowEnc d c u)
            ⟨(k : ℕ), lt_of_lt_of_le k.isLt hc⟩)) := by
      rw [Nat.sub_eq_zero_of_le hc, Nat.pow_zero]
      exact Fin.sum_univ_one _
    rw [hsumj]
    simp only [Equiv.symm_apply_apply]
  rw [hre]
  exact g10a_sum_restrict hc (fun x => Complex.normSq (ψ x))

/-- For a rational fraction with positive denominator and coprime numerator and denominator,
`ratEntryWidth` is the maximum of their binary lengths, computed from their absolute values. -/
theorem clause14Aux_ratEntryWidth_div {a b : ℤ} (hb : 0 < b)
    (hc : Nat.Coprime a.natAbs b.natAbs) :
    ratEntryWidth ((a / b : ℚ)) = max (Nat.log2 a.natAbs + 1) (Nat.log2 b.natAbs + 1) := by
  have hn : ((a / b : ℚ).num).natAbs = a.natAbs := by
    rw [Rat.num_div_eq_of_coprime hb hc]
  have hd : ((a / b : ℚ)).den = b.natAbs := by
    refine Int.natCast_inj.1 ?_
    rw [Rat.den_div_eq_of_coprime hb hc, Int.natAbs_of_nonneg hb.le]
  simp only [ratEntryWidth, hn, hd]

/-- For `p ≥ 2`, the rational entry width of `1 / p` is `Nat.log2 p + 1`. -/
theorem clause14Aux_ratEntryWidth_one_div {p : ℕ} (hp : 2 ≤ p) :
    ratEntryWidth ((1 : ℚ) / p) = Nat.log2 p + 1 := by
  have he : ((1 : ℚ) / p) = (((1 : ℤ) / (p : ℤ) : ℚ)) := by norm_num
  have hb : (0 : ℤ) < p := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 2) hp)
  have hc : Nat.Coprime ((1:ℤ)).natAbs (p:ℤ).natAbs := by
    rw [Int.natAbs_one, Int.natAbs_natCast]
    exact Nat.coprime_one_left _
  rw [he, clause14Aux_ratEntryWidth_div hb hc, Int.natAbs_one, Int.natAbs_natCast]
  have h1 : Nat.log2 1 = 0 := by decide
  have h2 : 1 ≤ Nat.log2 p := (Nat.le_log2 (by omega : p ≠ 0)).2 (by simpa using! hp)
  rw [h1]
  omega

/-- The rational entry width of one is one. -/
theorem clause14Aux_ratEntryWidth_one : ratEntryWidth (1 : ℚ) = 1 := by
  have h1 : Nat.log2 1 = 0 := by decide
  simp only [ratEntryWidth, Rat.num_one, Rat.den_one, Int.natAbs_one, h1]
  decide

/-- The four denominators `19`, `23`, `29`, and `31` used in the rational MPS width
counterexample. -/
def clause14Aux_primes : Fin 4 → ℕ := ![19, 23, 29, 31]

/-- Each of the four denominators selected by `clause14Aux_primes` is at least two. -/
theorem clause14Aux_primes_le (k : Fin 4) : 2 ≤ clause14Aux_primes k := by
  fin_cases k <;> decide

/-- The reciprocal of each selected denominator has rational entry width `Nat.log2 p + 1`. -/
theorem clause14Aux_primes_width (k : Fin 4) :
    ratEntryWidth ((1 : ℚ) / clause14Aux_primes k) = Nat.log2 (clause14Aux_primes k) + 1 :=
  clause14Aux_ratEntryWidth_one_div (clause14Aux_primes_le k)

/-- The reciprocal of each selected denominator has rational entry width at most five. -/
theorem clause14Aux_primes_width_le (k : Fin 4) :
    ratEntryWidth ((1 : ℚ) / clause14Aux_primes k) ≤ 5 := by
  rw [clause14Aux_primes_width]
  have h : Nat.log2 (clause14Aux_primes k) ≤ 4 := by
    fin_cases k <;> decide
  omega

/-- A two-site rational MPS of bond dimension four whose first tensor has reciprocal-prime
columns and whose second tensor has every entry equal to one. -/
def g14rA3 : Fin 2 → Fin 1 → Matrix (Fin 4) (Fin 4) ℚ :=
  fun i _ => Matrix.of fun _ k => if i.val = 0 then 1 / (clause14Aux_primes k : ℚ) else 1

/-- The unique physical configuration for the two-site rational MPS with local physical
dimension one. -/
def g14rX3 : Fin 2 → Fin 1 := fun _ => 0

/-- Every entry of the rational MPS `g14rA3` has rational entry width at most five. -/
theorem g14rA3_width : ∀ i y a b, ratEntryWidth (g14rA3 i y a b) ≤ 5 := by
  intro i y a b
  by_cases h : i.val = 0
  · have he : g14rA3 i y a b = 1 / (clause14Aux_primes b : ℚ) := by
      simp [g14rA3, Matrix.of_apply, h]
    rw [he]
    exact clause14Aux_primes_width_le b
  · have he : g14rA3 i y a b = 1 := by
      simp [g14rA3, Matrix.of_apply, h]
    rw [he, clause14Aux_ratEntryWidth_one]
    decide

/-- Every entry of the second tensor of `g14rA3`, evaluated at its physical configuration, is
one. -/
theorem g14rA3_site1 (i : Fin 2) (hi : i.val = 1) (k j : Fin 4) :
    g14rA3 i (g14rX3 i) k j = 1 := by
  simp [g14rA3, Matrix.of_apply, hi]

/-- The component indexed by `j` of the first MPS evaluation vector is the reciprocal of
`clause14Aux_primes j`. -/
theorem g14rA3_v0 (j : Fin 4) :
    mpsEvalVector g14rA3 g14rX3 (⟨0, by omega⟩ : Fin 2) j = 1 / (clause14Aux_primes j : ℚ) := by
  rw [mpsEvalVector.eq_1]
  simp [g14rA3, Matrix.of_apply]

/-- Every component of the second MPS evaluation vector is the sum of the reciprocals of the
four selected denominators. -/
theorem g14rA3_v1 (j : Fin 4) :
    mpsEvalVector g14rA3 g14rX3 (⟨1, by omega⟩ : Fin 2) j
      = ∑ k : Fin 4, 1 / (clause14Aux_primes k : ℚ) := by
  rw [mpsEvalVector.eq_2]
  simp only [g14rA3_site1, mul_one]
  exact Finset.sum_congr rfl fun k _ => g14rA3_v0 k

/-- The sum of the reciprocals of `19`, `23`, `29`, and `31` equals `63978 / 392863` as a
rational number. -/
theorem g14rA3_sum_eq :
    (∑ k : Fin 4, 1 / (clause14Aux_primes k : ℚ)) = (63978 : ℚ) / 392863 := by
  have e0 : (1 : ℚ) / (clause14Aux_primes 0 : ℚ) = 1 / ((19 : ℕ) : ℚ) := by
    rw [show clause14Aux_primes 0 = 19 from by decide]
  have e1 : (1 : ℚ) / (clause14Aux_primes 1 : ℚ) = 1 / ((23 : ℕ) : ℚ) := by
    rw [show clause14Aux_primes 1 = 23 from by decide]
  have e2 : (1 : ℚ) / (clause14Aux_primes 2 : ℚ) = 1 / ((29 : ℕ) : ℚ) := by
    rw [show clause14Aux_primes 2 = 29 from by decide]
  have e3 : (1 : ℚ) / (clause14Aux_primes 3 : ℚ) = 1 / ((31 : ℕ) : ℚ) := by
    rw [show clause14Aux_primes 3 = 31 from by decide]
  simp only [Fin.sum_univ_four, e0, e1, e2, e3]
  norm_num

/-- The rational entry width of the sum of the four selected reciprocals is exactly nineteen. -/
theorem g14rA3_sum_width : ratEntryWidth (∑ k : Fin 4, 1 / (clause14Aux_primes k : ℚ)) = 19 := by
  have h : ratEntryWidth (((63978 : ℤ) / (392863 : ℤ) : ℚ))
      = max (Nat.log2 63978 + 1) (Nat.log2 392863 + 1) :=
    clause14Aux_ratEntryWidth_div (by norm_num) (by decide)
  have h2 : ((63978 : ℚ) / 392863) = (((63978 : ℤ) / (392863 : ℤ) : ℚ)) := by norm_num
  rw [g14rA3_sum_eq, h2, h]
  decide

/-- The second evaluation vector of the explicit rational MPS violates the proposed width bound
`2 * (5 + Nat.log2 4 + 2)`, whose value is eighteen. -/
theorem g14rA3_width_fail :
    ¬ (ratEntryWidth (mpsEvalVector g14rA3 g14rX3 (⟨1, by omega⟩ : Fin 2) ⟨0, by omega⟩)
        ≤ 2 * (5 + Nat.log2 4 + 2)) := by
  intro h
  rw [g14rA3_v1] at h
  have h19 : 2 * (5 + Nat.log2 4 + 2) = 18 := by decide
  rw [h19, g14rA3_sum_width] at h
  exact absurd h (by decide)

/-- Refutes the universal rational-MPS claim combining the proposed evaluation-vector width
bound with bit-cost and storage bounds. The two-site example `g14rA3` already violates its
width bound. -/
theorem clause3_clause3_counter : ¬ (
    (∀ (n d D B : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℚ) (x : Fin n → Fin d),
      (∀ i y a b, ratEntryWidth (A i y a b) ≤ B) →
      (∀ i j, ratEntryWidth (@mpsEvalVector n d D ℚ _ hD A x i j)
          ≤ n * (B + Nat.log2 D + 2))
        ∧ (@mpsEvalWithCount n d D ℚ _ hn hD A x).2
            * ringOpBitCost (n * (B + Nat.log2 D + 2))
          ≤ mpsEvalOpCount n D
            * ringOpBitCost (n * B + n * (Nat.log2 D + 2) + 2)
        ∧ D * (n * (B + Nat.log2 D + 2) + 1)
          ≤ D * (n * B + n * (Nat.log2 D + 2) + 2))) := by
  intro H
  have h := H 2 1 4 5 (⟨by decide⟩ : NeZero 2) (⟨by decide⟩ : NeZero 4)
    g14rA3 g14rX3 g14rA3_width
  exact g14rA3_width_fail (h.1 ⟨1, by omega⟩ ⟨0, by omega⟩)

/-- The constant-one PEPS tensor on a single site with physical dimension one and bond dimension
two. -/
def g14rT7 : Fin 1 → Fin 1 → Fin 1 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun _ _ _ _ _ _ _ => 1

/-- The unique physical configuration of the single-site PEPS with physical dimension one. -/
def g14rX7 : Fin 1 → Fin 1 → Fin 1 := fun _ _ => 0

/-- The PEPS amplitude of the single-site constant-one example with bond dimension two is four. -/
theorem clause14Aux_pepsAmplitude_eq :
    pepsAmplitude (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7 = 4 := by
  have h : pepsAmplitude (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7
      = ∑ γ : Fin 1 × Fin 1 → Fin 2 × Fin 2, ∏ p : Fin 1 × Fin 1, (1:ℂ) := by
    unfold pepsAmplitude
    simp [g14rT7]
  rw [h]
  have hprod : (∏ p : Fin 1 × Fin 1, (1:ℂ)) = 1 := Finset.prod_eq_one fun _ _ => rfl
  rw [show (∑ γ : Fin 1 × Fin 1 → Fin 2 × Fin 2, (∏ p : Fin 1 × Fin 1, (1:ℂ)))
      = (∑ _γ : Fin 1 × Fin 1 → Fin 2 × Fin 2, (1:ℂ)) from
      Finset.sum_congr rfl fun _ _ => hprod]
  rw [Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card (Fin 1 × Fin 1 → Fin 2 × Fin 2) = 4 := by decide
  rw [hc]
  norm_num

/-- Every column-kernel value of the single-site constant-one PEPS example is one, independently
of its three boundary configurations. -/
theorem clause14Aux_peps_kernel (σ ρ χ : Fin 1 → Fin 2) :
    pepsColKernel (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7
      (⟨0, by omega⟩ : Fin 1) σ ρ χ = 1 := by
  unfold pepsColKernel
  simp only [g14rT7]
  exact Finset.prod_eq_one fun _ _ => rfl

/-- Summing a constant over the two functions from `Fin 1` to `Fin 2` gives twice that constant
in any additive commutative monoid. -/
theorem clause14Aux_sum_const2 {M : Type} [AddCommMonoid M] (c : M) :
    (∑ _ρ : Fin 1 → Fin 2, c) = (2:ℕ) • c := by
  rw [Finset.sum_const, Finset.card_univ]
  have hc : Fintype.card (Fin 1 → Fin 2) = 2 := by decide
  rw [hc]

/-- A finite sum whose only nonzero summand is the value `b` at the index `z` equals `b`. -/
theorem clause14Aux_sum_ite_const {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι) (b : ℂ) :
    (∑ x : ι, (if x = z then b else 0)) = b := by
  rw [Finset.sum_eq_single z]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ z) h

/-- For the explicit one-site tensor `g14rT7` and configuration `g14rX7`, one strip-fold step
produces the constant boundary function with value two. -/
theorem clause14Aux_pepsFold_fst :
    (pepsStripFold (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7 1).1
      = (fun _ : Fin 1 → Fin 2 => (2:ℂ)) := by
  rw [pepsStripFold.eq_2, pepsStripFold.eq_1]
  funext χ
  have hk : ∀ σ ρ : Fin 1 → Fin 2,
      (if h : (0:ℕ) < 1 then
        pepsColKernel (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7 ⟨0, h⟩ σ ρ χ else 0) = 1 := by
    intro σ ρ
    rw [dite_eq_left (by decide)]
    exact clause14Aux_peps_kernel σ ρ χ
  simp only [hk, mul_one]
  simp only [clause14Aux_sum_const2, smul_ite, nsmul_one, nsmul_zero]
  exact clause14Aux_sum_ite_const _ 2

/-- The value returned by the counted strip evaluator for `g14rT7` and `g14rX7` is two. -/
theorem clause14Aux_pepsStrip_val :
    (pepsStripEvalWithCount (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7).1 = (2:ℂ) := by
  rw [pepsStripEvalWithCount.eq_def]
  show (pepsStripFold (a := 1) (b := 1) (d := 1) (D := 2) g14rT7 g14rX7 1).1
    (fun _ : Fin 1 => (0:Fin 2)) = (2:ℂ)
  rw [clause14Aux_pepsFold_fst]

/-- The universal conjunction of correctness and the stated operation-count bound for
`pepsStripEvalWithCount` is false. The explicit one-site example contradicts the asserted
equality with `pepsAmplitude`. -/
theorem clause3_clause7_counter : ¬ (
    (∀ (a b d D : ℕ) (hD : NeZero D)
      (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
      (x : Fin a → Fin b → Fin d),
      (@pepsStripEvalWithCount a b d D hD T x).1 = @pepsAmplitude a b d D hD T x
        ∧ (@pepsStripEvalWithCount a b d D hD T x).2 ≤ pepsStripOpCount a b D)) := by
  intro H
  have h := H 1 1 1 2 (⟨by decide⟩ : NeZero 2) g14rT7 g14rX7
  rw [clause14Aux_pepsStrip_val, clause14Aux_pepsAmplitude_eq] at h
  exact absurd h.1 (by norm_num)

/-- The two-dimensional matrix unit whose only nonzero entry is one at row one and column one. -/
def g14rE11 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i.val = 1 ∧ j.val = 1 then 1 else 0

/-- The two-by-two complex matrix with every entry equal to one. -/
def g14rJ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun _ _ => 1

/-- The two-by-two complex matrix whose column one consists of ones and whose column zero
vanishes. -/
def g14rK : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun _ j => if j.val = 1 then 1 else 0

/-- A two-site, one-dimensional physical tensor family using `g14rE11` at site zero and `g14rJ`
at site one. -/
def g14rA4 : Fin 2 → Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i _ => if i.val = 0 then g14rE11 else g14rJ

/-- The unique physical configuration for the two-site example with physical dimension one. -/
def g14rX4 : Fin 2 → Fin 1 := fun _ => 0

/-- The one-by-one observable whose unique entry is one. -/
def g14rO : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => 1

/-- The matrix unit `g14rE11` is equal to its conjugate transpose. -/
theorem g14rE11_adjoint : g14rE11.conjTranspose = g14rE11 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.conjTranspose_apply, g14rE11, Matrix.of_apply, star_one, star_zero]

/-- The matrix unit `g14rE11` is idempotent. -/
theorem g14rE11_mul_self : g14rE11 * g14rE11 = g14rE11 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rw [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [g14rE11, Matrix.of_apply]

/-- The all-ones matrix `g14rJ` is equal to its conjugate transpose. -/
theorem g14rJ_adjoint : g14rJ.conjTranspose = g14rJ := by
  ext i j
  simp [Matrix.conjTranspose_apply, g14rJ, Matrix.of_apply, star_one]

/-- Multiplying `g14rJ` on the right by `g14rE11` gives `g14rK`. -/
theorem g14rJ_mul_E11 : g14rJ * g14rE11 = g14rK := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rw [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [g14rJ, g14rE11, g14rK, Matrix.of_apply]

/-- Multiplying `g14rK` on the right by `g14rJ` gives `g14rJ`. -/
theorem g14rK_mul_J : g14rK * g14rJ = g14rJ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rw [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [g14rJ, g14rK, Matrix.of_apply]

/-- The product of `g14rJ`, `g14rE11`, and `g14rJ`, in that order, is `g14rJ`. -/
theorem g14rJ_E11_J : g14rJ * g14rE11 * g14rJ = g14rJ := by
  rw [g14rJ_mul_E11, g14rK_mul_J]

/-- The row-zero, column-zero entry of `g14rJ` is one. -/
theorem g14rJ_zero_zero : g14rJ 0 0 = 1 := by simp [g14rJ, Matrix.of_apply]

/-- At a site whose natural-number index is zero, `g14rA4` equals `g14rE11` for every physical
index. -/
theorem g14rA4_at_zero (i : Fin 2) (hi : i.val = 0) (y : Fin 1) :
    g14rA4 i y = g14rE11 := by
  simp [g14rA4, hi]

/-- At a site whose natural-number index is one, `g14rA4` equals `g14rJ` for every physical
index. -/
theorem g14rA4_at_one (i : Fin 2) (hi : i.val = 1) (y : Fin 1) :
    g14rA4 i y = g14rJ := by
  simp [g14rA4, hi]

/-- The row-zero entries of `g14rA4` vanish at site zero. -/
theorem g14rA4_row0 (i : Fin 2) (hi : i.val = 0) (y : Fin 1) (k : Fin 2) :
    g14rA4 i y 0 k = 0 := by
  simp [g14rA4, g14rE11, Matrix.of_apply, hi]

/-- Every open-boundary MPS amplitude of the explicit tensor family `g14rA4` is zero. -/
theorem clause14Aux_amp_zero (x : Fin 2 → Fin 1) :
    mpsAmplitude (n := 2) (d := 1) (D := 2) g14rA4 x = 0 := by
  rw [mpsAmplitude.eq_def]
  apply Finset.sum_eq_zero
  intro α _
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin 2))
  show g14rA4 (⟨0, by omega⟩ : Fin 2) (x ⟨0, by omega⟩) (mpsLeftIdx α ⟨0, by omega⟩)
      (mpsRightIdx α ⟨0, by omega⟩) = 0
  rw [show mpsLeftIdx α (⟨0, by omega⟩ : Fin 2) = 0 by simp [mpsLeftIdx]]
  exact g14rA4_row0 _ (by decide) _ _

/-- The self inner-transfer matrix of `g14rA4` at site zero equals `g14rE11`. -/
theorem g14rA4_t0 : mpsInnerTransfer g14rA4 g14rA4 (⟨0, by omega⟩ : Fin 2) = g14rE11 := by
  rw [mpsInnerTransfer.eq_1]
  simp only [Fin.sum_univ_one]
  simp only [g14rA4_at_zero]
  rw [g14rE11_adjoint]
  exact g14rE11_mul_self

/-- The self inner-transfer matrix of `g14rA4` at site one equals `g14rJ`. -/
theorem g14rA4_t1 : mpsInnerTransfer g14rA4 g14rA4 (⟨1, by omega⟩ : Fin 2) = g14rJ := by
  rw [mpsInnerTransfer.eq_2]
  simp only [Fin.sum_univ_one, g14rA4_at_one, g14rA4_t0, g14rJ_adjoint]
  exact g14rJ_E11_J

/-- The value component of the counted self inner-transfer calculation at site zero equals
`g14rE11`. -/
theorem g14rA4_tc0 : (mpsInnerTransferCount g14rA4 g14rA4 (⟨0, by omega⟩ : Fin 2)).1
    = g14rE11 := by
  rw [mpsInnerTransferCount.eq_1]
  simp only [Fin.sum_univ_one, g14rA4_at_zero]
  rw [g14rE11_adjoint]
  exact g14rE11_mul_self

/-- The value component of the counted self inner-transfer calculation at site one equals
`g14rJ`. -/
theorem g14rA4_tc1 : (mpsInnerTransferCount g14rA4 g14rA4 (⟨1, by omega⟩ : Fin 2)).1
    = g14rJ := by
  rw [mpsInnerTransferCount.eq_2]
  simp only [Fin.sum_univ_one, g14rA4_at_one, g14rA4_tc0, g14rJ_adjoint]
  exact g14rJ_E11_J

/-- The self inner-product evaluator returns one for `g14rA4`, although all of its MPS
amplitudes vanish. -/
theorem clause14Aux_mpsInnerEval_eq :
    mpsInnerEval (n := 2) (d := 1) (D := 2) g14rA4 g14rA4 = 1 := by
  show mpsInnerTransfer g14rA4 g14rA4 (⟨1, by omega⟩ : Fin 2)
    ⟨0, NeZero.pos (2:ℕ)⟩ ⟨0, NeZero.pos (2:ℕ)⟩ = 1
  rw [g14rA4_t1]
  exact g14rJ_zero_zero

/-- The value component of the counted self inner-product evaluator is one for `g14rA4`. -/
theorem clause14Aux_mpsInnerEvalCount_fst :
    (mpsInnerEvalWithCount (n := 2) (d := 1) (D := 2) g14rA4 g14rA4).1 = 1 := by
  show (mpsInnerTransferCount g14rA4 g14rA4 (⟨1, by omega⟩ : Fin 2)).1
    ⟨0, NeZero.pos (2:ℕ)⟩ ⟨0, NeZero.pos (2:ℕ)⟩ = 1
  rw [g14rA4_tc1]
  exact g14rJ_zero_zero

/-- Applying the unique one-dimensional identity observable at site zero leaves `g14rA4`
unchanged. -/
theorem clause14Aux_obs_eq : obsTensors (n := 2) (d := 1) (D := 2) g14rA4 (0 : Fin 2) g14rO
    = g14rA4 := by
  funext i x
  by_cases h : i = (0 : Fin 2)
  · subst h
    simp only [obsTensors, ite_eq_left, Fin.sum_univ_one]
    have h0 : g14rA4 (0 : Fin 2) (0 : Fin 1) = g14rE11 := g14rA4_at_zero _ (by decide) _
    have hx : g14rA4 (0 : Fin 2) x = g14rE11 := g14rA4_at_zero _ (by decide) _
    have hO : g14rO x 0 = 1 := by simp [g14rO, Matrix.of_apply]
    rw [hO, h0, hx]
    exact one_smul ℂ g14rE11
  · simp only [obsTensors, ite_eq_right h]

/-- The sum of squared amplitude magnitudes for `g14rA4` is zero. -/
theorem clause14Aux_amp_pair_sum :
    (∑ x : Fin 2 → Fin 1, conj (mpsAmplitude (n := 2) (d := 1) (D := 2) g14rA4 x)
      * mpsAmplitude (n := 2) (d := 1) (D := 2) g14rA4 x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rw [clause14Aux_amp_zero x]
  simp

/-- The direct amplitude sum for the observable `g14rO` at site zero of `g14rA4` is zero. -/
theorem clause14Aux_obs_sum :
    (∑ x : Fin 2 → Fin 1, conj (mpsAmplitude (n := 2) (d := 1) (D := 2) g14rA4 x)
      * ∑ y : Fin 1, g14rO (x (0 : Fin 2)) y
          * mpsAmplitude (n := 2) (d := 1) (D := 2) g14rA4
              (Function.update x (0 : Fin 2) y)) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rw [clause14Aux_amp_zero x]
  simp

/-- The universal conjunction of correctness and the stated operation-count bound for
`mpsInnerEvalWithCount` is false. The tensor family `g14rA4` contradicts its asserted
equality with the direct amplitude inner product. -/
theorem clause3_clause4_counter : ¬ (
    (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      (@mpsInnerEvalWithCount n d D hn hD A B).1
        = ∑ x, conj (@mpsAmplitude n d D hD A x) * @mpsAmplitude n d D hD B x
        ∧ (@mpsInnerEvalWithCount n d D hn hD A B).2 ≤ mpsInnerOpCount n d D)) := by
  intro H
  have h := H 2 1 2 (⟨by decide⟩ : NeZero 2) (⟨by decide⟩ : NeZero 2) g14rA4 g14rA4
  rw [clause14Aux_mpsInnerEvalCount_fst, clause14Aux_amp_pair_sum] at h
  exact absurd h.1 (by norm_num)

/-- The claimed universal equality between `mpsInnerEval` with observable-modified tensors and
the direct local-observable amplitude sum is false. The tensor family `g14rA4` and
observable `g14rO` give a counterexample. -/
theorem clause3_clause5_counter : ¬ (
    (∀ (n d D : ℕ) (hn : NeZero n) (hD : NeZero D)
      (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
      (O : Matrix (Fin d) (Fin d) ℂ),
      @mpsInnerEval n d D hn hD A (@obsTensors n d D hD A z O)
        = ∑ x, conj (@mpsAmplitude n d D hD A x)
            * ∑ y : Fin d, O (x z) y * @mpsAmplitude n d D hD A (Function.update x z y))) := by
  intro H
  have h := H 2 1 2 (⟨by decide⟩ : NeZero 2) (⟨by decide⟩ : NeZero 2) g14rA4 (0 : Fin 2) g14rO
  rw [clause14Aux_obs_eq, clause14Aux_mpsInnerEval_eq, clause14Aux_obs_sum] at h
  exact absurd h (by norm_num)

/-- The cumulative sum of the natural-number counts strictly before time `t`. -/
def clause14Aux_cum (cnt : ℕ → ℕ) : ℕ → ℕ := fun t => (Finset.range t).sum cnt

/-- The cumulative count at time zero is zero. -/
theorem clause14Aux_cum_zero (cnt : ℕ → ℕ) : clause14Aux_cum cnt 0 = 0 := by
  simp [clause14Aux_cum]

/-- Advancing the cumulative count from `t` to `t + 1` adds the count at `t`. -/
theorem clause14Aux_cum_succ (cnt : ℕ → ℕ) (t : ℕ) :
    clause14Aux_cum cnt (t + 1) = clause14Aux_cum cnt t + cnt t := by
  simp [clause14Aux_cum, Finset.sum_range_succ]

/-- The cumulative sum of natural-number counts is monotone in its time argument. -/
theorem clause14Aux_cum_mono {cnt : ℕ → ℕ} {a b : ℕ} (h : a ≤ b) :
    clause14Aux_cum cnt a ≤ clause14Aux_cum cnt b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · refine (ih (Nat.le_of_lt_succ hlt)).trans ?_
      rw [clause14Aux_cum_succ]
      exact Nat.le_add_right _ _

set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix Complex
open scoped BigOperators Nat ComplexConjugate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Module

/-- A function on `Fin 1` equals the constant function given by its value at the unique index. -/
theorem g10a_finOne_eta {d : ℕ} (f : Fin 1 → Fin d) :
    f = fun _ => f ⟨0, by omega⟩ := by
  funext t
  exact congrArg f (Fin.ext (by have := t.isLt; omega))

/-- Encoding a one-site constant configuration with `finPowEnc` preserves the natural-number
value of its physical index. -/
theorem g10a_finPowEnc_one_val (d : ℕ) (y : Fin d) :
    (finPowEnc d 1 (fun _ => y) : ℕ) = y := by
  show (finFunctionFinEquiv (fun _ : Fin 1 => y) : ℕ) = _
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_one]
  simp

/-- The equivalence from `Fin d` to `Fin (d ^ 1)` obtained by encoding one-site configurations. -/
def g10a_finPowEnc_one (d : ℕ) : Fin d ≃ Fin (d ^ 1) where
  toFun := fun y => finPowEnc d 1 (fun _ => y)
  invFun := fun i => (finPowEnc d 1).symm i ⟨0, by omega⟩
  left_inv := by
    intro y
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro i
    have hval := g10a_finPowEnc_one_val d ((finPowEnc d 1).symm i ⟨0, by omega⟩)
    have hright : (i : ℕ) = ((finPowEnc d 1).symm i ⟨0, by omega⟩ : ℕ) := by
      conv_lhs => rw [← Equiv.apply_symm_apply (finPowEnc d 1) i]
      rw [show (finPowEnc d 1) ((finPowEnc d 1).symm i)
          = finPowEnc d 1 (fun _ => (finPowEnc d 1).symm i ⟨0, by omega⟩) from
          congrArg (finPowEnc d 1) (g10a_finOne_eta ((finPowEnc d 1).symm i))]
      exact g10a_finPowEnc_one_val d _
    exact Fin.ext (hval.trans hright.symm)

/-- Decoding a one-site index, reading its unique value, and encoding the resulting constant
configuration recovers that index. -/
theorem g10a_finPowEnc_one_symm (d : ℕ) (i : Fin (d ^ 1)) :
    finPowEnc d 1 (fun _ => (finPowEnc d 1).symm i ⟨0, by omega⟩) = i :=
  (g10a_finPowEnc_one d).apply_symm_apply i

/-- The two-site configuration obtained by decoding `i` at site zero and `j` at site one. -/
def g10a_twoCfg (d : ℕ) (i j : Fin (d ^ 1)) : Fin 2 → Fin d :=
  fun k => if (k : ℕ) = 0 then (finPowEnc d 1).symm i ⟨0, by omega⟩
    else (finPowEnc d 1).symm j ⟨0, by omega⟩

/-- Joining the one-site configurations decoded from `i` and `j` gives `g10a_twoCfg d i j`. -/
theorem g10a_splitJoin_two (d : ℕ) (i j : Fin (d ^ 1)) :
    splitJoin 2 1 d ((finPowEnc d 1).symm i) ((finPowEnc d 1).symm j)
      = g10a_twoCfg d i j := by
  funext k
  unfold splitJoin g10a_twoCfg
  by_cases hk : (k : ℕ) = 0
  · have hk1 : (k : ℕ) < 1 := by omega
    simp [hk]
  · have hk1 : ¬((k : ℕ) < 1) := by omega
    have hk2 : (k : ℕ) - 1 = 0 := by have := k.isLt; omega
    simp [hk, hk1, hk2]

/-- Encoding the two entries of a two-site configuration separately and combining them with
`g10a_twoCfg` recovers the configuration. -/
theorem g10a_twoCfg_self (d : ℕ) (x : Fin 2 → Fin d) :
    g10a_twoCfg d (finPowEnc d 1 (fun _ => x 0)) (finPowEnc d 1 (fun _ => x 1)) = x := by
  funext k
  unfold g10a_twoCfg
  by_cases hk : (k : ℕ) = 0
  · rw [ite_eq_left hk, Equiv.symm_apply_apply]
    exact congrArg x (Fin.ext hk).symm
  · have hk1 : k = 1 := Fin.ext (by have := k.isLt; omega)
    rw [ite_eq_right hk, Equiv.symm_apply_apply]
    rw [hk1]

/-- At site zero, `g10a_twoCfg d i j` equals the unique entry decoded from `i`. -/
theorem g10a_twoCfg_zero (d : ℕ) (i j : Fin (d ^ 1)) :
    g10a_twoCfg d i j 0 = (finPowEnc d 1).symm i ⟨0, by omega⟩ := by
  unfold g10a_twoCfg
  simp

/-- At site one, `g10a_twoCfg d i j` equals the unique entry decoded from `j`. -/
theorem g10a_twoCfg_one (d : ℕ) (i j : Fin (d ^ 1)) :
    g10a_twoCfg d i j 1 = (finPowEnc d 1).symm j ⟨0, by omega⟩ := by
  unfold g10a_twoCfg
  simp

/-- An entry of the central cut matrix of a two-site state is its amplitude at the configuration
assembled from the two matrix indices. -/
theorem g10a_cutMatrix_two {d : ℕ} (ψ : (Fin 2 → Fin d) → ℂ) (i j : Fin (d ^ 1)) :
    cutMatrix 2 d ψ 1 i j = ψ (g10a_twoCfg d i j) := by
  rw [g10a_cutMatrix_apply, g10a_splitJoin_two]

/-- A two-site amplitude is the corresponding entry of its central cut matrix, with each
physical value encoded as a one-site index. -/
theorem g10a_psi_eq_cutMatrix_two {d : ℕ} (ψ : (Fin 2 → Fin d) → ℂ) (x : Fin 2 → Fin d) :
    ψ x = cutMatrix 2 d ψ 1
      (finPowEnc d 1 (fun _ => x 0)) (finPowEnc d 1 (fun _ => x 1)) := by
  rw [g10a_cutMatrix_two, g10a_twoCfg_self]

/-- For positive bond dimension, the left bond index at site zero of a two-site open-boundary
MPS is zero. -/
theorem g10a_mpsLeftIdx_two_zero {D : ℕ} [NeZero D] (α : Fin (2 - 1) → Fin D) :
    mpsLeftIdx α (0 : Fin 2) = 0 := by
  unfold mpsLeftIdx
  simp

/-- For positive bond dimension, the right bond index at site zero of a two-site MPS is its
unique internal bond value. -/
theorem g10a_mpsRightIdx_two_zero {D : ℕ} [NeZero D] (α : Fin (2 - 1) → Fin D) :
    mpsRightIdx α (0 : Fin 2) = α ⟨0, by omega⟩ := by
  unfold mpsRightIdx
  simp

/-- For positive bond dimension, the left bond index at site one of a two-site MPS is its unique
internal bond value. -/
theorem g10a_mpsLeftIdx_two_one {D : ℕ} [NeZero D] (α : Fin (2 - 1) → Fin D) :
    mpsLeftIdx α (1 : Fin 2) = α ⟨0, by omega⟩ := by
  unfold mpsLeftIdx
  simp

/-- For positive bond dimension, the right bond index at site one of a two-site open-boundary
MPS is zero. -/
theorem g10a_mpsRightIdx_two_one {D : ℕ} [NeZero D] (α : Fin (2 - 1) → Fin D) :
    mpsRightIdx α (1 : Fin 2) = 0 := by
  unfold mpsRightIdx
  simp

/-- The equivalence between a bond assignment on `Fin 1` and its unique value in `Fin D`. -/
def g10a_finOneFun (D : ℕ) : (Fin 1 → Fin D) ≃ Fin D where
  toFun := fun f => f ⟨0, by omega⟩
  invFun := fun β _ => β
  left_inv := by
    intro f
    funext i
    exact congrArg f (Fin.ext (by have := i.isLt; omega))
  right_inv := fun _ => rfl

/-- For positive bond dimension, the amplitude of a two-site MPS is the sum over its internal
bond of the product of the first tensor's boundary row and the second tensor's boundary
column. -/
theorem g10a_mpsAmplitude_two {d D : ℕ} [NeZero D]
    (A : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin 2 → Fin d) :
    mpsAmplitude A x = ∑ β : Fin D, A 0 (x 0) 0 β * A 1 (x 1) β 0 := by
  have hconst : ∀ β : Fin D,
      (∏ i : Fin 2, A i (x i) (mpsLeftIdx (fun _ => β) i) (mpsRightIdx (fun _ => β) i))
        = A 0 (x 0) 0 β * A 1 (x 1) β 0 := by
    intro β
    rw [Fin.prod_univ_two (fun i : Fin 2 =>
      A i (x i) (mpsLeftIdx (fun _ => β) i) (mpsRightIdx (fun _ => β) i))]
    rw [g10a_mpsLeftIdx_two_zero, g10a_mpsRightIdx_two_zero,
      g10a_mpsLeftIdx_two_one, g10a_mpsRightIdx_two_one]
  have hα : ∀ α : Fin (2 - 1) → Fin D, α = fun _ => α ⟨0, by omega⟩ := by
    intro α
    funext t
    exact congrArg α (Fin.ext (by have := t.isLt; omega))
  unfold mpsAmplitude
  have h1 : (∑ α : Fin (2 - 1) → Fin D,
        ∏ i : Fin 2, A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
      = ∑ β : Fin D, ∏ i : Fin 2,
          A i (x i) (mpsLeftIdx (fun _ => β) i) (mpsRightIdx (fun _ => β) i) := by
    rw [← Equiv.sum_comp (g10a_finOneFun D)]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hα α]
    rfl
  rw [h1]
  exact Finset.sum_congr rfl (fun β _ => hconst β)

open Complex

/-- When `D` is at most `m`, summing over indices in `Fin m` smaller than `D` equals summing
over their canonical embeddings from `Fin D`. -/
theorem g10a_sum_univ_filter_lt {m D : ℕ} (hD : D ≤ m) (f : Fin m → ℂ) :
    (∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun (i : Fin m) => (i : ℕ) < D), f i)
      = ∑ β : Fin D, f (⟨(β : ℕ), lt_of_lt_of_le β.isLt hD⟩ : Fin m) := by
  refine Finset.sum_bij
    (fun (i : Fin m) (hi : i ∈ (Finset.univ : Finset (Fin m)).filter
        (fun (i : Fin m) => (i : ℕ) < D)) =>
      (⟨(i : ℕ), (Finset.mem_filter.mp hi).2⟩ : Fin D)) ?_ ?_ ?_ ?_
  · intro i _hi
    exact Finset.mem_univ _
  · intro i₁ _ i₂ _ heq
    exact Fin.ext (show (i₁ : ℕ) = (i₂ : ℕ) from congrArg (fun z : Fin D => (z : ℕ)) heq)
  · intro β _hb
    exact ⟨⟨(β : ℕ), lt_of_lt_of_le β.isLt hD⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by exact_mod_cast β.isLt⟩, Fin.ext rfl⟩
  · intro i _hi
    rfl

/-- When `D` does not exceed the column dimension, an entry of the truncated two-site cut matrix
is the sum of its first `D` singular components. -/
theorem g10a_svdTrunc_two {d : ℕ} (ψ : (Fin 2 → Fin d) → ℂ) (D : ℕ)
    (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1))))
    (p : Fin (d ^ 1)) (q : Fin (d ^ (2 - 1))) :
    g10g_svdTrunc (cutMatrix 2 d ψ 1) D p q
      = ∑ β : Fin D,
          (matrixSingularValues (cutMatrix 2 d ψ 1) (β : ℕ) : ℂ) *
            (leftSingularVector (cutMatrix 2 d ψ 1) ⟨(β : ℕ), lt_of_lt_of_le β.isLt hD⟩ p *
              star (rightSingularBasis (cutMatrix 2 d ψ 1)
                ⟨(β : ℕ), lt_of_lt_of_le β.isLt hD⟩ q)) := by
  have h := congrFun (congrFun (g10g_svdTrunc_eq_sum_filter (cutMatrix 2 d ψ 1) D) p) q
  rw [Matrix.sum_apply] at h
  have hterm : ∀ i : Fin (Fintype.card (Fin (d ^ (2 - 1)))),
      ((matrixSingularValues (cutMatrix 2 d ψ 1) i : ℂ) •
        vecMulVec (leftSingularVector (cutMatrix 2 d ψ 1) i)
          (star (rightSingularBasis (cutMatrix 2 d ψ 1) i))) p q
        = (matrixSingularValues (cutMatrix 2 d ψ 1) i : ℂ) *
          (leftSingularVector (cutMatrix 2 d ψ 1) i p *
            star (rightSingularBasis (cutMatrix 2 d ψ 1) i q)) :=
    fun i => g10g_rankOne_apply (cutMatrix 2 d ψ 1) i p q
  simp only [hterm] at h
  rw [h, g10a_sum_univ_filter_lt hD]

/-- These two-site MPS tensors use the first `D` singular components of the central cut matrix,
assuming `D` is at most the physical dimension. The first tensor stores left singular
vectors in boundary row zero, and the second stores singular-value-weighted conjugate right
singular vectors in boundary column zero. -/
noncomputable def g10a_twoTensor (d D : ℕ) (ψ : (Fin 2 → Fin d) → ℂ)
    (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))) :
    Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i y => Matrix.of fun a b =>
    if (i : ℕ) = 0 then
      if (a : ℕ) = 0 then
        leftSingularVector (cutMatrix 2 d ψ 1) ⟨(b : ℕ), lt_of_lt_of_le b.isLt hD⟩
          (finPowEnc d 1 (fun _ => y))
      else 0
    else
      if (b : ℕ) = 0 then
        (matrixSingularValues (cutMatrix 2 d ψ 1) (a : ℕ) : ℂ) *
          star (rightSingularBasis (cutMatrix 2 d ψ 1)
            ⟨(a : ℕ), lt_of_lt_of_le a.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
      else 0

/-- The first tensor of `g10a_twoTensor` contains left singular-vector entries in row zero and
vanishes in all other rows. -/
theorem g10a_twoTensor_zero {d D : ℕ} (ψ : (Fin 2 → Fin d) → ℂ)
    (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))) (y : Fin d) (a b : Fin D) :
    g10a_twoTensor d D ψ hD 0 y a b
      = if (a : ℕ) = 0 then
          leftSingularVector (cutMatrix 2 d ψ 1) ⟨(b : ℕ), lt_of_lt_of_le b.isLt hD⟩
            (finPowEnc d 1 (fun _ => y))
        else 0 := by
  unfold g10a_twoTensor
  simp only [Matrix.of_apply]
  rw [ite_eq_left (show ((0 : Fin 2) : ℕ) = 0 from rfl)]

/-- The second tensor of `g10a_twoTensor` contains singular-value-weighted conjugate right
singular-vector entries in column zero and vanishes in all other columns. -/
theorem g10a_twoTensor_one {d D : ℕ} (ψ : (Fin 2 → Fin d) → ℂ)
    (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))) (y : Fin d) (a b : Fin D) :
    g10a_twoTensor d D ψ hD 1 y a b
      = if (b : ℕ) = 0 then
          (matrixSingularValues (cutMatrix 2 d ψ 1) (a : ℕ) : ℂ) *
            star (rightSingularBasis (cutMatrix 2 d ψ 1)
              ⟨(a : ℕ), lt_of_lt_of_le a.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
        else 0 := by
  unfold g10a_twoTensor
  simp only [Matrix.of_apply]
  rw [ite_eq_right (show ¬((1 : Fin 2) : ℕ) = 0 from by decide)]

/-- For positive bond dimension, the amplitude of `g10a_twoTensor` equals the corresponding
entry of the truncated central cut matrix. -/
theorem g10a_twoTensor_amplitude {d D : ℕ} [NeZero D] (ψ : (Fin 2 → Fin d) → ℂ)
    (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))) (x : Fin 2 → Fin d) :
    mpsAmplitude (g10a_twoTensor d D ψ hD) x
      = g10g_svdTrunc (cutMatrix 2 d ψ 1) D
          (finPowEnc d 1 (fun _ => x 0)) (finPowEnc d 1 (fun _ => x 1)) := by
  rw [g10a_mpsAmplitude_two]
  have hz : (((0 : Fin D) : ℕ) = 0) := by simp
  have hterm : ∀ β : Fin D,
      g10a_twoTensor d D ψ hD 0 (x 0) 0 β * g10a_twoTensor d D ψ hD 1 (x 1) β 0
        = (matrixSingularValues (cutMatrix 2 d ψ 1) (β : ℕ) : ℂ) *
            (leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(β : ℕ), lt_of_lt_of_le β.isLt hD⟩ (finPowEnc d 1 (fun _ => x 0)) *
              star (rightSingularBasis (cutMatrix 2 d ψ 1)
                ⟨(β : ℕ), lt_of_lt_of_le β.isLt hD⟩ (finPowEnc d 1 (fun _ => x 1)))) := by
    intro β
    rw [g10a_twoTensor_zero, g10a_twoTensor_one, ite_eq_left hz, ite_eq_left hz]
    ring
  rw [Finset.sum_congr rfl (fun β _ => hterm β)]
  exact (g10a_svdTrunc_two ψ D hD _ _).symm

/-- Negating a matrix preserves its spectral Frobenius norm. -/
theorem g10a_spectralFrobenius_neg {O I : Type} [Fintype O] [Fintype I] (B : Matrix O I ℂ) :
    spectralFrobenius (-B) = spectralFrobenius B := by
  have h : (∑ i, ∑ j, Complex.normSq ((-B) i j)) = ∑ i, ∑ j, Complex.normSq (B i j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.neg_apply]
    exact Complex.normSq_neg _
  unfold spectralFrobenius
  rw [h]

/-- Swapping the order of two matrices in a difference preserves its spectral Frobenius norm. -/
theorem g10a_spectralFrobenius_sub_swap {O I : Type} [Fintype O] [Fintype I]
    (B C : Matrix O I ℂ) :
    spectralFrobenius (B - C) = spectralFrobenius (C - B) := by
  have h : B - C = -(C - B) := (neg_sub C B).symm
  rw [h, g10a_spectralFrobenius_neg]

/-- For positive `D` at most the physical dimension, the total squared amplitude error of the
two-site SVD tensors equals the discarded squared Schmidt tail at the central cut. -/
theorem g10a_twoTensor_error {d D : ℕ} [NeZero D] (ψ : (Fin 2 → Fin d) → ℂ)
    (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))) :
    ∑ x, Complex.normSq (mpsAmplitude (g10a_twoTensor d D ψ hD) x - ψ x)
      = schmidtTailSq 2 d ψ 1 D := by
  have hamp : ∀ x : Fin 2 → Fin d,
      mpsAmplitude (g10a_twoTensor d D ψ hD) x
        = g10g_svdTrunc (cutMatrix 2 d ψ 1) D
            (finPowEnc d 1 (fun _ => x 0)) (finPowEnc d 1 (fun _ => x 1)) :=
    fun x => g10a_twoTensor_amplitude ψ hD x
  have wentry : ∀ (i j : Fin (d ^ 1)),
      cutMatrix 2 d (fun x => mpsAmplitude (g10a_twoTensor d D ψ hD) x - ψ x) 1 i j
        = g10g_svdTrunc (cutMatrix 2 d ψ 1) D i j - cutMatrix 2 d ψ 1 i j := by
    intro i j
    rw [g10a_cutMatrix_two]
    show mpsAmplitude (g10a_twoTensor d D ψ hD) (g10a_twoCfg d i j)
        - ψ (g10a_twoCfg d i j) = _
    rw [hamp, g10a_psi_eq_cutMatrix_two ψ (g10a_twoCfg d i j), g10a_twoCfg_zero,
      g10a_twoCfg_one, g10a_finPowEnc_one_symm, g10a_finPowEnc_one_symm]
  have hmat : cutMatrix 2 d (fun x => mpsAmplitude (g10a_twoTensor d D ψ hD) x - ψ x) 1
      = g10g_svdTrunc (cutMatrix 2 d ψ 1) D - cutMatrix 2 d ψ 1 := by
    ext i j
    rw [wentry, Matrix.sub_apply]
  rw [← g10a_parseval (fun x => mpsAmplitude (g10a_twoTensor d D ψ hD) x - ψ x)
    (by omega : (1 : ℕ) ≤ 2), hmat, g10a_spectralFrobenius_sub_swap]
  exact (g10g_schmidtTailSq_eq_frob_sub_trunc (n := 2) (d := d) ψ 1 D).symm

/-- The two-site SVD tensors are left canonical when `D` is positive and does not exceed the
rank of the central cut matrix. -/
theorem g10a_twoTensor_leftCanonical {d D : ℕ} [NeZero D] (ψ : (Fin 2 → Fin d) → ℂ)
    {hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))}
    (hr : D ≤ Matrix.rank (cutMatrix 2 d ψ 1)) :
    LeftCanonical (g10a_twoTensor d D ψ hD) := by
  have hfin : Matrix.rank (cutMatrix 2 d ψ 1)
      = Module.finrank ℂ (LinearMap.range (cutMatrix 2 d ψ 1).toEuclideanLin) :=
    rank_eq_finrank_range_toEuclideanLin (cutMatrix 2 d ψ 1)
  intro i hi
  have hi0 : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst hi0
  ext b₁ b₂
  rw [Matrix.sum_apply]
  have hterm : ∀ y : Fin d,
      (((g10a_twoTensor d D ψ hD) 0 y)ᴴ * (g10a_twoTensor d D ψ hD) 0 y) b₁ b₂
        = star (leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
            * leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₂ : ℕ), lt_of_lt_of_le b₂.isLt hD⟩ (finPowEnc d 1 (fun _ => y)) := by
    intro y
    rw [Matrix.mul_apply]
    have hz : (((0 : Fin D) : ℕ) = 0) := by simp
    rw [Finset.sum_eq_single (0 : Fin D)]
    · rw [Matrix.conjTranspose_apply, g10a_twoTensor_zero, g10a_twoTensor_zero,
        ite_eq_left hz, ite_eq_left hz]
    · intro a _ha hne
      rw [Matrix.conjTranspose_apply, g10a_twoTensor_zero, g10a_twoTensor_zero]
      by_cases ha : (a : ℕ) = 0
      · exact absurd (Fin.ext ha) hne
      · simp only [ite_eq_right ha]
        ring
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  simp only [hterm]
  have hinner : (∑ y : Fin d,
        star (leftSingularVector (cutMatrix 2 d ψ 1)
            ⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
          * leftSingularVector (cutMatrix 2 d ψ 1)
            ⟨(b₂ : ℕ), lt_of_lt_of_le b₂.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
      = if b₁ = b₂ then (1 : ℂ) else 0 := by
    have hre : (∑ y : Fin d,
          star (leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
            * leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₂ : ℕ), lt_of_lt_of_le b₂.isLt hD⟩ (finPowEnc d 1 (fun _ => y)))
        = ∑ q : Fin (d ^ 1),
          star (leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩ q)
            * leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₂ : ℕ), lt_of_lt_of_le b₂.isLt hD⟩ q :=
      Equiv.sum_comp (g10a_finPowEnc_one d)
        (fun q : Fin (d ^ 1) =>
          star (leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩ q)
            * leftSingularVector (cutMatrix 2 d ψ 1)
              ⟨(b₂ : ℕ), lt_of_lt_of_le b₂.isLt hD⟩ q)
    rw [hre, ← g10g_inner_eq_sum]
    by_cases h : b₁ = b₂
    · subst h
      have hnorm : ‖leftSingularVector (cutMatrix 2 d ψ 1)
          ⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩‖ = 1 :=
        norm_leftSingularVector (cutMatrix 2 d ψ 1) _
          (lt_of_lt_of_le (by exact_mod_cast b₁.isLt) (hr.trans hfin.le))
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    · have hne : (⟨(b₁ : ℕ), lt_of_lt_of_le b₁.isLt hD⟩ :
          Fin (Fintype.card (Fin (d ^ (2 - 1))))) ≠
          ⟨(b₂ : ℕ), lt_of_lt_of_le b₂.isLt hD⟩ := by
        intro hcongr
        apply h
        apply Fin.ext
        exact congrArg (fun (z : Fin (Fintype.card (Fin (d ^ (2 - 1))))) => (z : ℕ)) hcongr
      rw [inner_leftSingularVector_of_ne (cutMatrix 2 d ψ 1) hne]
      simp [h]
  rw [hinner, Matrix.one_apply]

/-- Truncating the central two-site cut matrix at its rank recovers the entire matrix. -/
theorem g10a_svdTrunc_self {d r : ℕ} (ψ : (Fin 2 → Fin d) → ℂ)
    (hr : r = Matrix.rank (cutMatrix 2 d ψ 1)) :
    g10g_svdTrunc (cutMatrix 2 d ψ 1) r = cutMatrix 2 d ψ 1 := by
  have hfin : Matrix.rank (cutMatrix 2 d ψ 1)
      = Module.finrank ℂ (LinearMap.range (cutMatrix 2 d ψ 1).toEuclideanLin) :=
    rank_eq_finrank_range_toEuclideanLin (cutMatrix 2 d ψ 1)
  have hall : ∀ i : Fin (Fintype.card (Fin (d ^ (2 - 1)))),
      (if (i : ℕ) < r then
          (matrixSingularValues (cutMatrix 2 d ψ 1) i : ℂ) •
            vecMulVec (leftSingularVector (cutMatrix 2 d ψ 1) i)
              (star (rightSingularBasis (cutMatrix 2 d ψ 1) i))
        else 0)
        = (matrixSingularValues (cutMatrix 2 d ψ 1) i : ℂ) •
          vecMulVec (leftSingularVector (cutMatrix 2 d ψ 1) i)
            (star (rightSingularBasis (cutMatrix 2 d ψ 1) i)) := by
    intro i
    by_cases hi : (i : ℕ) < r
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      have hσ : matrixSingularValues (cutMatrix 2 d ψ 1) i = 0 := by
        by_contra hne
        have hpos : 0 < matrixSingularValues (cutMatrix 2 d ψ 1) i :=
          lt_of_le_of_ne (matrixSingularValues_nonneg _ _) (Ne.symm hne)
        have hlt : (i : ℕ) < Module.finrank ℂ
            (LinearMap.range (cutMatrix 2 d ψ 1).toEuclideanLin) :=
          (matrixSingularValues_pos_iff_lt_finrank_range _).1 hpos
        rw [← hfin, ← hr] at hlt
        exact hi hlt
      rw [hσ]
      simp
  rw [g10g_svdTrunc, Finset.sum_congr rfl (fun i _ => hall i),
    ← matrix_eq_sum_singularVectors (cutMatrix 2 d ψ 1)]

/-- If the central two-site cut matrix has positive rank `r`, the state has an exact
left-canonical MPS representation of bond dimension `r`. -/
theorem g10a_two_exact_core {d r : ℕ} (ψ : (Fin 2 → Fin d) → ℂ)
    (hr : r = Matrix.rank (cutMatrix 2 d ψ 1)) (hr1 : 1 ≤ r) :
    ∃ (hD : NeZero r) (A : Fin 2 → Fin d → Matrix (Fin r) (Fin r) ℂ),
      @IsMpsRepresentation 2 d r hD A ψ ∧ LeftCanonical A := by
  have hcard : r ≤ Fintype.card (Fin (d ^ (2 - 1))) := by
    rw [hr, Fintype.card_fin]
    exact Matrix.rank_le_width (cutMatrix 2 d ψ 1)
  have : NeZero r := ⟨by omega⟩
  refine ⟨inferInstance, g10a_twoTensor d r ψ hcard, ?_, ?_⟩
  · intro x
    rw [g10a_twoTensor_amplitude ψ hcard x, g10a_svdTrunc_self ψ hr,
      g10a_psi_eq_cutMatrix_two ψ x]
  · exact g10a_twoTensor_leftCanonical ψ (by rw [hr])

/-- When the physical dimension is zero, any real-valued sum over two-site configurations is
zero. -/
theorem g10a_sum_empty_cfg {d : ℕ} (hd : d = 0) (F : (Fin 2 → Fin d) → ℝ) :
    (∑ x : Fin 2 → Fin d, F x) = 0 := by
  subst hd
  have hcard : Fintype.card (Fin 2 → Fin 0) = 0 := by simp
  have he : (Finset.univ : Finset (Fin 2 → Fin 0)) = ∅ :=
    Finset.card_eq_zero.mp (by rw [Finset.card_univ]; exact hcard)
  rw [he, Finset.sum_empty]

/-- Every normalized two-site state has an exact left-canonical MPS representation whose bond
dimension is the maximum of one and its cut ranks. -/
theorem g10a_clause2_two (d : ℕ) (ψ : (Fin 2 → Fin d) → ℂ)
    (hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∃ (D : ℕ) (hD : NeZero D) (A : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation 2 d D hD A ψ ∧ LeftCanonical A ∧
        D = max 1 ((Finset.range 2).sup fun c => cutRank 2 d ψ c) := by
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [g10a_sum_empty_cfg hd0 (fun x => Complex.normSq (ψ x))] at hnorm
    exact absurd hnorm (by norm_num)
  have hx : ∃ x : Fin 2 → Fin d, ψ x ≠ 0 :=
    exists_ne_zero_of_normSq_eq_one ψ hnorm
  have hne : cutMatrix 2 d ψ 1 ≠ 0 := by
    intro hM
    obtain ⟨x, hx⟩ := hx
    have hzero : cutMatrix 2 d ψ 1
        (finPowEnc d 1 (fun _ => x 0)) (finPowEnc d 1 (fun _ => x 1)) = 0 := by
      rw [hM]
      rfl
    rw [← g10a_psi_eq_cutMatrix_two ψ x] at hzero
    exact hx hzero
  have hrank1 : 1 ≤ Matrix.rank (cutMatrix 2 d ψ 1) := by
    by_contra hlt
    have heq : Matrix.rank (cutMatrix 2 d ψ 1) = 0 := by omega
    exact hne ((matrixRank_eq_zero_iff (cutMatrix 2 d ψ 1)).mp heq)
  obtain ⟨hD, A, hrep, hcan⟩ := g10a_two_exact_core ψ rfl hrank1
  refine ⟨Matrix.rank (cutMatrix 2 d ψ 1), hD, A, hrep, hcan, ?_⟩
  have hsup : (Finset.range 2).sup (fun c => cutRank 2 d ψ c)
      = max (cutRank 2 d ψ 0) (cutRank 2 d ψ 1) := by
    rw [Finset.range_add_one, Finset.range_add_one, Finset.range_zero,
      Finset.sup_insert, Finset.sup_insert, Finset.sup_empty]
    show max (cutRank 2 d ψ 1) (max (cutRank 2 d ψ 0) 0) = _
    rw [Nat.max_zero]
    exact max_comm _ _
  rw [hsup]
  have hle : cutRank 2 d ψ 0 ≤ 1 := cutRank_le_one_left ψ
  have h1 : cutRank 2 d ψ 1 = Matrix.rank (cutMatrix 2 d ψ 1) :=
    cutRank_eq_matrixRank ψ 1
  omega

/-- For every positive bond dimension, a two-site state has an MPS approximation with total
squared amplitude error at most twice the sum of its discarded squared Schmidt tails. -/
theorem g10a_clause3_two (d : ℕ) (ψ : (Fin 2 → Fin d) → ℂ) :
    ∀ D : ℕ, 0 < D →
      ∃ (hD : NeZero D) (A : Fin 2 → Fin d → Matrix (Fin D) (Fin D) ℂ),
        ∑ x, Complex.normSq (@mpsAmplitude 2 d D hD A x - ψ x)
          ≤ 2 * ∑ c ∈ Finset.range 2, schmidtTailSq 2 d ψ c D := by
  intro D hDpos
  have hD' : NeZero D := ⟨Nat.pos_iff_ne_zero.mp hDpos⟩
  by_cases hd : d = 0
  · refine ⟨hD', fun _ _ => 0, ?_⟩
    rw [g10a_sum_empty_cfg hd (fun x =>
      Complex.normSq (@mpsAmplitude 2 d D hD' (fun _ _ => 0) x - ψ x))]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun c _ => schmidtTailSq_nonneg ψ c D))
  · have hdpos : 0 < d := by omega
    by_cases hrank : 1 ≤ Matrix.rank (cutMatrix 2 d ψ 1)
    · by_cases hle : D ≤ Matrix.rank (cutMatrix 2 d ψ 1)
      · have hcard : D ≤ Fintype.card (Fin (d ^ (2 - 1))) := by
          rw [Fintype.card_fin]
          exact le_trans hle (Matrix.rank_le_width (cutMatrix 2 d ψ 1))
        refine ⟨hD', g10a_twoTensor d D ψ hcard, ?_⟩
        rw [g10a_twoTensor_error ψ hcard]
        have h0 : schmidtTailSq 2 d ψ 0 D = 0 :=
          schmidtTailSq_eq_zero_of_cutRank_le ψ
            (le_trans (cutRank_le_one_left ψ) (by omega))
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
          zero_add, h0, zero_add]
        exact le_mul_of_one_le_left (schmidtTailSq_nonneg ψ 1 D) (by norm_num)
      · have hlt : Matrix.rank (cutMatrix 2 d ψ 1) < D := by omega
        obtain ⟨h₀, A₀, hrep, _hcan⟩ := g10a_two_exact_core ψ rfl hrank
        refine clause2_clause3_of_exact_le 2 d ψ hDpos
          ⟨Matrix.rank (cutMatrix 2 d ψ 1), h₀, A₀, hrep, by omega⟩ ?_
        intro c hc
        have hc2 : c = 0 ∨ c = 1 := by
          simp only [Finset.mem_range] at hc
          omega
        rcases hc2 with rfl | rfl
        · exact le_trans (cutRank_le_one_left ψ) (by omega)
        · rw [cutRank_eq_matrixRank]
          omega
    · have hrank0 : Matrix.rank (cutMatrix 2 d ψ 1) = 0 := by omega
      have hMz : cutMatrix 2 d ψ 1 = 0 :=
        (matrixRank_eq_zero_iff (cutMatrix 2 d ψ 1)).mp hrank0
      have hzero : ∀ x : Fin 2 → Fin d, ψ x = 0 := by
        intro x
        rw [g10a_psi_eq_cutMatrix_two ψ x, hMz]
        simp
      refine ⟨hD', fun _ _ => 0, ?_⟩
      have hamp : ∀ x : Fin 2 → Fin d,
          @mpsAmplitude 2 d D hD' (fun _ _ => 0) x = 0 := by
        intro x
        rw [g10a_mpsAmplitude_two]
        exact Finset.sum_eq_zero (fun β _ => by
          simp only [Matrix.zero_apply]
          ring)
      have hsum : (∑ x, Complex.normSq
          (@mpsAmplitude 2 d D hD' (fun _ _ => 0) x - ψ x)) = 0 := by
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [hamp x, hzero x]
        simp
      rw [hsum]
      have htail : ∀ c ∈ Finset.range 2, schmidtTailSq 2 d ψ c D = 0 := by
        intro c hc
        have hc2 : c = 0 ∨ c = 1 := by
          simp only [Finset.mem_range] at hc
          omega
        rcases hc2 with rfl | rfl
        · exact schmidtTailSq_eq_zero_of_cutRank_le ψ
            (le_trans (cutRank_le_one_left ψ) (by omega))
        · exact schmidtTailSq_eq_zero_of_cutRank_le ψ (by
            rw [cutRank_eq_matrixRank, hrank0]
            exact Nat.zero_le _)
      rw [Finset.sum_eq_zero htail, mul_zero]

open Qatlib
open Qatlib.Concepts.TensorNetwork.GaugeInvariance
open scoped ComplexConjugate BigOperators Nat

/-- The cumulative sum of natural-number counts over the times strictly smaller than the
argument. -/
def clause3Aux_cum (cnt : ℕ → ℕ) : ℕ → ℕ := fun t => (Finset.range t).sum cnt

/-- The cumulative count used in the sampling construction is zero at time zero. -/
theorem clause3Aux_cum_zero (cnt : ℕ → ℕ) : clause3Aux_cum cnt 0 = 0 := by
  simp [clause3Aux_cum]

/-- The next cumulative count is the current cumulative count plus the count at the current
time. -/
theorem clause3Aux_cum_succ (cnt : ℕ → ℕ) (t : ℕ) :
    clause3Aux_cum cnt (t + 1) = clause3Aux_cum cnt t + cnt t := by
  simp [clause3Aux_cum, Finset.sum_range_succ]

/-- The cumulative count used in the sampling construction is monotone. -/
theorem clause3Aux_cum_mono {cnt : ℕ → ℕ} {a b : ℕ} (h : a ≤ b) :
    clause3Aux_cum cnt a ≤ clause3Aux_cum cnt b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · refine (ih (Nat.le_of_lt_succ hlt)).trans ?_
      rw [clause3Aux_cum_succ]
      exact Nat.le_add_right _ _

/-- Extending a count function on `Fin N` by zero and taking its cumulative sum through `N`
gives the sum over `Fin N`. -/
theorem clause3Aux_cum_cast (N : ℕ) (cnt : Fin N → ℕ) :
    clause3Aux_cum (fun t => if h : t < N then cnt ⟨t, h⟩ else 0) N = ∑ j : Fin N, cnt j := by
  rw [clause3Aux_cum]
  symm
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.mpr j.isLt
  · intro j₁ _ j₂ _ h
    exact Fin.eq_of_val_eq h
  · intro t ht
    have ht' : t < N := Finset.mem_range.mp ht
    exact ⟨⟨t, ht'⟩, Finset.mem_univ _, by simp⟩
  · intro j _
    simp

/-- An equivalence between length-`k` Boolean strings and the finite index type of size `2 ^ k`. -/
def clause3Aux_bitsEnc (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

/-- An equivalence between indices in `Fin T` lying in the interval from `a` inclusive to `b`
exclusive and `Fin (b - a)`, provided `b` is at most `T`. -/
def clause3Aux_IcoFinEquiv' (T a b : ℕ) (hb : b ≤ T) : {u : Fin T // a ≤ u ∧ u < b} ≃ Fin (b - a) where
  toFun u := ⟨u.val - a, by have := u.property; omega⟩
  invFun v := by
    have hv : v.val < b - a := v.isLt
    refine ⟨⟨a + v.val, ?_⟩, ?_, ?_⟩
    · have := hb
      omega
    · show a ≤ a + v.val
      omega
    · show a + v.val < b
      omega
  left_inv u := by
    apply Subtype.ext
    apply Fin.ext
    show a + (u.val - a) = u.val
    have := u.property
    omega
  right_inv v := by
    apply Fin.ext
    show (a + v.val) - a = v.val
    have := v.isLt
    omega

/-- For every normalized MPS amplitude law with positive bond dimension and every positive
tolerance, a deterministic map from uniformly distributed Boolean strings approximates that
law in total variation. Its string length is bounded by the stated sum of binary logarithms
of the configuration count and the rounded reciprocal tolerance, plus two. -/
theorem clause3_clause6 : ∀ (n d D : ℕ) (hD : NeZero D)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
    (∑ x, Complex.normSq (@mpsAmplitude n d D hD A x) = 1) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (k : ℕ) (S : (Fin k → Bool) → (Fin n → Fin d)),
        tvDist (uniformPushForward S) (@mpsSampleLaw n d D hD A) ≤ ε
          ∧ k ≤ Nat.log2 (Fintype.card (Fin n → Fin d))
              + Nat.log2 (Nat.ceil (1 / ε)) + 2 := by
  intro n d D hD A hnorm ε hε
  have p_eq : ∀ x : Fin n → Fin d, mpsSampleLaw A x = Complex.normSq (mpsAmplitude A x) := by
    intro x
    simp [mpsSampleLaw, hnorm]
  have p_sum : ∑ x : Fin n → Fin d, mpsSampleLaw A x = 1 := by
    rw [show (∑ x : Fin n → Fin d, mpsSampleLaw A x)
        = ∑ x : Fin n → Fin d, Complex.normSq (mpsAmplitude A x) from
        Finset.sum_congr rfl fun x _ => p_eq x, hnorm]
  have p_nonneg : ∀ x : Fin n → Fin d, 0 ≤ mpsSampleLaw A x := by
    intro x
    rw [p_eq x]
    exact Complex.normSq_nonneg _
  set N : ℕ := Fintype.card (Fin n → Fin d)
  have hNcard : Fintype.card (Fin n → Fin d) = N := rfl
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have : IsEmpty (Fin n → Fin d) := Fintype.card_eq_zero_iff.1 (by rw [hNcard]; exact hN0)
    have h0 : (∑ x : Fin n → Fin d, Complex.normSq (mpsAmplitude A x)) = 0 := by simp
    rw [h0] at hnorm
    exact absurd hnorm (by norm_num)
  have : NeZero N := ⟨hNpos.ne'⟩
  have hc_pos : 0 < Nat.ceil (1 / ε) := by
    rw [Nat.ceil_pos]
    exact div_pos one_pos hε
  have hc_ge : 1 / ε ≤ (Nat.ceil (1 / ε) : ℝ) := (Nat.ceil_le).mp le_rfl
  set cval : ℕ := Nat.ceil (1 / ε)
  have hc_pos' : 0 < cval := hc_pos
  have hc_ge' : 1 / ε ≤ (cval : ℝ) := hc_ge
  set k : ℕ := Nat.log2 N + Nat.log2 cval + 2
  set T : ℕ := 2 ^ k
  have hNT : N * cval ≤ T := by
    have hA : N + 1 ≤ 2 * 2 ^ Nat.log2 N := by
      have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) N
      rw [← Nat.log2_eq_log_two] at h
      have h2 : 2 ^ (Nat.log2 N + 1) = 2 * 2 ^ Nat.log2 N := by
        rw [Nat.pow_succ]; ring
      rw [h2] at h
      omega
    have hB : cval + 1 ≤ 2 * 2 ^ Nat.log2 cval := by
      have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) cval
      rw [← Nat.log2_eq_log_two] at h
      have h2 : 2 ^ (Nat.log2 cval + 1) = 2 * 2 ^ Nat.log2 cval := by
        rw [Nat.pow_succ]; ring
      rw [h2] at h
      omega
    have hC : (N + 1) * (cval + 1) ≤ 2 * 2 ^ Nat.log2 N * (2 * 2 ^ Nat.log2 cval) :=
      Nat.mul_le_mul hA hB
    have hD' : 2 * 2 ^ Nat.log2 N * (2 * 2 ^ Nat.log2 cval)
        = 2 ^ (Nat.log2 N + Nat.log2 cval + 2) := by
      rw [Nat.pow_add, Nat.pow_succ]
      ring
    have hE : N * cval ≤ (N + 1) * (cval + 1) :=
      Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    have hF : (N + 1) * (cval + 1) ≤ 2 ^ (Nat.log2 N + Nat.log2 cval + 2) := by
      rw [← hD']
      exact hC
    show N * cval ≤ T
    exact hE.trans hF

  have hNe : Nonempty (Fin n → Fin d) := Fintype.card_pos_iff.1 hNpos
  set e : Fin N ≃ (Fin n → Fin d) := (Fintype.equivFin (Fin n → Fin d)).symm
  set w : Fin N → ℝ := fun j => (T : ℝ) * mpsSampleLaw A (e j)
  set m : Fin N → ℕ := fun j => Nat.floor (w j)
  have m_le : ∀ j : Fin N, (m j : ℝ) ≤ w j := by
    intro j
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (p_nonneg _))
  have m_gt : ∀ j : Fin N, w j < (m j : ℝ) + 1 := fun j => Nat.lt_floor_add_one (w j)
  have wsum : (∑ j : Fin N, w j) = (T : ℝ) := by
    have h1 : (∑ j : Fin N, w j) = (T : ℝ) * ∑ j : Fin N, mpsSampleLaw A (e j) := by
      simp only [w]
      rw [Finset.mul_sum]
    have h2 : (∑ j : Fin N, mpsSampleLaw A (e j)) = ∑ x : Fin n → Fin d, mpsSampleLaw A x :=
      Equiv.sum_comp e (mpsSampleLaw A)
    rw [h1, h2, p_sum]
    ring
  have msum_le : (∑ j : Fin N, (m j : ℝ)) ≤ (T : ℝ) :=
    (Finset.sum_le_sum fun j _ => m_le j).trans (le_of_eq wsum)
  have msum_nat : (∑ j : Fin N, m j) ≤ T := by
    have := msum_le
    rw [← Nat.cast_sum] at this
    exact_mod_cast this
  set L : ℕ := T - ∑ j : Fin N, m j
  have Lcast : (L : ℝ) = (T : ℝ) - ∑ j : Fin N, (m j : ℝ) := by
    rw [Nat.cast_sub msum_nat, Nat.cast_sum]
  have frac_sum : (∑ j : Fin N, (w j - (m j : ℝ))) = (L : ℝ) := by
    rw [Finset.sum_sub_distrib, Lcast]
    linarith [wsum]
  have frac_lt : ∀ j : Fin N, w j - (m j : ℝ) < 1 := by
    intro j
    linarith [m_gt j]
  have frac_nonneg : ∀ j : Fin N, 0 ≤ w j - (m j : ℝ) := by
    intro j
    linarith [m_le j]
  have L_le : L ≤ N := by
    have h1 : (L : ℝ) ≤ N := by
      rw [← frac_sum]
      calc
        (∑ j : Fin N, (w j - (m j : ℝ))) ≤ ∑ j : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => le_of_lt (frac_lt j)
        _ = N := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
    exact_mod_cast h1
  set cnt : Fin N → ℕ := fun j => m j + if j = 0 then L else 0
  have cnt_sum : (∑ j : Fin N, cnt j) = T := by
    have h1 : (∑ j : Fin N, (if j = 0 then L else 0)) = L := by
      rw [Finset.sum_eq_single (0 : Fin N)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin N)) h
    simp only [cnt, Finset.sum_add_distrib, h1]
    omega
  have cnt_zero : cnt 0 = m 0 + L := by simp [cnt]
  have cnt_succ : ∀ j : Fin N, j ≠ 0 → cnt j = m j := by
    intro j hj
    simp [cnt, hj]

  set cnt' : ℕ → ℕ := fun t => if h : t < N then cnt ⟨t, h⟩ else 0
  set c : ℕ → ℕ := clause3Aux_cum cnt'
  have c_zero : c 0 = 0 := clause3Aux_cum_zero cnt'
  have c_succ : ∀ t : ℕ, c (t + 1) = c t + cnt' t := clause3Aux_cum_succ cnt'
  have c_N : c N = T := by
    show clause3Aux_cum (fun t => if h : t < N then cnt ⟨t, h⟩ else 0) N = T
    rw [clause3Aux_cum_cast N cnt, cnt_sum]
  have c_mono : ∀ {a b : ℕ}, a ≤ b → c a ≤ c b := fun h => clause3Aux_cum_mono h
  have cN1 : c (N + 1) = T := by
    have h1 : cnt' N = 0 := by simp [cnt']
    rw [c_succ, c_N, h1, add_zero]
  have hex : ∀ u : ℕ, u < T → ∃ s : ℕ, u < c (s + 1) := by
    intro u hu
    exact ⟨N, by rw [cN1]; exact hu⟩
  have blk_find_eq : ∀ (u : Fin T) (j : ℕ),
      Nat.find (hex u.val u.isLt) = j ↔ c j ≤ u.val ∧ u.val < c (j + 1) := by
    intro u j
    rw [Nat.find_eq_iff]
    constructor
    · intro h
      have hlt : u.val < c (j + 1) := h.1
      have hmin : ∀ t < j, ¬ (u.val < c (t + 1)) := h.2
      have hle : c j ≤ u.val := by
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          rw [c_zero]
          omega
        · have hbad := hmin (j - 1) (by omega)
          rw [show (j - 1) + 1 = j by omega] at hbad
          omega
      exact ⟨hle, hlt⟩
    · intro h
      refine ⟨h.2, ?_⟩
      intro t htl
      have hmono : c (t + 1) ≤ c j := c_mono (by omega)
      omega
  have blk_lt : ∀ u : Fin T, Nat.find (hex u.val u.isLt) < N := by
    intro u
    have hp : u.val < c ((N - 1) + 1) := by
      rw [show (N - 1) + 1 = N by omega, c_N]
      exact u.isLt
    have hle := Nat.find_min' (hex u.val u.isLt) hp
    omega
  set blk : Fin T → Fin N := fun u => ⟨Nat.find (hex u.val u.isLt), blk_lt u⟩
  have blk_eq : ∀ (u : Fin T) (j : Fin N), blk u = j ↔ c j ≤ u.val ∧ u.val < c (j + 1) := by
    intro u j
    rw [Fin.ext_iff]
    show (Nat.find (hex u.val u.isLt) : ℕ) = j ↔ c j ≤ u.val ∧ u.val < c (j + 1)
    exact blk_find_eq u j
  refine ⟨k, fun t => e (blk (clause3Aux_bitsEnc k t)), ?_, le_refl _⟩

  have hjT : ∀ j : Fin N, c (j + 1) ≤ T := by
    intro j
    have h := c_mono (Nat.succ_le_of_lt j.isLt)
    rw [c_N] at h
    exact h
  have fiber : ∀ x : Fin n → Fin d,
      (Finset.univ.filter (fun t : Fin k → Bool =>
        e (blk (clause3Aux_bitsEnc k t)) = x)).card = cnt (e.symm x) := by
    intro x
    have hx : e (e.symm x) = x := e.apply_symm_apply x
    have hsub : (Finset.univ.filter (fun t : Fin k → Bool =>
        e (blk (clause3Aux_bitsEnc k t)) = x)).card
        = Fintype.card {t : Fin k → Bool // e (blk (clause3Aux_bitsEnc k t)) = x} :=
      (Fintype.card_subtype _).symm
    rw [hsub]
    have e1 : {t : Fin k → Bool // e (blk (clause3Aux_bitsEnc k t)) = x}
        ≃ {u : Fin T // blk u = e.symm x} :=
      (clause3Aux_bitsEnc k).subtypeEquiv fun t => by
        constructor
        · intro h
          exact e.injective (h.trans hx.symm)
        · intro h
          rw [← hx, h]
    rw [Fintype.card_congr e1]
    have e2 : {u : Fin T // blk u = e.symm x}
        ≃ {u : Fin T // c (e.symm x) ≤ u.val ∧ u.val < c (e.symm x + 1)} :=
      Equiv.refl _ |>.subtypeEquiv fun u => blk_eq u (e.symm x)
    rw [Fintype.card_congr e2]
    have e3 : {u : Fin T // c (e.symm x) ≤ u.val ∧ u.val < c (e.symm x + 1)}
        ≃ Fin (c (e.symm x + 1) - c (e.symm x)) :=
      clause3Aux_IcoFinEquiv' T (c (e.symm x)) (c (e.symm x + 1)) (hjT (e.symm x))
    rw [Fintype.card_congr e3, Fintype.card_fin]
    show c (e.symm x + 1) - c (e.symm x) = cnt (e.symm x)
    rw [c_succ]
    have hcn : cnt' (e.symm x) = cnt (e.symm x) := by
      simp [cnt']
    rw [hcn]
    omega

  have q_eq : ∀ x : Fin n → Fin d,
      uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))) x
        = (cnt (e.symm x) : ℝ) / (T : ℝ) := by
    intro x
    have h1 : uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))) x
        = ((Finset.univ.filter (fun t : Fin k → Bool =>
          e (blk (clause3Aux_bitsEnc k t)) = x)).card : ℝ) / (2 ^ k : ℝ) := rfl
    rw [h1, fiber]
    have hTk : ((T : ℕ) : ℝ) = (2 : ℝ) ^ k := by
      show ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k
      norm_cast
    rw [hTk]
  have cntw_eq : ∀ j : Fin N,
      (cnt j : ℝ) - w j = (if j = 0 then (L : ℝ) else 0) - (w j - (m j : ℝ)) := by
    intro j
    by_cases h : j = 0
    · subst h
      rw [cnt_zero]
      push_cast
      simp only [ite_true]
      ring
    · rw [cnt_succ j h]
      simp only [ite_eq_right h]
      ring
  have hsum : (∑ x : Fin n → Fin d,
      |uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))) x - mpsSampleLaw A x|)
      = (∑ j : Fin N, |(cnt j : ℝ) - w j|) / (T : ℝ) := by
    have h1 : (∑ x : Fin n → Fin d,
        |uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))) x - mpsSampleLaw A x|)
        = ∑ x : Fin n → Fin d, |(cnt (e.symm x) : ℝ) / (T : ℝ) - mpsSampleLaw A x| :=
      Finset.sum_congr rfl fun x _ => by rw [q_eq x]
    rw [h1]
    have h2 : (∑ x : Fin n → Fin d, |(cnt (e.symm x) : ℝ) / (T : ℝ) - mpsSampleLaw A x|)
        = ∑ j : Fin N, |(cnt j : ℝ) / (T : ℝ) - mpsSampleLaw A (e j)| := by
      have hcomp : (∑ x : Fin n → Fin d, |(cnt (e.symm x) : ℝ) / (T : ℝ) - mpsSampleLaw A x|)
          = ∑ j : Fin N, |(cnt (e.symm (e j)) : ℝ) / (T : ℝ) - mpsSampleLaw A (e j)| :=
        (Equiv.sum_comp e (fun x : Fin n → Fin d =>
          |(cnt (e.symm x) : ℝ) / (T : ℝ) - mpsSampleLaw A x|)).symm
      rw [hcomp]
      exact Finset.sum_congr rfl fun j _ => by rw [e.symm_apply_apply j]
    rw [h2]
    have h3 : ∀ j : Fin N,
        |(cnt j : ℝ) / (T : ℝ) - mpsSampleLaw A (e j)|
          = |(cnt j : ℝ) - w j| / (T : ℝ) := by
      intro j
      have hw : w j = (T : ℝ) * mpsSampleLaw A (e j) := rfl
      rw [hw]
      have hTpos : (0:ℝ) < T := by exact_mod_cast (pow_pos two_pos k)
      have hne : (T:ℝ) ≠ 0 := ne_of_gt hTpos
      have key : ((cnt j : ℝ) - (T : ℝ) * mpsSampleLaw A (e j)) / (T : ℝ)
          = (cnt j : ℝ) / (T : ℝ) - mpsSampleLaw A (e j) := by
        rw [sub_div]
        have h : (T:ℝ) * mpsSampleLaw A (e j) / (T:ℝ) = mpsSampleLaw A (e j) :=
          mul_div_cancel_left₀ _ hne
        rw [h]
      rw [← key, abs_div, abs_of_nonneg (le_of_lt hTpos)]
    rw [Finset.sum_congr rfl (fun j _ => h3 j), Finset.sum_div]
  have hsum_bound : (∑ j : Fin N, |(cnt j : ℝ) - w j|) ≤ 2 * N := by
    have h1 : ∀ j : Fin N, |(cnt j : ℝ) - w j| ≤ (if j = 0 then (L : ℝ) else 0)
        + (w j - (m j : ℝ)) := by
      intro j
      rw [cntw_eq j]
      have hnn : 0 ≤ w j - (m j : ℝ) := frac_nonneg j
      have hdd : 0 ≤ (if j = 0 then (L : ℝ) else 0) := by
        by_cases h : j = 0 <;> simp [h]
      have htri := abs_sub_le (if j = 0 then (L : ℝ) else 0) 0 (w j - (m j : ℝ))
      simp only [sub_zero, zero_sub, abs_neg] at htri
      rw [abs_of_nonneg hdd, abs_of_nonneg hnn] at htri
      exact htri
    have h2 : (∑ j : Fin N, |(cnt j : ℝ) - w j|)
        ≤ ∑ j : Fin N, ((if j = 0 then (L : ℝ) else 0) + (w j - (m j : ℝ))) :=
      Finset.sum_le_sum fun j _ => h1 j
    have h3 : (∑ j : Fin N, ((if j = 0 then (L : ℝ) else 0) + (w j - (m j : ℝ))))
        = (L : ℝ) + (L : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hL : (∑ j : Fin N, (if j = 0 then (L : ℝ) else 0)) = L := by
        rw [Finset.sum_eq_single (0 : Fin N)]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ (0 : Fin N)) h
      rw [hL, frac_sum]
    rw [h3] at h2
    have h4 : (L : ℝ) + (L : ℝ) ≤ 2 * N := by
      have : (L : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr L_le

      linarith
    exact h2.trans h4
  have hTV : tvDist (uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))))
        (mpsSampleLaw A) ≤ ε := by
    have h1 : tvDist (uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))))
        (mpsSampleLaw A)
        = (∑ x : Fin n → Fin d,
          |uniformPushForward (fun t => e (blk (clause3Aux_bitsEnc k t))) x
            - mpsSampleLaw A x|) / 2 := rfl
    rw [h1, hsum]
    have hNdiv : (N : ℝ) / T ≤ ε := by
      have hcv : (0:ℝ) < cval := by exact_mod_cast hc_pos'
      have hTpos' : (0:ℝ) < T := by exact_mod_cast (pow_pos two_pos k)
      have step1 : (N : ℝ) / (T : ℝ) ≤ 1 / (cval : ℝ) := by
        rw [div_le_div_iff₀ hTpos' hcv]
        have hNT' : (N : ℝ) * cval ≤ T := by exact_mod_cast hNT
        nlinarith
      have step2 : (1:ℝ) / (cval : ℝ) ≤ ε := by
        rw [div_le_iff₀ hcv]
        have hge : (1:ℝ) / ε ≤ (cval : ℝ) := hc_ge'
        rw [div_le_iff₀ hε] at hge
        nlinarith
      exact step1.trans step2
    have h2 : (∑ j : Fin N, |(cnt j : ℝ) - w j|) / (T : ℝ) / 2 ≤ ε := by
      have := hsum_bound

      have hTpos' : (0:ℝ) < T := by exact_mod_cast (pow_pos two_pos k)
      calc
        (∑ j : Fin N, |(cnt j : ℝ) - w j|) / (T : ℝ) / 2
            ≤ (2 * N) / (T : ℝ) / 2 := by gcongr
        _ = (N : ℝ) / (T : ℝ) := by ring
        _ ≤ ε := hNdiv
    exact h2
  exact hTV

open Qatlib.Concepts.TensorNetwork.GaugeInvariance Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Module
open scoped BigOperators ComplexConjugate

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The left singular-vector amplitude at cut `c`, evaluated on an encoded prefix configuration
and extended by zero to natural-number singular indices outside the column dimension. -/
noncomputable def g10gL (c : ℕ) (k : ℕ) (u : Fin c → Fin d) : ℂ :=
  if h : k < Fintype.card (Fin (d ^ (n - c))) then
    leftSingularVector (cutMatrix n d ψ c) ⟨k, h⟩ (finPowEnc d c u)
  else 0

/-- The singular-value-weighted conjugate right singular-vector amplitude at cut `c`, evaluated
on an encoded suffix and extended by zero outside the column dimension. -/
noncomputable def g10gS (c : ℕ) (k : ℕ) (v : Fin (n - c) → Fin d) : ℂ :=
  if h : k < Fintype.card (Fin (d ^ (n - c))) then
    ((matrixSingularValues (cutMatrix n d ψ c) k : ℂ)) *
      star (rightSingularBasis (cutMatrix n d ψ c) ⟨k, h⟩ (finPowEnc d (n - c) v))
  else 0

/-- The transition coefficient between adjacent cuts, formed from the right singular-vector
overlap after inserting physical value `y` and scaled by the current singular value and
inverse next singular value. It is zero when the cut or either singular index is outside its
permitted range. -/
noncomputable def g10gLink (c : ℕ) (k' k : ℕ) (y : Fin d) : ℂ :=
  if hc : c + 1 ≤ n then
    if hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1)))) then
      if hk : k < Fintype.card (Fin (d ^ (n - c))) then
        ((matrixSingularValues (cutMatrix n d ψ c) k : ℂ) *
          ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹)) *
          (∑ q : Fin (d ^ (n - c)),
            star (rightSingularBasis (cutMatrix n d ψ c) ⟨k, hk⟩ q) *
              (g10g_rightFactor (n := n) (c := c) hc y).mulVec
                (fun j' : Fin (d ^ (n - (c + 1))) =>
                  rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩ j') q)
      else 0
    else 0
  else 0

/-- For a singular index in the column range, `g10gL` is the corresponding left singular-vector
entry at the encoded prefix. -/
theorem g10gL_fin (c : ℕ) (k : Fin (Fintype.card (Fin (d ^ (n - c))))) (u : Fin c → Fin d) :
    g10gL ψ c k u = leftSingularVector (cutMatrix n d ψ c) k (finPowEnc d c u) := by
  unfold g10gL
  rw [dite_eq_left k.isLt]

/-- For a singular index in the column range, `g10gS` is the singular value times the conjugate
right singular-vector entry at the encoded suffix. -/
theorem g10gS_fin (c : ℕ) (k : Fin (Fintype.card (Fin (d ^ (n - c)))))
    (v : Fin (n - c) → Fin d) :
    g10gS ψ c k v = ((matrixSingularValues (cutMatrix n d ψ c) k : ℂ)) *
      star (rightSingularBasis (cutMatrix n d ψ c) k (finPowEnc d (n - c) v)) := by
  unfold g10gS
  rw [dite_eq_left k.isLt]

/-- For valid adjacent cuts and singular indices, `g10gLink` equals its singular-value-scaled
overlap formula without the range checks. -/
theorem g10gLink_fin (c : ℕ) (hc : c + 1 ≤ n)
    (k' : Fin (Fintype.card (Fin (d ^ (n - (c + 1))))))
    (k : Fin (Fintype.card (Fin (d ^ (n - c))))) (y : Fin d) :
    g10gLink ψ c k' k y
      = ((matrixSingularValues (cutMatrix n d ψ c) k : ℂ) *
          ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹)) *
          (∑ q : Fin (d ^ (n - c)),
            star (rightSingularBasis (cutMatrix n d ψ c) k q) *
              (g10g_rightFactor (n := n) (c := c) hc y).mulVec
                (fun j' : Fin (d ^ (n - (c + 1))) =>
                  rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j') q) := by
  unfold g10gLink
  rw [dite_eq_left hc, dite_eq_left k'.isLt, dite_eq_left k.isLt]

/-- For a valid adjacent-cut pair, the link coefficient vanishes when its next-cut singular
index is at least the next cut matrix's column dimension. -/
theorem g10gLink_eq_zero_of_k' (c : ℕ) (hc : c + 1 ≤ n) {k' : ℕ}
    (hk' : Fintype.card (Fin (d ^ (n - (c + 1)))) ≤ k') (k : ℕ) (y : Fin d) :
    g10gLink ψ c k' k y = 0 := by
  unfold g10gLink
  rw [dite_eq_left hc, dite_eq_right (by omega)]

/-- For a valid adjacent-cut pair, the link coefficient vanishes when its current-cut singular
index is at least the current cut matrix's column dimension. -/
theorem g10gLink_eq_zero_of_k (c : ℕ) (hc : c + 1 ≤ n) (k' : ℕ) {k : ℕ}
    (hk : Fintype.card (Fin (d ^ (n - c))) ≤ k) (y : Fin d) :
    g10gLink ψ c k' k y = 0 := by
  unfold g10gLink
  rw [dite_eq_left hc]
  by_cases hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1))))
  · rw [dite_eq_left hk', dite_eq_right (by omega)]
  · rw [dite_eq_right hk']

/-- The extended left singular amplitude is zero at a singular index outside the cut matrix's
column dimension. -/
theorem g10gL_eq_zero_of_not_lt (c : ℕ) {k : ℕ} (hk : Fintype.card (Fin (d ^ (n - c))) ≤ k)
    (u : Fin c → Fin d) : g10gL ψ c k u = 0 := by
  unfold g10gL
  rw [dite_eq_right (by omega)]

/-- The extended weighted right singular amplitude is zero at a singular index outside the cut
matrix's column dimension. -/
theorem g10gS_eq_zero_of_not_lt (c : ℕ) {k : ℕ} (hk : Fintype.card (Fin (d ^ (n - c))) ≤ k)
    (v : Fin (n - c) → Fin d) : g10gS ψ c k v = 0 := by
  unfold g10gS
  rw [dite_eq_right (by omega)]

/-- An entry of a cut matrix is the state amplitude at the configuration obtained by decoding
and joining its row and column indices. -/
theorem g10g_cutMatrix_entry (c : ℕ) (p : Fin (d ^ c)) (q : Fin (d ^ (n - c))) :
    cutMatrix n d ψ c p q
      = ψ (splitJoin n c d ((finPowEnc d c).symm p) ((finPowEnc d (n - c)).symm q)) := by
  simp [cutMatrix]

/-- Every cut-matrix entry is the sum of its singular values times the corresponding left
singular-vector entry and conjugate right singular-vector entry. -/
theorem g10g_matrix_entry_svd (c : ℕ) (p : Fin (d ^ c)) (q : Fin (d ^ (n - c))) :
    cutMatrix n d ψ c p q
      = ∑ i : Fin (Fintype.card (Fin (d ^ (n - c)))),
          (matrixSingularValues (cutMatrix n d ψ c) i : ℂ) *
            (leftSingularVector (cutMatrix n d ψ c) i p *
              star (rightSingularBasis (cutMatrix n d ψ c) i q)) := by
  have h := congrFun (congrFun (matrix_eq_sum_singularVectors (cutMatrix n d ψ c)) p) q
  rw [Matrix.sum_apply] at h
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply] at h
  exact h

/-- At a valid cut, the amplitude of a joined prefix and suffix is the sum of the products
`g10gL` and `g10gS` over all singular indices. -/
theorem g10g_svd_reconstruct (c : ℕ) (_hc : c ≤ n) (u : Fin c → Fin d) (v : Fin (n - c) → Fin d) :
    ψ (splitJoin n c d u v)
      = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))), g10gL ψ c k u * g10gS ψ c k v := by
  have hcut := g10g_cutMatrix_entry ψ c (finPowEnc d c u) (finPowEnc d (n - c) v)
  simp only [Equiv.symm_apply_apply] at hcut
  rw [← hcut, g10g_matrix_entry_svd]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [g10gL_fin, g10gS_fin]
  ring

/-- When `c + 1` is at most the chain length, moving the last value of a prefix to the beginning
of the suffix identifies the corresponding entries of the cut matrices at `c + 1` and `c`. -/
theorem g10g_entry_transfer (c : ℕ) (hc : c + 1 ≤ n) (u : Fin c → Fin d) (y : Fin d)
    (j' : Fin (d ^ (n - (c + 1)))) :
    cutMatrix n d ψ (c + 1) (finPowEnc d (c + 1) (g10g_snoc u y)) j'
      = cutMatrix n d ψ c (finPowEnc d c u)
          (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))) := by
  have hfact := g10g_cutMatrix_succ_eq_sum_factor ψ c hc
  have hi' : (finPowEnc d (c + 1)).symm (finPowEnc d (c + 1) (g10g_snoc u y))
      = g10g_snoc u y := (finPowEnc d (c + 1)).symm_apply_apply _
  have hlast : g10g_last ((finPowEnc d (c + 1)).symm
      (finPowEnc d (c + 1) (g10g_snoc u y))) = y := by
    rw [hi', g10g_last_snoc]
  have hinit : g10g_init ((finPowEnc d (c + 1)).symm
      (finPowEnc d (c + 1) (g10g_snoc u y))) = u := by
    rw [hi', g10g_init_snoc]
  rw [hfact]
  rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single y]
  · rw [g10g_factor_prod_apply hc ψ y (finPowEnc d (c + 1) (g10g_snoc u y)) j']
    simp only [hlast, hinit]
    rw [ite_true]
  · intro y0 _ hy0
    rw [g10g_factor_prod_apply hc ψ y0 (finPowEnc d (c + 1) (g10g_snoc u y)) j']
    simp only [hlast, hinit, ite_eq_right hy0]
  · intro hy
    exact absurd (Finset.mem_univ _) hy

/-- The insertion matrix `g10g_rightFactor` has entry one exactly when the old suffix index
encodes physical value `y` followed by the decoded new suffix, and entry zero otherwise. -/
theorem g10g_rightFactor_entry (c : ℕ) (hc : c + 1 ≤ n) (y : Fin d)
    (q : Fin (d ^ (n - c))) (j' : Fin (d ^ (n - (c + 1)))) :
    g10g_rightFactor (n := n) (c := c) hc y q j'
      = if q = finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))
        then 1 else 0 := by
  by_cases he : q = finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))
  · subst he
    rw [g10g_rightFactor_self]
    simp
  · rw [g10g_rightFactor_eq_zero_of_ne hc y q j' (by simpa using! he)]
    simp [he]

/-- Multiplication by the suffix-insertion matrix is the finite sum of its entries times the
input vector entries. -/
theorem g10g_rightFactor_mulVec (c : ℕ) (hc : c + 1 ≤ n) (y : Fin d)
    (w : Fin (d ^ (n - (c + 1))) → ℂ) (q : Fin (d ^ (n - c))) :
    (g10g_rightFactor (n := n) (c := c) hc y).mulVec w q
      = ∑ j' : Fin (d ^ (n - (c + 1))), (g10g_rightFactor (n := n) (c := c) hc y) q j' * w j' :=
  rfl

/-- For adjacent valid cuts, the next-cut left singular amplitude of an extended prefix is the
cut-matrix action on the matching right singular vector multiplied by the inverse singular
value, when its index is in range. It is zero outside that range. -/
theorem g10gL_snoc_eq (c : ℕ) (_hc : c + 1 ≤ n) (k' : ℕ) (u : Fin c → Fin d) (y : Fin d) :
    g10gL ψ (c + 1) k' (g10g_snoc u y)
      = if hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1)))) then
          ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹) *
            (∑ j' : Fin (d ^ (n - (c + 1))),
              cutMatrix n d ψ (c + 1) (finPowEnc d (c + 1) (g10g_snoc u y)) j' *
                rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩ j')
        else 0 := by
  by_cases hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1))))
  · rw [g10gL_fin ψ (c + 1) ⟨k', hk'⟩, dite_eq_left hk']
    have hdef : leftSingularVector (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩
        = ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹) •
          (cutMatrix n d ψ (c + 1)).toEuclideanLin
            (rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩) := rfl
    rw [hdef]
    have hsmul : ((((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹) •
          (cutMatrix n d ψ (c + 1)).toEuclideanLin
            (rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩)) :
          EuclideanSpace ℂ (Fin (d ^ (c + 1))))
          (finPowEnc d (c + 1) (g10g_snoc u y))
        = ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹) *
          ((cutMatrix n d ψ (c + 1)).toEuclideanLin
            (rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩)
            (finPowEnc d (c + 1) (g10g_snoc u y))) := by simp
    rw [hsmul]
    have hexp : (cutMatrix n d ψ (c + 1)).toEuclideanLin
          (rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩)
          (finPowEnc d (c + 1) (g10g_snoc u y))
        = ∑ j' : Fin (d ^ (n - (c + 1))),
            cutMatrix n d ψ (c + 1) (finPowEnc d (c + 1) (g10g_snoc u y)) j' *
              rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩ j' := rfl
    rw [hexp]
  · rw [g10gL_eq_zero_of_not_lt ψ (c + 1) (by omega), dite_eq_right hk']

/-- For adjacent valid cuts and an in-range next-cut singular index, the extended-prefix left
singular amplitude is expressed using the previous cut matrix, suffix insertion, and the
inverse next singular value. -/
theorem g10g_expand_common (c : ℕ) (hc : c + 1 ≤ n) (k' : ℕ) (u : Fin c → Fin d) (y : Fin d)
    (hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1))))) :
    g10gL ψ (c + 1) k' (g10g_snoc u y)
      = ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹) *
        (∑ j' : Fin (d ^ (n - (c + 1))),
          cutMatrix n d ψ c (finPowEnc d c u)
            (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))) *
            rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩ j') := by
  rw [g10gL_snoc_eq ψ c hc k' u y, dite_eq_left hk']
  congr 1
  exact Finset.sum_congr rfl (fun j' _ => by rw [g10g_entry_transfer ψ c hc u y j'])

/-- The overlap sum involving the suffix-insertion matrix reduces to a sum over the shorter
suffix indices, evaluating the current right singular vector at each inserted suffix. -/
theorem g10g_filter_sum (c : ℕ) (hc : c + 1 ≤ n) (y : Fin d)
    (k : Fin (Fintype.card (Fin (d ^ (n - c)))))
    (k' : Fin (Fintype.card (Fin (d ^ (n - (c + 1)))))) :
    (∑ q : Fin (d ^ (n - c)),
        star (rightSingularBasis (cutMatrix n d ψ c) k q) *
          (g10g_rightFactor (n := n) (c := c) hc y).mulVec
            (fun j' : Fin (d ^ (n - (c + 1))) => rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j') q)
      = ∑ j' : Fin (d ^ (n - (c + 1))),
        star (rightSingularBasis (cutMatrix n d ψ c) k
          (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')))) *
          rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j' := by
  have hinner : ∀ q : Fin (d ^ (n - c)),
      star (rightSingularBasis (cutMatrix n d ψ c) k q) *
        (g10g_rightFactor (n := n) (c := c) hc y).mulVec
          (fun j' : Fin (d ^ (n - (c + 1))) => rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j') q
        = ∑ j' : Fin (d ^ (n - (c + 1))),
          star (rightSingularBasis (cutMatrix n d ψ c) k q) *
            (g10g_rightFactor (n := n) (c := c) hc y) q j' *
            rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j' := by
    intro q
    rw [g10g_rightFactor_mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j' _ => by ring)
  calc (∑ q : Fin (d ^ (n - c)),
        star (rightSingularBasis (cutMatrix n d ψ c) k q) *
          (g10g_rightFactor (n := n) (c := c) hc y).mulVec
            (fun j' : Fin (d ^ (n - (c + 1))) => rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j') q)
      = ∑ q : Fin (d ^ (n - c)),
          ∑ j' : Fin (d ^ (n - (c + 1))),
            star (rightSingularBasis (cutMatrix n d ψ c) k q) *
              (g10g_rightFactor (n := n) (c := c) hc y) q j' *
              rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j' :=
        Finset.sum_congr rfl (fun q _ => hinner q)
    _ = ∑ j' : Fin (d ^ (n - (c + 1))),
          ∑ q : Fin (d ^ (n - c)),
            star (rightSingularBasis (cutMatrix n d ψ c) k q) *
              (g10g_rightFactor (n := n) (c := c) hc y) q j' *
              rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j' :=
        Finset.sum_comm
    _ = ∑ j' : Fin (d ^ (n - (c + 1))),
          star (rightSingularBasis (cutMatrix n d ψ c) k
            (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')))) *
            rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j' :=
        Finset.sum_congr rfl (fun j' _ => by
          have hq : ∀ q : Fin (d ^ (n - c)),
              star (rightSingularBasis (cutMatrix n d ψ c) k q) *
                  (if q = finPowEnc d (n - c)
                      (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))
                    then 1 else 0) *
                  rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j'
                = if q = finPowEnc d (n - c)
                      (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')) then
                    star (rightSingularBasis (cutMatrix n d ψ c) k
                        (finPowEnc d (n - c)
                          (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j')))) *
                      rightSingularBasis (cutMatrix n d ψ (c + 1)) k' j'
                  else 0 := by
            intro q
            by_cases he : q = finPowEnc d (n - c)
                (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))
            · subst he
              simp
            · simp [he]
          simp only [g10g_rightFactor_entry]
          rw [Finset.sum_congr rfl (fun q _ => hq q), Finset.sum_ite_eq']
          simp only [Finset.mem_univ, ite_true])

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- At adjacent valid cuts, each next-cut left singular amplitude expands as a sum of
current-cut left singular amplitudes multiplied by their link coefficients. -/
theorem g10g_expand_link (c : ℕ) (hc : c + 1 ≤ n) (k' : ℕ) (u : Fin c → Fin d) (y : Fin d) :
    g10gL ψ (c + 1) k' (g10g_snoc u y)
      = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          g10gL ψ c k u * g10gLink ψ c k' k y := by
  by_cases hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1))))
  · rw [g10g_expand_common ψ c hc k' u y hk']
    symm
    have hR : (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          g10gL ψ c k u * g10gLink ψ c k' k y)
        = ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ)⁻¹) *
          (∑ j' : Fin (d ^ (n - (c + 1))),
            cutMatrix n d ψ c (finPowEnc d c u)
              (finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))) *
              rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩ j') := by

      set p : Fin (d ^ c) := finPowEnc d c u with hp
      set qj : Fin (d ^ (n - (c + 1))) → Fin (d ^ (n - c)) :=
        (fun j' => finPowEnc d (n - c) (g10g_cons hc y ((finPowEnc d (n - (c + 1))).symm j'))) with hqj
      set W : Fin (d ^ (n - (c + 1))) → ℂ :=
        (fun j' => rightSingularBasis (cutMatrix n d ψ (c + 1)) ⟨k', hk'⟩ j') with hW
      set V : Fin (Fintype.card (Fin (d ^ (n - c)))) → Fin (d ^ (n - c)) → ℂ :=
        (fun i q => rightSingularBasis (cutMatrix n d ψ c) i q) with hV
      set L : Fin (Fintype.card (Fin (d ^ (n - c)))) → Fin (d ^ c) → ℂ :=
        (fun i p => leftSingularVector (cutMatrix n d ψ c) i p) with hL
      set Sg : ℕ → ℝ := (fun i => matrixSingularValues (cutMatrix n d ψ c) i) with hSg
      set Sg' : ℝ := matrixSingularValues (cutMatrix n d ψ (c + 1)) k' with hSg'

      have hstep1 : (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            g10gL ψ c k u * g10gLink ψ c k' k y)
          = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
              L k p * ((Sg k * (Sg' : ℂ)⁻¹) *
                (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j')) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [g10gL_fin, g10gLink_fin ψ c hc ⟨k', hk'⟩ k y, g10g_filter_sum ψ c hc y k ⟨k', hk'⟩]
      rw [hstep1]

      have hterm : ∀ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          L k p * ((Sg k * (Sg' : ℂ)⁻¹) * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j'))
            = (Sg' : ℂ)⁻¹ *
              ((Sg k) * (L k p * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j'))) := by
        intro k
        ring
      rw [show (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            L k p * ((Sg k * (Sg' : ℂ)⁻¹) * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j')))
          = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
              (Sg' : ℂ)⁻¹ *
                ((Sg k) * (L k p * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j'))) from
        Finset.sum_congr rfl (fun k _ => hterm k)]

      rw [show (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            (Sg' : ℂ)⁻¹ *
              ((Sg k) * (L k p * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j'))))
          = (Sg' : ℂ)⁻¹ *
            (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
              ((Sg k) * (L k p * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j')))) from
        (Finset.mul_sum ..).symm]
      congr 1
      have hinner : ∀ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          (Sg k) * (L k p * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j'))
            = ∑ j' : Fin (d ^ (n - (c + 1))),
              ((Sg k) * (L k p * star (V k (qj j')))) * W j' := by
        intro k
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j' _ => by ring)
      calc (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            ((Sg k) * (L k p * (∑ j' : Fin (d ^ (n - (c + 1))), star (V k (qj j')) * W j'))))
          = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
              ∑ j' : Fin (d ^ (n - (c + 1))),
                ((Sg k) * (L k p * star (V k (qj j')))) * W j' :=
            Finset.sum_congr rfl (fun k _ => hinner k)
        _ = ∑ j' : Fin (d ^ (n - (c + 1))),
              ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
                ((Sg k) * (L k p * star (V k (qj j')))) * W j' :=
            Finset.sum_comm
        _ = ∑ j' : Fin (d ^ (n - (c + 1))),
              (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
                ((Sg k) * (L k p * star (V k (qj j'))))) * W j' :=
            Finset.sum_congr rfl (fun j' _ => (Finset.sum_mul ..).symm)
        _ = ∑ j' : Fin (d ^ (n - (c + 1))),
              cutMatrix n d ψ c p (qj j') * W j' :=
            Finset.sum_congr rfl (fun j' _ => by
              have hentry := (g10g_matrix_entry_svd ψ c p (qj j')).symm
              show ((∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
                  (matrixSingularValues (cutMatrix n d ψ c) k : ℂ) *
                    (leftSingularVector (cutMatrix n d ψ c) k p *
                      star (rightSingularBasis (cutMatrix n d ψ c) k (qj j')))) : ℂ) * _
                = cutMatrix n d ψ c p (qj j') * _
              congr 1
)
    rw [hR]
  · rw [g10gL_snoc_eq ψ c hc k' u y, dite_eq_right hk']
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [g10gLink_eq_zero_of_k' ψ c hc (by omega) k y, mul_zero]

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- A singular value of a cut matrix is zero when its index is at least the cut rank. -/
theorem g10g_singular_eq_zero_of_cutRank_le {c k : ℕ} (hk : cutRank n d ψ c ≤ k) :
    matrixSingularValues (cutMatrix n d ψ c) k = 0 := by
  by_contra hne
  have hmem : k ∈ (matrixSingularValues (cutMatrix n d ψ c)).support :=
    Finsupp.mem_support_iff.mpr hne
  rw [support_matrixSingularValues_cutMatrix] at hmem
  simp only [Finset.mem_range] at hmem
  omega

/-- The extended left singular amplitude vanishes at every index at least the cut rank. -/
theorem g10gL_eq_zero_of_cutRank_le {c k : ℕ} (hk : cutRank n d ψ c ≤ k)
    (u : Fin c → Fin d) : g10gL ψ c k u = 0 := by
  unfold g10gL
  by_cases hlt : k < Fintype.card (Fin (d ^ (n - c)))
  · rw [dite_eq_left hlt]
    have hz : leftSingularVector (cutMatrix n d ψ c) ⟨k, hlt⟩ = 0 :=
      leftSingularVector_eq_zero (cutMatrix n d ψ c) ⟨k, hlt⟩
        (show matrixSingularValues (cutMatrix n d ψ c) k = 0 from
          g10g_singular_eq_zero_of_cutRank_le ψ hk)
    rw [hz]
    simp
  · rw [dite_eq_right hlt]

/-- The weighted right singular amplitude vanishes at every index at least the cut rank. -/
theorem g10gS_eq_zero_of_cutRank_le {c k : ℕ} (hk : cutRank n d ψ c ≤ k)
    (v : Fin (n - c) → Fin d) : g10gS ψ c k v = 0 := by
  unfold g10gS
  by_cases hlt : k < Fintype.card (Fin (d ^ (n - c)))
  · rw [dite_eq_left hlt]
    rw [g10g_singular_eq_zero_of_cutRank_le ψ hk]
    simp
  · rw [dite_eq_right hlt]

/-- For adjacent valid cuts, a link coefficient vanishes when its current-cut singular index is
at least the current cut rank. -/
theorem g10gLink_eq_zero_of_cutRank_le_left {c k : ℕ} (hc : c + 1 ≤ n)
    (hk : cutRank n d ψ c ≤ k) (k' : ℕ) (y : Fin d) :
    g10gLink ψ c k' k y = 0 := by
  unfold g10gLink
  rw [dite_eq_left hc]
  by_cases hk' : k' < Fintype.card (Fin (d ^ (n - (c + 1))))
  · rw [dite_eq_left hk']
    by_cases hk2 : k < Fintype.card (Fin (d ^ (n - c)))
    · rw [dite_eq_left hk2]
      rw [g10g_singular_eq_zero_of_cutRank_le ψ hk]
      simp
    · rw [dite_eq_right hk2]
  · rw [dite_eq_right hk']

/-- For adjacent valid cuts, a link coefficient vanishes when its next-cut singular index is at
least the next cut rank. -/
theorem g10gLink_eq_zero_of_cutRank_le_right {c k' : ℕ} (hc : c + 1 ≤ n)
    (hk' : cutRank n d ψ (c + 1) ≤ k') (k : ℕ) (y : Fin d) :
    g10gLink ψ c k' k y = 0 := by
  unfold g10gLink
  rw [dite_eq_left hc]
  by_cases hk'2 : k' < Fintype.card (Fin (d ^ (n - (c + 1))))
  · rw [dite_eq_left hk'2]
    have hσ : matrixSingularValues (cutMatrix n d ψ (c + 1)) k' = 0 :=
      g10g_singular_eq_zero_of_cutRank_le ψ hk'
    have hinv : ((matrixSingularValues (cutMatrix n d ψ (c + 1)) k' : ℂ))⁻¹ = 0 := by
      rw [hσ]
      simp
    by_cases hk2 : k < Fintype.card (Fin (d ^ (n - c)))
    · rw [dite_eq_left hk2]
      rw [hinv]
      simp
    · rw [dite_eq_right hk2]
  · rw [dite_eq_right hk'2]

/-- Left singular amplitudes with indices below the cut rank are orthonormal under summation
over prefix configurations. -/
theorem g10gL_inner_eq_ite (c : ℕ) (k k' : Fin (Fintype.card (Fin (d ^ (n - c)))))
    (hk : (k : ℕ) < cutRank n d ψ c) (hk' : (k' : ℕ) < cutRank n d ψ c) :
    ∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c k' u
      = if k = k' then (1 : ℂ) else 0 := by
  have hsum : (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c k' u)
      = ∑ q : Fin (d ^ c),
          star (leftSingularVector (cutMatrix n d ψ c) k q)
            * leftSingularVector (cutMatrix n d ψ c) k' q := by
    rw [← Equiv.sum_comp (finPowEnc d c)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [g10gL_fin, g10gL_fin]
  rw [hsum, ← g10g_inner_eq_sum]
  have hfin : Matrix.rank (cutMatrix n d ψ c)
      = Module.finrank ℂ (LinearMap.range (cutMatrix n d ψ c).toEuclideanLin) :=
    rank_eq_finrank_range_toEuclideanLin (cutMatrix n d ψ c)
  by_cases heq : k = k'
  · subst heq
    rw [inner_self_eq_norm_sq_to_K]
    have hnorm : ‖leftSingularVector (cutMatrix n d ψ c) k‖ = 1 :=
      norm_leftSingularVector (cutMatrix n d ψ c) k (by
        rw [← hfin, ← cutRank_eq_matrixRank]
        exact hk)
    rw [hnorm]
    simp
  · rw [inner_leftSingularVector_of_ne (cutMatrix n d ψ c) heq]
    simp [heq]

/-- Every value of the left singular amplitude is zero when its singular index is at least the
cut rank. -/
theorem g10gL_inner_self_eq_zero_of_cutRank_le {c k : ℕ} (hk : cutRank n d ψ c ≤ k)
    (u : Fin c → Fin d) : g10gL ψ c k u = 0 :=
  g10gL_eq_zero_of_cutRank_le ψ hk u

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The equivalence between a prefix together with one physical value and the configuration
obtained by appending that value. -/
def g10g_snocEquiv {c d : ℕ} : ((Fin c → Fin d) × Fin d) ≃ (Fin (c + 1) → Fin d) where
  toFun := fun p => g10g_snoc p.1 p.2
  invFun := fun u => (g10g_init u, g10g_last u)
  left_inv := by
    intro p
    rcases p with ⟨u, y⟩
    show (g10g_init (g10g_snoc u y), g10g_last (g10g_snoc u y)) = (u, y)
    rw [g10g_init_snoc, g10g_last_snoc]
  right_inv := fun u => g10g_snoc_init_last u

/-- Applying `g10g_snocEquiv` to a prefix and a physical value appends that value to the prefix. -/
theorem g10g_snocEquiv_apply {c d : ℕ} (u : Fin c → Fin d) (y : Fin d) :
    g10g_snocEquiv (u, y) = g10g_snoc u y := rfl

/-- The Gram sum of two extended left singular amplitudes is one exactly when their indices
agree below the cut rank, and zero otherwise. -/
theorem g10gL_gram (c : ℕ) (k j : Fin (Fintype.card (Fin (d ^ (n - c))))) :
    (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c j u)
      = if k = j ∧ (k : ℕ) < cutRank n d ψ c then (1 : ℂ) else 0 := by
  by_cases hk : (k : ℕ) < cutRank n d ψ c
  · by_cases hj : (j : ℕ) < cutRank n d ψ c
    · rw [g10gL_inner_eq_ite ψ c k j hk hj]
      by_cases heq : k = j
      · subst heq
        rw [ite_eq_left rfl, ite_eq_left ⟨rfl, hk⟩]
      · rw [ite_eq_right heq, ite_eq_right (fun h => heq h.1)]
    · have hz : g10gL ψ c j = fun _ => 0 := by
        funext u
        exact g10gL_eq_zero_of_cutRank_le ψ (by omega) u
      rw [hz]
      simp
      by_cases heq : k = j
      · subst heq
        exact absurd hk (by omega)
      · simp [heq]
  · have hsum0 : (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c j u) = 0 := by
      apply Finset.sum_eq_zero
      intro u _hu
      rw [g10gL_eq_zero_of_cutRank_le ψ (by omega : cutRank n d ψ c ≤ k) u]
      simp
    rw [hsum0]
    by_cases heq : k = j
    · subst heq
      rw [ite_eq_right (fun h => hk h.2)]
    · rw [ite_eq_right (fun h => heq h.1)]

/-- For adjacent valid cuts, link coefficients for next-cut indices below the next cut rank are
orthonormal after summing over the current singular index and physical value. -/
theorem g10g_link_gram (c : ℕ) (hc : c + 1 ≤ n)
    (k' k'' : Fin (Fintype.card (Fin (d ^ (n - (c + 1))))))
    (hk' : (k' : ℕ) < cutRank n d ψ (c + 1)) (hk'' : (k'' : ℕ) < cutRank n d ψ (c + 1)) :
    ∑ y : Fin d, ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
      star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y
      = if k' = k'' then (1 : ℂ) else 0 := by
  have hR : (∑ w : Fin (c + 1) → Fin d,
        star (g10gL ψ (c + 1) k' w) * g10gL ψ (c + 1) k'' w)
      = ∑ u : Fin c → Fin d, ∑ y : Fin d,
          star (g10gL ψ (c + 1) k' (g10g_snoc u y)) * g10gL ψ (c + 1) k'' (g10g_snoc u y) := by
    have h1 : (∑ w : Fin (c + 1) → Fin d,
          star (g10gL ψ (c + 1) k' w) * g10gL ψ (c + 1) k'' w)
        = ∑ p : (Fin c → Fin d) × Fin d,
            star (g10gL ψ (c + 1) k' (g10g_snocEquiv (c := c) p))
              * g10gL ψ (c + 1) k'' (g10g_snocEquiv p) :=
      (Fintype.sum_equiv (g10g_snocEquiv (c := c) (d := d)) _ _ (fun _ => rfl)).symm
    rw [h1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rfl
  have hexp : ∀ (u : Fin c → Fin d) (y : Fin d),
      g10gL ψ (c + 1) k' (g10g_snoc u y)
        = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            g10gL ψ c k u * g10gLink ψ c k' k y := fun u y => g10g_expand_link ψ c hc k' u y
  have hexp2 : ∀ (u : Fin c → Fin d) (y : Fin d),
      g10gL ψ (c + 1) k'' (g10g_snoc u y)
        = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            g10gL ψ c k u * g10gLink ψ c k'' k y := fun u y => g10g_expand_link ψ c hc k'' u y
  have hcoll : (∑ y : Fin d, ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
        star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y)
      = ∑ w : Fin (c + 1) → Fin d,
          star (g10gL ψ (c + 1) k' w) * g10gL ψ (c + 1) k'' w := by
    rw [hR]
    have hterm : ∀ (u : Fin c → Fin d) (y : Fin d),
        star (g10gL ψ (c + 1) k' (g10g_snoc u y)) * g10gL ψ (c + 1) k'' (g10g_snoc u y)
          = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
              ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
                (star (g10gLink ψ c k' k y) * star (g10gL ψ c k u))
                  * (g10gL ψ c j u * g10gLink ψ c k'' j y) := by
      intro u y
      rw [hexp, hexp2, star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [star_mul]
    rw [show (∑ u : Fin c → Fin d, ∑ y : Fin d,
          star (g10gL ψ (c + 1) k' (g10g_snoc u y)) * g10gL ψ (c + 1) k'' (g10g_snoc u y))
        = ∑ u : Fin c → Fin d, ∑ y : Fin d,
            ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
              ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
                (star (g10gLink ψ c k' k y) * star (g10gL ψ c k u))
                  * (g10gL ψ c j u * g10gLink ψ c k'' j y) from
      Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun y _ => hterm u y))]
    rw [g10g_sum_swap (Finset.univ : Finset (Fin (Fintype.card (Fin (d ^ (n - c))))))
        (Finset.univ : Finset (Fin (Fintype.card (Fin (d ^ (n - c))))))]
    have hfac : ∀ k j : Fin (Fintype.card (Fin (d ^ (n - c)))),
        (∑ u : Fin c → Fin d, ∑ y : Fin d,
            (star (g10gLink ψ c k' k y) * star (g10gL ψ c k u))
              * (g10gL ψ c j u * g10gLink ψ c k'' j y))
          = (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c j u)
              * (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' j y) := by
      intro k j
      have hsplit : ∀ (u : Fin c → Fin d) (y : Fin d),
          (star (g10gLink ψ c k' k y) * star (g10gL ψ c k u))
            * (g10gL ψ c j u * g10gLink ψ c k'' j y)
          = (star (g10gL ψ c k u) * g10gL ψ c j u)
              * (star (g10gLink ψ c k' k y) * g10gLink ψ c k'' j y) := by
        intro u y
        ring
      rw [show (∑ u : Fin c → Fin d, ∑ y : Fin d,
            (star (g10gLink ψ c k' k y) * star (g10gL ψ c k u))
              * (g10gL ψ c j u * g10gLink ψ c k'' j y))
          = ∑ u : Fin c → Fin d, ∑ y : Fin d,
              (star (g10gL ψ c k u) * g10gL ψ c j u)
                * (star (g10gLink ψ c k' k y) * g10gLink ψ c k'' j y) from
        Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun y _ => hsplit u y))]
      exact (Finset.sum_mul_sum (Finset.univ : Finset (Fin c → Fin d))
        (Finset.univ : Finset (Fin d)) _ _).symm
    rw [show (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
            ∑ u : Fin c → Fin d, ∑ y : Fin d,
              (star (g10gLink ψ c k' k y) * star (g10gL ψ c k u))
                * (g10gL ψ c j u * g10gLink ψ c k'' j y))
        = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
              (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c j u)
                * (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' j y) from
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hfac k j))]

    have hU : ∀ k j : Fin (Fintype.card (Fin (d ^ (n - c)))),
        (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c j u) * (∑ y : Fin d,
            star (g10gLink ψ c k' k y) * g10gLink ψ c k'' j y)
          = if k = j then (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y) else 0 := by
      intro k j
      by_cases heq : k = j
      · subst heq
        by_cases hk : (k : ℕ) < cutRank n d ψ c
        · have hUk : (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c k u) = (1 : ℂ) := by
            rw [g10gL_gram]
            simp [hk]
          rw [hUk, ite_eq_left rfl, one_mul]
        · have hY : (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y) = 0 := by
            apply Finset.sum_eq_zero
            intro y _hy
            rw [g10gLink_eq_zero_of_cutRank_le_left ψ hc (by omega : cutRank n d ψ c ≤ k) k' y]
            simp
          rw [hY, mul_zero, ite_eq_left rfl]
      · have hgram := g10gL_gram ψ c k j
        have hne : ¬(k = j ∧ (k : ℕ) < cutRank n d ψ c) := by
          intro h
          exact heq h.1
        rw [ite_eq_right hne] at hgram
        rw [hgram, zero_mul, ite_eq_right heq]
    rw [show (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
            (∑ u : Fin c → Fin d, star (g10gL ψ c k u) * g10gL ψ c j u)
              * (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' j y))
        = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
              if k = j then (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y) else 0 from
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hU k j))]
    have hcoll2 : (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          ∑ j : Fin (Fintype.card (Fin (d ^ (n - c)))),
            if k = j then (∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y) else 0)
        = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
            ∑ y : Fin d, star (g10gLink ψ c k' k y) * g10gLink ψ c k'' k y := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_ite_eq]
      simp
    rw [hcoll2]
    exact Finset.sum_comm
  rw [hcoll]
  exact g10gL_inner_eq_ite ψ (c + 1) k' k'' hk' hk''

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- Two finite sums of a natural-indexed complex function agree when both ranges contain its
support below `K` and the function vanishes at every index at least `K`. -/
theorem g10g_sum_fin_eq_of_zero {K m m' : ℕ} (f : ℕ → ℂ) (hm : K ≤ m) (hm' : K ≤ m')
    (hz : ∀ k : ℕ, K ≤ k → f k = 0) : (∑ k : Fin m, f k) = ∑ k : Fin m', f k := by
  have h1 : (∑ k : Fin m, f k) = ∑ k ∈ Finset.range K, f k := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (Finset.sum_subset (Finset.range_mono hm)
      (fun k _ hnot => hz k (Nat.le_of_not_lt (fun h => hnot (Finset.mem_range.mpr h))))).symm
  have h2 : (∑ k : Fin m', f k) = ∑ k ∈ Finset.range K, f k := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (Finset.sum_subset (Finset.range_mono hm')
      (fun k _ hnot => hz k (Nat.le_of_not_lt (fun h => hnot (Finset.mem_range.mpr h))))).symm
  exact h1.trans h2.symm

/-- A product indexed by `Fin (m + 1)` factors into the product over its first `m` indices and
its final factor. -/
theorem g10g_prod_fin_succ {m : ℕ} {α : Type} [CommMonoid α] (g : Fin (m + 1) → α) :
    (∏ i : Fin (m + 1), g i) = (∏ i : Fin m, g ⟨(i : ℕ), by omega⟩) * g ⟨m, by omega⟩ := by
  set f : ℕ → α := fun k => if h : k < m + 1 then g ⟨k, h⟩ else 1
  have hf1 : ∀ i : Fin (m + 1), f i = g i := by
    intro i
    show (if h : (i : ℕ) < m + 1 then g ⟨(i : ℕ), h⟩ else 1) = g i
    rw [dite_eq_left i.isLt]
  have hf2 : ∀ (k : ℕ) (hk : k < m), f k = g ⟨k, by omega⟩ := by
    intro k hk
    show (if h : k < m + 1 then g ⟨k, h⟩ else 1) = g ⟨k, by omega⟩
    rw [dite_eq_left (by omega : k < m + 1)]
  have hL : (∏ i : Fin (m + 1), g i) = ∏ k ∈ Finset.range (m + 1), f k := by
    rw [← Fin.prod_univ_eq_prod_range f (m + 1)]
    exact Finset.prod_congr rfl (fun i _ => (hf1 i).symm)
  have hM : (∏ i : Fin m, g ⟨(i : ℕ), by omega⟩) = ∏ k ∈ Finset.range m, f k := by
    rw [← Fin.prod_univ_eq_prod_range f m]
    exact Finset.prod_congr rfl (fun i _ => (hf2 i i.isLt).symm)
  have hm1 : f m = g ⟨m, by omega⟩ := by
    simp [f]
  rw [hL, Finset.prod_range_succ, ← hM, hm1]

/-- The first-site block formed from the cut-one left singular amplitudes, placed in rows whose
incoming bond index is zero. -/
noncomputable def g10g_site0Block (D : ℕ) :
    Matrix (Fin (D * d)) (Fin (cutRank n d ψ 1)) ℂ :=
  Matrix.of fun p j =>
    if (((finProdFinEquiv (m := D) (n := d)).symm p).1 : ℕ) = 0 then
      g10gL ψ 1 (j : ℕ) (fun _ => ((finProdFinEquiv (m := D) (n := d)).symm p).2)
    else 0

/-- An entry of the first-site block is the matching cut-one left singular amplitude when the
incoming bond index is zero, and is zero otherwise. -/
theorem g10g_site0Block_apply (D : ℕ) (p : Fin (D * d)) (j : Fin (cutRank n d ψ 1)) :
    g10g_site0Block ψ D p j
      = if (((finProdFinEquiv (m := D) (n := d)).symm p).1 : ℕ) = 0 then
        g10gL ψ 1 (j : ℕ) (fun _ => ((finProdFinEquiv (m := D) (n := d)).symm p).2) else 0 :=
  rfl

/-- The first-site block has orthonormal columns when the cut-one rank is at most `D`. -/
theorem g10g_site0Block_gram {D : ℕ} (hr : cutRank n d ψ 1 ≤ D) :
    (g10g_site0Block ψ D)ᴴ * g10g_site0Block ψ D = 1 := by
  refine eq_one_of_gram_apply _ (fun j₁ j₂ => ?_)
  obtain rfl | hDpos : D = 0 ∨ 0 < D := Nat.eq_zero_or_pos D
  · have hle : cutRank n d ψ 1 = 0 := by omega
    exact (Fin.elim0 (hle ▸ j₁))
  · have : NeZero D := ⟨by omega⟩
    have hsum : (∑ p : Fin (D * d), star (g10g_site0Block ψ D p j₁) * g10g_site0Block ψ D p j₂)
        = ∑ a : Fin D, ∑ y : Fin d,
            star (g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (a, y)) j₁)
              * g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (a, y)) j₂ := by
      have h1 : (∑ p : Fin (D * d), star (g10g_site0Block ψ D p j₁) * g10g_site0Block ψ D p j₂)
          = ∑ q : Fin D × Fin d,
              star (g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) q) j₁)
                * g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) q) j₂ :=
        (Fintype.sum_equiv (finProdFinEquiv (m := D) (n := d))
          (fun q : Fin D × Fin d =>
            star (g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) q) j₁)
              * g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) q) j₂)
          (fun p => star (g10g_site0Block ψ D p j₁) * g10g_site0Block ψ D p j₂)
          (fun _ => rfl)).symm
      rw [h1]
      exact Fintype.sum_prod_type _
    rw [hsum]
    have hite : ∀ a : Fin D, ∀ y : Fin d,
        (star (g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (a, y)) j₁)
            * g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (a, y)) j₂)
          = if (a : ℕ) = 0 then
            star (g10gL ψ 1 (j₁ : ℕ) (fun _ => y)) * g10gL ψ 1 (j₂ : ℕ) (fun _ => y) else 0 := by
      intro a y
      rw [g10g_site0Block_apply, g10g_site0Block_apply]
      by_cases ha : (a : ℕ) = 0
      · simp [ha]
      · simp [ha]
    rw [show (∑ a : Fin D, ∑ y : Fin d,
          star (g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (a, y)) j₁)
            * g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (a, y)) j₂)
        = ∑ a : Fin D, ∑ y : Fin d,
            (if (a : ℕ) = 0 then
              star (g10gL ψ 1 (j₁ : ℕ) (fun _ => y)) * g10gL ψ 1 (j₂ : ℕ) (fun _ => y) else 0) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun y _ => hite a y))]
    have hsum0 : (∑ a : Fin D, ∑ y : Fin d,
          (if (a : ℕ) = 0 then
            star (g10gL ψ 1 (j₁ : ℕ) (fun _ => y)) * g10gL ψ 1 (j₂ : ℕ) (fun _ => y) else 0))
        = ∑ y : Fin d, star (g10gL ψ 1 (j₁ : ℕ) (fun _ => y)) * g10gL ψ 1 (j₂ : ℕ) (fun _ => y) := by
      rw [Finset.sum_eq_single (0 : Fin D)]
      · simp
      · intro a _ha ha
        exact Finset.sum_eq_zero (fun y _ => ite_eq_right (by exact_mod_cast ha))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum0]
    have hinner : (∑ y : Fin d,
          star (g10gL ψ 1 (j₁ : ℕ) (fun _ => y)) * g10gL ψ 1 (j₂ : ℕ) (fun _ => y))
        = ∑ u : Fin 1 → Fin d, star (g10gL ψ 1 (j₁ : ℕ) u) * g10gL ψ 1 (j₂ : ℕ) u :=
      (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d))
        (fun u : Fin 1 → Fin d => star (g10gL ψ 1 (j₁ : ℕ) u) * g10gL ψ 1 (j₂ : ℕ) u)
        (fun y => star (g10gL ψ 1 (j₁ : ℕ) (fun _ => y)) * g10gL ψ 1 (j₂ : ℕ) (fun _ => y))
        (fun u => congrArg (fun w => star (g10gL ψ 1 (j₁ : ℕ) w) * g10gL ψ 1 (j₂ : ℕ) w)
          (funext (fun k => congrArg u (Subsingleton.elim k default))))).symm
    rw [hinner]
    set q₁ : Fin (Fintype.card (Fin (d ^ (n - 1)))) := ⟨(j₁ : ℕ), by
      have h1 := j₁.isLt
      have h2 := cutRank_le_pow_right ψ 1
      have h3 : Fintype.card (Fin (d ^ (n - 1))) = d ^ (n - 1) := Fintype.card_fin _
      omega⟩
    set q₂ : Fin (Fintype.card (Fin (d ^ (n - 1)))) := ⟨(j₂ : ℕ), by
      have h1 := j₂.isLt
      have h2 := cutRank_le_pow_right ψ 1
      have h3 : Fintype.card (Fin (d ^ (n - 1))) = d ^ (n - 1) := Fintype.card_fin _
      omega⟩
    have hcast : (∑ u : Fin 1 → Fin d, star (g10gL ψ 1 (j₁ : ℕ) u) * g10gL ψ 1 (j₂ : ℕ) u)
        = ∑ u : Fin 1 → Fin d, star (g10gL ψ 1 q₁ u) * g10gL ψ 1 q₂ u := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rfl
    rw [hcast, g10gL_gram ψ 1 q₁ q₂]
    have hj₁ : (q₁ : ℕ) < cutRank n d ψ 1 := by
      show (j₁ : ℕ) < cutRank n d ψ 1
      exact j₁.isLt
    have hiff : (q₁ = q₂) ↔ (j₁ = j₂) := by
      constructor
      · intro h
        apply Fin.ext
        have h1 := congrArg Fin.val h
        simpa [q₁, q₂] using! h1
      · intro h
        apply Fin.ext
        show (j₁ : ℕ) = (j₂ : ℕ)
        exact congrArg Fin.val h
    simp only [hiff]
    simp [hj₁]

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The site block whose rows combine the incoming bond and physical indices and whose columns
are link coefficients indexed below the next cut rank. -/
noncomputable def g10g_siteIBlock (i : ℕ) (_hi : i + 1 ≤ n) (D : ℕ) :
    Matrix (Fin (D * d)) (Fin (cutRank n d ψ (i + 1))) ℂ :=
  Matrix.of fun p j =>
    g10gLink ψ i (j : ℕ)
      (((finProdFinEquiv (m := D) (n := d)).symm p).1 : ℕ)
      ((finProdFinEquiv (m := D) (n := d)).symm p).2

/-- An entry of the site block equals the link coefficient obtained by unpacking its row into
incoming bond and physical indices. -/
theorem g10g_siteIBlock_apply (i : ℕ) (_hi : i + 1 ≤ n) (D : ℕ)
    (p : Fin (D * d)) (j : Fin (cutRank n d ψ (i + 1))) :
    g10g_siteIBlock ψ i _hi D p j
      = g10gLink ψ i (j : ℕ)
          (((finProdFinEquiv (m := D) (n := d)).symm p).1 : ℕ)
          ((finProdFinEquiv (m := D) (n := d)).symm p).2 :=
  rfl

/-- The site block at a valid cut has orthonormal columns when `D` contains the current cut
rank. -/
theorem g10g_siteIBlock_gram (i : ℕ) (hi : i + 1 ≤ n) (D : ℕ)
    (hri : cutRank n d ψ i ≤ D) :
    (g10g_siteIBlock ψ i hi D)ᴴ * g10g_siteIBlock ψ i hi D = 1 := by
  refine eq_one_of_gram_apply _ (fun j₁ j₂ => ?_)
  have hkey : (∑ p : Fin (D * d),
        star (g10g_siteIBlock ψ i hi D p j₁) * g10g_siteIBlock ψ i hi D p j₂)
      = ∑ y : Fin d, ∑ k : Fin (Fintype.card (Fin (d ^ (n - i)))),
          star (g10gLink ψ i (j₁ : ℕ) k y) * g10gLink ψ i (j₂ : ℕ) k y := by
    have h1 : (∑ p : Fin (D * d),
          star (g10g_siteIBlock ψ i hi D p j₁) * g10g_siteIBlock ψ i hi D p j₂)
        = ∑ q : Fin D × Fin d,
            star (g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) q) j₁)
              * g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) q) j₂ :=
      (Fintype.sum_equiv (finProdFinEquiv (m := D) (n := d))
        (fun q : Fin D × Fin d =>
          star (g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) q) j₁)
            * g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) q) j₂)
        (fun p => star (g10g_siteIBlock ψ i hi D p j₁) * g10g_siteIBlock ψ i hi D p j₂)
        (fun _ => rfl)).symm
    rw [h1, Fintype.sum_prod_type]
    have hite : ∀ a : Fin D, ∀ y : Fin d,
        (star (g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) (a, y)) j₁)
            * g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) (a, y)) j₂)
          = star (g10gLink ψ i (j₁ : ℕ) (a : ℕ) y) * g10gLink ψ i (j₂ : ℕ) (a : ℕ) y := by
      intro a y
      rw [g10g_siteIBlock_apply, g10g_siteIBlock_apply, Equiv.symm_apply_apply]
    rw [show (∑ a : Fin D, ∑ y : Fin d,
          star (g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) (a, y)) j₁)
            * g10g_siteIBlock ψ i hi D (finProdFinEquiv (m := D) (n := d) (a, y)) j₂)
        = ∑ a : Fin D, ∑ y : Fin d,
            star (g10gLink ψ i (j₁ : ℕ) (a : ℕ) y) * g10gLink ψ i (j₂ : ℕ) (a : ℕ) y from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun y _ => hite a y))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hz : ∀ k : ℕ, cutRank n d ψ i ≤ k →
        (star (g10gLink ψ i (j₁ : ℕ) k y) * g10gLink ψ i (j₂ : ℕ) k y) = 0 := by
      intro k hk
      rw [g10gLink_eq_zero_of_cutRank_le_left ψ hi hk j₁ y]
      simp
    exact g10g_sum_fin_eq_of_zero
      (fun k => star (g10gLink ψ i (j₁ : ℕ) k y) * g10gLink ψ i (j₂ : ℕ) k y)
      hri ((cutRank_le_pow_right ψ i).trans (le_of_eq (Fintype.card_fin _).symm)) hz
  rw [hkey]
  have hcard : Fintype.card (Fin (d ^ (n - (i + 1)))) = d ^ (n - (i + 1)) := Fintype.card_fin _
  have hq₁ : (j₁ : ℕ) < Fintype.card (Fin (d ^ (n - (i + 1)))) := by
    have h1 := j₁.isLt
    have h2 := cutRank_le_pow_right ψ (i + 1)
    omega
  have hq₂ : (j₂ : ℕ) < Fintype.card (Fin (d ^ (n - (i + 1)))) := by
    have h1 := j₂.isLt
    have h2 := cutRank_le_pow_right ψ (i + 1)
    omega
  set q₁ : Fin (Fintype.card (Fin (d ^ (n - (i + 1))))) := ⟨(j₁ : ℕ), hq₁⟩
  set q₂ : Fin (Fintype.card (Fin (d ^ (n - (i + 1))))) := ⟨(j₂ : ℕ), hq₂⟩
  have hcast : (∑ y : Fin d, ∑ k : Fin (Fintype.card (Fin (d ^ (n - i)))),
        star (g10gLink ψ i (j₁ : ℕ) k y) * g10gLink ψ i (j₂ : ℕ) k y)
      = ∑ y : Fin d, ∑ k : Fin (Fintype.card (Fin (d ^ (n - i)))),
          star (g10gLink ψ i q₁ k y) * g10gLink ψ i q₂ k y := by
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun k _ => ?_))
    rfl
  rw [hcast]
  have hgr := g10g_link_gram ψ i hi q₁ q₂ (by
    show (j₁ : ℕ) < cutRank n d ψ (i + 1)
    exact j₁.isLt) (by
    show (j₂ : ℕ) < cutRank n d ψ (i + 1)
    exact j₂.isLt)
  have hiff : (q₁ = q₂) ↔ (j₁ = j₂) := by
    constructor
    · intro h
      apply Fin.ext
      have h1 := congrArg Fin.val h
      simpa [q₁, q₂] using! h1
    · intro h
      apply Fin.ext
      show (j₁ : ℕ) = (j₂ : ℕ)
      exact congrArg Fin.val h
  simp only [hiff] at hgr
  exact hgr

/-- An isometric extension of the first-site block to `D` columns, chosen when the cut-one rank
is at most `D` and the physical dimension is positive. -/
noncomputable def g10g_site0Ext {D : ℕ} (hr : cutRank n d ψ 1 ≤ D) (hd : 0 < d) :
    Matrix (Fin (D * d)) (Fin D) ℂ :=
  Classical.choose (exists_isometry_extend hr hd (g10g_site0Block ψ D) (g10g_site0Block_gram ψ hr))

/-- The chosen extension of the first-site block has orthonormal columns. -/
theorem g10g_site0Ext_gram {D : ℕ} {hr : cutRank n d ψ 1 ≤ D} {hd : 0 < d} :
    (g10g_site0Ext ψ hr hd)ᴴ * g10g_site0Ext ψ hr hd = 1 :=
  (Classical.choose_spec
    (exists_isometry_extend hr hd (g10g_site0Block ψ D) (g10g_site0Block_gram ψ hr))).1

/-- On columns below the cut-one rank, the chosen first-site extension agrees with the original
first-site block. -/
theorem g10g_site0Ext_apply {D : ℕ} {hr : cutRank n d ψ 1 ≤ D} {hd : 0 < d}
    (p : Fin (D * d)) (j : Fin (cutRank n d ψ 1)) :
    g10g_site0Ext ψ hr hd p ⟨(j : ℕ), lt_of_lt_of_le j.isLt hr⟩ = g10g_site0Block ψ D p j :=
  (Classical.choose_spec
    (exists_isometry_extend hr hd (g10g_site0Block ψ D) (g10g_site0Block_gram ψ hr))).2 j p

/-- An isometric extension of the link-based site block to `D` columns, assuming both adjacent
cut ranks are at most `D` and the physical dimension is positive. -/
noncomputable def g10g_siteIExt (i : ℕ) (hi : i + 1 ≤ n) {D : ℕ}
    (hri : cutRank n d ψ i ≤ D) (hr : cutRank n d ψ (i + 1) ≤ D) (hd : 0 < d) :
    Matrix (Fin (D * d)) (Fin D) ℂ :=
  Classical.choose (exists_isometry_extend hr hd (g10g_siteIBlock ψ i hi D)
    (g10g_siteIBlock_gram ψ i hi D hri))

/-- The chosen extension of a link-based site block has orthonormal columns. -/
theorem g10g_siteIExt_gram (i : ℕ) (hi : i + 1 ≤ n) {D : ℕ}
    {hri : cutRank n d ψ i ≤ D} {hr : cutRank n d ψ (i + 1) ≤ D} {hd : 0 < d} :
    (g10g_siteIExt ψ i hi hri hr hd)ᴴ * g10g_siteIExt ψ i hi hri hr hd = 1 :=
  (Classical.choose_spec (exists_isometry_extend hr hd (g10g_siteIBlock ψ i hi D)
    (g10g_siteIBlock_gram ψ i hi D hri))).1

/-- On columns below the next cut rank, the chosen site extension agrees with its original
link-based block. -/
theorem g10g_siteIExt_apply (i : ℕ) (hi : i + 1 ≤ n) {D : ℕ}
    {hri : cutRank n d ψ i ≤ D} {hr : cutRank n d ψ (i + 1) ≤ D} {hd : 0 < d}
    (p : Fin (D * d)) (j : Fin (cutRank n d ψ (i + 1))) :
    g10g_siteIExt ψ i hi hri hr hd p ⟨(j : ℕ), lt_of_lt_of_le j.isLt hr⟩
      = g10g_siteIBlock ψ i hi D p j :=
  (Classical.choose_spec (exists_isometry_extend hr hd (g10g_siteIBlock ψ i hi D)
    (g10g_siteIBlock_gram ψ i hi D hri))).2 j p

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The MPS tensor chain assembled from the extended first-site and intermediate isometries,
with the weighted right singular amplitude closing the final boundary. It is defined for at
least two sites, positive physical dimension, and a bond dimension bounding every cut rank
before `n`. -/
noncomputable def g10g_chainA (D : ℕ) (_h2 : 2 ≤ n) (hd : 0 < d)
    (hle : ∀ c, c < n → cutRank n d ψ c ≤ D) :
    Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i y => Matrix.of fun a b =>
    if h0 : (i : ℕ) = 0 then
      g10g_site0Ext ψ (hle 1 (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b
    else if hn1 : (i : ℕ) = n - 1 then
      if (b : ℕ) = 0 then g10gS ψ (n - 1) (a : ℕ) (fun _ => y) else 0
    else
      g10g_siteIExt ψ i (by omega) (hle i (by omega)) (hle (i + 1) (by omega)) hd
        (finProdFinEquiv (m := D) (n := d) (a, y)) b

/-- Entries of the constructed chain are given by the first-site extension, the final weighted
right singular amplitude in column zero, or the intermediate extension according to the site
index. -/
theorem g10g_chainA_apply {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (i : Fin n) (y : Fin d) (a b : Fin D) :
    g10g_chainA ψ D h2 hd hle i y a b
      = if _h0 : (i : ℕ) = 0 then
          g10g_site0Ext ψ (hle 1 (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b
        else if hn1 : (i : ℕ) = n - 1 then
          if (b : ℕ) = 0 then g10gS ψ (n - 1) (a : ℕ) (fun _ => y) else 0
        else
          g10g_siteIExt ψ i (by omega) (hle i (by omega)) (hle (i + 1) (by omega)) hd
            (finProdFinEquiv (m := D) (n := d) (a, y)) b :=
  rfl

/-- At site zero, the constructed MPS chain equals the packed first-site isometric extension. -/
theorem g10g_chainA_zero {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (y : Fin d) (a b : Fin D) :
    g10g_chainA ψ D h2 hd hle ⟨0, by omega⟩ y a b
      = g10g_site0Ext ψ (hle 1 (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b := by
  rw [g10g_chainA_apply]
  exact dite_eq_left rfl

/-- At the final site, the constructed chain contains the weighted right singular amplitude in
column zero and vanishes in the other columns. -/
theorem g10g_chainA_last {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (y : Fin d) (a b : Fin D) :
    g10g_chainA ψ D h2 hd hle ⟨n - 1, by omega⟩ y a b
      = if (b : ℕ) = 0 then g10gS ψ (n - 1) (a : ℕ) (fun _ => y) else 0 := by
  rw [g10g_chainA_apply]
  have hval : (((⟨n - 1, by omega⟩ : Fin n) : ℕ) = n - 1) := rfl
  have h0 : ¬(((⟨n - 1, by omega⟩ : Fin n) : ℕ) = 0) := by
    rw [hval]
    omega
  have hn1 : (((⟨n - 1, by omega⟩ : Fin n) : ℕ) = n - 1) := rfl
  rw [dite_eq_right h0, dite_eq_left hn1]

/-- At a site strictly between the first and final sites, the constructed chain equals the
packed intermediate isometric extension. -/
theorem g10g_chainA_mid {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} {i : Fin n}
    (hi0 : (0 : ℕ) < i) (hi1 : (i : ℕ) + 1 < n) (y : Fin d) (a b : Fin D) :
    g10g_chainA ψ D h2 hd hle i y a b
      = g10g_siteIExt ψ i (by omega) (hle i (by omega)) (hle (i + 1) (by omega)) hd
          (finProdFinEquiv (m := D) (n := d) (a, y)) b := by
  rw [g10g_chainA_apply]
  rw [dite_eq_right (by omega : ¬(i : ℕ) = 0), dite_eq_right (by omega : ¬(i : ℕ) = n - 1)]

/-- At site zero and incoming boundary index zero, a column below the first cut rank equals the
corresponding left singular amplitude. -/
theorem g10g_chainA_zero_used {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (y : Fin d) {b : Fin D}
    (hb : (b : ℕ) < cutRank n d ψ 1) :
    g10g_chainA ψ D h2 hd hle ⟨0, by omega⟩ y ⟨0, by omega⟩ b = g10gL ψ 1 (b : ℕ) (fun _ => y) := by
  rw [g10g_chainA_zero]
  have happ : g10g_site0Ext ψ (hle 1 (by omega)) hd
      (finProdFinEquiv (m := D) (n := d) (⟨0, by omega⟩, y)) b
      = g10g_site0Block ψ D (finProdFinEquiv (m := D) (n := d) (⟨0, by omega⟩, y)) ⟨(b : ℕ), hb⟩ :=
    g10g_site0Ext_apply ψ (j := ⟨(b : ℕ), hb⟩) _
  rw [happ, g10g_site0Block_apply]
  have hp : (finProdFinEquiv (m := D) (n := d)).symm
      (finProdFinEquiv (m := D) (n := d) (⟨0, by omega⟩, y)) = (⟨0, by omega⟩, y) :=
    (finProdFinEquiv (m := D) (n := d)).symm_apply_apply _
  rw [hp]
  simp

/-- At an intermediate site, columns below the next cut rank of the constructed tensor equal the
corresponding link coefficients. -/
theorem g10g_chainA_mid_used {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} {i : Fin n}
    (hi0 : (0 : ℕ) < i) (hi1 : (i : ℕ) + 1 < n) (y : Fin d) (a : Fin D) {b : Fin D}
    (hb : (b : ℕ) < cutRank n d ψ (i + 1)) :
    g10g_chainA ψ D h2 hd hle i y a b = g10gLink ψ i (b : ℕ) (a : ℕ) y := by
  rw [show g10g_chainA ψ D h2 hd hle i y a b
      = g10g_siteIExt ψ i (by omega) (hle i (by omega)) (hle (i + 1) (by omega)) hd
          (finProdFinEquiv (m := D) (n := d) (a, y)) b from @g10g_chainA_mid n d ψ D h2 hd hle i hi0 hi1 y a b]
  have happ : g10g_siteIExt ψ i (by omega) (hle i (by omega)) (hle (i + 1) (by omega)) hd
      (finProdFinEquiv (m := D) (n := d) (a, y)) b
      = g10g_siteIBlock ψ i (by omega) D (finProdFinEquiv (m := D) (n := d) (a, y)) ⟨(b : ℕ), hb⟩ :=
    g10g_siteIExt_apply ψ i (by omega) (j := ⟨(b : ℕ), hb⟩) _
  rw [happ, g10g_siteIBlock_apply]
  have hp : (finProdFinEquiv (m := D) (n := d)).symm
      (finProdFinEquiv (m := D) (n := d) (a, y)) = (a, y) :=
    (finProdFinEquiv (m := D) (n := d)).symm_apply_apply _
  rw [hp]

/-- At an intermediate site, a tensor entry vanishes when its incoming index is at least the
current cut rank and its outgoing index is below the next cut rank. -/
theorem g10g_chainA_mid_eq_zero_of_cutRank_le {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} {i : Fin n}
    (hi0 : (0 : ℕ) < i) (hi1 : (i : ℕ) + 1 < n) (y : Fin d) (a : Fin D) {b : Fin D}
    (ha : cutRank n d ψ i ≤ (a : ℕ)) (hb : (b : ℕ) < cutRank n d ψ (i + 1)) :
    g10g_chainA ψ D h2 hd hle i y a b = 0 := by
  rw [show g10g_chainA ψ D h2 hd hle i y a b = g10gLink ψ i (b : ℕ) (a : ℕ) y from
    @g10g_chainA_mid_used n d ψ D h2 hd hle i hi0 hi1 y a b hb]
  exact g10gLink_eq_zero_of_cutRank_le_left ψ (by omega) ha (b : ℕ) y

/-- In boundary column zero, the final tensor of the constructed chain equals the weighted right
singular amplitude at the last cut. -/
theorem g10g_chainA_last_col {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (y : Fin d) (a b : Fin D)
    (hb : (b : ℕ) = 0) :
    g10g_chainA ψ D h2 hd hle ⟨n - 1, by omega⟩ y a b
      = g10gS ψ (n - 1) (a : ℕ) (fun _ => y) := by
  rw [g10g_chainA_last]
  simp [hb]

/-- An entry in boundary column zero of the final tensor vanishes when its incoming index is at
least the last cut rank. -/
theorem g10g_chainA_last_eq_zero_of_cutRank_le {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (y : Fin d) (a b : Fin D)
    (ha : cutRank n d ψ (n - 1) ≤ (a : ℕ)) (hb : (b : ℕ) = 0) :
    g10g_chainA ψ D h2 hd hle ⟨n - 1, by omega⟩ y a b = 0 := by
  rw [g10g_chainA_last_col ψ y a b hb]
  exact g10gS_eq_zero_of_cutRank_le ψ ha (fun _ => y)

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The sequential contraction of an MPS prefix with a fixed physical configuration and a free
outgoing bond. Its initial value is the indicator of bond index zero, and a step beyond the
chain returns zero. -/
noncomputable def g10g_contr {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) : ℕ → Fin D → ℂ
  | 0, k => if (k : ℕ) = 0 then (1 : ℂ) else 0
  | m + 1, k => if h : m < n then
      ∑ j : Fin D, g10g_contr A x m j * A ⟨m, h⟩ (x ⟨m, h⟩) j k
    else 0

/-- The initial prefix contraction is one at bond index zero and zero at every other bond index. -/
theorem g10g_contr_zero {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (k : Fin D) :
    g10g_contr A x 0 k = if (k : ℕ) = 0 then (1 : ℂ) else 0 := rfl

/-- For a site within the chain, extending a prefix contraction multiplies by the site's tensor
and sums over the previous outgoing bond. -/
theorem g10g_contr_succ {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (m : ℕ) (hm : m < n) (k : Fin D) :
    g10g_contr A x (m + 1) k
      = ∑ j : Fin D, g10g_contr A x m j * A ⟨m, hm⟩ (x ⟨m, hm⟩) j k := by
  show (if h : m < n then
      ∑ j : Fin D, g10g_contr A x m j * A ⟨m, h⟩ (x ⟨m, h⟩) j k else 0)
    = ∑ j : Fin D, g10g_contr A x m j * A ⟨m, hm⟩ (x ⟨m, hm⟩) j k
  rw [dite_eq_left hm]

/-- The explicit sum over all bond assignments of a length-`m` prefix, constrained to start at
zero and end at `k`, equals its sequential contraction at `k`. -/
theorem g10g_contr_freeEnd {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) :
    ∀ (m : ℕ) (_hm : m ≤ n) (k : Fin D),
      ∑ β : Fin (m + 1) → Fin D,
          ((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(m : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0)
        = g10g_contr A x m k := by
  intro m
  induction m with
  | zero =>
    intro _hm k
    have hprod : ∀ β : Fin (0 + 1) → Fin D,
        (∏ i : Fin 0, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
            (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩)) = (1 : ℂ) := by
      intro β
      refine Finset.prod_eq_one (fun i _ => ?_)
      exact Fin.elim0 i
    have hsum : (∑ β : Fin (0 + 1) → Fin D,
          ((∏ i : Fin 0, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(0 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0))
        = ∑ y : Fin D, (if (y : ℕ) = 0 then (1 : ℂ) else 0)
            * (if y = k then (1 : ℂ) else 0) := by
      have h1 := Equiv.sum_comp ((Equiv.funUnique (Fin 1) (Fin D)).symm)
        (fun β : Fin (0 + 1) → Fin D =>
          ((∏ i : Fin 0, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(0 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0))
      rw [← h1]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hprod _, one_mul]
      rfl
    rw [hsum, Finset.sum_eq_single k]
    · rw [ite_eq_left rfl, mul_one, g10g_contr_zero]
    · intro y _ hy
      rw [ite_eq_right hy, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | succ m ih =>
    intro hm k
    have hmn : m < n := by omega
    have hprod : ∀ β : Fin (m + 2) → Fin D,
        (∏ i : Fin (m + 1), A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
            (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
          = (∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (β ⟨m, by omega⟩) (β ⟨m + 1, by omega⟩) := by
      intro β
      exact g10g_prod_fin_succ (m := m) (α := ℂ)
        (fun i => A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
          (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
    rw [show (∑ β : Fin (m + 2) → Fin D,
          ((∏ i : Fin (m + 1), A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0))
        = ∑ β : Fin (m + 2) → Fin D,
            (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
              * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (β ⟨m, by omega⟩) (β ⟨m + 1, by omega⟩))
              * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
              * (if (β ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0) from
      Finset.sum_congr rfl (fun β _ => by rw [hprod β])]

    have hsnoc : (∑ β : Fin (m + 2) → Fin D,
          (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
            * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (β ⟨m, by omega⟩) (β ⟨m + 1, by omega⟩))
            * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * (if (β ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0))
        = ∑ rest : Fin (m + 1) → Fin D, ∑ last : Fin D,
            (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                ((g10g_snoc rest last) ⟨(i : ℕ), by omega⟩)
                ((g10g_snoc rest last) ⟨(i : ℕ) + 1, by omega⟩))
              * A ⟨m, by omega⟩ (x ⟨m, by omega⟩)
                ((g10g_snoc rest last) ⟨m, by omega⟩)
                ((g10g_snoc rest last) ⟨m + 1, by omega⟩))
              * (if ((g10g_snoc rest last) ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
              * (if ((g10g_snoc rest last) ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k
                  then (1 : ℂ) else 0) := by
      have h1 : (∑ β : Fin (m + 2) → Fin D,
            (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                (β ⟨(i : ℕ), by omega⟩) (β ⟨(i : ℕ) + 1, by omega⟩))
              * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (β ⟨m, by omega⟩) (β ⟨m + 1, by omega⟩))
              * (if (β ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
              * (if (β ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0))
          = ∑ p : (Fin (m + 1) → Fin D) × Fin D,
              (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                  ((g10g_snocEquiv (c := m + 1) (d := D) p) ⟨(i : ℕ), by omega⟩)
                  ((g10g_snocEquiv (c := m + 1) (d := D) p) ⟨(i : ℕ) + 1, by omega⟩))
                * A ⟨m, by omega⟩ (x ⟨m, by omega⟩)
                  ((g10g_snocEquiv (c := m + 1) (d := D) p) ⟨m, by omega⟩)
                  ((g10g_snocEquiv (c := m + 1) (d := D) p) ⟨m + 1, by omega⟩))
                * (if ((g10g_snocEquiv (c := m + 1) (d := D) p) ⟨0, by omega⟩ : Fin D).val = 0
                    then (1 : ℂ) else 0))
                * (if ((g10g_snocEquiv (c := m + 1) (d := D) p)
                    ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k then (1 : ℂ) else 0) :=
        (Fintype.sum_equiv (g10g_snocEquiv (c := m + 1) (d := D)) _ _ (fun _ => rfl)).symm
      rw [h1]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun rest _ => ?_)
      refine Finset.sum_congr rfl (fun last _ => ?_)
      rfl
    rw [hsnoc]
    have hval : ∀ rest : Fin (m + 1) → Fin D, ∀ last : Fin D,
        (g10g_snoc rest last) ⟨(m + 1 : ℕ), by omega⟩ = last ∧
        (g10g_snoc rest last) ⟨0, by omega⟩ = rest ⟨0, by omega⟩ ∧
        ((g10g_snoc rest last) ⟨m, by omega⟩ = rest ⟨m, by omega⟩) ∧
        (∀ i : Fin m, (g10g_snoc rest last) ⟨(i : ℕ), by omega⟩ = rest ⟨(i : ℕ), by omega⟩
          ∧ (g10g_snoc rest last) ⟨(i : ℕ) + 1, by omega⟩ = rest ⟨(i : ℕ) + 1, by omega⟩) := by
      intro rest last
      constructor
      · exact g10g_snoc_last rest last
      constructor
      · have hlt : ((⟨0, by omega⟩ : Fin (m + 2)) : ℕ) < m + 1 := by
          show (0 : ℕ) < m + 1
          omega
        exact g10g_snoc_of_lt rest last hlt
      constructor
      · have hlt : ((⟨m, by omega⟩ : Fin (m + 2)) : ℕ) < m + 1 := by
          show (m : ℕ) < m + 1
          omega
        exact g10g_snoc_of_lt rest last hlt
      · intro i
        constructor
        · have hlt : ((⟨(i : ℕ), by omega⟩ : Fin (m + 2)) : ℕ) < m + 1 := by
            show (i : ℕ) < m + 1
            have hi := i.isLt
            omega
          exact g10g_snoc_of_lt rest last hlt
        · have hlt : ((⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 2)) : ℕ) < m + 1 := by
            show (i : ℕ) + 1 < m + 1
            have hi := i.isLt
            omega
          exact g10g_snoc_of_lt rest last hlt
    have hcore : (∑ rest : Fin (m + 1) → Fin D, ∑ last : Fin D,
          (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              ((g10g_snoc rest last) ⟨(i : ℕ), by omega⟩)
              ((g10g_snoc rest last) ⟨(i : ℕ) + 1, by omega⟩))
            * A ⟨m, by omega⟩ (x ⟨m, by omega⟩)
              ((g10g_snoc rest last) ⟨m, by omega⟩)
              ((g10g_snoc rest last) ⟨m + 1, by omega⟩))
            * (if ((g10g_snoc rest last) ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * (if ((g10g_snoc rest last) ⟨(m + 1 : ℕ), by omega⟩ : Fin D) = k
                then (1 : ℂ) else 0))
        = ∑ rest : Fin (m + 1) → Fin D,
            ((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
              * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
              * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (rest ⟨m, by omega⟩) k := by
      refine Finset.sum_congr rfl (fun rest _ => ?_)
      rw [Finset.sum_eq_single (k : Fin D)]
      · have h1 := (hval rest k).1
        have h2 := (hval rest k).2.1
        have h3 := (hval rest k).2.2.1
        have h4 := (hval rest k).2.2.2
        rw [h1, h2, h3, ite_eq_left rfl, mul_one]
        have hp : (∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              ((g10g_snoc rest k) ⟨(i : ℕ), by omega⟩)
              ((g10g_snoc rest k) ⟨(i : ℕ) + 1, by omega⟩))
            = (∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩)) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          obtain ⟨ha, hb⟩ := h4 i
          rw [ha, hb]
        rw [hp]
        ring
      · intro last _ hne
        have h1 := (hval rest last).1
        rw [h1, ite_eq_right hne, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hcore]
    have hsplit : (∑ rest : Fin (m + 1) → Fin D,
          ((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
            * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (rest ⟨m, by omega⟩) k)
        = ∑ j : Fin D, (∑ rest : Fin (m + 1) → Fin D,
            ((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
              * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
              * (if (rest ⟨m, by omega⟩ : Fin D) = j then (1 : ℂ) else 0))
            * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) j k := by
      have hterm : ∀ rest : Fin (m + 1) → Fin D,
          ((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
              (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
            * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
            * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (rest ⟨m, by omega⟩) k
          = ∑ j : Fin D,
              (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                  (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
                * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
                * (if (rest ⟨m, by omega⟩ : Fin D) = j then (1 : ℂ) else 0))
              * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) j k := by
        intro rest
        rw [Finset.sum_eq_single (rest ⟨m, by omega⟩)]
        · rw [ite_eq_left rfl, mul_one]
        · intro j _ hne
          rw [ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [show (∑ rest : Fin (m + 1) → Fin D,
            ((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
              * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
              * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) (rest ⟨m, by omega⟩) k)
          = ∑ rest : Fin (m + 1) → Fin D,
              ∑ j : Fin D,
                (((∏ i : Fin m, A ⟨(i : ℕ), by omega⟩ (x ⟨(i : ℕ), by omega⟩)
                    (rest ⟨(i : ℕ), by omega⟩) (rest ⟨(i : ℕ) + 1, by omega⟩))
                  * (if (rest ⟨0, by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0))
                  * (if (rest ⟨m, by omega⟩ : Fin D) = j then (1 : ℂ) else 0))
                * A ⟨m, by omega⟩ (x ⟨m, by omega⟩) j k from
        Finset.sum_congr rfl (fun rest _ => hterm rest)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact (Finset.sum_mul ..).symm
    rw [hsplit, g10g_contr_succ A x m hmn k]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact congrArg (fun z : ℂ => z * A ⟨m, hmn⟩ (x ⟨m, hmn⟩) j k) (ih (by omega) j)

variable {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)

/-- The restriction of a configuration to its first `m` sites, assuming `m` is at most the chain
length. -/
def g10g_prefix {n d : ℕ} (x : Fin n → Fin d) (m : ℕ) (_hm : m ≤ n) : Fin m → Fin d :=
  fun i => x ⟨(i : ℕ), by omega⟩

/-- Appending the physical value at site `m` to the length-`m` prefix gives the length-`m + 1`
prefix. -/
theorem g10g_prefix_snoc {n d : ℕ} (x : Fin n → Fin d) (m : ℕ) (hm : m + 1 ≤ n) :
    g10g_snoc (g10g_prefix x m (by omega)) (x ⟨m, by omega⟩)
      = g10g_prefix x (m + 1) hm := by
  funext i
  by_cases hi : (i : ℕ) < m
  · rw [g10g_snoc_of_lt _ _ hi]
    rfl
  · have hieq : (i : ℕ) = m := by have hi' := i.isLt; omega
    have hfi : i = (⟨m, by omega⟩ : Fin (m + 1)) := Fin.ext hieq
    rw [hfi, g10g_snoc_last]
    rfl

/-- For a chain of at least two sites, joining its prefix of length `n - 1` with its final
physical value recovers the full configuration. -/
theorem g10g_splitJoin_prefix_last {n d : ℕ} (x : Fin n → Fin d) (hm : 2 ≤ n) :
    splitJoin n (n - 1) d (g10g_prefix x (n - 1) (by omega))
      (fun _ => x ⟨n - 1, by omega⟩) = x := by
  funext k
  show (if h : (k : ℕ) < n - 1 then g10g_prefix x (n - 1) (by omega) ⟨k, h⟩
        else (fun _ : Fin (n - (n - 1)) => x ⟨n - 1, by omega⟩)
          ⟨(k : ℕ) - (n - 1), by omega⟩) = x ⟨(k : ℕ), _⟩
  by_cases hk : (k : ℕ) < n - 1
  · rw [dite_eq_left hk]
    rfl
  · rw [dite_eq_right hk]
    have hke : (k : ℕ) = n - 1 := by have hk' := k.isLt; omega
    exact congrArg x (Fin.ext hke.symm)

/-- For positive bond dimension, the full sequential contraction evaluated at outgoing boundary
index zero equals the open-boundary MPS amplitude. -/
theorem g10g_contr_eq_mpsAmplitude {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    g10g_contr A x n (0 : Fin D) = mpsAmplitude A x := by
  have hF := g10g_contr_freeEnd A x n le_rfl (0 : Fin D)
  have hN := normalForm_eq_amplitude A x
  have hdelta : ∀ β : Fin (n + 1) → Fin D,
      (if (β ⟨(n : ℕ), by omega⟩ : Fin D) = (0 : Fin D) then (1 : ℂ) else 0)
        = (if (β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0 then (1 : ℂ) else 0) := by
    intro β
    by_cases hb : (β ⟨(n : ℕ), by omega⟩ : Fin D) = (0 : Fin D)
    · have hb2 : ((β ⟨(n : ℕ), by omega⟩ : Fin D).val) = 0 := by
        rw [hb]
        exact Fin.val_zero D
      rw [ite_eq_left hb, ite_eq_left hb2]
    · have hb2 : ¬((β ⟨(n : ℕ), by omega⟩ : Fin D).val = 0) := by
        intro h
        exact hb (Fin.eq_of_val_eq (h.trans (Fin.val_zero D).symm))
      rw [ite_eq_right hb, ite_eq_right hb2]
  rw [← hN, ← hF]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [hdelta β]

/-- For positive bond dimension and a nonempty prefix of length at most `n - 1`, contracting the
constructed tensor chain at an index below the prefix cut rank gives the corresponding left
singular amplitude. -/
theorem g10g_contr_eq_g10gL {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} [NeZero D]
    (x : Fin n → Fin d) :
    ∀ (m : ℕ) (_hm1 : 1 ≤ m) (hmn : m + 1 ≤ n) (k : Fin D),
      (k : ℕ) < cutRank n d ψ m →
        g10g_contr (g10g_chainA ψ D h2 hd hle) x m k
          = g10gL ψ m (k : ℕ) (g10g_prefix x m (by omega)) := by
  intro m
  induction m with
  | zero =>
    intro hm1 _hmn _k _hk
    exact absurd hm1 (by omega)
  | succ m ih =>
    intro hm1 hmn k hk
    obtain hm0 | hmpos : m = 0 ∨ 0 < m := Nat.eq_zero_or_pos m
    · subst hm0
      rw [g10g_contr_succ (g10g_chainA ψ D h2 hd hle) x 0 (by omega) k]
      have hs : (∑ j : Fin D,
            g10g_contr (g10g_chainA ψ D h2 hd hle) x 0 j
              * g10g_chainA ψ D h2 hd hle ⟨0, by omega⟩ (x ⟨0, by omega⟩) j k)
          = g10g_chainA ψ D h2 hd hle ⟨0, by omega⟩ (x ⟨0, by omega⟩)
              ⟨0, by omega⟩ k := by
        rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin D)]
        · rw [g10g_contr_zero, ite_eq_left rfl, one_mul]
        · intro j _ hj
          have hjv : ¬((j : ℕ) = 0) := by
            intro h
            exact hj (Fin.eq_of_val_eq h)
          rw [g10g_contr_zero, ite_eq_right hjv, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hs]
      rw [g10g_chainA_zero_used ψ (x ⟨0, by omega⟩) (b := k) hk]
      refine congrArg (fun u : Fin 1 → Fin d => g10gL ψ 1 (k : ℕ) u) ?_
      funext i
      have hi : (i : ℕ) = 0 := by have hi' := i.isLt; omega
      exact (congrArg x (Fin.ext hi)).symm
    · have hm_n : m < n := by omega
      have hle_m : cutRank n d ψ m ≤ D := hle m hm_n
      have hcard : cutRank n d ψ m ≤ Fintype.card (Fin (d ^ (n - m))) :=
        (cutRank_le_pow_right ψ m).trans (le_of_eq (Fintype.card_fin _).symm)
      rw [g10g_contr_succ (g10g_chainA ψ D h2 hd hle) x m hm_n k]
      have hterm : ∀ j : Fin D,
          g10g_contr (g10g_chainA ψ D h2 hd hle) x m j
            * g10g_chainA ψ D h2 hd hle ⟨m, hm_n⟩ (x ⟨m, hm_n⟩) j k
          = g10gL ψ m (j : ℕ) (g10g_prefix x m (by omega))
              * g10gLink ψ m (k : ℕ) (j : ℕ) (x ⟨m, hm_n⟩) := by
        intro j
        have hi0 : (0 : ℕ) < ((⟨m, hm_n⟩ : Fin n) : ℕ) := by
          show (0 : ℕ) < m
          omega
        have hi1 : ((⟨m, hm_n⟩ : Fin n) : ℕ) + 1 < n := by
          show (m : ℕ) + 1 < n
          omega
        by_cases hj : (j : ℕ) < cutRank n d ψ m
        · rw [ih (by omega) (by omega) j hj]
          have hmid : g10g_chainA ψ D h2 hd hle ⟨m, hm_n⟩ (x ⟨m, hm_n⟩) j k
              = g10gLink ψ m (k : ℕ) (j : ℕ) (x ⟨m, hm_n⟩) :=
            g10g_chainA_mid_used ψ (i := ⟨m, hm_n⟩) hi0 hi1
              (x ⟨m, hm_n⟩) j (b := k) hk
          rw [hmid]
        · have ha : cutRank n d ψ ((⟨m, hm_n⟩ : Fin n) : ℕ) ≤ (j : ℕ) := by
            show cutRank n d ψ m ≤ (j : ℕ)
            omega
          have hmid0 : g10g_chainA ψ D h2 hd hle ⟨m, hm_n⟩ (x ⟨m, hm_n⟩) j k = 0 :=
            g10g_chainA_mid_eq_zero_of_cutRank_le ψ (i := ⟨m, hm_n⟩) hi0 hi1
              (x ⟨m, hm_n⟩) j ha (b := k) hk
          rw [hmid0, mul_zero]
          rw [g10gL_eq_zero_of_cutRank_le ψ (by omega : cutRank n d ψ m ≤ (j : ℕ))
            (g10g_prefix x m _), zero_mul]
      rw [show (∑ j : Fin D,
            g10g_contr (g10g_chainA ψ D h2 hd hle) x m j
              * g10g_chainA ψ D h2 hd hle ⟨m, hm_n⟩ (x ⟨m, hm_n⟩) j k)
          = ∑ j : Fin D,
              g10gL ψ m (j : ℕ) (g10g_prefix x m (by omega))
                * g10gLink ψ m (k : ℕ) (j : ℕ) (x ⟨m, hm_n⟩) from
        Finset.sum_congr rfl (fun j _ => hterm j)]
      have hzero : ∀ t : ℕ, cutRank n d ψ m ≤ t →
          g10gL ψ m t (g10g_prefix x m (by omega))
            * g10gLink ψ m (k : ℕ) t (x ⟨m, hm_n⟩) = 0 := by
        intro t ht
        rw [g10gL_eq_zero_of_cutRank_le ψ ht _, zero_mul]
      rw [g10g_sum_fin_eq_of_zero (m := D) (m' := Fintype.card (Fin (d ^ (n - m))))
            (fun t => g10gL ψ m t (g10g_prefix x m (by omega))
              * g10gLink ψ m (k : ℕ) t (x ⟨m, hm_n⟩))
            hle_m hcard hzero]
      rw [← g10g_expand_link ψ m (by omega) (k : ℕ) (g10g_prefix x m (by omega))
        (x ⟨m, hm_n⟩)]
      congr 1
      exact g10g_prefix_snoc x m (by omega)

/-- For nonzero bond dimension, the constructed tensor chain reproduces every amplitude of the
original state exactly. -/
theorem g10g_chainA_amplitude {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (hD : NeZero D)
    (x : Fin n → Fin d) :
    @mpsAmplitude n d D hD (g10g_chainA ψ D h2 hd hle) x = ψ x := by
  have : NeZero D := hD
  have hcontr := @g10g_contr_eq_mpsAmplitude n d D hD (g10g_chainA ψ D h2 hd hle) x
  rw [← hcontr]
  have hnn : n - 1 + 1 = n := by omega
  have hstep := g10g_contr_succ (g10g_chainA ψ D h2 hd hle) x (n - 1) (by omega) (0 : Fin D)
  rw [hnn] at hstep
  rw [hstep]
  have hterm : ∀ j : Fin D,
      g10g_contr (g10g_chainA ψ D h2 hd hle) x (n - 1) j
        * g10g_chainA ψ D h2 hd hle ⟨n - 1, by omega⟩ (x ⟨n - 1, by omega⟩) j (0 : Fin D)
      = g10gL ψ (n - 1) (j : ℕ) (g10g_prefix x (n - 1) (by omega))
          * g10gS ψ (n - 1) (j : ℕ) (fun _ => x ⟨n - 1, by omega⟩) := by
    intro j
    have hcol := g10g_chainA_last_col ψ (h2 := h2) (hd := hd) (hle := hle)
      (x ⟨n - 1, by omega⟩) j (0 : Fin D) (by simp)
    by_cases hj : (j : ℕ) < cutRank n d ψ (n - 1)
    · rw [hcol]
      rw [g10g_contr_eq_g10gL ψ x (n - 1) (by omega) (by omega) j hj]
    · have hS : g10gS ψ (n - 1) (j : ℕ) (fun _ => x ⟨n - 1, by omega⟩) = 0 :=
        g10gS_eq_zero_of_cutRank_le ψ (by omega) _
      rw [hcol, hS, mul_zero, mul_zero]
  rw [show (∑ j : Fin D,
        g10g_contr (g10g_chainA ψ D h2 hd hle) x (n - 1) j
          * g10g_chainA ψ D h2 hd hle ⟨n - 1, by omega⟩ (x ⟨n - 1, by omega⟩) j (0 : Fin D))
      = ∑ j : Fin D, g10gL ψ (n - 1) (j : ℕ) (g10g_prefix x (n - 1) (by omega))
          * g10gS ψ (n - 1) (j : ℕ) (fun _ => x ⟨n - 1, by omega⟩) from
    Finset.sum_congr rfl (fun j _ => hterm j)]
  have hzero : ∀ t : ℕ, cutRank n d ψ (n - 1) ≤ t →
      g10gL ψ (n - 1) t (g10g_prefix x (n - 1) (by omega))
        * g10gS ψ (n - 1) t (fun _ => x ⟨n - 1, by omega⟩) = 0 := by
    intro t ht
    rw [g10gL_eq_zero_of_cutRank_le ψ ht _, zero_mul]
  rw [g10g_sum_fin_eq_of_zero (m := D) (m' := Fintype.card (Fin (d ^ (n - (n - 1)))))
        (fun t => g10gL ψ (n - 1) t (g10g_prefix x (n - 1) (by omega))
          * g10gS ψ (n - 1) t (fun _ => x ⟨n - 1, by omega⟩))
        (hle (n - 1) (by omega))
        ((cutRank_le_pow_right ψ (n - 1)).trans (le_of_eq (Fintype.card_fin _).symm)) hzero]
  rw [← g10g_svd_reconstruct ψ (n - 1) (by omega)
    (g10g_prefix x (n - 1) (by omega)) (fun _ => x ⟨n - 1, by omega⟩)]
  exact congrArg ψ (g10g_splitJoin_prefix_last x h2)

/-- The constructed tensor chain is an exact MPS representation of the state for nonzero bond
dimension. -/
theorem g10g_chainA_isMps {n d D : ℕ} (ψ : (Fin n → Fin d) → ℂ)
    {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} (hD : NeZero D) :
    @IsMpsRepresentation n d D hD (g10g_chainA ψ D h2 hd hle) ψ := by
  intro x
  exact g10g_chainA_amplitude ψ hD x

/-- Packing the rows of a matrix into incoming-bond and physical indices expresses its Gram
matrix as the sum of the packed tensors' Gram matrices over the physical index. -/
theorem g10g_rowPacking_gram {d D : ℕ} (W : Matrix (Fin (D * d)) (Fin D) ℂ) :
    ∑ y : Fin d, ((Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
        (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)) = Wᴴ * W := by
  have hentry : ∀ k k' : Fin D,
      ((∑ y : Fin d, ((Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
        (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b))) k k')
        = (Wᴴ * W) k k' := by
    intro k k'
    rw [Matrix.sum_apply]
    have h1 : (∑ y : Fin d, ((Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
          (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)) k k')
        = ∑ p : Fin (D * d), star (W p k) * W p k' := by
      have h1a : (∑ y : Fin d, ((Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
            (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)) k k')
          = ∑ y : Fin d, ∑ s : Fin D,
              star (W (finProdFinEquiv (m := D) (n := d) (s, y)) k)
                * W (finProdFinEquiv (m := D) (n := d) (s, y)) k' := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        calc ((Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
            (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)) k k'
            = ∑ s : Fin D,
                ((Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ) k s
                  * (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b) s k' :=
              Matrix.mul_apply (M := (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ)
                (N := Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b)
                (i := k) (k := k')
          _ = ∑ s : Fin D, star (W (finProdFinEquiv (m := D) (n := d) (s, y)) k)
                * W (finProdFinEquiv (m := D) (n := d) (s, y)) k' :=
              Finset.sum_congr rfl (fun s _ => by
                rw [Matrix.conjTranspose_apply
                  (Matrix.of fun a b => W (finProdFinEquiv (m := D) (n := d) (a, y)) b) s k]
                rw [Matrix.of_apply, Matrix.of_apply])
      rw [h1a]
      have h1b : (∑ y : Fin d, ∑ s : Fin D,
            star (W (finProdFinEquiv (m := D) (n := d) (s, y)) k)
              * W (finProdFinEquiv (m := D) (n := d) (s, y)) k')
          = ∑ q : Fin D × Fin d,
              star (W (finProdFinEquiv (m := D) (n := d) q) k)
                * W (finProdFinEquiv (m := D) (n := d) q) k' :=
        (Fintype.sum_prod_type_right
          (fun q : Fin D × Fin d =>
            star (W (finProdFinEquiv (m := D) (n := d) q) k)
              * W (finProdFinEquiv (m := D) (n := d) q) k')).symm
      rw [h1b]
      exact Equiv.sum_comp (finProdFinEquiv (m := D) (n := d))
        (fun p : Fin (D * d) => star (W p k) * W p k')
    rw [h1]
    have h3 : (Wᴴ * W) k k' = ∑ p : Fin (D * d), star (W p k) * W p k' := by
      calc (Wᴴ * W) k k' = ∑ p : Fin (D * d), (Wᴴ) k p * W p k' :=
            Matrix.mul_apply (M := Wᴴ) (N := W) (i := k) (k := k')
        _ = ∑ p : Fin (D * d), star (W p k) * W p k' :=
            Finset.sum_congr rfl (fun p _ => by rw [Matrix.conjTranspose_apply W p k])
    exact h3.symm
  refine Matrix.ext (fun k k' => ?_)
  exact hentry k k'

/-- At a site whose index is zero, the constructed tensor is the matrix obtained by packing the
first-site isometric extension. -/
theorem g10g_chainA_zero_matrix {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} {i : Fin n} (hi : (i : ℕ) = 0) (y : Fin d) :
    g10g_chainA ψ D h2 hd hle i y
      = Matrix.of fun a b => g10g_site0Ext ψ (hle 1 (by omega)) hd
          (finProdFinEquiv (m := D) (n := d) (a, y)) b := by
  funext a b
  rw [g10g_chainA_apply, dite_eq_left hi]
  rfl

/-- At a site strictly between the boundaries, the constructed tensor is the matrix obtained by
packing the intermediate isometric extension. -/
theorem g10g_chainA_mid_matrix {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} {i : Fin n}
    (hi0 : 0 < (i : ℕ)) (hi1 : (i : ℕ) + 1 < n) (y : Fin d) :
    g10g_chainA ψ D h2 hd hle i y
      = Matrix.of fun a b => g10g_siteIExt ψ i (by omega) (hle i (by omega))
          (hle (i + 1) (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b := by
  funext a b
  rw [g10g_chainA_apply]
  rw [dite_eq_right (by omega : ¬(i : ℕ) = 0)]
  rw [dite_eq_right (by omega : ¬(i : ℕ) = n - 1)]
  rfl

/-- The MPS chain assembled from the extended singular-vector blocks is left canonical. -/
theorem g10g_chainA_leftCanonical {D : ℕ} {h2 : 2 ≤ n} {hd : 0 < d}
    {hle : ∀ c, c < n → cutRank n d ψ c ≤ D} :
    LeftCanonical (g10g_chainA ψ D h2 hd hle) := by
  intro i hi
  obtain hi0 | hi0 : (i : ℕ) = 0 ∨ 0 < (i : ℕ) := Nat.eq_zero_or_pos i
  · have hmat : ∀ y : Fin d, g10g_chainA ψ D h2 hd hle i y
        = Matrix.of fun a b => g10g_site0Ext ψ (hle 1 (by omega)) hd
            (finProdFinEquiv (m := D) (n := d) (a, y)) b :=
      fun y => g10g_chainA_zero_matrix ψ hi0 y
    rw [show (∑ y : Fin d, (g10g_chainA ψ D h2 hd hle i y)ᴴ * (g10g_chainA ψ D h2 hd hle i y))
        = ∑ y : Fin d, ((Matrix.of fun a b => g10g_site0Ext ψ (hle 1 (by omega)) hd
            (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
          (Matrix.of fun a b => g10g_site0Ext ψ (hle 1 (by omega)) hd
            (finProdFinEquiv (m := D) (n := d) (a, y)) b)) from
      Finset.sum_congr rfl (fun y _ => by rw [hmat y])]
    exact (g10g_rowPacking_gram _).trans (g10g_site0Ext_gram ψ)
  · have hi1 : (i : ℕ) + 1 < n := by omega
    have hmat : ∀ y : Fin d, g10g_chainA ψ D h2 hd hle i y
        = Matrix.of fun a b => g10g_siteIExt ψ i (by omega) (hle i (by omega))
            (hle (i + 1) (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b :=
      fun y => g10g_chainA_mid_matrix ψ hi0 hi1 y
    rw [show (∑ y : Fin d, (g10g_chainA ψ D h2 hd hle i y)ᴴ * (g10g_chainA ψ D h2 hd hle i y))
        = ∑ y : Fin d, ((Matrix.of fun a b => g10g_siteIExt ψ i (by omega) (hle i (by omega))
            (hle (i + 1) (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b)ᴴ *
          (Matrix.of fun a b => g10g_siteIExt ψ i (by omega) (hle i (by omega))
            (hle (i + 1) (by omega)) hd (finProdFinEquiv (m := D) (n := d) (a, y)) b)) from
      Finset.sum_congr rfl (fun y _ => by rw [hmat y])]
    exact (g10g_rowPacking_gram _).trans (g10g_siteIExt_gram ψ i (by omega))

/-- For a nonempty chain with zero physical dimension, every real-valued sum over physical
configurations is zero. -/
theorem g10g_sum_empty_cfg {n d : ℕ} (hn : 1 ≤ n) (hd : d = 0) (F : (Fin n → Fin d) → ℝ) :
    (∑ x : Fin n → Fin d, F x) = 0 := by
  subst hd
  exact Fintype.sum_eq_zero F (fun x => Fin.elim0 (x ⟨0, by omega⟩))

/-- On a chain with at least one site and nonzero bond dimension, setting every tensor to zero
makes every MPS amplitude zero. -/
theorem g10g_mpsAmplitude_zero {n d D : ℕ} (hD : NeZero D) (hn : 1 ≤ n) (x : Fin n → Fin d) :
    @mpsAmplitude n d D hD (fun _ _ => 0) x = 0 := by
  have : NeZero D := hD
  unfold mpsAmplitude
  refine Finset.sum_eq_zero (fun α _ => ?_)
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin n)) ?_
  simp [Matrix.zero_apply]

/-- Every normalized state on at least one site has an exact left-canonical MPS representation
with bond dimension equal to the maximum of one and its cut ranks before `n`. This
formalizes the completeness and canonical-form construction associated with Theorem 1 of
[PerezGarciaEtAl2007]. -/
theorem clause2_clause2 (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ)
    (_hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    1 ≤ n → ∃ (D : ℕ) (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      @IsMpsRepresentation n d D hD A ψ ∧ LeftCanonical A ∧
        D = max 1 ((Finset.range n).sup fun c => cutRank n d ψ c) := by
  intro hn
  obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
  · exact clause2_clause2_one d ψ _hnorm
  · have hd : 0 < d := by
      by_contra h
      have hd0 : d = 0 := by omega
      have h0 : ∑ x : Fin n → Fin d, Complex.normSq (ψ x) = 0 :=
        g10g_sum_empty_cfg hn hd0 _
      rw [h0] at _hnorm
      exact absurd _hnorm (by norm_num)
    refine ⟨max 1 ((Finset.range n).sup fun c => cutRank n d ψ c),
      neZero_max_one_supCutRank n d ψ,
      g10g_chainA ψ _ h2 hd (cutRank_le_max_one_supCutRank ψ), ?_, ?_, rfl⟩
    · exact g10g_chainA_isMps ψ (neZero_max_one_supCutRank n d ψ)
    · exact g10g_chainA_leftCanonical ψ

/-- For a normalized state on a nonempty chain, the desired MPS approximation bound holds
whenever twice the total discarded squared Schmidt tail is at least one. Any positive
requested bond dimension can be used. -/
theorem g10g_clause3_of_one_le_two_tail (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ)
    (hnorm : ∑ x, Complex.normSq (ψ x) = 1) (hn : 1 ≤ n) (D : ℕ) (hDpos : 0 < D)
    (htail : 1 ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D) :
    ∃ (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∑ x, Complex.normSq (@mpsAmplitude n d D hD A x - ψ x)
        ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  have hD : NeZero D := NeZero.of_pos hDpos
  refine ⟨hD, fun _ _ => 0, ?_⟩
  have hamp : ∀ x : Fin n → Fin d, @mpsAmplitude n d D hD (fun _ _ => 0) x = 0 :=
    fun x => g10g_mpsAmplitude_zero hD hn x
  have hsum : (∑ x : Fin n → Fin d,
      Complex.normSq (@mpsAmplitude n d D hD (fun _ _ => 0) x - ψ x)) = 1 := by
    refine (Finset.sum_congr rfl (fun x _ => ?_)).trans hnorm
    rw [hamp x, zero_sub, Complex.normSq_neg]
  rw [hsum]
  exact htail

/-- For a nonempty chain, if every cut rank before `n` is at most a positive bond dimension `D`,
there is a bond-`D` MPS satisfying the bound by twice the total discarded squared Schmidt
tail. -/
theorem g10g_clause3_of_cutRank_le (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ)
    (hn : 1 ≤ n) (D : ℕ) (hDpos : 0 < D)
    (hrank : ∀ c ∈ Finset.range n, cutRank n d ψ c ≤ D) :
    ∃ (hD' : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∑ x, Complex.normSq (@mpsAmplitude n d D hD' A x - ψ x)
        ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
  · exact clause2_clause3_one d ψ D hDpos
  · by_cases hd0 : d = 0
    · have hD' : NeZero D := NeZero.of_pos hDpos
      refine ⟨hD', fun _ _ => 0, ?_⟩
      rw [g10g_sum_empty_cfg hn hd0
            (fun x => Complex.normSq (@mpsAmplitude n d D hD' (fun _ _ => 0) x - ψ x))]
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg (fun c _ => schmidtTailSq_nonneg ψ c D))
    · have hd : 0 < d := by omega
      refine clause2_clause3_of_exact_le n d ψ hDpos ?_ hrank
      refine ⟨max 1 ((Finset.range n).sup fun c => cutRank n d ψ c),
        neZero_max_one_supCutRank n d ψ,
        g10g_chainA ψ _ h2 hd (cutRank_le_max_one_supCutRank ψ),
        g10g_chainA_isMps ψ (neZero_max_one_supCutRank n d ψ), ?_⟩
      have h1 : 1 ≤ D := by omega
      have hsup : (Finset.range n).sup (fun c => cutRank n d ψ c) ≤ D :=
        Finset.sup_le (fun c hc => hrank c hc)
      exact Nat.max_le.mpr ⟨h1, hsup⟩

/-- An amplitude function whose cut ranks are at most positive `D` and whose squared error has
the required Schmidt-tail bound yields a bond-`D` MPS with the same error bound, for a
nonempty chain. -/
theorem g10g_clause3_of_approximant (n d : ℕ) (ψ ψ' : (Fin n → Fin d) → ℂ)
    (hn : 1 ≤ n) (D : ℕ) (hDpos : 0 < D)
    (hcut : ∀ c < n, cutRank n d ψ' c ≤ D)
    (herr : ∑ x, Complex.normSq (ψ' x - ψ x)
      ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D) :
    ∃ (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      ∑ x, Complex.normSq (@mpsAmplitude n d D hD A x - ψ x)
        ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
  · exact clause2_clause3_one d ψ D hDpos
  · by_cases hd0 : d = 0
    · have hD' : NeZero D := NeZero.of_pos hDpos
      refine ⟨hD', fun _ _ => 0, ?_⟩
      rw [g10g_sum_empty_cfg hn hd0
            (fun x => Complex.normSq (@mpsAmplitude n d D hD' (fun _ _ => 0) x - ψ x))]
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg (fun c _ => schmidtTailSq_nonneg ψ c D))
    · have hd : 0 < d := by omega
      have hD' : NeZero D := NeZero.of_pos hDpos
      refine ⟨hD', g10g_chainA ψ' D h2 hd hcut, ?_⟩
      have hamp : ∀ x : Fin n → Fin d,
          @mpsAmplitude n d D hD' (g10g_chainA ψ' D h2 hd hcut) x = ψ' x := by
        intro x
        exact g10g_chainA_amplitude ψ' hD' x
      calc (∑ x : Fin n → Fin d,
              Complex.normSq (@mpsAmplitude n d D hD' (g10g_chainA ψ' D h2 hd hcut) x - ψ x))
            = ∑ x : Fin n → Fin d, Complex.normSq (ψ' x - ψ x) := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              rw [hamp x]
        _ ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := herr

/-- The amplitude function obtained from a matrix at cut `c` by splitting each configuration and
encoding its prefix and suffix as row and column indices. -/
noncomputable def g10t_ofCut {n d : ℕ} (c : ℕ) (hc : c ≤ n)
    (M : Matrix (Fin (d ^ c)) (Fin (d ^ (n - c))) ℂ) : (Fin n → Fin d) → ℂ :=
  fun x => M (finPowEnc d c ((g10a_splitJoinEquiv n c d hc).symm x).1)
      (finPowEnc d (n - c) ((g10a_splitJoinEquiv n c d hc).symm x).2)

/-- Taking the cut matrix of the amplitude function reconstructed from a matrix at the same
valid cut recovers that matrix. -/
theorem g10t_cutMatrix_ofCut {n d : ℕ} {c : ℕ} (hc : c ≤ n)
    (M : Matrix (Fin (d ^ c)) (Fin (d ^ (n - c))) ℂ) :
    cutMatrix n d (g10t_ofCut c hc M) c = M := by
  ext i j
  rw [g10a_cutMatrix_apply]
  show g10t_ofCut c hc M
      (splitJoin n c d ((finPowEnc d c).symm i) ((finPowEnc d (n - c)).symm j)) = M i j
  simp only [g10t_ofCut]
  have hpair : (g10a_splitJoinEquiv n c d hc)
        ((finPowEnc d c).symm i, (finPowEnc d (n - c)).symm j)
      = splitJoin n c d ((finPowEnc d c).symm i) ((finPowEnc d (n - c)).symm j) := rfl
  rw [← hpair, Equiv.symm_apply_apply]
  simp

/-- Reconstructing an amplitude function from its matrix at a valid cut recovers the function. -/
theorem g10t_ofCut_cutMatrix {n d : ℕ} {c : ℕ} (hc : c ≤ n) (f : (Fin n → Fin d) → ℂ) :
    g10t_ofCut c hc (cutMatrix n d f c) = f := by
  funext x
  show g10t_ofCut c hc (cutMatrix n d f c) x = f x
  simp only [g10t_ofCut]
  rw [g10a_cutMatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg f ((g10a_splitJoinEquiv n c d hc).apply_symm_apply x)

/-- Reconstruction from a matrix at a valid cut preserves addition. -/
theorem g10t_ofCut_add {n d : ℕ} {c : ℕ} (hc : c ≤ n)
    (M N : Matrix (Fin (d ^ c)) (Fin (d ^ (n - c))) ℂ) :
    g10t_ofCut c hc (M + N) = g10t_ofCut c hc M + g10t_ofCut c hc N := by
  funext x
  simp [g10t_ofCut]

/-- Reconstruction from a matrix at a valid cut preserves multiplication by a complex scalar. -/
theorem g10t_ofCut_smul {n d : ℕ} {c : ℕ} (hc : c ≤ n) (a : ℂ)
    (M : Matrix (Fin (d ^ c)) (Fin (d ^ (n - c))) ℂ) :
    g10t_ofCut c hc (a • M) = a • g10t_ofCut c hc M := by
  funext x
  simp [g10t_ofCut]

/-- The cut-matrix construction preserves addition of amplitude functions. -/
theorem g10t_cutMatrix_add {n d : ℕ} {c : ℕ} (f χ : (Fin n → Fin d) → ℂ) :
    cutMatrix n d (f + χ) c = cutMatrix n d f c + cutMatrix n d χ c := by
  ext i j
  simp [g10a_cutMatrix_apply]

/-- The cut-matrix construction preserves multiplication of an amplitude function by a complex
scalar. -/
theorem g10t_cutMatrix_smul {n d : ℕ} {c : ℕ} (a : ℂ) (f : (Fin n → Fin d) → ℂ) :
    cutMatrix n d (a • f) c = a • cutMatrix n d f c := by
  ext i j
  simp [g10a_cutMatrix_apply]

/-- The cut-matrix construction preserves subtraction of amplitude functions. -/
theorem g10t_cutMatrix_sub {n d : ℕ} {c : ℕ} (f χ : (Fin n → Fin d) → ℂ) :
    cutMatrix n d (f - χ) c = cutMatrix n d f c - cutMatrix n d χ c := by
  ext i j
  simp [g10a_cutMatrix_apply]

/-- The outer product of a left singular vector with its conjugate, viewed as a square matrix on
the output indices. -/
noncomputable def g10t_rk {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (k : Fin (Fintype.card I)) : Matrix O O ℂ :=
  Matrix.of fun p q =>
    leftSingularVector A k p * star (leftSingularVector A k q)

/-- An entry of `g10t_rk A k` is the left singular-vector value at its row times the conjugate
value at its column. -/
@[simp] theorem g10t_rk_apply {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    {A : Matrix O I ℂ} {k : Fin (Fintype.card I)} (p q : O) :
    g10t_rk A k p q
      = leftSingularVector A k p * star (leftSingularVector A k q) :=
  rfl

/-- The inner product of two left singular vectors is one exactly when their indices agree and
the corresponding singular value is nonzero, and is zero otherwise. -/
theorem g10t_inner_leftSingular {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    {A : Matrix O I ℂ} (k j : Fin (Fintype.card I)) :
    (∑ p : O, star (leftSingularVector A k p) * leftSingularVector A j p)
      = if k = j ∧ matrixSingularValues A k ≠ 0 then (1 : ℂ) else 0 := by
  have hcol := congrFun (congrFun (leftSingularColumns_gram A) k) j
  have hentry : ((leftSingularColumns A)ᴴ * leftSingularColumns A) k j
      = ∑ p : O, star (leftSingularVector A k p) * leftSingularVector A j p := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, leftSingularColumns, mul_comm]
  rw [← hentry, hcol, Matrix.diagonal_apply]
  by_cases hkj : k = j
  · subst hkj
    by_cases hσ : matrixSingularValues A k = 0
    · rw [ite_eq_left hσ, ite_eq_right (by simp [hσ] : ¬(k = k ∧ matrixSingularValues A k ≠ 0)),
        ite_eq_left rfl]
    · rw [ite_eq_right hσ, ite_eq_left (⟨rfl, hσ⟩ : k = k ∧ matrixSingularValues A k ≠ 0),
        ite_eq_left rfl]
  · rw [ite_eq_right hkj]
    rw [ite_eq_right (fun h => hkj h.1 : ¬(k = j ∧ matrixSingularValues A k ≠ 0))]

/-- The outer product matrix associated with a left singular vector is equal to its conjugate
transpose. -/
theorem g10t_rk_conjTranspose {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    {A : Matrix O I ℂ} (k : Fin (Fintype.card I)) : (g10t_rk A k)ᴴ = g10t_rk A k := by
  ext p q
  rw [Matrix.conjTranspose_apply, g10t_rk_apply, g10t_rk_apply]
  simp only [star_mul, star_star]

/-- The outer product matrices of distinct left singular vectors multiply to zero, while each
such matrix is idempotent. -/
theorem g10t_rk_mul_rk {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    {A : Matrix O I ℂ} (k j : Fin (Fintype.card I)) :
    g10t_rk A k * g10t_rk A j = if k = j then g10t_rk A k else 0 := by
  by_cases hkj : k = j
  · subst hkj
    by_cases hσ : matrixSingularValues A k = 0
    · have hz : g10t_rk A k = 0 := by
        ext p q
        rw [g10t_rk_apply, leftSingularVector_eq_zero A k hσ]
        simp
      rw [hz, mul_zero, ite_eq_left rfl]
    · rw [ite_eq_left rfl]
      ext p q
      rw [Matrix.mul_apply]
      have hterm : ∀ r : O,
          g10t_rk A k p r * g10t_rk A k r q
            = leftSingularVector A k p * star (leftSingularVector A k q)
              * (star (leftSingularVector A k r) * leftSingularVector A k r) := by
        intro r
        rw [g10t_rk_apply, g10t_rk_apply]
        ring
      rw [show (∑ r : O, g10t_rk A k p r * g10t_rk A k r q)
          = ∑ r : O, leftSingularVector A k p * star (leftSingularVector A k q)
              * (star (leftSingularVector A k r) * leftSingularVector A k r) from
        Finset.sum_congr rfl (fun r _ => hterm r)]
      rw [← Finset.mul_sum]
      have hgram : (∑ r : O, star (leftSingularVector A k r) * leftSingularVector A k r)
          = (1 : ℂ) := by
        rw [g10t_inner_leftSingular k k,
          ite_eq_left (⟨rfl, hσ⟩ : k = k ∧ matrixSingularValues A k ≠ 0)]
      rw [hgram, mul_one, g10t_rk_apply]
  · rw [ite_eq_right hkj]
    ext p q
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have hterm : ∀ r : O,
        g10t_rk A k p r * g10t_rk A j r q
          = leftSingularVector A k p * star (leftSingularVector A j q)
            * (star (leftSingularVector A k r) * leftSingularVector A j r) := by
      intro r
      rw [g10t_rk_apply, g10t_rk_apply]
      ring
    rw [show (∑ r : O, g10t_rk A k p r * g10t_rk A j r q)
        = ∑ r : O, leftSingularVector A k p * star (leftSingularVector A j q)
            * (star (leftSingularVector A k r) * leftSingularVector A j r) from
      Finset.sum_congr rfl (fun r _ => hterm r)]
    rw [← Finset.mul_sum]
    have hgram : (∑ r : O, star (leftSingularVector A k r) * leftSingularVector A j r)
        = (0 : ℂ) := by
      rw [g10t_inner_leftSingular k j,
        ite_eq_right (fun h => hkj h.1 : ¬(k = j ∧ matrixSingularValues A k ≠ 0))]
    rw [hgram, mul_zero]

/-- The sum of the left singular-vector outer products of the cut matrix whose singular indices
are smaller than `D`. -/
noncomputable def g10t_projMat {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) :
    Matrix (Fin (d ^ c)) (Fin (d ^ c)) ℂ :=
  ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
    if (k : ℕ) < D then g10t_rk (cutMatrix n d ψ c) k else 0

/-- The cut projection matrix is the sum of the left singular-vector outer products over the
finite set of singular indices smaller than `D`. -/
theorem g10t_projMat_eq_sum_filter {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) :
    g10t_projMat ψ c D
      = ∑ k ∈ Finset.univ.filter (fun k : Fin (Fintype.card (Fin (d ^ (n - c)))) =>
          (k : ℕ) < D), g10t_rk (cutMatrix n d ψ c) k := by
  rw [g10t_projMat, ← Finset.sum_filter]

/-- The cut projection matrix is idempotent. -/
theorem g10t_projMat_mul_self {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) :
    g10t_projMat ψ c D * g10t_projMat ψ c D = g10t_projMat ψ c D := by
  rw [g10t_projMat_eq_sum_filter]
  rw [Finset.sum_mul_sum]
  have hterm : ∀ k j : Fin (Fintype.card (Fin (d ^ (n - c)))),
      g10t_rk (cutMatrix n d ψ c) k * g10t_rk (cutMatrix n d ψ c) j
        = if k = j then g10t_rk (cutMatrix n d ψ c) k else 0 := fun k j =>
    g10t_rk_mul_rk k j
  rw [show (∑ k ∈ Finset.univ.filter
        (fun k : Fin (Fintype.card (Fin (d ^ (n - c)))) => (k : ℕ) < D),
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (Fintype.card (Fin (d ^ (n - c)))) => (j : ℕ) < D),
        g10t_rk (cutMatrix n d ψ c) k * g10t_rk (cutMatrix n d ψ c) j)
      = ∑ k ∈ Finset.univ.filter
          (fun k : Fin (Fintype.card (Fin (d ^ (n - c)))) => (k : ℕ) < D),
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin (Fintype.card (Fin (d ^ (n - c)))) => (j : ℕ) < D),
          (if k = j then g10t_rk (cutMatrix n d ψ c) k else 0) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hterm k j))]
  have hinner : ∀ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
      (∑ j ∈ Finset.univ.filter
          (fun j : Fin (Fintype.card (Fin (d ^ (n - c)))) => (j : ℕ) < D),
        (if k = j then g10t_rk (cutMatrix n d ψ c) k else 0))
        = if (k : ℕ) < D then g10t_rk (cutMatrix n d ψ c) k else 0 := by
    intro k
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_congr rfl (fun k _ => hinner k)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  simp [hk]

/-- The cut projection matrix is equal to its conjugate transpose. -/
theorem g10t_projMat_conjTranspose {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) :
    (g10t_projMat ψ c D)ᴴ = g10t_projMat ψ c D := by
  rw [g10t_projMat_eq_sum_filter]
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun k _ => g10t_rk_conjTranspose k)

/-- Pairing a left singular vector with a matrix column gives the corresponding singular value
times the conjugate right singular-vector entry. -/
theorem g10t_inner_row {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (k : Fin (Fintype.card I)) (q : I) :
    (∑ r : O, star (leftSingularVector A k r) * A r q)
      = (matrixSingularValues A k : ℂ) * star (rightSingularBasis A k q) := by
  have hentry : ∀ r : O, A r q = ∑ i : Fin (Fintype.card I),
      (matrixSingularValues A i : ℂ) *
        (leftSingularVector A i r * star (rightSingularBasis A i q)) := by
    intro r
    have h := congrFun (congrFun (matrix_eq_sum_singularVectors A) r) q
    rw [Matrix.sum_apply] at h
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply] at h
    exact h
  have step1 : (∑ r : O, star (leftSingularVector A k r) * A r q)
      = ∑ r : O, star (leftSingularVector A k r) *
          ∑ i : Fin (Fintype.card I),
            (matrixSingularValues A i : ℂ) *
              (leftSingularVector A i r * star (rightSingularBasis A i q)) :=
    Finset.sum_congr rfl (fun r _ => by rw [hentry r])
  rw [step1]
  have step2 : (∑ r : O, star (leftSingularVector A k r) *
          ∑ i : Fin (Fintype.card I),
            (matrixSingularValues A i : ℂ) *
              (leftSingularVector A i r * star (rightSingularBasis A i q)))
      = ∑ r : O, ∑ i : Fin (Fintype.card I),
          (matrixSingularValues A i : ℂ) * star (rightSingularBasis A i q)
            * (star (leftSingularVector A k r) * leftSingularVector A i r) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [step2, Finset.sum_comm]
  have hterm : ∀ i : Fin (Fintype.card I),
      (∑ r : O, (matrixSingularValues A i : ℂ) * star (rightSingularBasis A i q)
          * (star (leftSingularVector A k r) * leftSingularVector A i r))
        = (matrixSingularValues A i : ℂ) * star (rightSingularBasis A i q)
            * (∑ r : O, star (leftSingularVector A k r) * leftSingularVector A i r) := by
    intro i
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_eq_single k]
  · rw [g10t_inner_leftSingular k k]
    by_cases hσ : matrixSingularValues A k = 0
    · rw [ite_eq_right (by simp [hσ] : ¬(k = k ∧ matrixSingularValues A k ≠ 0))]
      rw [hσ]
      simp
    · rw [ite_eq_left (⟨rfl, hσ⟩ : k = k ∧ matrixSingularValues A k ≠ 0), mul_one]
  · intro i _hi hik
    rw [g10t_inner_leftSingular k i]
    rw [ite_eq_right (fun h => hik h.1.symm : ¬(k = i ∧ matrixSingularValues A k ≠ 0))]
    ring
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Right multiplication of a finite sum of matrices distributes over that sum. -/
theorem g10t_sum_mul_matrix {m n p : ℕ} {ι : Type} [Fintype ι]
    (T : ι → Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p) ℂ) :
    (∑ i : ι, T i) * B = ∑ i : ι, T i * B := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  have hstep : (∑ j : Fin n, (∑ i : ι, T i a j) * B j b)
      = ∑ j : Fin n, ∑ i : ι, T i a j * B j b :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_mul _ _ _)
  rw [hstep, Finset.sum_comm]

/-- Left-multiplying a matrix by the outer product of its `k`th left singular vector extracts
its `k`th singular component. -/
theorem g10t_rk_mul_matrix {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (k : Fin (Fintype.card I)) :
    g10t_rk A k * A
      = (matrixSingularValues A k : ℂ) •
          Matrix.vecMulVec (leftSingularVector A k).ofLp
            (fun q => star ((rightSingularBasis A k).ofLp q)) := by
  ext p q
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  have hterm : ∀ r : O,
      g10t_rk A k p r * A r q
        = leftSingularVector A k p * (star (leftSingularVector A k r) * A r q) := by
    intro r
    rw [g10t_rk_apply]
    ring
  rw [show (∑ r : O, g10t_rk A k p r * A r q)
      = ∑ r : O, leftSingularVector A k p * (star (leftSingularVector A k r) * A r q) from
    Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [← Finset.mul_sum, g10t_inner_row]
  ring

/-- Left multiplication of a cut matrix by its cut projection matrix gives the SVD truncation at
`D`. -/
theorem g10t_projMat_mul_cutMatrix {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) :
    g10t_projMat ψ c D * cutMatrix n d ψ c
      = g10g_svdTrunc (cutMatrix n d ψ c) D := by
  rw [g10t_projMat]
  rw [show (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          (if (k : ℕ) < D then g10t_rk (cutMatrix n d ψ c) k else 0))
        * cutMatrix n d ψ c
      = ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
          (if (k : ℕ) < D then g10t_rk (cutMatrix n d ψ c) k else 0)
            * cutMatrix n d ψ c from g10t_sum_mul_matrix _ _]
  simp only [g10g_svdTrunc]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : (k : ℕ) < D
  · rw [ite_eq_left hk, ite_eq_left hk]
    exact g10t_rk_mul_matrix (cutMatrix n d ψ c) k
  · rw [ite_eq_right hk, ite_eq_right hk, Matrix.zero_mul _]

/-- The operator on amplitude functions that left-multiplies their cut matrices by the
projection onto the reference state's first `D` left singular components and then
reconstructs the functions. -/
noncomputable def g10t_cutProj {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) (hc : c ≤ n) :
    ((Fin n → Fin d) → ℂ) → ((Fin n → Fin d) → ℂ) :=
  fun f => g10t_ofCut c hc (g10t_projMat ψ c D * cutMatrix n d f c)

/-- At the projection's own valid cut, the matrix of a projected amplitude function is the
projection matrix times the original cut matrix. -/
theorem g10t_cutMatrix_cutProj {n d : ℕ} {c : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ)
    (hc : c ≤ n) (f : (Fin n → Fin d) → ℂ) :
    cutMatrix n d (g10t_cutProj ψ c D hc f) c
      = g10t_projMat ψ c D * cutMatrix n d f c :=
  g10t_cutMatrix_ofCut hc _

/-- The cut projection operator preserves addition of amplitude functions. -/
theorem g10t_cutProj_add {n d : ℕ} {c : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ)
    (hc : c ≤ n) (f g : (Fin n → Fin d) → ℂ) :
    g10t_cutProj ψ c D hc (f + g)
      = g10t_cutProj ψ c D hc f + g10t_cutProj ψ c D hc g := by
  unfold g10t_cutProj
  rw [g10t_cutMatrix_add, Matrix.mul_add, g10t_ofCut_add]

/-- Applying the same cut projection twice has the same result as applying it once. -/
theorem g10t_cutProj_self {n d : ℕ} {c : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ)
    (hc : c ≤ n) (f : (Fin n → Fin d) → ℂ) :
    g10t_cutProj ψ c D hc (g10t_cutProj ψ c D hc f) = g10t_cutProj ψ c D hc f := by
  change g10t_ofCut c hc
      (g10t_projMat ψ c D * cutMatrix n d (g10t_cutProj ψ c D hc f) c)
    = g10t_cutProj ψ c D hc f
  rw [g10t_cutMatrix_cutProj, ← Matrix.mul_assoc, g10t_projMat_mul_self]
  rfl

/-- The cut projection operator preserves multiplication by a complex scalar. -/
theorem g10t_cutProj_smul {n d : ℕ} {c : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ)
    (hc : c ≤ n) (a : ℂ) (f : (Fin n → Fin d) → ℂ) :
    g10t_cutProj ψ c D hc (a • f) = a • g10t_cutProj ψ c D hc f := by
  unfold g10t_cutProj
  rw [g10t_cutMatrix_smul, Matrix.mul_smul, g10t_ofCut_smul]

/-- Negating a matrix preserves the square of its spectral Frobenius norm. -/
theorem g10t_frob_neg {O I : Type} [Fintype O] [Fintype I] (Y : Matrix O I ℂ) :
    spectralFrobenius (-Y) ^ 2 = spectralFrobenius Y ^ 2 := by
  rw [spectralFrobenius_sq, spectralFrobenius_sq]
  simp only [Matrix.neg_apply, Complex.normSq_neg]

/-- If `A * B` is zero, then the trace of `X` conjugate-transposed times `A`, `B`, and `Y`, in
that order, is zero. -/
theorem g10t_trace_cross_zero {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ)
    (A B : Matrix (Fin m) (Fin m) ℂ) (hAB : A * B = 0) :
    Matrix.trace ((X ᴴ * A) * (B * Y)) = 0 := by
  have h1 : (X ᴴ * A) * (B * Y) = (X ᴴ * (A * B)) * Y := by
    calc (X ᴴ * A) * (B * Y) = X ᴴ * (A * (B * Y)) := Matrix.mul_assoc _ _ _
      _ = X ᴴ * ((A * B) * Y) := by rw [← Matrix.mul_assoc A B Y]
      _ = (X ᴴ * (A * B)) * Y := (Matrix.mul_assoc _ _ _).symm
  rw [h1, hAB]
  simp

/-- When the trace inner product of `X` and `Y` is zero, the squared spectral Frobenius norm of
their sum is the sum of their squared norms. -/
theorem g10t_frob_add {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℂ)
    (h : Matrix.trace (X ᴴ * Y) = 0) :
    spectralFrobenius (X + Y) ^ 2 = spectralFrobenius X ^ 2 + spectralFrobenius Y ^ 2 := by
  have hmain := spectralFrobenius_sq_sub X (-Y)
  have hXY : X - -Y = X + Y := by rw [sub_eq_add_neg, neg_neg]
  rw [hXY] at hmain
  rw [g10t_frob_neg] at hmain
  have hre : (Matrix.trace (X ᴴ * (-Y))).re = 0 := by
    rw [Matrix.mul_neg, Matrix.trace_neg, h]
    simp
  rw [hre] at hmain
  linarith

/-- Left multiplication by a self-adjoint idempotent matrix cannot increase the squared spectral
Frobenius norm. -/
theorem g10t_frob_proj_le {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin m) (Fin n) ℂ)
    (hP : P * P = P) (hPh : P ᴴ = P) :
    spectralFrobenius (P * X) ^ 2 ≤ spectralFrobenius X ^ 2 := by
  have hAB : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  have hcross : Matrix.trace ((P * X) ᴴ * ((1 - P) * X)) = 0 := by
    rw [Matrix.conjTranspose_mul, hPh]
    exact g10t_trace_cross_zero X X P (1 - P) hAB
  have hdecomp : X = P * X + (1 - P) * X := by
    rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  have hsum := g10t_frob_add (P * X) ((1 - P) * X) hcross
  rw [← hdecomp] at hsum
  have hnonneg : 0 ≤ spectralFrobenius ((1 - P) * X) ^ 2 := sq_nonneg _
  linarith

/-- For a self-adjoint idempotent `P`, the squared norm of `M - P * N` splits into the squared
norm of `M - P * M` and that of `P * (M - N)`. -/
theorem g10t_frob_pythagoras {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ)
    (M N : Matrix (Fin m) (Fin n) ℂ) (hP : P * P = P) (hPh : P ᴴ = P) :
    spectralFrobenius (M - P * N) ^ 2
      = spectralFrobenius (M - P * M) ^ 2 + spectralFrobenius (P * (M - N)) ^ 2 := by
  have hAB : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP, sub_self]
  have hconj : (M - P * M) ᴴ = M ᴴ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPh, Matrix.mul_sub,
      Matrix.mul_one]
  have hcross : Matrix.trace ((M - P * M) ᴴ * (P * (M - N))) = 0 := by
    rw [hconj]
    exact g10t_trace_cross_zero M (M - N) (1 - P) P hAB
  have hadd := g10t_frob_add (M - P * M) (P * (M - N)) hcross
  have hdecomp : M - P * N = (M - P * M) + P * (M - N) := by
    rw [Matrix.mul_sub]
    abel
  rw [hdecomp, hadd]

/-- Projecting the reference state at a valid cut gives a total squared amplitude error equal to
that cut's discarded squared Schmidt tail. -/
theorem g10t_error_self {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) (hc : c ≤ n) :
    ∑ x, Complex.normSq (ψ x - g10t_cutProj ψ c D hc ψ x) = schmidtTailSq n d ψ c D := by
  have hM : cutMatrix n d (ψ - g10t_cutProj ψ c D hc ψ) c
      = cutMatrix n d ψ c - g10g_svdTrunc (cutMatrix n d ψ c) D := by
    rw [g10t_cutMatrix_sub, g10t_cutMatrix_cutProj, g10t_projMat_mul_cutMatrix]
  have hparse : ∑ x, Complex.normSq (ψ x - g10t_cutProj ψ c D hc ψ x)
      = spectralFrobenius (cutMatrix n d (ψ - g10t_cutProj ψ c D hc ψ) c) ^ 2 :=
    (g10a_parseval (ψ - g10t_cutProj ψ c D hc ψ) hc).symm
  rw [hparse, hM]
  exact (g10g_schmidtTailSq_eq_frob_sub_trunc ψ c D).symm

/-- Projecting an approximating amplitude function at a valid cut increases its squared error
from the reference state by at most that cut's discarded squared Schmidt tail. -/
theorem g10t_error_step {n d : ℕ} (ψ f : (Fin n → Fin d) → ℂ) (c D : ℕ) (hc : c ≤ n) :
    ∑ x, Complex.normSq (ψ x - g10t_cutProj ψ c D hc f x)
      ≤ schmidtTailSq n d ψ c D + ∑ x, Complex.normSq (ψ x - f x) := by
  have hcut : cutMatrix n d (ψ - g10t_cutProj ψ c D hc f) c
      = cutMatrix n d ψ c - g10t_projMat ψ c D * cutMatrix n d f c := by
    rw [g10t_cutMatrix_sub, g10t_cutMatrix_cutProj]
  have hpy := g10t_frob_pythagoras (g10t_projMat ψ c D) (cutMatrix n d ψ c)
    (cutMatrix n d f c) (g10t_projMat_mul_self ψ c D) (g10t_projMat_conjTranspose ψ c D)
  have h1 : cutMatrix n d ψ c - g10t_projMat ψ c D * cutMatrix n d ψ c
      = cutMatrix n d ψ c - g10g_svdTrunc (cutMatrix n d ψ c) D := by
    rw [g10t_projMat_mul_cutMatrix]
  have hcomp : spectralFrobenius
        (g10t_projMat ψ c D * (cutMatrix n d ψ c - cutMatrix n d f c)) ^ 2
      ≤ spectralFrobenius (cutMatrix n d ψ c - cutMatrix n d f c) ^ 2 :=
    g10t_frob_proj_le (g10t_projMat ψ c D) _
      (g10t_projMat_mul_self ψ c D) (g10t_projMat_conjTranspose ψ c D)
  calc ∑ x, Complex.normSq (ψ x - g10t_cutProj ψ c D hc f x)
      = spectralFrobenius (cutMatrix n d (ψ - g10t_cutProj ψ c D hc f) c) ^ 2 :=
        (g10a_parseval (ψ - g10t_cutProj ψ c D hc f) hc).symm
    _ = spectralFrobenius (cutMatrix n d ψ c
          - g10t_projMat ψ c D * cutMatrix n d f c) ^ 2 := by rw [hcut]
    _ = spectralFrobenius (cutMatrix n d ψ c
          - g10t_projMat ψ c D * cutMatrix n d ψ c) ^ 2
          + spectralFrobenius (g10t_projMat ψ c D
            * (cutMatrix n d ψ c - cutMatrix n d f c)) ^ 2 := hpy
    _ = schmidtTailSq n d ψ c D
          + spectralFrobenius (g10t_projMat ψ c D
            * (cutMatrix n d ψ c - cutMatrix n d f c)) ^ 2 := by
        rw [h1, ← g10g_schmidtTailSq_eq_frob_sub_trunc ψ c D]
    _ ≤ schmidtTailSq n d ψ c D
          + spectralFrobenius (cutMatrix n d ψ c - cutMatrix n d f c) ^ 2 :=
        add_le_add le_rfl hcomp
    _ = schmidtTailSq n d ψ c D + ∑ x, Complex.normSq (ψ x - f x) := by
        rw [← g10t_cutMatrix_sub]
        have hconv : (∑ x, Complex.normSq (ψ x - f x))
            = ∑ x, Complex.normSq ((ψ - f) x) :=
          Finset.sum_congr rfl (fun x _ => rfl)
        rw [hconv, ← g10a_parseval (ψ - f) hc]

/-- The sequence beginning at the reference state and successively applying its cut projections
at cuts `n - 1 - k`. -/
noncomputable def g10t_iter {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ) :
    ℕ → ((Fin n → Fin d) → ℂ)
  | 0 => ψ
  | k + 1 => g10t_cutProj ψ (n - 1 - k) D (by omega) (g10t_iter ψ D k)

/-- After `k` successive cut projections, the total squared error is bounded by the sum of the
discarded squared Schmidt tails at the cuts used in those steps. -/
theorem g10t_iter_error {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ) :
    ∀ k, ∑ x, Complex.normSq (ψ x - g10t_iter ψ D k x)
      ≤ ∑ j ∈ Finset.range k, schmidtTailSq n d ψ (n - 1 - j) D := by
  intro k
  induction k with
  | zero =>
    simp [g10t_iter]
  | succ k ih =>
    have hstep := g10t_error_step ψ (g10t_iter ψ D k) (n - 1 - k) D (by omega)
    calc ∑ x, Complex.normSq (ψ x - g10t_iter ψ D (k + 1) x)
        = ∑ x, Complex.normSq (ψ x
            - g10t_cutProj ψ (n - 1 - k) D (by omega) (g10t_iter ψ D k) x) := rfl
      _ ≤ schmidtTailSq n d ψ (n - 1 - k) D
            + ∑ x, Complex.normSq (ψ x - g10t_iter ψ D k x) := hstep
      _ ≤ schmidtTailSq n d ψ (n - 1 - k) D
            + ∑ j ∈ Finset.range k, schmidtTailSq n d ψ (n - 1 - j) D :=
        add_le_add le_rfl ih
      _ = ∑ j ∈ Finset.range (k + 1), schmidtTailSq n d ψ (n - 1 - j) D := by
        rw [Finset.sum_range_succ]
        exact add_comm _ _

/-- For a nonempty chain, the squared error after `n - 1` cut projections is at most twice the
total discarded squared Schmidt tail over cuts before `n`. -/
theorem g10t_iter_error_final {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (hn : 1 ≤ n) (D : ℕ) :
    ∑ x, Complex.normSq (g10t_iter ψ D (n - 1) x - ψ x)
      ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  have hinj : ∀ x ∈ Finset.range (n - 1), ∀ y ∈ Finset.range (n - 1),
      n - 1 - x = n - 1 - y → x = y := by
    intro x hx y hy h
    simp only [Finset.mem_range] at hx hy
    omega
  have hsub : (Finset.range (n - 1)).image (fun j : ℕ => n - 1 - j) ⊆ Finset.range n := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    rw [Finset.mem_range]
    omega
  have hsum : (∑ j ∈ Finset.range (n - 1), schmidtTailSq n d ψ (n - 1 - j) D)
      ≤ ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
    calc (∑ j ∈ Finset.range (n - 1), schmidtTailSq n d ψ (n - 1 - j) D)
        = ∑ c ∈ (Finset.range (n - 1)).image (fun j : ℕ => n - 1 - j),
            schmidtTailSq n d ψ c D :=
          (Finset.sum_image (f := fun c : ℕ => schmidtTailSq n d ψ c D)
            (g := fun j : ℕ => n - 1 - j) hinj).symm
      _ ≤ ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => schmidtTailSq_nonneg ψ y D)
  have hflip : ∑ x, Complex.normSq (g10t_iter ψ D (n - 1) x - ψ x)
      = ∑ x, Complex.normSq (ψ x - g10t_iter ψ D (n - 1) x) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← neg_sub, Complex.normSq_neg]
  have h3 : ∑ x, Complex.normSq (g10t_iter ψ D (n - 1) x - ψ x)
      ≤ ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
    rw [hflip]
    exact le_trans (g10t_iter_error ψ D (n - 1)) hsum
  have h4 : 0 ≤ ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D :=
    Finset.sum_nonneg (fun c _ => schmidtTailSq_nonneg ψ c D)
  linarith

/-- The outer product matrix of a left singular vector has rank at most one. -/
theorem g10t_rk_rank_le {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (k : Fin (Fintype.card I)) : Matrix.rank (g10t_rk A k) ≤ 1 := by
  have h : g10t_rk A k = Matrix.vecMulVec (fun p => leftSingularVector A k p)
      (fun q => star (leftSingularVector A k q)) := by
    ext p q
    simp [g10t_rk, Matrix.vecMulVec]
  rw [h]
  exact rank_vecMulVec_le _ _

/-- The number of indices in `Fin N` whose natural-number values are smaller than `D` is at most
`D`. -/
theorem g10t_card_lt_le (N D : ℕ) :
    (Finset.univ.filter (fun k : Fin N => (k : ℕ) < D)).card ≤ D := by
  have key : (Finset.univ.filter (fun k : Fin N => (k : ℕ) < D)).card
      ≤ (Finset.range D).card :=
    Finset.card_le_card_of_injOn (fun k : Fin N => k.val)
      (fun k hk => Finset.mem_coe.mpr (Finset.mem_range.mpr
        ((Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2)))
      (fun x _ y _ h => Fin.ext h)
  rwa [Finset.card_range] at key

/-- The cut projection matrix has rank at most `D`. -/
theorem g10t_projMat_rank_le {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) :
    Matrix.rank (g10t_projMat ψ c D) ≤ D := by
  have hterm : ∀ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
      Matrix.rank (if (k : ℕ) < D then g10t_rk (cutMatrix n d ψ c) k else 0)
        ≤ (if (k : ℕ) < D then (1 : ℕ) else 0) := by
    intro k
    by_cases hk : (k : ℕ) < D
    · rw [ite_eq_left hk, ite_eq_left hk]
      exact g10t_rk_rank_le _ _
    · rw [ite_eq_right hk, ite_eq_right hk, Matrix.rank_zero]
  have hcount : (∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
      (if (k : ℕ) < D then (1 : ℕ) else 0)) ≤ D := by
    rw [Finset.sum_boole]
    exact g10t_card_lt_le _ _
  have hsum : Matrix.rank (g10t_projMat ψ c D)
      ≤ ∑ k : Fin (Fintype.card (Fin (d ^ (n - c)))),
        Matrix.rank (if (k : ℕ) < D then g10t_rk (cutMatrix n d ψ c) k else 0) := by
    rw [g10t_projMat]
    exact g10g_matrixRank_sum_le _
  exact le_trans hsum (le_trans (Finset.sum_le_sum (fun k _ => hterm k)) hcount)

/-- Projecting at a valid cut makes the resulting amplitude function's rank at that cut at most
`D`. -/
theorem g10t_cutProj_cutRank_self {n d : ℕ} (ψ f : (Fin n → Fin d) → ℂ) (c D : ℕ)
    (hc : c ≤ n) : cutRank n d (g10t_cutProj ψ c D hc f) c ≤ D := by
  show Matrix.rank (cutMatrix n d (g10t_cutProj ψ c D hc f) c) ≤ D
  rw [g10t_cutMatrix_cutProj]
  exact le_trans (Matrix.rank_mul_le_left _ _) (g10t_projMat_rank_le ψ c D)

/-- For `j` at most `c`, the first `j` entries of a configuration joined at cut `j` recover its
first component. -/
theorem g10t_splitJoin_head {d j c : ℕ} (hjc : j ≤ c) (u₁ : Fin j → Fin d)
    (u₂ : Fin (c - j) → Fin d) :
    (fun k : Fin j => splitJoin c j d u₁ u₂ ⟨(k : ℕ), lt_of_lt_of_le k.isLt hjc⟩) = u₁ := by
  funext k
  show splitJoin c j d u₁ u₂ ⟨(k : ℕ), lt_of_lt_of_le k.isLt hjc⟩ = u₁ k
  unfold splitJoin
  simp only [Fin.is_lt]
  exact congrArg u₁ (Fin.ext rfl)

/-- For `j` at most `c`, the entries from `j` onward of a configuration joined at cut `j`
recover its second component. -/
theorem g10t_splitJoin_tail {d j c : ℕ} (hjc : j ≤ c) (u₁ : Fin j → Fin d)
    (u₂ : Fin (c - j) → Fin d) :
    (fun k : Fin (c - j) => splitJoin c j d u₁ u₂ ⟨j + (k : ℕ), by omega⟩) = u₂ := by
  funext k
  show splitJoin c j d u₁ u₂ ⟨j + (k : ℕ), by omega⟩ = u₂ k
  unfold splitJoin
  have hnk : ¬(j + (k : ℕ) < j) := by omega
  simp only [hnk]
  refine congrArg u₂ (Fin.ext ?_)
  show j + (k : ℕ) - j = (k : ℕ)
  omega

/-- When `j` is at most `c` and `c` is at most `n`, a configuration joined at cut `c` can
instead be joined at cut `j` by splitting its prefix again. -/
theorem g10t_splitJoin_assoc {n d j c : ℕ} (hjc : j ≤ c) (hcn : c ≤ n)
    (u : Fin c → Fin d) (v : Fin (n - c) → Fin d) :
    splitJoin n c d u v
      = splitJoin n j d (fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt hjc⟩)
          (fun k : Fin (n - j) =>
            if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
            else v ⟨(k : ℕ) - (c - j), by omega⟩) := by
  funext x
  show splitJoin n c d u v x
    = splitJoin n j d (fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt hjc⟩)
        (fun k : Fin (n - j) =>
          if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
          else v ⟨(k : ℕ) - (c - j), by omega⟩) x
  unfold splitJoin
  by_cases hxj : (x : ℕ) < j
  · have hxc : (x : ℕ) < c := lt_of_lt_of_le hxj hjc
    simp only [hxj, hxc]
    exact congrArg u (Fin.ext rfl)
  · by_cases hxc : (x : ℕ) < c
    · have hlt : (x : ℕ) - j < c - j := by omega
      simp only [hxj, hxc, hlt]
      refine congrArg u (Fin.ext ?_)
      show (x : ℕ) = j + ((x : ℕ) - j)
      omega
    · have hlt : ¬((x : ℕ) - j < c - j) := by omega
      simp only [hxj, hxc, hlt]
      refine congrArg v (Fin.ext ?_)
      show (x : ℕ) - c = (x : ℕ) - j - (c - j)
      omega

/-- Joining three consecutive configuration blocks first at cut `j` or first within the prefix
of length `c` gives the same full configuration, for `j` at most `c` at most `n`. -/
theorem g10t_splitJoin_assoc' {n d j c : ℕ} (hjc : j ≤ c) (hcn : c ≤ n)
    (u₁ : Fin j → Fin d) (u₂ : Fin (c - j) → Fin d) (v : Fin (n - c) → Fin d) :
    splitJoin n j d u₁ (fun k : Fin (n - j) =>
        if h : (k : ℕ) < c - j then u₂ ⟨(k : ℕ), h⟩
        else v ⟨(k : ℕ) - (c - j), by omega⟩)
      = splitJoin n c d (splitJoin c j d u₁ u₂) v := by
  funext x
  show splitJoin n j d u₁ (fun k : Fin (n - j) =>
      if h : (k : ℕ) < c - j then u₂ ⟨(k : ℕ), h⟩
      else v ⟨(k : ℕ) - (c - j), by omega⟩) x
    = splitJoin n c d (splitJoin c j d u₁ u₂) v x
  unfold splitJoin
  by_cases hxj : (x : ℕ) < j
  · have hxc : (x : ℕ) < c := lt_of_lt_of_le hxj hjc
    simp only [hxj, hxc]
    exact congrArg u₁ (Fin.ext rfl)
  · by_cases hxc : (x : ℕ) < c
    · have hlt : (x : ℕ) - j < c - j := by omega
      simp only [hxj, hxc, hlt]
      exact congrArg u₂ (Fin.ext rfl)
    · have hlt : ¬((x : ℕ) - j < c - j) := by omega
      simp only [hxj, hxc, hlt]
      refine congrArg v (Fin.ext ?_)
      show (x : ℕ) - j - (c - j) = (x : ℕ) - c
      omega

/-- The encoded first `j` entries of a configuration encoded by an index of `Fin (d ^ c)`,
assuming `j` is at most `c`. -/
noncomputable def g10t_headEnc {d j c : ℕ} (hjc : j ≤ c) (i : Fin (d ^ c)) : Fin (d ^ j) :=
  finPowEnc d j (fun k : Fin j => (finPowEnc d c).symm i
    ⟨(k : ℕ), lt_of_lt_of_le k.isLt hjc⟩)

/-- The encoded final `c - j` entries of a configuration encoded by an index of `Fin (d ^ c)`,
assuming `j` is at most `c`. -/
noncomputable def g10t_tailEnc {d j c : ℕ} (hjc : j ≤ c) (i : Fin (d ^ c)) : Fin (d ^ (c - j)) :=
  finPowEnc d (c - j) (fun k : Fin (c - j) => (finPowEnc d c).symm i
    ⟨j + (k : ℕ), by have h := hjc; omega⟩)

/-- The index encoding the join of decoded blocks of lengths `j` and `c - j`. -/
noncomputable def g10t_joinEnc {d j c : ℕ} (_hjc : j ≤ c) (u₁ : Fin (d ^ j))
    (u₂ : Fin (d ^ (c - j))) : Fin (d ^ c) :=
  finPowEnc d c (splitJoin c j d ((finPowEnc d j).symm u₁) ((finPowEnc d (c - j)).symm u₂))

/-- Extracting the encoded head of the join of two encoded configuration blocks recovers the
first block's index. -/
theorem g10t_headEnc_joinEnc {d j c : ℕ} (hjc : j ≤ c) (u₁ : Fin (d ^ j))
    (u₂ : Fin (d ^ (c - j))) :
    g10t_headEnc hjc (g10t_joinEnc hjc u₁ u₂) = u₁ := by
  simp only [g10t_headEnc, g10t_joinEnc, Equiv.symm_apply_apply]
  rw [g10t_splitJoin_head hjc]
  exact (finPowEnc d j).apply_symm_apply u₁

/-- Extracting the encoded tail of the join of two encoded configuration blocks recovers the
second block's index. -/
theorem g10t_tailEnc_joinEnc {d j c : ℕ} (hjc : j ≤ c) (u₁ : Fin (d ^ j))
    (u₂ : Fin (d ^ (c - j))) :
    g10t_tailEnc hjc (g10t_joinEnc hjc u₁ u₂) = u₂ := by
  simp only [g10t_tailEnc, g10t_joinEnc, Equiv.symm_apply_apply]
  rw [g10t_splitJoin_tail hjc]
  exact (finPowEnc d (c - j)).apply_symm_apply u₂

/-- Joining the encoded head and tail extracted from a configuration index recovers that index. -/
theorem g10t_joinEnc_head_tail {d j c : ℕ} (hjc : j ≤ c) (i : Fin (d ^ c)) :
    g10t_joinEnc hjc (g10t_headEnc hjc i) (g10t_tailEnc hjc i) = i := by
  simp only [g10t_headEnc, g10t_tailEnc, g10t_joinEnc]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have h : splitJoin c j d
        (fun k : Fin j => (finPowEnc d c).symm i ⟨(k : ℕ), lt_of_lt_of_le k.isLt hjc⟩)
        (fun k : Fin (c - j) => (finPowEnc d c).symm i ⟨j + (k : ℕ), by omega⟩)
      = (finPowEnc d c).symm i :=
    (g10a_splitJoinEquiv c j d hjc).apply_symm_apply ((finPowEnc d c).symm i)
  rw [h]
  exact (finPowEnc d c).apply_symm_apply i

/-- The equivalence between a pair of encoded configuration blocks of lengths `j` and `c - j`
and an encoded configuration of length `c`. -/
noncomputable def g10t_joinEncEquiv {d j c : ℕ} (hjc : j ≤ c) :
    (Fin (d ^ j) × Fin (d ^ (c - j))) ≃ Fin (d ^ c) where
  toFun := fun p => g10t_joinEnc hjc p.1 p.2
  invFun := fun i => (g10t_headEnc hjc i, g10t_tailEnc hjc i)
  left_inv := by
    intro p
    rcases p with ⟨u₁, u₂⟩
    show (g10t_headEnc hjc (g10t_joinEnc hjc u₁ u₂),
      g10t_tailEnc hjc (g10t_joinEnc hjc u₁ u₂)) = (u₁, u₂)
    rw [g10t_headEnc_joinEnc, g10t_tailEnc_joinEnc]
  right_inv := by
    intro i
    exact g10t_joinEnc_head_tail hjc i

/-- A sum over encoded configurations of length `c` equals the iterated sum over their encoded
head and tail blocks. -/
theorem g10t_sum_joinEnc {d j c : ℕ} (hjc : j ≤ c) (F : Fin (d ^ c) → ℂ) :
    ∑ i : Fin (d ^ c), F i
      = ∑ u₁ : Fin (d ^ j), ∑ u₂ : Fin (d ^ (c - j)), F (g10t_joinEnc hjc u₁ u₂) := by
  rw [← Equiv.sum_comp (g10t_joinEncEquiv hjc) F]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u₁ _ => ?_)
  refine Finset.sum_congr rfl (fun u₂ _ => ?_)
  rfl

/-- Regrouping a configuration at cuts `j` and `c` preserves it when the middle block is taken
from the tail of a length-`c` configuration, assuming `j` is at most `c` at most `n`. -/
theorem g10t_splitJoin_assoc_mid {n d j c : ℕ} (hjc : j ≤ c) (hcn : c ≤ n)
    (u₁ : Fin j → Fin d) (u : Fin c → Fin d) (v : Fin (n - c) → Fin d) :
    splitJoin n j d u₁ (fun k : Fin (n - j) =>
        if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
        else v ⟨(k : ℕ) - (c - j), by omega⟩)
      = splitJoin n c d
          (splitJoin c j d u₁ (fun k : Fin (c - j) => u ⟨j + (k : ℕ), by omega⟩)) v := by
  funext x
  show splitJoin n j d u₁ (fun k : Fin (n - j) =>
      if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
      else v ⟨(k : ℕ) - (c - j), by omega⟩) x
    = splitJoin n c d
        (splitJoin c j d u₁ (fun k : Fin (c - j) => u ⟨j + (k : ℕ), by omega⟩)) v x
  unfold splitJoin
  by_cases hxj : (x : ℕ) < j
  · have hxc : (x : ℕ) < c := lt_of_lt_of_le hxj hjc
    simp only [hxj, hxc]
    exact congrArg u₁ (Fin.ext rfl)
  · by_cases hxc : (x : ℕ) < c
    · have hlt : (x : ℕ) - j < c - j := by omega
      simp only [hxj, hxc, hlt]
      exact congrArg u (Fin.ext rfl)
    · have hlt : ¬((x : ℕ) - j < c - j) := by omega
      simp only [hxj, hxc, hlt]
      refine congrArg v (Fin.ext ?_)
      show (x : ℕ) - j - (c - j) = (x : ℕ) - c
      omega

/-- The matrix acting by `P` on the encoded head of length `j` and by the identity on the
encoded tail of length `c - j`. -/
noncomputable def g10t_leftKron {d j c : ℕ} (hjc : j ≤ c)
    (P : Matrix (Fin (d ^ j)) (Fin (d ^ j)) ℂ) : Matrix (Fin (d ^ c)) (Fin (d ^ c)) ℂ :=
  Matrix.of fun i i' =>
    P (g10t_headEnc hjc i) (g10t_headEnc hjc i')
      * if g10t_tailEnc hjc i = g10t_tailEnc hjc i' then 1 else 0

/-- An entry of the extended head matrix is the corresponding entry of `P` when the encoded
tails agree, and zero otherwise. -/
theorem g10t_leftKron_apply {d j c : ℕ} (hjc : j ≤ c)
    (P : Matrix (Fin (d ^ j)) (Fin (d ^ j)) ℂ) (i i' : Fin (d ^ c)) :
    g10t_leftKron hjc P i i'
      = P (g10t_headEnc hjc i) (g10t_headEnc hjc i')
        * if g10t_tailEnc hjc i = g10t_tailEnc hjc i' then 1 else 0 :=
  rfl

/-- Applying the extended head matrix to a vector sums over head indices while keeping the
output index's encoded tail fixed. -/
theorem g10t_leftKron_entry {d j c : ℕ} (hjc : j ≤ c)
    (P : Matrix (Fin (d ^ j)) (Fin (d ^ j)) ℂ) (i : Fin (d ^ c)) (F' : Fin (d ^ c) → ℂ) :
    (∑ i' : Fin (d ^ c), g10t_leftKron hjc P i i' * F' i')
      = ∑ u₁ : Fin (d ^ j), P (g10t_headEnc hjc i) u₁
          * F' (g10t_joinEnc hjc u₁ (g10t_tailEnc hjc i)) := by
  rw [g10t_sum_joinEnc hjc (fun i' => g10t_leftKron hjc P i i' * F' i')]
  refine Finset.sum_congr rfl (fun u₁ _ => ?_)
  have hkey : ∀ u₂ : Fin (d ^ (c - j)),
      g10t_leftKron hjc P i (g10t_joinEnc hjc u₁ u₂)
        = P (g10t_headEnc hjc i) u₁ * (if g10t_tailEnc hjc i = u₂ then (1 : ℂ) else 0) := by
    intro u₂
    rw [g10t_leftKron_apply, g10t_headEnc_joinEnc, g10t_tailEnc_joinEnc]
  rw [show (∑ u₂ : Fin (d ^ (c - j)),
        g10t_leftKron hjc P i (g10t_joinEnc hjc u₁ u₂)
          * F' (g10t_joinEnc hjc u₁ u₂))
      = ∑ u₂ : Fin (d ^ (c - j)),
          (P (g10t_headEnc hjc i) u₁ * (if g10t_tailEnc hjc i = u₂ then (1 : ℂ) else 0))
            * F' (g10t_joinEnc hjc u₁ u₂) from
    Finset.sum_congr rfl (fun u₂ _ => by rw [hkey u₂])]
  have hδ : (∑ u₂ : Fin (d ^ (c - j)),
      (P (g10t_headEnc hjc i) u₁ * (if g10t_tailEnc hjc i = u₂ then (1 : ℂ) else 0))
        * F' (g10t_joinEnc hjc u₁ u₂))
      = (P (g10t_headEnc hjc i) u₁
          * (if g10t_tailEnc hjc i = g10t_tailEnc hjc i then (1 : ℂ) else 0))
        * F' (g10t_joinEnc hjc u₁ (g10t_tailEnc hjc i)) :=
    Finset.sum_eq_single (g10t_tailEnc hjc i)
      (fun u₂ _ hne => by rw [ite_eq_right (fun h => hne h.symm), mul_zero, zero_mul])
      (fun ha => absurd (Finset.mem_univ (g10t_tailEnc hjc i)) ha)
  rw [hδ, ite_eq_left rfl, mul_one]

/-- For `j < c` and `c` at most `n`, evaluating the cut-`j` projection on a configuration joined
at `c` is the corresponding entry of the projected cut-`j` matrix after regrouping its
blocks. -/
theorem g10t_cutProj_apply_left {n d : ℕ} {j c : ℕ} (hjc : j < c) (hcn : c ≤ n)
    (ψ f : (Fin n → Fin d) → ℂ) (D : ℕ) (u : Fin c → Fin d) (v : Fin (n - c) → Fin d) :
    g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f (splitJoin n c d u v)
      = (g10t_projMat ψ j D * cutMatrix n d f j)
          (finPowEnc d j (fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt (le_of_lt hjc)⟩))
          (finPowEnc d (n - j) (fun k : Fin (n - j) =>
            if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
            else v ⟨(k : ℕ) - (c - j), by omega⟩)) := by
  have hassoc : splitJoin n c d u v
      = splitJoin n j d (fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt (le_of_lt hjc)⟩)
          (fun k : Fin (n - j) =>
            if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
            else v ⟨(k : ℕ) - (c - j), by omega⟩) :=
    g10t_splitJoin_assoc (le_of_lt hjc) hcn u v
  unfold g10t_cutProj
  rw [hassoc]
  show g10t_ofCut j (le_of_lt (lt_of_lt_of_le hjc hcn))
      (g10t_projMat ψ j D * cutMatrix n d f j)
      (splitJoin n j d
        (fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt (le_of_lt hjc)⟩)
        (fun k : Fin (n - j) =>
          if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
          else v ⟨(k : ℕ) - (c - j), by omega⟩))
    = _
  simp only [g10t_ofCut]
  rw [show splitJoin n j d
        (fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt (le_of_lt hjc)⟩)
        (fun k : Fin (n - j) =>
          if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
          else v ⟨(k : ℕ) - (c - j), by omega⟩)
      = (g10a_splitJoinEquiv n j d (le_of_lt (lt_of_lt_of_le hjc hcn)))
          ((fun k : Fin j => u ⟨(k : ℕ), lt_of_lt_of_le k.isLt (le_of_lt hjc)⟩),
            (fun k : Fin (n - j) =>
              if h : (k : ℕ) < c - j then u ⟨j + (k : ℕ), by omega⟩
              else v ⟨(k : ℕ) - (c - j), by omega⟩)) from rfl]
  rw [Equiv.symm_apply_apply]

/-- For `j < c` and `c` at most `n`, an entry of the cut-`c` matrix after projection at `j` is a
sum over head indices weighted by the cut-`j` projection matrix, with the tail index fixed. -/
theorem g10t_cutProj_entry_lt {n d : ℕ} {j c : ℕ} (hjc : j < c) (hcn : c ≤ n)
    (ψ f : (Fin n → Fin d) → ℂ) (D : ℕ) (i : Fin (d ^ c)) (jcol : Fin (d ^ (n - c))) :
    cutMatrix n d (g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f) c i jcol
      = ∑ k : Fin (d ^ j),
          g10t_projMat ψ j D (g10t_headEnc (le_of_lt hjc) i) k
            * cutMatrix n d f c
                (g10t_joinEnc (le_of_lt hjc) k (g10t_tailEnc (le_of_lt hjc) i)) jcol := by
  have hval : cutMatrix n d (g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f) c i jcol
      = g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f
          (splitJoin n c d ((finPowEnc d c).symm i) ((finPowEnc d (n - c)).symm jcol)) := rfl
  rw [hval]
  rw [g10t_cutProj_apply_left hjc hcn ψ f D ((finPowEnc d c).symm i)
    ((finPowEnc d (n - c)).symm jcol)]
  rw [Matrix.mul_apply]
  have hhead : (finPowEnc d j (fun k : Fin j => (finPowEnc d c).symm i
        ⟨(k : ℕ), lt_of_lt_of_le k.isLt (le_of_lt hjc)⟩))
      = g10t_headEnc (le_of_lt hjc) i := rfl
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hhead]
  congr 1
  have hA : cutMatrix n d f j k
        (finPowEnc d (n - j) (fun m : Fin (n - j) =>
          if h : (m : ℕ) < c - j then (finPowEnc d c).symm i ⟨j + (m : ℕ), by omega⟩
          else (finPowEnc d (n - c)).symm jcol ⟨(m : ℕ) - (c - j), by omega⟩))
      = f (splitJoin n j d ((finPowEnc d j).symm k) (fun m : Fin (n - j) =>
          if h : (m : ℕ) < c - j then (finPowEnc d c).symm i ⟨j + (m : ℕ), by omega⟩
          else (finPowEnc d (n - c)).symm jcol ⟨(m : ℕ) - (c - j), by omega⟩)) := by
    rw [g10a_cutMatrix_apply]
    congr 1
    congr 1
    exact (finPowEnc d (n - j)).symm_apply_apply _
  rw [hA]
  rw [g10t_splitJoin_assoc_mid (le_of_lt hjc) hcn ((finPowEnc d j).symm k)
    ((finPowEnc d c).symm i) ((finPowEnc d (n - c)).symm jcol)]
  have hC : f (splitJoin n c d
        (splitJoin c j d ((finPowEnc d j).symm k)
          (fun m : Fin (c - j) => (finPowEnc d c).symm i ⟨j + (m : ℕ), by omega⟩))
        ((finPowEnc d (n - c)).symm jcol))
      = cutMatrix n d f c
          (finPowEnc d c (splitJoin c j d ((finPowEnc d j).symm k)
            (fun m : Fin (c - j) => (finPowEnc d c).symm i ⟨j + (m : ℕ), by omega⟩))) jcol := by
    rw [g10a_cutMatrix_apply]
    congr 1
    congr 1
    exact ((finPowEnc d c).symm_apply_apply _).symm
  rw [hC]
  congr 1
  have hfin : finPowEnc d c
        (splitJoin c j d ((finPowEnc d j).symm k)
          (fun m : Fin (c - j) => (finPowEnc d c).symm i ⟨j + (m : ℕ), by omega⟩))
      = g10t_joinEnc (le_of_lt hjc) k (g10t_tailEnc (le_of_lt hjc) i) := by
    rw [g10t_joinEnc, g10t_tailEnc]
    congr 1
    congr 1
    exact ((finPowEnc d (c - j)).symm_apply_apply _).symm
  rw [hfin]

/-- For `j < c` and `c` at most `n`, projecting at cut `j` acts on the cut-`c` matrix by left
multiplication with the projection matrix extended by the identity on the intervening block. -/
theorem g10t_cutMatrix_cutProj_of_lt {n d : ℕ} {j c : ℕ} (hjc : j < c) (hcn : c ≤ n)
    (ψ f : (Fin n → Fin d) → ℂ) (D : ℕ) :
    cutMatrix n d (g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f) c
      = g10t_leftKron (le_of_lt hjc) (g10t_projMat ψ j D) * cutMatrix n d f c := by
  ext i jcol
  rw [Matrix.mul_apply, g10t_cutProj_entry_lt hjc hcn ψ f D i jcol,
    g10t_leftKron_entry (le_of_lt hjc) (g10t_projMat ψ j D) i
      (fun i' => cutMatrix n d f c i' jcol)]

/-- Projection at an earlier cut `j` cannot increase the rank at a later valid cut `c`. -/
theorem g10t_cutRank_cutProj_of_lt {n d : ℕ} {j c : ℕ} (hjc : j < c) (hcn : c ≤ n)
    (ψ f : (Fin n → Fin d) → ℂ) (D : ℕ) :
    cutRank n d (g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f) c
      ≤ cutRank n d f c := by
  show Matrix.rank (cutMatrix n d (g10t_cutProj ψ j D (le_of_lt (lt_of_lt_of_le hjc hcn)) f) c)
    ≤ Matrix.rank (cutMatrix n d f c)
  rw [g10t_cutMatrix_cutProj_of_lt hjc hcn ψ f D]
  exact Matrix.rank_mul_le_right _ _

/-- After `k` successive projections, every cut `c` with `n - k` at most `c` and `c < n` has
rank at most `D`. -/
theorem g10t_iter_cutRank_aux {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ) :
    ∀ k c, n - k ≤ c → c < n → cutRank n d (g10t_iter ψ D k) c ≤ D := by
  intro k
  induction k with
  | zero =>
    intro c h1 h2
    omega
  | succ k ih =>
    intro c h1 h2
    have hstep : g10t_iter ψ D (k + 1)
        = g10t_cutProj ψ (n - 1 - k) D (by omega) (g10t_iter ψ D k) := rfl
    rw [hstep]
    by_cases hc : c = n - 1 - k
    · subst hc
      exact g10t_cutProj_cutRank_self ψ (g10t_iter ψ D k) (n - 1 - k) D (by omega)
    · have hlt : n - 1 - k < c := by omega
      exact le_trans
        (g10t_cutRank_cutProj_of_lt hlt (le_of_lt h2) ψ (g10t_iter ψ D k) D)
        (ih c (by omega) h2)

/-- For positive `D`, every cut before `n` of the state obtained after `n - 1` successive
projections has rank at most `D`. -/
theorem g10t_iter_cutRank_le {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ) (D : ℕ) (hD : 0 < D) :
    ∀ c < n, cutRank n d (g10t_iter ψ D (n - 1)) c ≤ D := by
  intro c hc
  by_cases h0 : c = 0
  · subst h0
    exact le_trans (cutRank_le_one_left (g10t_iter ψ D (n - 1))) (by omega)
  · exact g10t_iter_cutRank_aux ψ D (n - 1) c (by omega) hc

/-- For a nonempty chain and positive `D`, there is an approximating amplitude function with
every cut rank before `n` at most `D` and squared error at most twice the total discarded
squared Schmidt tail. -/
theorem g10t_trunc_approximant (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) (hn : 1 ≤ n)
    (D : ℕ) (hDpos : 0 < D) :
    ∃ ψ' : (Fin n → Fin d) → ℂ, (∀ c < n, cutRank n d ψ' c ≤ D)
      ∧ ∑ x, Complex.normSq (ψ' x - ψ x)
        ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  refine ⟨g10t_iter ψ D (n - 1), g10t_iter_cutRank_le ψ D hDpos,
    g10t_iter_error_final ψ hn D⟩

/-- Every normalized state on at least one site has, for each positive bond dimension `D`, an
MPS approximation with total squared amplitude error at most twice the sum of its discarded
squared Schmidt tails over cuts before `n`. This is the approximation estimate associated
with Theorem 15 of [PerezGarciaEtAl2007]. -/
theorem clause2_clause3 (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ)
    (_hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    1 ≤ n → ∀ D : ℕ, 0 < D →
      ∃ (hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
        ∑ x, Complex.normSq (@mpsAmplitude n d D hD A x - ψ x)
          ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D := by
  intro hn D hDpos
  by_cases hrank : ∀ c ∈ Finset.range n, cutRank n d ψ c ≤ D
  · exact g10g_clause3_of_cutRank_le n d ψ hn D hDpos hrank
  · by_cases htail : 1 ≤ 2 * ∑ c ∈ Finset.range n, schmidtTailSq n d ψ c D
    · exact g10g_clause3_of_one_le_two_tail n d ψ _hnorm hn D hDpos htail
    · obtain ⟨ψ', hcut, herr⟩ := g10t_trunc_approximant n d ψ hn D hDpos
      exact g10g_clause3_of_approximant n d ψ ψ' hn D hDpos hcut herr

end Qatlib.Concepts.TensorNetwork.GaugeInvariance
