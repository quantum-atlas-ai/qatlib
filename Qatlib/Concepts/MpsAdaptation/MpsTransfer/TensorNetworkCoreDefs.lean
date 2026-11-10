/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
set_option warningAsError false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix
open scoped BigOperators Nat ComplexConjugate

structure TensorNet where

  nv : ℕ

  nh : ℕ

  dims : Fin nh → ℕ

  site : Fin nh → Fin nv

  partner : Fin nh → Option (Fin nh)
  involution : ∀ h k, partner h = some k → partner k = some h
  no_self_loop : ∀ h k, partner h = some k → h ≠ k
  dims_match : ∀ h k, partner h = some k → dims h = dims k

  tensor : (v : Fin nv) → (∀ h : {h : Fin nh // site h = v}, Fin (dims h.val)) → ℂ

def OpenLeg (N : TensorNet) : Type := {h : Fin N.nh // N.partner h = none}

def InternalEdge (N : TensorNet) : Type := {h : Fin N.nh // ∃ k, N.partner h = some k ∧ h < k}

instance {N : TensorNet} : Fintype (OpenLeg N) := Subtype.fintype _

instance {N : TensorNet} : Fintype (InternalEdge N) := Subtype.fintype _

instance {N : TensorNet} : DecidableEq (InternalEdge N) :=
  fun a b =>
    if h : a.val = b.val then isTrue (Subtype.ext h)
    else isFalse (fun g => h (congrArg Subtype.val g))

instance {N : TensorNet} : Fintype (∀ i : InternalEdge N, Fin (N.dims i.val)) :=
  Pi.instFintype

instance {N : TensorNet} (v : Fin N.nv) :
    Fintype (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) := Pi.instFintype

noncomputable def portValue (N : TensorNet) (ext : ∀ o : OpenLeg N, Fin (N.dims o.val))
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) (j : Fin N.nh) : Fin (N.dims j) :=
  match hj : N.partner j with
  | none => ext ⟨j, hj⟩
  | some k =>
      if hlt : j < k then e ⟨j, ⟨k, hj, hlt⟩⟩
      else
        (e ⟨k, ⟨j, N.involution j k hj,
              (lt_or_gt_of_ne (N.no_self_loop j k hj)).resolve_left hlt⟩⟩).cast
          (by rw [← N.dims_match j k hj])

noncomputable def netContract (N : TensorNet) (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) : ℂ :=
  ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
    ∏ v : Fin N.nv, N.tensor v (fun h => portValue N ext e h.val)

def netBondDimension (N : TensorNet) : ℕ :=
  Finset.univ.sup fun i : InternalEdge N => N.dims i.val

noncomputable def tensorSumNorm (N : TensorNet) (v : Fin N.nv) : ℝ :=
  ∑ a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val), ‖N.tensor v a‖

structure NetIso (N₁ N₂ : TensorNet) where

  vertexMap : Fin N₁.nv ≃ Fin N₂.nv

  halfMap : Fin N₁.nh ≃ Fin N₂.nh
  dims_map : ∀ h, N₂.dims (halfMap h) = N₁.dims h
  site_map : ∀ h, N₂.site (halfMap h) = vertexMap (N₁.site h)
  partner_map : ∀ h, N₂.partner (halfMap h) = (N₁.partner h).map halfMap
  tensor_map : ∀ (v : Fin N₁.nv) (a : ∀ h : {h : Fin N₁.nh // N₁.site h = v},
      Fin (N₁.dims h.val)),
    N₂.tensor (vertexMap v)
        (fun h' => (a ⟨halfMap.symm h'.val, by
          have h2 := site_map (halfMap.symm h'.val)
          rw [Equiv.apply_symm_apply] at h2
          exact vertexMap.injective (h2.symm.trans h'.property)⟩).cast
          ((dims_map (halfMap.symm h'.val)).symm.trans
            (congrArg N₂.dims (halfMap.apply_symm_apply h'.val)))) = N₁.tensor v a

noncomputable def gaugeKernel (N : TensorNet)
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    {h k : Fin N.nh} (hk : N.partner h = some k) (i i' : Fin (N.dims h)) : ℂ :=
  if hlt : h < k then U ⟨h, ⟨k, hk, hlt⟩⟩ i i'
  else
    conj (U ⟨k, ⟨h, N.involution h k hk,
          (lt_or_gt_of_ne (N.no_self_loop h k hk)).resolve_left hlt⟩⟩
      (i.cast (by rw [← N.dims_match h k hk]))
      (i'.cast (by rw [← N.dims_match h k hk])))

noncomputable def gaugeTensor (N : TensorNet)
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) : ℂ :=
  ∑ x : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
    (∏ h : {h : Fin N.nh // N.site h = v},
      match hk : N.partner h.val with
      | none => if a h = x h then (1 : ℂ) else 0
      | some _k => gaugeKernel N U hk (a h) (x h)) * N.tensor v x

noncomputable def gaugeNet (N : TensorNet)
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ) :
    TensorNet where
  nv := N.nv
  nh := N.nh
  dims := N.dims
  site := N.site
  partner := N.partner
  involution := N.involution
  no_self_loop := N.no_self_loop
  dims_match := N.dims_match
  tensor := gaugeTensor N U

def mpsLeftIdx {n D : ℕ} [NeZero D] (α : Fin (n - 1) → Fin D) (i : Fin n) : Fin D :=
  if (i : ℕ) = 0 then 0
  else if h2 : (i : ℕ) - 1 < n - 1 then α ⟨(i : ℕ) - 1, h2⟩ else 0

def mpsRightIdx {n D : ℕ} [NeZero D] (α : Fin (n - 1) → Fin D) (i : Fin n) : Fin D :=
  if h : (i : ℕ) < n - 1 then α ⟨(i : ℕ), h⟩ else 0

noncomputable def mpsAmplitude {n d D : ℕ} [NeZero D] (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) : ℂ :=
  ∑ α : Fin (n - 1) → Fin D,
    ∏ i : Fin n, A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)

noncomputable def periodicMpsAmplitude {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) : ℂ :=
  ∑ α : Fin n → Fin D,
    ∏ i : Fin n, A i (x i) (α i) (α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)

noncomputable def pepsAmplitude {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) : ℂ :=
  ∑ γ : Fin a × Fin b → Fin D × Fin D,
    ∏ p : Fin a × Fin b,
      T p.1 p.2 (x p.1 p.2)
        (if h : (p.1 : ℕ) = 0 then 0
          else (γ ((⟨(p.1 : ℕ) - 1, by have := p.1.isLt; omega⟩ : Fin a), p.2)).1)
        (if (p.1 : ℕ) + 1 = a then 0 else (γ p).1)
        (if (p.2 : ℕ) + 1 = b then 0 else (γ p).2)
        (if h : (p.2 : ℕ) = 0 then 0
          else (γ (p.1, (⟨(p.2 : ℕ) - 1, by have := p.2.isLt; omega⟩ : Fin b))).2)

def splitJoin (n c d : ℕ) (u : Fin c → Fin d) (v : Fin (n - c) → Fin d) : Fin n → Fin d :=
  fun k =>
    if h : (k : ℕ) < c then u ⟨k, h⟩
    else v ⟨(k : ℕ) - c, by have hk := k.isLt; omega⟩

def finPowEnc (d k : ℕ) : (Fin k → Fin d) ≃ Fin (d ^ k) := finFunctionFinEquiv

noncomputable def cutMatrix (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) (c : ℕ) :
    Matrix (Fin (d ^ c)) (Fin (d ^ (n - c))) ℂ :=
  Matrix.of fun i j => ψ (splitJoin n c d ((finPowEnc d c).symm i) ((finPowEnc d (n - c)).symm j))

noncomputable def cutRank (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) (c : ℕ) : ℕ :=
  Matrix.rank (cutMatrix n d ψ c)

noncomputable def schmidtTailSq (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) (c D : ℕ) : ℝ :=
  ∑ i ∈ (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (cutMatrix n d ψ c)).support.filter (fun i => D ≤ i),
    (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues (cutMatrix n d ψ c) i) ^ 2

def IsMpsRepresentation {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x, mpsAmplitude A x = ψ x

def LeftCanonical {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ i : Fin n, (i : ℕ) + 2 ≤ n → ∑ x : Fin d, (A i x)ᴴ * (A i x) = 1

def ratEntryWidth (q : ℚ) : ℕ :=
  max (Nat.log2 q.num.natAbs + 1) (Nat.log2 q.den + 1)

def ringOpBitCost (w : ℕ) : ℕ := (w + 2) ^ 2

noncomputable def mpsEvalVector {n d D : ℕ} {R : Type} [CommRing R] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d) :
    (i : Fin n) → Fin D → R
  | ⟨0, h0⟩ => fun j => A ⟨0, h0⟩ (x ⟨0, h0⟩) ⟨0, NeZero.pos D⟩ j
  | ⟨i + 1, hi⟩ =>
      fun j => ∑ k : Fin D,
        mpsEvalVector A x ⟨i, Nat.lt_of_succ_lt hi⟩ k
          * A ⟨i + 1, hi⟩ (x ⟨i + 1, hi⟩) k j
termination_by i => i.val

noncomputable def mpsEval {n d D : ℕ} {R : Type} [CommRing R] [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d) : R :=
  ∑ j : Fin D, mpsEvalVector A x ⟨n - 1, Nat.sub_lt (NeZero.pos n) one_pos⟩ j

def mpsEvalOpCount (n D : ℕ) : ℕ := n * (2 * D * D) + D

noncomputable def mpsEvalVectorCount {n d D : ℕ} {R : Type} [CommRing R] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d) :
    (i : Fin n) → (Fin D → R) × ℕ
  | ⟨0, h0⟩ => ((fun j => A ⟨0, h0⟩ (x ⟨0, h0⟩) ⟨0, NeZero.pos D⟩ j), 0)
  | ⟨i + 1, hi⟩ =>
      let prev := mpsEvalVectorCount A x ⟨i, Nat.lt_of_succ_lt hi⟩
      ((fun j => ∑ k : Fin D, prev.1 k * A ⟨i + 1, hi⟩ (x ⟨i + 1, hi⟩) k j),
        prev.2 + 2 * D * D)
termination_by i => i.val

noncomputable def mpsEvalWithCount {n d D : ℕ} {R : Type} [CommRing R] [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) R) (x : Fin n → Fin d) : R × ℕ :=
  let last := mpsEvalVectorCount A x ⟨n - 1, Nat.sub_lt (NeZero.pos n) one_pos⟩
  (∑ j : Fin D, last.1 j, last.2 + D)

noncomputable def mpsInnerTransfer {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) : (i : Fin n) → Matrix (Fin D) (Fin D) ℂ
  | ⟨0, h0⟩ => ∑ x : Fin d, (A ⟨0, h0⟩ x)ᴴ * (B ⟨0, h0⟩ x)
  | ⟨i + 1, hi⟩ =>
      ∑ x : Fin d, (A ⟨i + 1, hi⟩ x)ᴴ *
        mpsInnerTransfer A B ⟨i, Nat.lt_of_succ_lt hi⟩ * (B ⟨i + 1, hi⟩ x)
termination_by i => i.val

noncomputable def mpsInnerEval {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  mpsInnerTransfer A B ⟨n - 1, Nat.sub_lt (NeZero.pos n) one_pos⟩ ⟨0, NeZero.pos D⟩ ⟨0, NeZero.pos D⟩

def mpsInnerOpCount (n d D : ℕ) : ℕ := n * (2 * d * D * D * D + 2 * D * D)

noncomputable def mpsInnerTransferCount {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (i : Fin n) → Matrix (Fin D) (Fin D) ℂ × ℕ
  | ⟨0, h0⟩ =>
      (∑ x : Fin d, (A ⟨0, h0⟩ x)ᴴ * (B ⟨0, h0⟩ x), d * (2 * D * D * D))
  | ⟨i + 1, hi⟩ =>
      let prev := mpsInnerTransferCount A B ⟨i, Nat.lt_of_succ_lt hi⟩
      (∑ x : Fin d, (A ⟨i + 1, hi⟩ x)ᴴ * prev.1 * (B ⟨i + 1, hi⟩ x),
        prev.2 + d * (2 * D * D * D) + 2 * D * D)
termination_by i => i.val

noncomputable def mpsInnerEvalWithCount {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) : ℂ × ℕ :=
  let last := mpsInnerTransferCount A B ⟨n - 1, Nat.sub_lt (NeZero.pos n) one_pos⟩
  (last.1 ⟨0, NeZero.pos D⟩ ⟨0, NeZero.pos D⟩, last.2 + D)

noncomputable def obsTensors {n d D : ℕ} [NeZero D] (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (z : Fin n) (O : Matrix (Fin d) (Fin d) ℂ) : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i x => if i = z then (∑ y : Fin d, O x y • B z y) else B i x

def pepsStripOpCount (a b D : ℕ) : ℕ := b * ((D ^ a) ^ 3 * (a + 2) + 1)

noncomputable def pepsColKernel {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) (j : Fin b) (σ ρ χ : Fin a → Fin D) : ℂ :=
  ∏ i : Fin a,
    T i j (x i j)
      (if (i : ℕ) = 0 then 0 else ρ ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩)
      (if (i : ℕ) + 1 = a then 0 else ρ i)
      (if (j : ℕ) + 1 = b then 0 else χ i)
      (if (j : ℕ) = 0 then 0 else σ i)

noncomputable def pepsStripFold {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) : ℕ → ((Fin a → Fin D) → ℂ) × ℕ
  | 0 => ((fun σ => if σ = fun _ => ⟨0, NeZero.pos D⟩ then 1 else 0), 0)
  | j + 1 =>
      let prev := pepsStripFold T x j
      ((fun χ => ∑ σ : Fin a → Fin D, ∑ ρ : Fin a → Fin D,
          prev.1 σ * (if h : j < b then pepsColKernel T x ⟨j, h⟩ σ ρ χ else 0)),
        prev.2 + (D ^ a) ^ 3 * (a + 2))
termination_by j => j

noncomputable def pepsStripEvalWithCount {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) : ℂ × ℕ :=
  let r := pepsStripFold T x b
  (r.1 (fun _ => ⟨0, NeZero.pos D⟩), r.2)

noncomputable def tvDist {ι : Type} [Fintype ι] (p q : ι → ℝ) : ℝ := (∑ i, |p i - q i|) / 2

noncomputable def uniformPushForward {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (S : (Fin k → Bool) → ι) : ι → ℝ :=
  fun x => (Finset.univ.filter (fun t => S t = x)).card / (2 ^ k : ℝ)

noncomputable def mpsSampleLaw {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) : (Fin n → Fin d) → ℝ :=
  fun x => Complex.normSq (mpsAmplitude A x)
    / ∑ x', Complex.normSq (mpsAmplitude A x')

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
