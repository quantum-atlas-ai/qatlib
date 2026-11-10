/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkExt
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin.Basic

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

set_option autoImplicit false

namespace Qatlib.Concepts.DyadicOverlap.ArithLedger

open Matrix
open scoped BigOperators

structure BitTensorNet (N : TensorNet) where

  precision : ℕ

  num : (v : Fin N.nv) → (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) → ℤ

noncomputable def decodeNet (N : TensorNet) (T : BitTensorNet N) : TensorNet :=
  { N with tensor := fun v a => (T.num v a : ℂ) / 2 ^ T.precision }

noncomputable def netContractInt (N : TensorNet) (T : BitTensorNet N)
    (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)) : ℤ :=
  ∑ e : ∀ i : InternalEdge N, Fin (N.dims i.val),
    ∏ v : Fin N.nv, T.num v (fun h => portValue N ext e h.val)

noncomputable def bitTensorSumNorm (N : TensorNet) (T : BitTensorNet N) (v : Fin N.nv) : ℝ :=
  ∑ a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val),
    ‖((T.num v a : ℤ) : ℝ)‖

def bitTensorMaxAbs (N : TensorNet) (T : BitTensorNet N) : ℕ :=
  (Finset.univ.sup fun v : Fin N.nv =>
    (Finset.univ.sup fun a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) =>
      (T.num v a).natAbs))

def BitMps (n d D : ℕ) : Type :=
  Fin n → Fin d → Matrix (Fin D) (Fin D) ℤ

def bitMpsSiteList {n d D : ℕ} (A : BitMps n d D) (x : Fin n → Fin d) :
    List (Fin D → Fin D → ℤ) :=
  List.ofFn fun i : Fin n => fun l r => A i (x i) l r

noncomputable def bitMpsAmplitude {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) : ℤ :=
  ∑ α : Fin (n - 1) → Fin D,
    ∏ i : Fin n, A i (x i) (mpsLeftIdx α i) (mpsRightIdx α i)

noncomputable def bitPeriodicMpsAmplitude {n d D : ℕ} [NeZero n] [NeZero D]
    (A : BitMps n d D) (x : Fin n → Fin d) : ℤ :=
  ∑ α : Fin n → Fin D,
    ∏ i : Fin n, A i (x i) (α i)
      (α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)

def BitPeps (a b d D : ℕ) : Type :=
  Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℤ

def bitPepsLeft {a b D : ℕ} [NeZero D] (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.1 : ℕ) = 0 then 0 else (γ (⟨(p.1 : ℕ) - 1, by omega⟩, p.2)).1

def bitPepsRight {a b D : ℕ} [NeZero D] (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.1 : ℕ) + 1 = a then 0 else (γ p).1

def bitPepsUp {a b D : ℕ} [NeZero D] (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.2 : ℕ) = 0 then 0 else (γ (p.1, ⟨(p.2 : ℕ) - 1, by omega⟩)).2

def bitPepsDown {a b D : ℕ} [NeZero D] (γ : Fin a × Fin b → Fin D × Fin D)
    (p : Fin a × Fin b) : Fin D :=
  if (p.2 : ℕ) + 1 = b then 0 else (γ p).2

noncomputable def bitPepsAmplitude {a b d D : ℕ} [NeZero D] (T : BitPeps a b d D)
    (x : Fin a → Fin b → Fin d) : ℤ :=
  ∑ γ : Fin a × Fin b → Fin D × Fin D,
    ∏ p : Fin a × Fin b,
      T p.1 p.2 (x p.1 p.2)
        (bitPepsLeft γ p) (bitPepsRight γ p) (bitPepsUp γ p) (bitPepsDown γ p)

def bitShortChainTensors : Fin 3 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ :=
  fun i y => Matrix.of fun a b =>
    if (i : ℕ) = 0 then
      (if (a : ℕ) = 0 then (if (y : ℕ) = 0 then (if (b : ℕ) = 0 then 1 else 0) else 1) else 0)
    else if (i : ℕ) = 1 then
      (if (y : ℕ) = 0 ∧ a = b then 1 else 0)
    else (if (b : ℕ) = 0 then (if (y : ℕ) = 0 then (if (a : ℕ) = 1 then 1 else 0) else 1) else 0)

structure IntLedger where

  muls : ℕ

  adds : ℕ

  subs : ℕ
  deriving DecidableEq

def bitTimeOf (w : ℕ) (l : IntLedger) : ℕ :=
  (l.muls + l.adds + l.subs) * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost w

def peakWorkspace (D : ℕ) : ℕ := D

noncomputable def bitSampleLaw {n d D : ℕ} [NeZero D] (A : BitMps n d D) :
    (Fin n → Fin d) → ℚ :=
  fun x => (bitMpsAmplitude A x ^ 2) / (∑ y, bitMpsAmplitude A y ^ 2)

def clause1StatementNext : Prop :=
  Clause18Claim
  ∧ (∀ (N : TensorNet) (T : BitTensorNet N)
        (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)),
      netContract (decodeNet N T) ext
        = ((2 : ℂ) ^ (T.precision * N.nv))⁻¹ * (netContractInt N T ext : ℂ))
  ∧ (∀ (N : TensorNet) (T : BitTensorNet N)
        (ext : ∀ o : OpenLeg N, Fin (N.dims o.val)),
      ‖netContract (decodeNet N T) ext‖
        ≤ ((2 : ℝ) ^ (T.precision * N.nv))⁻¹
          * ∏ v : Fin N.nv, bitTensorSumNorm N T v)
  ∧ (∀ (N : TensorNet) (T : BitTensorNet N),
      (∃ i : InternalEdge N, N.dims i.val = 0) →
        ∀ ext : ∀ o : OpenLeg N, Fin (N.dims o.val), netContractInt N T ext = 0)
  ∧ (∀ (N : TensorNet) (T : BitTensorNet N), N.nv = 0 → N.nh = 0 →
        ∀ ext : ∀ o : OpenLeg N, Fin (N.dims o.val), netContractInt N T ext = 1)
  ∧ (∀ {n d D : ℕ} [NeZero D] (A : BitMps n d D) (x : Fin n → Fin d),
      n = 0 → bitMpsAmplitude A x = 1)
  ∧ (∀ {n d : ℕ} (g : Fin n → Fin d → ℤ) (x : Fin n → Fin d),
      @bitMpsAmplitude n d 1 inferInstance
        ((fun (i : Fin n) (y : Fin d) => Matrix.of (fun _ _ => g i y))
          : Fin n → Fin d → Matrix (Fin 1) (Fin 1) ℤ) x
        = ∏ i, g i (x i))
  ∧ (∀ x : Fin 3 → Fin 2,
      bitMpsAmplitude bitShortChainTensors x
        = if (x 1 : ℕ) = 0 then
            (if (x 0 : ℕ) = 1 then (1 : ℤ) else 0) + (if (x 2 : ℕ) = 1 then (1 : ℤ) else 0)
          else 0)
  ∧ (∀ (N : TensorNet) (T : BitTensorNet N) (v : Fin N.nv)
      (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      (T.num v a).natAbs ≤ bitTensorMaxAbs N T)
  ∧ (∀ (N : TensorNet) (T : BitTensorNet N) (w : ℕ),
      (∀ (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
        (T.num v a).natAbs ≤ 2 ^ w) →
      ∀ v : Fin N.nv,
        bitTensorSumNorm N T v
          ≤ (Fintype.card (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val))) * 2 ^ w)

abbrev BitSiteList (D : ℕ) := List (Fin D → Fin D → ℤ)

def chainKeys {D : ℕ} (k : ℕ) (b c : Fin D) (γ : Fin (k - 1) → Fin D) : Fin (k + 1) → Fin D :=
  fun j => dite ((j : ℕ) = 0) (fun _ => b)
    (fun h0 => dite ((j : ℕ) = k) (fun _ => c)
      (fun hk => γ ⟨(j : ℕ) - 1, by omega⟩))

noncomputable def chainSum {D : ℕ} (Ms : BitSiteList D)
    (β : Fin (Ms.length + 1) → Fin D) : ℤ :=
  ∏ p : Fin Ms.length, Ms[p]
    (β ⟨(p : ℕ), by omega⟩) (β ⟨(p : ℕ) + 1, by omega⟩)

noncomputable def chainTotal {D : ℕ} (Ms : BitSiteList D) (b c : Fin D) : ℤ :=
  match Ms with
  | [] => if b = c then 1 else 0
  | M :: rest =>
      ∑ γ : Fin rest.length → Fin D, chainSum (M :: rest) (chainKeys (rest.length + 1) b c γ)

theorem sum_fin_zero_pi {D : ℕ} {M : Type*} [AddCommMonoid M] (c : M) :
    (∑ _ : Fin 0 → Fin D, c) = c := by
  have e : (Fin 0 → Fin D) ≃ Fin 1 :=
    { toFun := fun _ => ⟨0, by decide⟩
      invFun := fun _ => fun i => Fin.elim0 i
      left_inv := by
        intro f
        funext i
        exact Fin.elim0 i
      right_inv := by
        intro f
        apply Fin.ext
        have := f.isLt
        omega }
  have h := Fintype.sum_equiv e (fun _ : Fin 0 → Fin D => c) (fun _ : Fin 1 => c) (fun _ => rfl)
  rw [h]
  exact Fintype.sum_unique (fun _ : Fin 1 => c)

noncomputable def chainBackVec {D : ℕ} (Ms : BitSiteList D) (c : Fin D) : Fin D → ℤ :=
  match Ms with
  | [] => fun j => if j = c then 1 else 0
  | M :: Ms' => fun j => ∑ k : Fin D, M j k * chainBackVec Ms' c k

structure BitBackState (D : ℕ) where

  vec : Fin D → ℤ

  ledger : IntLedger

noncomputable def chainBackCount {D : ℕ} (Ms : BitSiteList D) (c : Fin D) : BitBackState D :=
  match Ms with
  | [] => ⟨fun j => if j = c then 1 else 0, ⟨0, 0, 0⟩⟩
  | M :: Ms' =>
      let s := chainBackCount Ms' c
      ⟨fun j => ∑ k : Fin D, M j k * s.vec k,
        ⟨s.ledger.muls + D * D, s.ledger.adds + D * D, s.ledger.subs⟩⟩

def finConsEquiv {m : ℕ} {X : Type*} : (Fin (m + 1) → X) ≃ X × (Fin m → X) where
  toFun f := (f 0, fun j => f ⟨(j : ℕ) + 1, by omega⟩)
  invFun p := fun j => if h : j = 0 then p.1 else p.2 ⟨(j : ℕ) - 1, by omega⟩
  left_inv := by
    intro f
    funext j
    refine Fin.cases ?_ (fun j' => ?_) j
    · rfl
    · have hne : j'.succ ≠ 0 := Fin.succ_ne_zero _
      simp only [dif_neg hne]
      congr 1
  right_inv := by
    intro p
    rcases p with ⟨a, g⟩
    apply Prod.ext
    · rfl
    · funext j
      have hne : (⟨(j : ℕ) + 1, by omega⟩ : Fin (m + 1)) ≠ 0 := by
        intro h
        have hh := congrArg Fin.val h
        simp at hh
      simp only [dif_neg hne]
      congr 1

noncomputable def bitMpsContractWithCount {n d D : ℕ} [NeZero D]
    (A : BitMps n d D) (x : Fin n → Fin d) : ℤ × IntLedger :=
  let s := chainBackCount (bitMpsSiteList A x) 0
  (s.vec 0, s.ledger)

noncomputable def bitMpsContract {n d D : ℕ} [NeZero D]
    (A : BitMps n d D) (x : Fin n → Fin d) : ℤ :=
  (bitMpsContractWithCount A x).1

def bitContractOpBound (n D : ℕ) : ℕ := n * (D * D)

def bitContractWidthBound (n d D w : ℕ) : ℕ :=
  w + n * (Nat.clog 2 (D + 1) + 1) + n * (Nat.clog 2 (d + 1) + 1)

def bitContractSpace (D : ℕ) : ℕ := D

def bitRoundError (p : ℕ) : ℕ := 2 ^ p

def bitRoundInt (p : ℕ) (z : ℤ) : ℤ := z / (2 : ℤ) ^ p

def bitRoundScaled (p : ℕ) (z : ℤ) : ℤ := bitRoundInt p z * ((2 : ℤ) ^ p)

def bitPepsTreewidthCost (a b D : ℕ) : ℕ :=
  b * (D ^ a) ^ 3 * (a + 2)

def bitPepsTreewidthBound (a b D : ℕ) : ℕ :=
  (2 : ℕ) ^ (3 * a * Nat.clog 2 D) * ((a + 2) * b + 1)

def MixedKey (DA DB : ℕ) : Type := Fin DA × Fin DB

def mixedKeyEnc (DA DB : ℕ) : MixedKey DA DB ≃ Fin (DA * DB) :=
  finProdFinEquiv

def mixedKeyDec (DA DB : ℕ) : Fin (DA * DB) → MixedKey DA DB :=
  (mixedKeyEnc DA DB).symm

instance instNeZeroMixedKey {DA DB : ℕ} [NeZero DA] [NeZero DB] : NeZero (DA * DB) :=
  ⟨Nat.mul_ne_zero (NeZero.ne DA) (NeZero.ne DB)⟩

instance instFintypeMixedKey (DA DB : ℕ) : Fintype (MixedKey DA DB) :=
  inferInstanceAs (Fintype (Fin DA × Fin DB))

noncomputable def bitInnerSite {n d DA DB : ℕ}
    (A : BitMps n d DA) (B : BitMps n d DB) (i : Fin n) :
    MixedKey DA DB → MixedKey DA DB → ℤ :=
  fun p q => ∑ s : Fin d, (A i s p.1 q.1) * (B i s p.2 q.2)

noncomputable def bitInnerList {n d DA DB : ℕ} (A : BitMps n d DA) (B : BitMps n d DB) :
    List (Fin (DA * DB) → Fin (DA * DB) → ℤ) :=
  List.ofFn fun i : Fin n => fun p q =>
    bitInnerSite A B i (mixedKeyDec DA DB p) (mixedKeyDec DA DB q)

noncomputable def bitInnerWithCount {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) : ℤ × IntLedger :=
  let s := chainBackCount (bitInnerList A B) 0
  (s.vec 0,
    ⟨s.ledger.muls + n * ((DA * DB) ^ 2 * d),
      s.ledger.adds + n * ((DA * DB) ^ 2 * d),
      s.ledger.subs⟩)

noncomputable def bitInner {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) : ℤ :=
  (bitInnerWithCount A B).1

noncomputable def bitInnerMath {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) : ℤ :=
  ∑ x : Fin n → Fin d, (bitMpsAmplitude A x) * (bitMpsAmplitude B x)

def bitInnerOpBound (n d DA DB : ℕ) : ℕ :=
  n * (DA * DB) ^ 2 * (d + 1)

def bitInnerWidthBound (n d DA DB w : ℕ) : ℕ :=
  2 * w + Nat.clog 2 (d + 1) + n * (Nat.clog 2 (DA * DB + 1) + 1)

def bitInnerSpace (DA DB : ℕ) : ℕ := DA * DB

def mixedLeftIdx {n DA DB : ℕ} [NeZero DA] [NeZero DB]
    (γ : Fin (n - 1) → MixedKey DA DB) (i : Fin n) : MixedKey DA DB :=
  (mpsLeftIdx (fun j => (γ j).1) i, mpsLeftIdx (fun j => (γ j).2) i)

def mixedRightIdx {n DA DB : ℕ} [NeZero DA] [NeZero DB]
    (γ : Fin (n - 1) → MixedKey DA DB) (i : Fin n) : MixedKey DA DB :=
  (mpsRightIdx (fun j => (γ j).1) i, mpsRightIdx (fun j => (γ j).2) i)

noncomputable def bitInnerSiteProd {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB)
    (α : Fin (n - 1) → Fin DA) (β : Fin (n - 1) → Fin DB) (i : Fin n) (s : Fin d) : ℤ :=
  (A i s (mpsLeftIdx α i) (mpsRightIdx α i))
    * (B i s (mpsLeftIdx β i) (mpsRightIdx β i))

noncomputable def bitInnerPair {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB)
    (x : Fin n → Fin d) (α : Fin (n - 1) → Fin DA) (β : Fin (n - 1) → Fin DB) (i : Fin n) : ℤ :=
  bitInnerSiteProd A B α β i (x i)

noncomputable def bitInnerChainSum {n d DA DB : ℕ} [NeZero DA] [NeZero DB]
    (A : BitMps n d DA) (B : BitMps n d DB) : ℤ :=
  ∑ γ : Fin (n - 1) → MixedKey DA DB,
    ∏ i : Fin n, bitInnerSite A B i (mixedLeftIdx γ i) (mixedRightIdx γ i)

def BitLocalObs (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℤ

def bitObsMps {n d D : ℕ} (A : BitMps n d D) (z : Fin n) (O : BitLocalObs d) :
    BitMps n d D :=
  fun i s => if h : i = z then Matrix.of fun a b => ∑ y : Fin d, O s y * A z y a b
    else A i s

noncomputable def bitLocalObs {n d D : ℕ} [NeZero D] (A : BitMps n d D) (z : Fin n)
    (O : BitLocalObs d) : ℤ :=
  bitInner A (bitObsMps A z O)

noncomputable def bitLocalObsMath {n d D : ℕ} [NeZero D]
    (A : BitMps n d D) (z : Fin n) (O : BitLocalObs d) : ℤ :=
  ∑ x : Fin n → Fin d,
    (bitMpsAmplitude A x)
      * (∑ y : Fin d, O (x z) y * bitMpsAmplitude A (Function.update x z y))

noncomputable def bitNormSq {n d D : ℕ} [NeZero D] (A : BitMps n d D) : ℤ :=
  bitInner A A

noncomputable def bitSampleProb {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) : ℚ :=
  (bitMpsAmplitude A x) ^ 2 / (bitNormSq A)

noncomputable def bitSampleMass {n d D : ℕ} [NeZero D] (A : BitMps n d D) : ℤ :=
  ∑ x : Fin n → Fin d, (bitMpsAmplitude A x) ^ 2

def bitSampleProbError (eps : ℚ) : ℚ := 2 * eps / (1 - eps)

noncomputable def bitSampleProbApprox {n d D : ℕ} [NeZero D] (A : BitMps n d D)
    (x : Fin n → Fin d) (N' : ℚ) : ℚ :=
  (bitMpsAmplitude A x) ^ 2 / N'

def splitInv {n d k : ℕ} (hk : k ≤ n) (p : (Fin k → Fin d) × (Fin (n - k) → Fin d)) :
    Fin n → Fin d :=
  fun j => dite (j.val < k) (fun h => p.1 ⟨j.val, h⟩)
    (fun h => p.2 ⟨j.val - k, by omega⟩)

def splitEquiv {n d : ℕ} (k : ℕ) (hk : k ≤ n) :
    (Fin n → Fin d) ≃ ((Fin k → Fin d) × (Fin (n - k) → Fin d)) where
  toFun f := (fun j => f ⟨j.val, by omega⟩, fun j => f ⟨k + j.val, by omega⟩)
  invFun p := splitInv hk p
  left_inv := by
    intro f
    funext j
    by_cases h : j.val < k
    · simp only [splitInv, dif_pos h]
    · have hle : k ≤ j.val := by omega
      have hval : k + (j.val - k) = j.val := by omega
      have heq : (⟨k + (j.val - k), by omega⟩ : Fin n) = j := by
        apply Fin.ext
        exact hval
      simp only [splitInv, dif_neg h]
      exact congrArg f heq
  right_inv := by
    intro p
    apply Prod.ext
    · funext j
      have hjlt : j.val < k := j.isLt
      simp only [splitInv, dif_pos hjlt]
    · funext j
      have hjge : ¬ k + j.val < k := by omega
      have hval : k + j.val - k = j.val := by omega
      have heq : (⟨k + j.val - k, by omega⟩ : Fin (n - k)) = j := by
        apply Fin.ext
        exact hval
      simp only [splitInv, dif_neg hjge]
      exact congrArg p.2 heq

def bitPrefixFixedMps {n d D : ℕ} (A : BitMps n d D) (k : ℕ)
    (lo : Fin k → Fin d) (s : Fin d) : BitMps n d D :=
  fun j t => dite (j.val < k) (fun h => A j (lo ⟨j.val, h⟩))
    (fun _ => dite (j.val = k) (fun _ => A j s) (fun _ => A j t))

def prefixFixedConfig {n d k : ℕ} (lo : Fin k → Fin d) (s : Fin d) (t : Fin n → Fin d) :
    Fin n → Fin d :=
  fun j => dite (j.val < k) (fun h => lo ⟨j.val, h⟩)
    (fun _ => dite (j.val = k) (fun _ => s) (fun _ => t j))

def prefixSnoc {k d : ℕ} (lo : Fin k → Fin d) (s : Fin d) : Fin (k + 1) → Fin d :=
  fun j => dite (j.val < k) (fun h => lo ⟨j.val, h⟩) (fun _ => s)

noncomputable def bitTailMass {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ) (hk : k < n)
    (lo : Fin k → Fin d) (s : Fin d) : ℤ :=
  ∑ hi : Fin (n - k - 1) → Fin d,
    (bitMpsAmplitude A (splitInv (n := n) (d := d) (k := k + 1) (Nat.succ_le_of_lt hk)
      (prefixSnoc lo s, hi))) ^ 2

noncomputable def bitCondWeight {n d D : ℕ} [NeZero D] (A : BitMps n d D) (k : ℕ)
    (lo : Fin k → Fin d) (s : Fin d) : ℤ :=
  bitInner (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)

def bitCondStepOpBound (n d D : ℕ) : ℕ := d * bitInnerOpBound n d D D

def bitCondTotalOpBound (n d D : ℕ) : ℕ := n * bitCondStepOpBound n d D

def clause2StatementNext : Prop :=
  (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (x : Fin n → Fin d),
    bitMpsContract A x = chainTotal (bitMpsSiteList A x) 0 0)
  ∧ (∀ {D : ℕ} [NeZero D] (Ms : BitSiteList D), Ms ≠ [] →
    chainTotal Ms 0 0
      = ∑ γ : Fin (Ms.length - 1) → Fin D,
          ∏ p : Fin Ms.length, Ms[p] (mpsLeftIdx γ p) (mpsRightIdx γ p))
  ∧ (∀ (n d D _w : ℕ) [NeZero D] (A : BitMps n d D) (x : Fin n → Fin d),
    (bitMpsContractWithCount A x).2.muls ≤ bitContractOpBound n D
    ∧ (bitMpsContractWithCount A x).2.adds ≤ bitContractOpBound n D
    ∧ (bitMpsContractWithCount A x).2.subs = 0)
  ∧ (∀ (n d D w : ℕ) [NeZero D] (A : BitMps n d D) (x : Fin n → Fin d),
    bitTimeOf (bitContractWidthBound n d D w) (bitMpsContractWithCount A x).2
      ≤ 2 * bitContractOpBound n D * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitContractWidthBound n d D w))
  ∧ (∀ D : ℕ, bitContractSpace D = D)
  ∧ (∀ (p : ℕ) (z : ℤ),
    0 ≤ z - bitRoundScaled p z ∧ z - bitRoundScaled p z < (2 : ℤ) ^ p)
  ∧ (∀ (a b D : ℕ), 0 < D → bitPepsTreewidthCost a b D ≤ bitPepsTreewidthBound a b D)
  ∧ (∀ (n d DA DB : ℕ) [NeZero DA] [NeZero DB]
      (A : BitMps n d DA) (B : BitMps n d DB),
      bitInner A B = bitInnerMath A B)
  ∧ (∀ (n d DA DB : ℕ) [NeZero DA] [NeZero DB]
      (A : BitMps n d DA) (B : BitMps n d DB),
      (bitInnerWithCount A B).2.muls ≤ bitInnerOpBound n d DA DB
      ∧ (bitInnerWithCount A B).2.adds ≤ bitInnerOpBound n d DA DB
      ∧ (bitInnerWithCount A B).2.subs = 0)
  ∧ (∀ (n d DA DB w : ℕ) [NeZero DA] [NeZero DB]
      (A : BitMps n d DA) (B : BitMps n d DB),
      bitTimeOf (bitInnerWidthBound n d DA DB w) (bitInnerWithCount A B).2
        ≤ 2 * bitInnerOpBound n d DA DB
          * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitInnerWidthBound n d DA DB w))
  ∧ (∀ DA DB : ℕ, bitInnerSpace DA DB = DA * DB)
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (x : Fin n → Fin d),
      bitSampleProb A x = bitSampleLaw A x)
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (hA : bitNormSq A ≠ 0),
      (∑ x : Fin n → Fin d, bitSampleProb A x) = 1)
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (hA : bitNormSq A ≠ 0)
      (x : Fin n → Fin d), 0 ≤ bitSampleProb A x)
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (z : Fin n) (O : BitLocalObs d),
      bitLocalObs A z O = bitLocalObsMath A z O)
  ∧ (∀ (n d D w : ℕ) [NeZero D] (A : BitMps n d D) (z : Fin n) (O : BitLocalObs d),
      bitTimeOf (bitInnerWidthBound n d D D w) (bitInnerWithCount A (bitObsMps A z O)).2
        ≤ 2 * bitInnerOpBound n d D D
          * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitInnerWidthBound n d D D w))
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (x : Fin n → Fin d) (N' eps : ℚ),
      (0 : ℚ) < (bitNormSq A : ℚ) → (0 : ℚ) < N' → (0 : ℚ) ≤ eps → eps < 1 →
      |N' - (bitNormSq A : ℚ)| ≤ eps * (bitNormSq A : ℚ) →
        |bitSampleProbApprox A x N' - bitSampleProb A x| ≤ bitSampleProbError eps)
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (k : ℕ) (hk : k < n)
      (lo : Fin k → Fin d) (s : Fin d),
      bitCondWeight A k lo s * (∑ s' : Fin d, bitTailMass A k hk lo s')
        = bitTailMass A k hk lo s * (∑ s' : Fin d, bitCondWeight A k lo s'))
  ∧ (∀ (n d D : ℕ) [NeZero D] (A : BitMps n d D) (k : ℕ)
      (lo : Fin k → Fin d) (s : Fin d),
      (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2.muls
        ≤ bitInnerOpBound n d D D
      ∧ (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2.adds
        ≤ bitInnerOpBound n d D D
      ∧ (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2.subs
        = 0)
  ∧ (∀ (n d D w : ℕ) [NeZero D] (A : BitMps n d D) (k : ℕ)
      (lo : Fin k → Fin d) (s : Fin d),
      bitTimeOf (bitInnerWidthBound n d D D w)
          (bitInnerWithCount (bitPrefixFixedMps A k lo s) (bitPrefixFixedMps A k lo s)).2
        ≤ 2 * bitInnerOpBound n d D D
          * Qatlib.Concepts.MpsAdaptation.MpsTransfer.ringOpBitCost (bitInnerWidthBound n d D D w))

end Qatlib.Concepts.DyadicOverlap.ArithLedger
