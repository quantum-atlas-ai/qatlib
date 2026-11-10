/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorNetwork.GaugeInvariance
import Qatlib.Concepts.TensorNetwork.CanonicalMPS
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
open Qatlib
open Qatlib.Concepts.TensorNetwork.CanonicalMPS
open Qatlib.Concepts.TensorNetwork.GaugeInvariance
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
open scoped BigOperators ComplexConjugate

def permDims (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (j : Fin N.nh) : ℕ :=
  N.dims (π.symm j)

def permSite (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (j : Fin N.nh) : Fin N.nv :=
  N.site (π.symm j)

def permPartner (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (j : Fin N.nh) :
    Option (Fin N.nh) :=
  (N.partner (π.symm j)).map π

def permTensor (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (v : Fin N.nv)
    (a : ∀ h : {h : Fin N.nh // permSite N π h = v}, Fin (permDims N π h.val)) : ℂ :=
  N.tensor v (fun g : {g : Fin N.nh // N.site g = v} =>
    (a ⟨π g.val, by
        simp only [permSite, Equiv.symm_apply_apply]
        exact g.property⟩).cast (by
        simp only [permDims, Equiv.symm_apply_apply]))

def permNet (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) : TensorNet where
  nv := N.nv
  nh := N.nh
  dims := permDims N π
  site := permSite N π
  partner := permPartner N π
  involution := by
    intro j k hj
    rw [permPartner, Option.map_eq_some_iff] at hj
    obtain ⟨m, hm, hmk⟩ := hj
    have hkm : π.symm k = m := by
      rw [← hmk]
      exact π.symm_apply_apply m
    show permPartner N π k = some j
    rw [permPartner, hkm, N.involution _ _ hm, Option.map_some, π.apply_symm_apply]
  no_self_loop := by
    intro j k hj
    rw [permPartner, Option.map_eq_some_iff] at hj
    obtain ⟨m, hm, hmk⟩ := hj
    intro hcon
    refine N.no_self_loop (π.symm j) m hm ?_
    exact π.injective (by rw [π.apply_symm_apply j, hcon]; exact hmk.symm)
  dims_match := by
    intro j k hj
    rw [permPartner, Option.map_eq_some_iff] at hj
    obtain ⟨m, hm, hmk⟩ := hj
    have hkm : π.symm k = m := by
      rw [← hmk]
      exact π.symm_apply_apply m
    show permDims N π j = permDims N π k
    rw [permDims, permDims, hkm]
    exact N.dims_match _ _ hm
  tensor := permTensor N π

theorem permNet_dims (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (h : Fin N.nh) :
    (permNet N π).dims (π h) = N.dims h := by
  show permDims N π (π h) = N.dims h
  simp only [permDims, Equiv.symm_apply_apply]

theorem permNet_site (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (h : Fin N.nh) :
    (permNet N π).site (π h) = N.site h := by
  show permSite N π (π h) = N.site h
  simp only [permSite, Equiv.symm_apply_apply]

theorem permNet_partner (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (h : Fin N.nh) :
    (permNet N π).partner (π h) = (N.partner h).map π := by
  show permPartner N π (π h) = (N.partner h).map π
  simp only [permPartner, Equiv.symm_apply_apply]

theorem permNet_partner_none (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (o : OpenLeg N) : (permNet N π).partner (π o.val) = none := by
  rw [permNet_partner, o.property, Option.map_none]

theorem permNet_partner_of_none {N : TensorNet} {π : Fin N.nh ≃ Fin N.nh}
    {j : Fin N.nh} (hj : (permNet N π).partner j = none) :
    N.partner (π.symm j) = none := by
  have h' : (N.partner (π.symm j)).map π = none := hj
  rw [Option.map_eq_none_iff] at h'
  exact h'

def permOpenLeg (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    OpenLeg N ≃ OpenLeg (permNet N π) where
  toFun o := ⟨π o.val, permNet_partner_none N π o⟩
  invFun o' := ⟨π.symm o'.val, permNet_partner_of_none o'.property⟩
  left_inv o := Subtype.ext (π.symm_apply_apply o.val)
  right_inv o' := Subtype.ext (π.apply_symm_apply o'.val)

abbrev OpenAssign (N : TensorNet) : Type := ∀ o : OpenLeg N, Fin (N.dims o.val)

instance {N : TensorNet} : DecidableEq (OpenLeg N) :=
  fun a b =>
    if h : a.val = b.val then isTrue (Subtype.ext h)
    else isFalse (fun g => h (congrArg Subtype.val g))

instance {N : TensorNet} : Fintype (OpenAssign N) := Pi.instFintype

noncomputable def openPull (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign (permNet N π)) : OpenAssign N :=
  fun o => (y (permOpenLeg N π o)).cast (permNet_dims N π o.val)

noncomputable def openPush (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign N) : OpenAssign (permNet N π) :=
  fun o' => (y ((permOpenLeg N π).symm o')).cast (by
    show (permNet N π).dims o'.val = N.dims ((permOpenLeg N π).symm o').val
    rfl)

theorem openPull_push (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (y : OpenAssign N) :
    openPull N π (openPush N π y) = y := by
  funext o
  apply Fin.ext
  exact congrArg (fun w : OpenLeg N => (y w).val) ((permOpenLeg N π).left_inv o)

theorem openPush_pull (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign (permNet N π)) : openPush N π (openPull N π y) = y := by
  funext o'
  apply Fin.ext
  exact congrArg (fun w : OpenLeg (permNet N π) => (y w).val)
    ((permOpenLeg N π).right_inv o')

noncomputable def openAssignEquiv (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    OpenAssign (permNet N π) ≃ OpenAssign N where
  toFun := openPull N π
  invFun := openPush N π
  left_inv := openPush_pull N π
  right_inv := openPull_push N π

noncomputable def permIso (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    NetIso N (permNet N π) where
  vertexMap := Equiv.refl _
  halfMap := π
  dims_map := fun h => permNet_dims N π h
  site_map := fun h => by
    show (permNet N π).site (π h) = Equiv.refl _ (N.site h)
    exact permNet_site N π h
  partner_map := fun h => permNet_partner N π h
  tensor_map := by
    intro v a
    refine congrArg (N.tensor v) (funext fun g => ?_)
    show ((a ⟨π.symm (π g.val), _⟩).cast _).cast _ = a g
    have hg : (⟨π.symm (π g.val), by rw [π.symm_apply_apply]; exact g.property⟩ :
        {g : Fin N.nh // N.site g = v}) = g := Subtype.ext (π.symm_apply_apply g.val)
    exact Fin.ext (congrArg (fun w : {g : Fin N.nh // N.site g = v} => (a w).val) hg)

theorem netContract_permNet (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign (permNet N π)) :
    netContract (permNet N π) y = netContract N (openPull N π y) :=
  clause1_clause1 N (permNet N π) (permIso N π) y

theorem netContract_permPush (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign N) :
    netContract (permNet N π) (openPush N π y) = netContract N y := by
  rw [netContract_permNet, openPull_push]

theorem netContract_permNet_gauge (N : TensorNet)
    (U : ∀ i : InternalEdge N, Matrix (Fin (N.dims i.val)) (Fin (N.dims i.val)) ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup (Fin (N.dims i.val)) ℂ)
    (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign (permNet (gaugeNet N U) π)) :
    netContract (permNet (gaugeNet N U) π) y
      = netContract N (openPull (gaugeNet N U) π y) := by
  rw [netContract_permNet]
  exact clause1_clause2 N U hU _

noncomputable def netInner (N : TensorNet) (ψ φ : OpenAssign N → ℂ) : ℂ :=
  ∑ x : OpenAssign N, conj (ψ x) * φ x

theorem netInner_perm (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh)
    (ψ φ : OpenAssign N → ℂ) :
    netInner (permNet N π) (fun y => ψ (openPull N π y)) (fun y => φ (openPull N π y))
      = netInner N ψ φ := by
  exact Fintype.sum_equiv (openAssignEquiv N π)
    (fun y => conj (ψ (openPull N π y)) * φ (openPull N π y))
    (fun x => conj (ψ x) * φ x)
    (fun _ => rfl)

theorem netInner_state_perm (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    netInner (permNet N π) (netContract (permNet N π)) (netContract (permNet N π))
      = netInner N (netContract N) (netContract N) := by
  have hf : netContract (permNet N π) = fun y => netContract N (openPull N π y) :=
    funext (netContract_permNet N π)
  rw [hf]
  exact netInner_perm N π (netContract N) (netContract N)

theorem sum_config_reindex {n d : ℕ} (g : (Fin n → Fin d) → ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d, g (fun i => x (e.symm i))
      = ∑ x : Fin n → Fin d, g x :=
  Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl (Fin d))) _ _ (fun _ => rfl)

theorem mpsInner_reindex {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (mpsAmplitude B (fun i => x (e.symm i)))
          * mpsAmplitude A (fun i => x (e.symm i))
      = ∑ x : Fin n → Fin d, conj (mpsAmplitude B x) * mpsAmplitude A x :=
  sum_config_reindex (fun x => conj (mpsAmplitude B x) * mpsAmplitude A x) e

theorem mpsObsExpectation_reindex {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (mpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, O ((fun i => x (e.symm i)) z) y
              * mpsAmplitude A (Function.update (fun i => x (e.symm i)) z y)
      = ∑ x : Fin n → Fin d,
          conj (mpsAmplitude A x)
            * ∑ y : Fin d, O (x z) y * mpsAmplitude A (Function.update x z y) :=
  sum_config_reindex
    (fun x => conj (mpsAmplitude A x)
      * ∑ y : Fin d, O (x z) y * mpsAmplitude A (Function.update x z y)) e

theorem netContract_mpsNet_permPush {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (π : Fin (3 * n + 2) ≃ Fin (3 * n + 2)) :
    netContract (permNet (mpsNet n d D A) π)
        (openPush (mpsNet n d D A) π (mpsEnc n d D A x)) = mpsAmplitude A x := by
  rw [netContract_permPush, netContract_mpsNet_eq_mpsAmplitude]

def physLegPerm (n : ℕ) (ρ : Fin n ≃ Fin n) : Fin (3 * n + 2) ≃ Fin (3 * n + 2) :=
  (((Equiv.cast (congrArg Fin (by omega : 3 * n + 2 = 2 * (n + 1) + n))).trans
      (finSumFinEquiv (m := 2 * (n + 1))).symm).trans
    ((Equiv.refl (Fin (2 * (n + 1)))).sumCongr ρ)).trans
    ((finSumFinEquiv (m := 2 * (n + 1))).trans
      (Equiv.cast (congrArg Fin (by omega : 3 * n + 2 = 2 * (n + 1) + n))).symm)

def mpsPhysLegIdx (n : ℕ) (i : Fin n) : Fin (3 * n + 2) :=
  ⟨2 * (n + 1) + (i : ℕ), by
    show 2 * (n + 1) + (i : ℕ) < 3 * n + 2
    have := i.isLt
    omega⟩

theorem mpsPhysLegIdx_val (n : ℕ) (i : Fin n) :
    (mpsPhysLegIdx n i : ℕ) = 2 * (n + 1) + (i : ℕ) := rfl

theorem mpsPartner_physLegIdx_none (n : ℕ) (i : Fin n) :
    mpsPartner n (mpsPhysLegIdx n i) = none := by
  rw [mpsPartner, dif_neg (by
    show ¬(2 * (n + 1) + (i : ℕ) < 2 * (n + 1))
    have := i.isLt
    omega)]

noncomputable def mpsPhysLeg (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : Fin n) : OpenLeg (mpsNet n d D A) where
  val := mpsPhysLegIdx n i
  property := mpsPartner_physLegIdx_none n i

theorem mpsNet_dims_physLeg (n d D : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin n) :
    (mpsNet n d D A).dims (mpsPhysLeg n d D A i).val = d := by
  show mpsDim n d D (2 * (n + 1) + (i : ℕ)) = d
  rw [mpsDim, if_neg (by
    show ¬(2 * (n + 1) + (i : ℕ) < 2 * (n + 1))
    have := i.isLt
    omega)]

noncomputable def openDecode (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (mpsNet n d D A)) : Fin n → Fin d :=
  fun i => (y (mpsPhysLeg n d D A i)).cast (mpsNet_dims_physLeg n d D A i)

theorem mpsEnc_physLeg (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (i : Fin n) :
    (mpsEnc n d D A x (mpsPhysLeg n d D A i)).cast (mpsNet_dims_physLeg n d D A i)
      = x i := by
  have hi : (⟨2 * (n + 1) + (i : ℕ) - 2 * (n + 1), by
      show 2 * (n + 1) + (i : ℕ) - 2 * (n + 1) < n
      have := i.isLt
      omega⟩ : Fin n) = i :=
    Fin.ext (by
      show 2 * (n + 1) + (i : ℕ) - 2 * (n + 1) = (i : ℕ)
      omega)
  show ((x ⟨2 * (n + 1) + (i : ℕ) - 2 * (n + 1), by
      show 2 * (n + 1) + (i : ℕ) - 2 * (n + 1) < n
      have := i.isLt
      omega⟩).cast (by
      show d = mpsDim n d D (2 * (n + 1) + (i : ℕ))
      rw [mpsDim, if_neg (by
        show ¬(2 * (n + 1) + (i : ℕ) < 2 * (n + 1))
        have := i.isLt
        omega)])).cast (mpsNet_dims_physLeg n d D A i) = x i
  rw [hi]
  exact Fin.ext (by simp)

theorem openDecode_mpsEnc (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (i : Fin n) :
    openDecode n d D A (mpsEnc n d D A x) i = x i :=
  mpsEnc_physLeg n d D A x i

theorem mpsEnc_openDecode (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (mpsNet n d D A)) :
    mpsEnc n d D A (openDecode n d D A y) = y := by
  funext o
  have hge : 2 * (n + 1) ≤ (o.val : ℕ) := mpsPartner_none_ge o.property
  have hlt : (o.val : ℕ) < 3 * n + 2 := o.val.isLt
  have hleg : mpsPhysLeg n d D A ⟨(o.val : ℕ) - 2 * (n + 1), by
      show (o.val : ℕ) - 2 * (n + 1) < n
      omega⟩ = o :=
    Subtype.ext (Fin.ext (by
      show 2 * (n + 1) + ((o.val : ℕ) - 2 * (n + 1)) = (o.val : ℕ)
      omega))
  show ((y (mpsPhysLeg n d D A ⟨(o.val : ℕ) - 2 * (n + 1), by
      show (o.val : ℕ) - 2 * (n + 1) < n
      omega⟩)).cast (by
      show mpsDim n d D (2 * (n + 1) + ((o.val : ℕ) - 2 * (n + 1))) = d
      rw [mpsDim, if_neg (by omega)])).cast (by
      show d = mpsDim n d D (o.val : ℕ)
      rw [mpsDim, if_neg (by omega)]) = y o
  refine Fin.ext ?_
  simp only [Fin.val_cast]
  exact congrArg (fun l => (y l).val) hleg

noncomputable def openAssignCfgEquiv (n d D : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    OpenAssign (mpsNet n d D A) ≃ (Fin n → Fin d) where
  toFun := openDecode n d D A
  invFun := mpsEnc n d D A
  left_inv := mpsEnc_openDecode n d D A
  right_inv := fun x => funext (fun i => openDecode_mpsEnc n d D A x i)

theorem netContract_mpsNet_eval {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (mpsNet n d D A)) :
    netContract (mpsNet n d D A) y = mpsAmplitude A (openDecode n d D A y) := by
  rw [← netContract_mpsNet_eq_mpsAmplitude n d D A (openDecode n d D A y),
    mpsEnc_openDecode n d D A y]

theorem netInner_mpsNet_eq {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    netInner (mpsNet n d D A) (netContract (mpsNet n d D A)) (netContract (mpsNet n d D A))
      = ∑ x : Fin n → Fin d, conj (mpsAmplitude A x) * mpsAmplitude A x :=
  Fintype.sum_equiv (openAssignCfgEquiv n d D A)
    (fun y => conj (netContract (mpsNet n d D A) y) * netContract (mpsNet n d D A) y)
    (fun x => conj (mpsAmplitude A x) * mpsAmplitude A x)
    (fun y => by
      show conj (netContract (mpsNet n d D A) y) * netContract (mpsNet n d D A) y
          = conj (mpsAmplitude A (openDecode n d D A y))
              * mpsAmplitude A (openDecode n d D A y)
      rw [netContract_mpsNet_eval])

theorem netInner_mpsNet_perm {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (π : Fin (3 * n + 2) ≃ Fin (3 * n + 2)) :
    netInner (permNet (mpsNet n d D A) π) (netContract (permNet (mpsNet n d D A) π))
        (netContract (permNet (mpsNet n d D A) π))
      = ∑ x : Fin n → Fin d, conj (mpsAmplitude A x) * mpsAmplitude A x := by
  rw [netInner_state_perm, netInner_mpsNet_eq]

def perPhysLegPerm (n : ℕ) (ρ : Fin n ≃ Fin n) : Fin (3 * n) ≃ Fin (3 * n) :=
  (((Equiv.cast (congrArg Fin (by omega : 3 * n = 2 * n + n))).trans
      (finSumFinEquiv (m := 2 * n)).symm).trans
    ((Equiv.refl (Fin (2 * n))).sumCongr ρ)).trans
    ((finSumFinEquiv (m := 2 * n)).trans
      (Equiv.cast (congrArg Fin (by omega : 3 * n = 2 * n + n))).symm)

theorem netContract_perNet_permPush {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (π : Fin (3 * n) ≃ Fin (3 * n)) :
    netContract (permNet (perNet n d D A) π)
        (openPush (perNet n d D A) π (perEnc n d D A x)) = periodicMpsAmplitude A x := by
  rw [netContract_permPush, netContract_perNet_eq]

def perPhysLegIdx (n : ℕ) (i : Fin n) : Fin (3 * n) :=
  ⟨2 * n + (i : ℕ), by
    show 2 * n + (i : ℕ) < 3 * n
    have := i.isLt
    omega⟩

theorem perPhysLegIdx_val (n : ℕ) (i : Fin n) :
    (perPhysLegIdx n i : ℕ) = 2 * n + (i : ℕ) := rfl

theorem perPartner_perPhysLegIdx_none (n : ℕ) (i : Fin n) :
    perPartner n (perPhysLegIdx n i) = none := by
  rw [perPartner, dif_neg (by
    show ¬(2 * n + (i : ℕ) < 2 * n)
    have := i.isLt
    omega)]

noncomputable def perPhysLeg (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : Fin n) : OpenLeg (perNet n d D A) where
  val := perPhysLegIdx n i
  property := perPartner_perPhysLegIdx_none n i

theorem perNet_dims_physLeg (n d D : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin n) :
    (perNet n d D A).dims (perPhysLeg n d D A i).val = d := by
  show perDim n d D (2 * n + (i : ℕ)) = d
  rw [perDim, if_neg (by
    show ¬(2 * n + (i : ℕ) < 2 * n)
    have := i.isLt
    omega)]

noncomputable def perOpenDecode (n d D : ℕ) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (perNet n d D A)) : Fin n → Fin d :=
  fun i => (y (perPhysLeg n d D A i)).cast (perNet_dims_physLeg n d D A i)

theorem perEnc_physLeg (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) (i : Fin n) :
    (perEnc n d D A x (perPhysLeg n d D A i)).cast (perNet_dims_physLeg n d D A i)
      = x i := by
  have hi : (⟨2 * n + (i : ℕ) - 2 * n, by
      show 2 * n + (i : ℕ) - 2 * n < n
      have := i.isLt
      omega⟩ : Fin n) = i :=
    Fin.ext (by
      show 2 * n + (i : ℕ) - 2 * n = (i : ℕ)
      omega)
  show ((x ⟨2 * n + (i : ℕ) - 2 * n, by
      show 2 * n + (i : ℕ) - 2 * n < n
      have := i.isLt
      omega⟩).cast (by
      show d = perDim n d D (2 * n + (i : ℕ))
      rw [perDim, if_neg (by
        show ¬(2 * n + (i : ℕ) < 2 * n)
        have := i.isLt
        omega)])).cast (perNet_dims_physLeg n d D A i) = x i
  rw [hi]
  exact Fin.ext (by simp)

theorem perOpenDecode_perEnc (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) (i : Fin n) :
    perOpenDecode n d D A (perEnc n d D A x) i = x i :=
  perEnc_physLeg n d D A x i

theorem perEnc_perOpenDecode (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (perNet n d D A)) :
    perEnc n d D A (perOpenDecode n d D A y) = y := by
  funext o
  have hge : ¬((o.val : ℕ) < 2 * n) := perPartner_none_lt n o.property
  have hlt : (o.val : ℕ) < 3 * n := o.val.isLt
  have hleg : perPhysLeg n d D A ⟨(o.val : ℕ) - 2 * n, by
      show (o.val : ℕ) - 2 * n < n
      omega⟩ = o :=
    Subtype.ext (Fin.ext (by
      show 2 * n + ((o.val : ℕ) - 2 * n) = (o.val : ℕ)
      omega))
  show ((y (perPhysLeg n d D A ⟨(o.val : ℕ) - 2 * n, by
      show (o.val : ℕ) - 2 * n < n
      omega⟩)).cast (by
      show perDim n d D (2 * n + ((o.val : ℕ) - 2 * n)) = d
      rw [perDim, if_neg (by omega)])).cast (by
      show d = perDim n d D (o.val : ℕ)
      rw [perDim, if_neg (by omega)]) = y o
  refine Fin.ext ?_
  simp only [Fin.val_cast]
  exact congrArg (fun l => (y l).val) hleg

noncomputable def perOpenAssignCfgEquiv (n d D : ℕ) [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    OpenAssign (perNet n d D A) ≃ (Fin n → Fin d) where
  toFun := perOpenDecode n d D A
  invFun := perEnc n d D A
  left_inv := perEnc_perOpenDecode n d D A
  right_inv := fun x => funext (fun i => perOpenDecode_perEnc n d D A x i)

theorem netContract_perNet_eval {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (perNet n d D A)) :
    netContract (perNet n d D A) y = periodicMpsAmplitude A (perOpenDecode n d D A y) := by
  rw [← netContract_perNet_eq A (perOpenDecode n d D A y),
    perEnc_perOpenDecode n d D A y]

theorem netInner_perNet_eq {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    netInner (perNet n d D A) (netContract (perNet n d D A)) (netContract (perNet n d D A))
      = ∑ x : Fin n → Fin d, conj (periodicMpsAmplitude A x) * periodicMpsAmplitude A x :=
  Fintype.sum_equiv (perOpenAssignCfgEquiv n d D A)
    (fun y => conj (netContract (perNet n d D A) y) * netContract (perNet n d D A) y)
    (fun x => conj (periodicMpsAmplitude A x) * periodicMpsAmplitude A x)
    (fun y => by
      show conj (netContract (perNet n d D A) y) * netContract (perNet n d D A) y
          = conj (periodicMpsAmplitude A (perOpenDecode n d D A y))
              * periodicMpsAmplitude A (perOpenDecode n d D A y)
      rw [netContract_perNet_eval])

theorem netInner_perNet_perm {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (π : Fin (3 * n) ≃ Fin (3 * n)) :
    netInner (permNet (perNet n d D A) π) (netContract (permNet (perNet n d D A) π))
        (netContract (permNet (perNet n d D A) π))
      = ∑ x : Fin n → Fin d, conj (periodicMpsAmplitude A x) * periodicMpsAmplitude A x := by
  rw [netInner_state_perm, netInner_perNet_eq]

theorem perInner_reindex {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude B (fun i => x (e.symm i)))
          * periodicMpsAmplitude A (fun i => x (e.symm i))
      = ∑ x : Fin n → Fin d, conj (periodicMpsAmplitude B x) * periodicMpsAmplitude A x :=
  sum_config_reindex (fun x => conj (periodicMpsAmplitude B x) * periodicMpsAmplitude A x) e

theorem perObsExpectation_reindex {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, O ((fun i => x (e.symm i)) z) y
              * periodicMpsAmplitude A (Function.update (fun i => x (e.symm i)) z y)
      = ∑ x : Fin n → Fin d,
          conj (periodicMpsAmplitude A x)
            * ∑ y : Fin d, O (x z) y * periodicMpsAmplitude A (Function.update x z y) :=
  sum_config_reindex
    (fun x => conj (periodicMpsAmplitude A x)
      * ∑ y : Fin d, O (x z) y * periodicMpsAmplitude A (Function.update x z y)) e

theorem mpsTwoPointExpectation_reindex {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z w : Fin n)
    (O P : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (mpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, ∑ u : Fin d, O ((fun i => x (e.symm i)) z) y
              * P ((fun i => x (e.symm i)) w) u
              * mpsAmplitude A
                  (Function.update (Function.update (fun i => x (e.symm i)) z y) w u)
      = ∑ x : Fin n → Fin d,
          conj (mpsAmplitude A x)
            * ∑ y : Fin d, ∑ u : Fin d, O (x z) y * P (x w) u
                * mpsAmplitude A (Function.update (Function.update x z y) w u) :=
  sum_config_reindex
    (fun x => conj (mpsAmplitude A x)
      * ∑ y : Fin d, ∑ u : Fin d, O (x z) y * P (x w) u
        * mpsAmplitude A (Function.update (Function.update x z y) w u)) e

theorem mpsThreePointExpectation_reindex {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z w v : Fin n)
    (O P Q : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (mpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
              O ((fun i => x (e.symm i)) z) y
                * P ((fun i => x (e.symm i)) w) u
                * Q ((fun i => x (e.symm i)) v) t
                * mpsAmplitude A
                    (Function.update
                      (Function.update (Function.update (fun i => x (e.symm i)) z y) w u) v t)
      = ∑ x : Fin n → Fin d,
          conj (mpsAmplitude A x)
            * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
                O (x z) y * P (x w) u * Q (x v) t
                  * mpsAmplitude A
                      (Function.update (Function.update (Function.update x z y) w u) v t) :=
  sum_config_reindex
    (fun x => conj (mpsAmplitude A x)
      * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
          O (x z) y * P (x w) u * Q (x v) t
            * mpsAmplitude A
                (Function.update (Function.update (Function.update x z y) w u) v t)) e

theorem perTwoPointExpectation_reindex {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z w : Fin n)
    (O P : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, ∑ u : Fin d, O ((fun i => x (e.symm i)) z) y
              * P ((fun i => x (e.symm i)) w) u
              * periodicMpsAmplitude A
                  (Function.update (Function.update (fun i => x (e.symm i)) z y) w u)
      = ∑ x : Fin n → Fin d,
          conj (periodicMpsAmplitude A x)
            * ∑ y : Fin d, ∑ u : Fin d, O (x z) y * P (x w) u
                * periodicMpsAmplitude A (Function.update (Function.update x z y) w u) :=
  sum_config_reindex
    (fun x => conj (periodicMpsAmplitude A x)
      * ∑ y : Fin d, ∑ u : Fin d, O (x z) y * P (x w) u
        * periodicMpsAmplitude A (Function.update (Function.update x z y) w u)) e

theorem perThreePointExpectation_reindex {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z w v : Fin n)
    (O P Q : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
              O ((fun i => x (e.symm i)) z) y
                * P ((fun i => x (e.symm i)) w) u
                * Q ((fun i => x (e.symm i)) v) t
                * periodicMpsAmplitude A
                    (Function.update
                      (Function.update (Function.update (fun i => x (e.symm i)) z y) w u) v t)
      = ∑ x : Fin n → Fin d,
          conj (periodicMpsAmplitude A x)
            * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
                O (x z) y * P (x w) u * Q (x v) t
                  * periodicMpsAmplitude A
                      (Function.update (Function.update (Function.update x z y) w u) v t) :=
  sum_config_reindex
    (fun x => conj (periodicMpsAmplitude A x)
      * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
          O (x z) y * P (x w) u * Q (x v) t
            * periodicMpsAmplitude A
                (Function.update (Function.update (Function.update x z y) w u) v t)) e

def perRot {n : ℕ} [NeZero n] (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩

def snocPath {ι : Type} {n : ℕ} (w : Fin n → ι) (b : ι) : Fin (n + 1) → ι :=
  fun k => if h : (k : ℕ) < n then w ⟨(k : ℕ), h⟩ else b

theorem snocPath_castSucc {ι : Type} {n : ℕ} (w : Fin n → ι) (b : ι) (j : Fin n) :
    snocPath w b (Fin.castSucc j) = w j := by
  have hval : ((Fin.castSucc j : Fin (n + 1)) : ℕ) = (j : ℕ) := Fin.val_castSucc j
  have hlt : ((Fin.castSucc j : Fin (n + 1)) : ℕ) < n := by omega
  simp only [snocPath]
  rw [dif_pos hlt]
  exact congrArg w (Fin.ext hval)

theorem snocPath_succ_castSucc {ι : Type} {n : ℕ} (w : Fin (n + 1) → ι) (b : ι)
    (i : Fin n) :
    snocPath w b (Fin.succ (Fin.castSucc i)) = w (Fin.succ i) := by
  have hval : ((Fin.succ (Fin.castSucc i) : Fin (n + 2)) : ℕ) = (i : ℕ) + 1 := by
    simp only [Fin.val_succ, Fin.val_castSucc]
  have hlt : ((Fin.succ (Fin.castSucc i) : Fin (n + 2)) : ℕ) < n + 1 := by omega
  simp only [snocPath]
  rw [dif_pos hlt]
  exact congrArg w (Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]))

theorem snocPath_succ_last {ι : Type} {n : ℕ} (w : Fin (n + 1) → ι) (b : ι) :
    snocPath w b (Fin.succ (Fin.last n)) = b := by
  have hnge : ¬(((Fin.succ (Fin.last n) : Fin (n + 2)) : ℕ) < n + 1) := by
    simp only [Fin.val_succ, Fin.val_last]
    omega
  simp only [snocPath]
  rw [dif_neg hnge]

theorem snocPath_succ_of_lt {ι : Type} {n : ℕ} (w : Fin n → ι) (b : ι) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    snocPath w b (Fin.succ i) = w ⟨(i : ℕ) + 1, hi⟩ := by
  have hval : ((Fin.succ i : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
  have hlt : ((Fin.succ i : Fin (n + 1)) : ℕ) < n := by omega
  simp only [snocPath]
  rw [dif_pos hlt]
  exact congrArg w (Fin.ext hval)

theorem snocPath_last {ι : Type} {n : ℕ} (w : Fin n → ι) (b : ι) :
    snocPath w b (Fin.last n) = b := by
  have hnge : ¬(((Fin.last n : Fin (n + 1)) : ℕ) < n) := by
    simp only [Fin.val_last]
    omega
  simp only [snocPath]
  rw [dif_neg hnge]

theorem snocPath_zero {ι : Type} {n : ℕ} [NeZero n] (w : Fin n → ι) (b : ι) :
    snocPath w b 0 = w ⟨0 % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
  have hn : 0 < n := NeZero.pos n
  have hval : ((0 : Fin (n + 1)) : ℕ) = 0 := by simp
  have hlt : ((0 : Fin (n + 1)) : ℕ) < n := by rw [hval]; exact hn
  simp only [snocPath]
  rw [dif_pos hlt]
  exact congrArg w (Fin.ext (hval.trans (Nat.zero_mod n).symm))

noncomputable def chainProd {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | m + 1 => chainProd M m * M m

theorem chainProd_succ {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ℕ → Matrix ι ι ℂ) (m : ℕ) :
    chainProd M (m + 1) = chainProd M m * M m := rfl

theorem chainProd_congr {ι : Type} [Fintype ι] [DecidableEq ι] {M M' : ℕ → Matrix ι ι ℂ} :
    ∀ m : ℕ, (∀ k < m, M k = M' k) → chainProd M m = chainProd M' m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [chainProd_succ, chainProd_succ,
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]

theorem chainProd_shift {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → Matrix ι ι ℂ) :
    ∀ m : ℕ, M 0 * chainProd (fun k => M (k + 1)) m = chainProd M (m + 1) := by
  intro m
  induction m with
  | zero =>
    show M 0 * (1 : Matrix ι ι ℂ) = chainProd M (0 + 1)
    rw [mul_one, chainProd_succ]
    exact (one_mul (M 0)).symm
  | succ m ih =>
    show M 0 * (chainProd (fun k => M (k + 1)) m * M (m + 1))
        = chainProd M (m + 1) * M (m + 1)
    rw [← mul_assoc, ih]

theorem sum_subtype_dite {κ : Type} [Fintype κ] [DecidableEq κ]
    {q : κ → Prop} [DecidablePred q] (F : {w : κ // q w} → ℂ) :
    (∑ w : {w : κ // q w}, F w)
      = ∑ w : κ, dite (q w) (fun h => F ⟨w, h⟩) (fun _ => 0) := by
  have h1 : ∑ w : {w : κ // q w}, F w
      = ∑ w : {w : κ // q w},
          dite (q w.1) (fun h => F ⟨w.1, h⟩) (fun _ => 0) :=
    Finset.sum_congr rfl fun w _ => by rw [dif_pos w.2]
  have h2 : ∑ w : {w : κ // q w},
        dite (q w.1) (fun h => F ⟨w.1, h⟩) (fun _ => 0)
      = ∑ w ∈ Finset.univ.filter q,
          dite (q w) (fun h => F ⟨w, h⟩) (fun _ => 0) :=
    (Finset.sum_subtype (p := q) (Finset.univ.filter q)
      (fun x => by simp [Finset.mem_filter])
      (fun w => dite (q w) (fun h => F ⟨w, h⟩) (fun _ => 0))).symm
  rw [h1, h2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : q w
  · rw [if_pos hw, dif_pos hw]
  · rw [if_neg hw, dif_neg hw]

theorem sum_swap_fintype {ι κ : Type} [Fintype ι] [Fintype κ] (F : ι → κ → ℂ) :
    ∑ c : ι, ∑ w : κ, F c w = ∑ w : κ, ∑ c : ι, F c w := by
  rw [← Fintype.sum_prod_type (f := fun p : ι × κ => F p.1 p.2),
    ← Fintype.sum_prod_type (f := fun p : κ × ι => F p.2 p.1)]
  exact Fintype.sum_equiv (Equiv.prodComm ι κ)
    (fun p : ι × κ => F p.1 p.2) (fun q : κ × ι => F q.2 q.1) (fun p => rfl)

theorem sum_fiber_subtype {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {P : κ → Prop} [DecidablePred P]
    (g : κ → ι) (F : ι → {w : κ // P w} → ℂ) :
    ∑ c : ι, ∑ w : {w : κ // P w ∧ g w = c}, F c ⟨w.1, w.2.1⟩
      = ∑ w : {w : κ // P w}, F (g w.1) w := by
  have e1 : ∀ c : ι, ∑ w : {w : κ // P w ∧ g w = c}, F c ⟨w.1, w.2.1⟩
      = ∑ w : κ, dite (P w ∧ g w = c) (fun h => F c ⟨w, h.1⟩) (fun _ => 0) :=
    fun c => sum_subtype_dite _
  have e2 : ∀ w : κ, ∑ c : ι,
      dite (P w ∧ g w = c) (fun h => F c ⟨w, h.1⟩) (fun _ => 0)
        = dite (P w) (fun hp => F (g w) ⟨w, hp⟩) (fun _ => 0) := by
    intro w
    by_cases hw : P w
    · have hrw : ∀ c : ι, dite (P w ∧ g w = c) (fun h => F c ⟨w, h.1⟩) (fun _ => 0)
          = ite (g w = c) (F c ⟨w, hw⟩) 0 := by
        intro c
        by_cases hc : g w = c
        · rw [dif_pos ⟨hw, hc⟩, if_pos hc]
        · rw [dif_neg (fun h => hc h.2), if_neg hc]
      rw [dif_pos hw, Finset.sum_congr rfl (fun c _ => hrw c), Finset.sum_ite_eq]
      simp
    · rw [dif_neg hw, Finset.sum_eq_zero (M := ℂ) fun c _ => dif_neg (fun h => hw h.1)]
  simp only [e1]
  rw [sum_swap_fintype (F := fun (c : ι) (w : κ) =>
    dite (P w ∧ g w = c) (fun h => F c ⟨w, h.1⟩) (fun _ => 0))]
  simp only [e2]
  rw [sum_subtype_dite]

noncomputable def perTransferProd {n d D : ℕ} [NeZero n]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  chainProd (fun k : ℕ => A ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
    (x ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩)) n

theorem chainProd_apply_eq_pathSum {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∀ (m : ℕ) (M : ℕ → Matrix ι ι ℂ) (a b : ι),
      chainProd M m a b
        = ∑ w : {w : Fin (m + 1) → ι //
            w 0 = a ∧ w (Fin.last m) = b},
          ∏ i : Fin m, M (i : ℕ) (w.1 (Fin.castSucc i)) (w.1 i.succ) := by
  intro m
  induction m with
  | zero =>
    intro M a b
    show (if a = b then (1 : ℂ) else 0) = _
    rcases eq_or_ne a b with hab | hab
    · rw [if_pos hab]
      let w0 : {w : Fin (0 + 1) → ι // w 0 = a ∧ w (Fin.last 0) = b} :=
        ⟨fun _ => a, by simp [hab]⟩
      have hval : (∏ i : Fin 0, M (i : ℕ)
          (w0.1 (Fin.castSucc i)) (w0.1 i.succ)) = 1 := by simp
      rw [Finset.sum_eq_single_of_mem (M := ℂ) w0 (Finset.mem_univ _) ?_, hval]
      rintro ⟨w, hw0, hw1⟩ _ hwne
      refine absurd (Subtype.ext (funext fun j => ?_)) hwne
      have hj : j = 0 := by omega
      rw [hj]
      exact hw0
    · rw [if_neg hab]
      refine Eq.symm (Finset.sum_eq_zero (M := ℂ) fun w _ => ?_)
      exact absurd (w.2.1.symm.trans w.2.2) hab
  | succ m ih =>
    intro M a b
    rw [chainProd_succ, Matrix.mul_apply]
    simp only [ih M a, Finset.sum_mul]
    rw [sum_fiber_subtype
      (g := fun w : Fin (m + 1) → ι => w (Fin.last m))
      (F := fun c w => (∏ i : Fin m, M (i : ℕ)
          (w.1 (Fin.castSucc i)) (w.1 i.succ)) * M m c b)]
    let ee : {w : Fin (m + 1) → ι // w 0 = a}
        ≃ {W : Fin (m + 2) → ι // W 0 = a ∧ W (Fin.last (m + 1)) = b} :=
      { toFun := fun w =>
          ⟨snocPath w.1 b, (snocPath_zero w.1 b).trans w.2, snocPath_last w.1 b⟩
        invFun := fun W =>
          ⟨fun j => W.1 (Fin.castSucc j), by
            show (fun j => W.1 (Fin.castSucc j)) 0 = a
            exact W.2.1⟩
        left_inv := by
          rintro ⟨w, hw⟩
          exact Subtype.ext (funext fun k => snocPath_castSucc w b k)
        right_inv := by
          rintro ⟨W, hW0, hW1⟩
          refine Subtype.ext (funext fun k => ?_)
          by_cases hk : (k : ℕ) < m + 1
          · have hc : k = Fin.castSucc ⟨(k : ℕ), hk⟩ := Fin.ext rfl
            rw [hc]
            show snocPath (fun j => W (Fin.castSucc j)) b (Fin.castSucc ⟨(k : ℕ), hk⟩)
              = W (Fin.castSucc ⟨(k : ℕ), hk⟩)
            rw [snocPath_castSucc]
          · have hkl : (k : ℕ) = m + 1 := by have := k.isLt; omega
            have hl : k = Fin.last (m + 1) := Fin.ext hkl
            rw [hl]
            show snocPath (fun j => W (Fin.castSucc j)) b (Fin.last (m + 1))
              = W (Fin.last (m + 1))
            rw [snocPath_last]
            exact hW1.symm }
    refine Fintype.sum_equiv ee
      (f := fun w => (∏ i : Fin m, M (i : ℕ)
          (w.1 (Fin.castSucc i)) (w.1 i.succ))
        * M m (w.1 (Fin.last m)) b)
      (g := fun W => ∏ i : Fin (m + 1), M (i : ℕ)
        (W.1 (Fin.castSucc i)) (W.1 i.succ))
      (fun w => by
        show (∏ i : Fin m, M (i : ℕ) (w.1 (Fin.castSucc i)) (w.1 i.succ))
            * M m (w.1 (Fin.last m)) b
          = ∏ i : Fin (m + 1), M (i : ℕ)
              (snocPath w.1 b (Fin.castSucc i)) (snocPath w.1 b (Fin.succ i))
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          rw [Fin.val_castSucc, snocPath_castSucc, snocPath_succ_castSucc]
        · rw [Fin.val_last, snocPath_castSucc, snocPath_succ_last])

theorem periodicMpsAmplitude_eq_trace {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    periodicMpsAmplitude A x = (perTransferProd A x).trace := by
  simp only [periodicMpsAmplitude, perTransferProd, Matrix.trace, Matrix.diag_apply]
  have hps := chainProd_apply_eq_pathSum n
    (fun k : ℕ => A ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (x ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩))
  simp only [hps]
  let ereq : ∀ c : Fin D,
      {w : Fin (n + 1) → Fin D // w 0 = c ∧ w (Fin.last n) = c} ≃
        {w : Fin (n + 1) → Fin D // w (Fin.last n) = w 0 ∧ w 0 = c} :=
    fun c =>
      { toFun := fun w => ⟨w.1, ⟨w.2.2.trans w.2.1.symm, w.2.1⟩⟩,
        invFun := fun w => ⟨w.1, ⟨w.2.2, w.2.1.trans w.2.2⟩⟩,
        left_inv := fun w => rfl,
        right_inv := fun w => rfl }
  have ereord : ∀ c : Fin D,
      ∑ w : {w : Fin (n + 1) → Fin D //
          w 0 = c ∧ w (Fin.last n) = c},
          ∏ i : Fin n, A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
            (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
            (w.1 (Fin.castSucc i)) (w.1 i.succ)
        = ∑ w : {w : Fin (n + 1) → Fin D //
            w (Fin.last n) = w 0 ∧ w 0 = c},
          ∏ i : Fin n, A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
            (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
            (w.1 (Fin.castSucc i)) (w.1 i.succ) :=
    fun c => Fintype.sum_equiv (ereq c)
      (f := fun w => ∏ i : Fin n, A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
        (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        (w.1 (Fin.castSucc i)) (w.1 i.succ))
      (g := fun w => ∏ i : Fin n, A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
        (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        (w.1 (Fin.castSucc i)) (w.1 i.succ))
      (fun w => rfl)
  rw [Finset.sum_congr rfl (fun c _ => ereord c)]
  rw [sum_fiber_subtype
    (g := fun w : Fin (n + 1) → Fin D => w 0)
    (F := fun _c w => ∏ i : Fin n, A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
      (w.1 (Fin.castSucc i)) (w.1 i.succ))]
  let ee : (Fin n → Fin D)
      ≃ {w : Fin (n + 1) → Fin D // w (Fin.last n) = w 0} :=
    { toFun := fun α =>
        ⟨snocPath α (α 0), by
          show snocPath α (α 0) (Fin.last n) = snocPath α (α 0) 0
          rw [snocPath_last, snocPath_zero]
          exact congrArg α (Fin.ext ((Fin.val_zero n).trans (Nat.zero_mod n).symm))⟩
      invFun := fun w => fun j => w.1 (Fin.castSucc j)
      left_inv := by
        intro α
        exact funext fun j => snocPath_castSucc α (α 0) j
      right_inv := by
        intro w
        refine Subtype.ext (funext fun k => ?_)
        by_cases hk : (k : ℕ) < n
        · have hc : k = Fin.castSucc ⟨(k : ℕ), hk⟩ := Fin.ext rfl
          rw [hc]
          show snocPath (fun j => w.1 (Fin.castSucc j)) (w.1 (Fin.castSucc 0))
              (Fin.castSucc ⟨(k : ℕ), hk⟩) = w.1 (Fin.castSucc ⟨(k : ℕ), hk⟩)
          rw [snocPath_castSucc]
        · have hkl : (k : ℕ) = n := by have := k.isLt; omega
          have hl : k = Fin.last n := Fin.ext hkl
          rw [hl]
          show snocPath (fun j => w.1 (Fin.castSucc j)) (w.1 (Fin.castSucc 0)) (Fin.last n)
            = w.1 (Fin.last n)
          rw [snocPath_last]
          exact (congrArg (w.1 : Fin (n + 1) → Fin D) (Fin.castSucc_zero (n := n))).trans
            (w.2 : (w.1 : Fin (n + 1) → Fin D) (Fin.last n) = w.1 0).symm }
  refine Fintype.sum_equiv ee
    (f := fun α => ∏ i : Fin n, A i (x i) (α i)
      (α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
    (g := fun w => ∏ i : Fin n, A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
      (w.1 (Fin.castSucc i)) (w.1 i.succ))
    (fun α => by
      have hE : ∀ k : Fin (n + 1),
          ((ee α).1 : Fin (n + 1) → Fin D) k = snocPath α (α 0) k := fun k => rfl
      refine Finset.prod_congr rfl fun i _ => ?_
      have himod : A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩
          (x ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩) = A i (x i) := by
        have hi : (⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i :=
          Fin.ext (Nat.mod_eq_of_lt i.isLt)
        rw [hi]
      have hsucc : snocPath α (α 0) (Fin.succ i)
          = α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
        rcases Nat.lt_or_ge ((i : ℕ) + 1) n with hk | hk
        · rw [snocPath_succ_of_lt _ _ _ hk]
          exact congrArg α (Fin.ext (Nat.mod_eq_of_lt hk).symm)
        · have hnge : ¬(((Fin.succ i : Fin (n + 1)) : ℕ) < n) := by
            simp only [Fin.val_succ]
            omega
          simp only [snocPath]
          rw [dif_neg hnge]
          have hi : (i : ℕ) = n - 1 := by have := i.isLt; omega
          rw [hi]
          have hz : (n - 1 + 1) % n = 0 := by
            rw [show n - 1 + 1 = n from by omega]
            exact Nat.mod_self n
          have hc : (0 : Fin n) = ⟨(n - 1 + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
            Fin.ext ((Fin.val_zero n).trans hz.symm)
          rw [hc]
      rw [himod, hE (Fin.castSucc i), hE (Fin.succ i),
        snocPath_castSucc α (α 0) i, hsucc])

theorem trace_prod_perRot {n : ℕ} [NeZero n] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ℕ → Matrix ι ι ℂ) :
    (chainProd (fun k => M ((k + 1) % n)) n).trace = (chainProd M n).trace := by
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hmod : (k + 1) % (k + 1) = 0 := Nat.mod_self _
  have hcongr : chainProd (fun j => M ((j + 1) % (k + 1))) k
      = chainProd (fun j => M (j + 1)) k := by
    refine chainProd_congr k fun j hj => ?_
    have hj1 : j + 1 < k + 1 := by omega
    rw [Nat.mod_eq_of_lt hj1]
  rw [chainProd_succ, hmod, Matrix.trace_mul_comm, hcongr, chainProd_shift]

theorem perAmp_siteRotate {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    periodicMpsAmplitude (fun i => A (perRot i)) (fun i => x (perRot i))
      = periodicMpsAmplitude A x := by
  rw [periodicMpsAmplitude_eq_trace, periodicMpsAmplitude_eq_trace]
  show (chainProd (fun k : ℕ => A (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (x (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))) n).trace
      = (chainProd (fun k : ℕ => A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩
          (x ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n).trace
  have hL : chainProd (fun k : ℕ => A (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (x (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))) n
      = chainProd (fun k : ℕ => A ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩
          (x ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩)) n := by
    refine chainProd_congr n fun k hk => ?_
    have hpe : perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩
        = ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩ := by
      rw [perRot]
      exact Fin.ext (Nat.mod_add_mod k n 1)
    show A (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (x (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))
      = A ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩
          (x ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩)
    rw [hpe]
  have hstep1 : chainProd (fun k : ℕ => A ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩
        (x ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩)) n
      = chainProd (fun k : ℕ =>
          (fun j : ℕ => A ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩
            (x ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩)) ((k + 1) % n)) n := by
    refine chainProd_congr n fun k _ => ?_
    show A ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩
        (x ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩)
      = A ⟨((k + 1) % n) % n, Nat.mod_lt ((k + 1) % n) (NeZero.pos n)⟩
          (x ⟨((k + 1) % n) % n, Nat.mod_lt ((k + 1) % n) (NeZero.pos n)⟩)
    have hfin : (⟨((k + 1) % n) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n)
        = ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩ :=
      Fin.ext (Nat.mod_mod (k + 1) n)
    rw [hfin]
  rw [hL, hstep1]
  exact trace_prod_perRot (M := fun j : ℕ =>
    A ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩ (x ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩))

theorem perAmp_siteRotatePow {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) (k : ℕ) :
    periodicMpsAmplitude (fun i => A ((perRot^[k]) i)) (fun i => x ((perRot^[k]) i))
      = periodicMpsAmplitude A x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (perAmp_siteRotate (fun j => A (perRot^[k] j))
      (fun j => x (perRot^[k] j))).trans ih

theorem perAmp_cfgRotate {n d D : ℕ} [NeZero n] [NeZero D]
    (B : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    periodicMpsAmplitude (fun _ => B) (fun i => x (perRot i))
      = periodicMpsAmplitude (fun _ => B) x :=
  perAmp_siteRotate (fun _ => B) x

theorem conj_sum_eq {σ : Type} [Fintype σ] (F : σ → ℂ) :
    conj (∑ u : σ, F u) = ∑ u : σ, conj (F u) := by
  rw [show conj (∑ u : σ, F u) = starRingEnd ℂ (∑ u : σ, F u) from rfl,
    map_sum (starRingEnd ℂ) F Finset.univ]

theorem conj_prod_eq {n : ℕ} (g : Fin n → ℂ) :
    conj (∏ i : Fin n, g i) = ∏ i : Fin n, conj (g i) := by
  rw [show conj (∏ i : Fin n, g i) = starRingEnd ℂ (∏ i : Fin n, g i) from rfl,
    map_prod (starRingEnd ℂ) g Finset.univ]

theorem prod_univ_eq_mul_erase {n : ℕ} {M : Type} [CommMonoid M] (F : Fin n → M) (z : Fin n) :
    ∏ i : Fin n, F i = F z * ∏ i ∈ Finset.univ.erase z, F i :=
  (Finset.mul_prod_erase Finset.univ F (Finset.mem_univ z)).symm

theorem sum_pi_prod_eq {n : ℕ} {σ : Type} [Fintype σ] (f : Fin n → σ → ℂ) :
    ∑ x : Fin n → σ, ∏ i : Fin n, f i (x i) = ∏ i : Fin n, ∑ u : σ, f i u :=
  (Fintype.prod_sum f).symm

theorem sum_rotate3 {σ₁ σ₂ σ₃ : Type} [Fintype σ₁] [Fintype σ₂] [Fintype σ₃]
    (T : σ₁ → σ₂ → σ₃ → ℂ) :
    ∑ a : σ₁, ∑ b : σ₂, ∑ c : σ₃, T a b c = ∑ b : σ₂, ∑ c : σ₃, ∑ a : σ₁, T a b c := by
  rw [sum_swap_fintype (F := fun a b => ∑ c : σ₃, T a b c)]
  exact Finset.sum_congr rfl fun b _ =>
    sum_swap_fintype (F := fun a c => T a b c)

theorem perPhysLeg_sum_pi {n d D : ℕ} [NeZero n]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (b c : Fin n → Fin D) :
    ∑ w : Fin n → Fin d,
        ∏ i : Fin n,
          conj (B i (w i) (b i) (b ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
            * A i (w i) (c i) (c ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
      = ∏ i : Fin n,
          ∑ u : Fin d,
            conj (B i u (b i) (b ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
              * A i u (c i) (c ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) :=
  sum_pi_prod_eq (f := fun (i : Fin n) (u : Fin d) =>
    conj (B i u (b i) (b ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
      * A i u (c i) (c ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))

theorem chainProd_trace_eq_ringSum {n : ℕ} [NeZero n] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ℕ → Matrix ι ι ℂ) :
    (chainProd M n).trace
      = ∑ α : Fin n → ι,
          ∏ i : Fin n, M (i : ℕ) (α i)
            (α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  have hps := chainProd_apply_eq_pathSum n M
  simp only [hps]
  let ereq : ∀ c : ι,
      {w : Fin (n + 1) → ι // w 0 = c ∧ w (Fin.last n) = c} ≃
        {w : Fin (n + 1) → ι // w (Fin.last n) = w 0 ∧ w 0 = c} :=
    fun c =>
      { toFun := fun w => ⟨w.1, ⟨w.2.2.trans w.2.1.symm, w.2.1⟩⟩,
        invFun := fun w => ⟨w.1, ⟨w.2.2, w.2.1.trans w.2.2⟩⟩,
        left_inv := fun w => rfl,
        right_inv := fun w => rfl }
  have ereord : ∀ c : ι,
      ∑ w : {w : Fin (n + 1) → ι // w 0 = c ∧ w (Fin.last n) = c},
          ∏ i : Fin n, M (i : ℕ) (w.1 (Fin.castSucc i)) (w.1 i.succ)
        = ∑ w : {w : Fin (n + 1) → ι // w (Fin.last n) = w 0 ∧ w 0 = c},
          ∏ i : Fin n, M (i : ℕ) (w.1 (Fin.castSucc i)) (w.1 i.succ) :=
    fun c => Fintype.sum_equiv (ereq c) _ _ (fun w => rfl)
  rw [Finset.sum_congr rfl (fun c _ => ereord c)]
  rw [sum_fiber_subtype
    (g := fun w : Fin (n + 1) → ι => w 0)
    (F := fun _c w => ∏ i : Fin n, M (i : ℕ) (w.1 (Fin.castSucc i)) (w.1 i.succ))]
  let ee : (Fin n → ι) ≃ {w : Fin (n + 1) → ι // w (Fin.last n) = w 0} :=
    { toFun := fun α =>
        ⟨snocPath α (α 0), by
          show snocPath α (α 0) (Fin.last n) = snocPath α (α 0) 0
          rw [snocPath_last, snocPath_zero]
          exact congrArg α (Fin.ext ((Fin.val_zero n).trans (Nat.zero_mod n).symm))⟩
      invFun := fun w => fun j => w.1 (Fin.castSucc j)
      left_inv := by
        intro α
        exact funext fun j => snocPath_castSucc α (α 0) j
      right_inv := by
        intro w
        refine Subtype.ext (funext fun k => ?_)
        by_cases hk : (k : ℕ) < n
        · have hc : k = Fin.castSucc ⟨(k : ℕ), hk⟩ := Fin.ext rfl
          rw [hc]
          show snocPath (fun j => w.1 (Fin.castSucc j)) (w.1 (Fin.castSucc 0))
              (Fin.castSucc ⟨(k : ℕ), hk⟩) = w.1 (Fin.castSucc ⟨(k : ℕ), hk⟩)
          rw [snocPath_castSucc]
        · have hkl : (k : ℕ) = n := by have := k.isLt; omega
          have hl : k = Fin.last n := Fin.ext hkl
          rw [hl]
          show snocPath (fun j => w.1 (Fin.castSucc j)) (w.1 (Fin.castSucc 0)) (Fin.last n)
              = w.1 (Fin.last n)
          rw [snocPath_last]
          exact (congrArg (w.1 : Fin (n + 1) → ι) (Fin.castSucc_zero (n := n))).trans
            (w.2 : (w.1 : Fin (n + 1) → ι) (Fin.last n) = w.1 0).symm }
  refine (Fintype.sum_equiv ee
    (f := fun α => ∏ i : Fin n, M (i : ℕ) (α i)
      (α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
    (g := fun w => ∏ i : Fin n, M (i : ℕ) (w.1 (Fin.castSucc i)) (w.1 i.succ))
    (fun α => by
      have hE : ∀ k : Fin (n + 1),
          ((ee α).1 : Fin (n + 1) → ι) k = snocPath α (α 0) k := fun k => rfl
      refine Finset.prod_congr rfl fun i _ => ?_
      have hsucc : snocPath α (α 0) (Fin.succ i)
          = α ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
        rcases Nat.lt_or_ge ((i : ℕ) + 1) n with hk | hk
        · rw [snocPath_succ_of_lt _ _ _ hk]
          exact congrArg α (Fin.ext (Nat.mod_eq_of_lt hk).symm)
        · have hnge : ¬(((Fin.succ i : Fin (n + 1)) : ℕ) < n) := by
            simp only [Fin.val_succ]
            omega
          simp only [snocPath]
          rw [dif_neg hnge]
          have hi : (i : ℕ) = n - 1 := by have := i.isLt; omega
          rw [hi]
          have hz : (n - 1 + 1) % n = 0 := by
            rw [show n - 1 + 1 = n from by omega]
            exact Nat.mod_self n
          have hc : (0 : Fin n) = ⟨(n - 1 + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
            Fin.ext ((Fin.val_zero n).trans hz.symm)
          rw [hc]
      rw [hE (Fin.castSucc i), hE (Fin.succ i), snocPath_castSucc α (α 0) i, hsucc])).symm

noncomputable def perE {d D : ℕ} (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ x : Fin d, M x p.1 q.1 * conj (M x p.2 q.2)

theorem perE_apply {d D : ℕ} (M : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (p q : Fin D × Fin D) :
    perE M p q = ∑ x : Fin d, M x p.1 q.1 * conj (M x p.2 q.2) := rfl

noncomputable def perED {d D : ℕ} (M N : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ x : Fin d, M x p.1 q.1 * conj (N x p.2 q.2)

theorem perED_self {d D : ℕ} (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    perED M M = perE M := rfl

theorem perInner_eq_trace {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude B x) * periodicMpsAmplitude A x
      = (chainProd (fun k : ℕ =>
          perED (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
            (B ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n).trace := by
  rw [chainProd_trace_eq_ringSum
    (M := fun k : ℕ =>
      perED (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (B ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))]
  simp only [periodicMpsAmplitude]
  simp only [conj_sum_eq, Finset.sum_mul_sum]
  simp_rw [conj_prod_eq, ← Finset.prod_mul_distrib]
  rw [sum_rotate3 (T := fun (w : Fin n → Fin d) (c b : Fin n → Fin D) =>
    ∏ i : Fin n,
      conj (B i (w i) (c i) (c ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
        * A i (w i) (b i) (b ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))]
  simp only [perPhysLeg_sum_pi A B]
  rw [← Fintype.sum_prod_type (f := fun q : (Fin n → Fin D) × (Fin n → Fin D) =>
    ∏ i : Fin n,
      ∑ u : Fin d,
        conj (B i u (q.1 i) (q.1 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
          * A i u (q.2 i) (q.2 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))]
  let ps : (Fin n → Fin D × Fin D) ≃ (Fin n → Fin D) × (Fin n → Fin D) :=
    { toFun := fun p => (fun i => (p i).2, fun i => (p i).1),
      invFun := fun q => fun i => (q.2 i, q.1 i),
      left_inv := fun p => funext fun i => rfl,
      right_inv := fun q => rfl }
  refine (Fintype.sum_equiv ps
    (f := fun p =>
      ∏ i : Fin n,
        perED (A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
          (B ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩) (p i)
          (p ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
    (g := fun q =>
      ∏ i : Fin n,
        ∑ u : Fin d,
          conj (B i u (q.1 i) (q.1 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
            * A i u (q.2 i) (q.2 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
    (fun p => ?_)).symm
  have hmodA : ∀ i : Fin n,
      A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = A i :=
    fun i => congrArg A (Fin.ext (Nat.mod_eq_of_lt i.isLt))
  have hmodB : ∀ i : Fin n,
      B ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = B i :=
    fun i => congrArg B (Fin.ext (Nat.mod_eq_of_lt i.isLt))
  refine Finset.prod_congr rfl fun i _ => ?_
  show (∑ x : Fin d,
        A ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩ x (p i).1
            (p ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩).1
          * conj (B ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩ x (p i).2
              (p ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩).2))
      = ∑ u : Fin d,
        conj (B i u ((ps p).1 i)
            ((ps p).1 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
          * A i u ((ps p).2 i)
            ((ps p).2 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
  rw [hmodA i, hmodB i]
  exact Finset.sum_congr rfl fun u _ => mul_comm _ _

theorem perNorm_eq_trace {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A x) * periodicMpsAmplitude A x
      = (chainProd (fun k : ℕ => perE (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n).trace :=
  perInner_eq_trace A A

theorem perNorm_siteRotate {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude (fun i => A (perRot i)) x)
          * periodicMpsAmplitude (fun i => A (perRot i)) x
      = ∑ x : Fin n → Fin d,
          conj (periodicMpsAmplitude A x) * periodicMpsAmplitude A x := by
  rw [perNorm_eq_trace, perNorm_eq_trace]
  have h1 : (chainProd (fun k : ℕ => perE ((fun i => A (perRot i))
        ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n).trace
      = (chainProd (fun k : ℕ =>
          (fun j : ℕ => perE (A ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩)) ((k + 1) % n)) n).trace := by
    have hcongr : chainProd (fun k : ℕ => perE ((fun i => A (perRot i))
        ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n
      = chainProd (fun k : ℕ =>
          (fun j : ℕ => perE (A ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩)) ((k + 1) % n)) n := by
      refine chainProd_congr n fun k hk => ?_
      have hpe : (fun i => A (perRot i)) ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩
          = A ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩ := by
        have hrot : perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩
            = ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩ :=
          Fin.ext (Nat.mod_add_mod k n 1)
        show A (perRot ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩) = _
        rw [hrot]
      rw [hpe]
      have hfin : (⟨((k + 1) % n) % n, Nat.mod_lt ((k + 1) % n) (NeZero.pos n)⟩ : Fin n)
          = ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩ :=
        Fin.ext (Nat.mod_mod (k + 1) n)
      show perE (A ⟨(k + 1) % n, Nat.mod_lt (k + 1) (NeZero.pos n)⟩)
          = perE (A ⟨((k + 1) % n) % n, Nat.mod_lt ((k + 1) % n) (NeZero.pos n)⟩)
      rw [hfin]
    rw [hcongr]
  rw [h1]
  exact trace_prod_perRot (M := fun j : ℕ =>
    perE (A ⟨j % n, Nat.mod_lt j (NeZero.pos n)⟩))

theorem chainProd_const {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ∀ m : ℕ, chainProd (fun _ => M) m = M ^ m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [chainProd_succ, ih, pow_succ]

theorem perNorm_eq_trace_pow {n d D : ℕ} [NeZero n] [NeZero D]
    (B : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude (fun _ => B) x) * periodicMpsAmplitude (fun _ => B) x
      = (perE B ^ n).trace := by
  rw [perNorm_eq_trace (fun _ => B)]
  have hcongr : chainProd (fun k : ℕ => perE ((fun _ : Fin n => B)
      ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n = chainProd (fun _ => perE B) n :=
    chainProd_congr n fun k _ => rfl
  rw [hcongr, chainProd_const]

noncomputable def perObsTensor {n d D : ℕ}
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i => if i = z then Matrix.of fun u l r => ∑ y : Fin d, O u y * A i y l r else A i

theorem perObsTensor_self {n d D : ℕ}
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) :
    perObsTensor A z O z = Matrix.of fun u l r => ∑ y : Fin d, O u y * A z y l r := by
  show (if z = z then Matrix.of fun u l r => ∑ y : Fin d, O u y * A z y l r else A z) = _
  rw [if_pos rfl]

theorem perObsTensor_of_ne {n d D : ℕ}
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) {i : Fin n} (hi : i ≠ z) :
    perObsTensor A z O i = A i := by
  show (if i = z then Matrix.of fun u l r => ∑ y : Fin d, O u y * A i y l r else A i) = _
  rw [if_neg hi]

theorem perAmp_obsUpdate_eq {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) (x : Fin n → Fin d) :
    ∑ y : Fin d, O (x z) y * periodicMpsAmplitude A (Function.update x z y)
      = periodicMpsAmplitude (perObsTensor A z O) x := by
  simp only [periodicMpsAmplitude]
  have hket : ∀ (y : Fin d) (β : Fin n → Fin D),
      ∏ i : Fin n, A i (Function.update x z y i) (β i)
          (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        = A z y (β z) (β ⟨((z : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
            * ∏ i ∈ Finset.univ.erase z, A i (x i) (β i)
                (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) := by
    intro y β
    rw [prod_univ_eq_mul_erase, Function.update_self]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun i hi => ?_)
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have hobs : ∀ β : Fin n → Fin D,
      ∏ i : Fin n, perObsTensor A z O i (x i) (β i)
          (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        = (∑ y : Fin d, O (x z) y
              * A z y (β z) (β ⟨((z : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
            * ∏ i ∈ Finset.univ.erase z, A i (x i) (β i)
                (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) := by
    intro β
    rw [prod_univ_eq_mul_erase]
    refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun i hi => ?_)
    · rw [perObsTensor_self]
      rfl
    · rw [perObsTensor_of_ne A z O (Finset.mem_erase.mp hi).1]
  simp only [hket]
  simp only [Finset.mul_sum]
  rw [sum_swap_fintype (F := fun (y : Fin d) (β : Fin n → Fin D) =>
    O (x z) y * (A z y (β z) (β ⟨((z : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
      * ∏ i ∈ Finset.univ.erase z, A i (x i) (β i)
          (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)))]
  simp only [hobs]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]

noncomputable def perEO {d D : ℕ} (O : Matrix (Fin d) (Fin d) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ u : Fin d,
    (∑ y : Fin d, O u y * M y p.1 q.1) * conj (M u p.2 q.2)

noncomputable def perObsChain {n d D : ℕ} [NeZero n]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) :
    ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun k =>
  if (k % n) = (z : ℕ) then perEO O (A z)
  else perE (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)

theorem perObsExpectation_eq_trace {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A x)
          * ∑ y : Fin d, O (x z) y * periodicMpsAmplitude A (Function.update x z y)
      = (chainProd (perObsChain A z O) n).trace := by
  rw [Finset.sum_congr rfl (fun x _ => by rw [perAmp_obsUpdate_eq A z O x])]
  rw [perInner_eq_trace]
  refine congrArg Matrix.trace (chainProd_congr n fun k hk => ?_)
  by_cases hz : (k % n) = (z : ℕ)
  · have hke : (⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩ : Fin n) = z := Fin.ext hz
    show perED (perObsTensor A z O ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
      = (if (k % n) = (z : ℕ) then perEO O (A z)
          else perE (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))
    rw [if_pos hz, hke, perObsTensor_self]
    rfl
  · show perED (perObsTensor A z O ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
      = (if (k % n) = (z : ℕ) then perEO O (A z)
          else perE (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))
    rw [if_neg hz, perObsTensor_of_ne A z O
      (fun h => hz (congrArg (fun i : Fin n => (i : ℕ)) h))]
    exact congrArg₂ perED rfl rfl

def pepsPhysLegIdx (a b : ℕ) (v : Fin (a * b)) : Fin (pepsNh a b) :=
  ⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩

theorem pepsPhysLegIdx_val (a b : ℕ) (v : Fin (a * b)) :
    (pepsPhysLegIdx a b v : ℕ) = 5 * (v : ℕ) := rfl

theorem pepsPartner_pepsPhysLegIdx_none (a b : ℕ) (v : Fin (a * b)) :
    pepsPartner a b (pepsPhysLegIdx a b v) = none :=
  pepsPartner_phys a b (v : ℕ) (peps_pos_of_v a b v).1 (peps_pos_of_v a b v).2 v.isLt

theorem pepsPartner_of_phys (a b : ℕ) {j : Fin (pepsNh a b)}
    (hreg : (j : ℕ) < 5 * a * b) (hmod : (j : ℕ) % 5 = 0) :
    pepsPartner a b j = none := by
  unfold pepsPartner
  by_cases hz : a = 0 ∨ b = 0
  · rw [dif_pos hz]
  · rw [dif_neg hz, dif_pos hreg, dif_pos hmod]

noncomputable def pepsPhysLeg (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (v : Fin (a * b)) : OpenLeg (pepsNet a b d D T) where
  val := pepsPhysLegIdx a b v
  property := pepsPartner_pepsPhysLegIdx_none a b v

theorem pepsNet_dims_physLeg (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (v : Fin (a * b)) :
    (pepsNet a b d D T).dims (pepsPhysLeg a b d D T v).val = d := by
  show pepsDim a b d D (5 * (v : ℕ) + 0) = d
  rw [pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
    (pepsLeg_mod (v : ℕ) 0 (by omega))]

theorem pepsNet_dims_internal (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (i : InternalEdge (pepsNet a b d D T)) :
    (pepsNet a b d D T).dims i.val = D := by
  obtain ⟨k, hk, _⟩ := i.property
  show pepsDim a b d D (i.val : ℕ) = D
  by_cases hz : a = 0 ∨ b = 0
  · exfalso
    have hn : (pepsNet a b d D T).partner i.val = none := by
      show pepsPartner a b i.val = none
      unfold pepsPartner
      rw [dif_pos hz]
    rw [hn] at hk
    exact absurd hk (by simp)
  · by_cases hreg : (i.val : ℕ) < 5 * a * b
    · by_cases hmod : (i.val : ℕ) % 5 = 0
      · exfalso
        have hn : (pepsNet a b d D T).partner i.val = none :=
          pepsPartner_of_phys a b hreg hmod
        rw [hn] at hk
        exact absurd hk (by simp)
      · rw [pepsDim, if_neg (fun hc => hmod hc.2)]
    · rw [pepsDim, if_neg (fun hc => absurd hc.1 hreg)]

noncomputable def pepsEdgeAssign (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (i : InternalEdge (pepsNet a b d D T)) : Fin ((pepsNet a b d D T).dims i.val) :=
  (0 : Fin D).cast (pepsNet_dims_internal a b d D T i).symm

theorem portValue_ext_congr_of_partner_some {N : TensorNet} (y y' : OpenAssign N)
    (e : ∀ i : InternalEdge N, Fin (N.dims i.val)) {j : Fin N.nh}
    (hj : N.partner j ≠ none) :
    portValue N y e j = portValue N y' e j := by
  cases hk : N.partner j with
  | none => exact absurd hk hj
  | some k =>
    rcases lt_trichotomy j k with hlt | heq | hgt
    · rw [portValue_of_partner_eq y e j k hk hlt, portValue_of_partner_eq y' e j k hk hlt]
    · exact absurd heq (N.no_self_loop j k hk)
    · rw [portValue_of_partner_eq_rev y e j k hk hgt (N.involution j k hk)
        (N.dims_match j k hk).symm,
        portValue_of_partner_eq_rev y' e j k hk hgt (N.involution j k hk)
          (N.dims_match j k hk).symm]

def pepsPhysPort (a b : ℕ) (v : Fin (a * b)) :
    {h : Fin (pepsNh a b) // pepsSite a b h = v} :=
  ⟨pepsPhysLegIdx a b v, by exact pepsSite_leg a b v 0 (by omega)⟩

theorem pepsTensor_congr_ports (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) (v : Fin (a * b))
    (α α' : ∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v},
        Fin (pepsDim a b d D h.val.val))
    (hphys : α (pepsPhysPort a b v) = α' (pepsPhysPort a b v))
    (hbond : ∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v},
        pepsPartner a b h.val ≠ none → α h = α' h) :
    pepsTensor a b d D T v α = pepsTensor a b d D T v α' := by
  have ha := (peps_pos_of_v a b v).1
  have hb := (peps_pos_of_v a b v).2
  have hdm : b * ((v : ℕ) / b) + (v : ℕ) % b = (v : ℕ) := peps_divmod (v : ℕ) b
  have hmb : (v : ℕ) % b < b := Nat.mod_lt _ hb
  have hpf : (((finProdFinEquiv (m := a) (n := b)).symm v).1 : ℕ) = (v : ℕ) / b :=
    pepsP_fst a b v
  have hps : (((finProdFinEquiv (m := a) (n := b)).symm v).2 : ℕ) = (v : ℕ) % b :=
    pepsP_snd a b v
  have hlt : (v : ℕ) / b < a := by rw [← hpf]; exact
    (((finProdFinEquiv (m := a) (n := b)).symm v).1).isLt
  simp only [pepsTensor]
  rw [hpf, hps]
  congr 1
  · exact congrArg _ hphys
  · by_cases h1 : (v : ℕ) / b = 0
    · rw [dif_pos h1, dif_pos h1]
    · rw [dif_neg h1, dif_neg h1]
      refine congrArg _ (hbond ⟨⟨5 * (v : ℕ) + 1,
          pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
          pepsSite_leg a b v 1 (by omega)⟩ ?_)
      have hle : b * 1 ≤ b * ((v : ℕ) / b) := Nat.mul_le_mul_left b (by omega)
      rw [Nat.mul_one] at hle
      simp [pepsPartner_left_bond a b (v : ℕ) ha hb (by omega) v.isLt]
  · by_cases h2 : (v : ℕ) / b + 1 = a
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      refine congrArg _ (hbond ⟨⟨5 * (v : ℕ) + 2,
          pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
          pepsSite_leg a b v 2 (by omega)⟩ ?_)
      have hlast : (a - 1) * b + b = a * b := by
        have h0 : (a - 1) + 1 = a := by omega
        nlinarith [Nat.add_mul (a - 1) 1 b]
      have hlin : (v : ℕ) / b + 1 ≤ a - 1 := by omega
      have hle : b * ((v : ℕ) / b + 1) ≤ (a - 1) * b := by
        rw [Nat.mul_comm b ((v : ℕ) / b + 1)]
        exact Nat.mul_le_mul_right b hlin
      have hexp : b * ((v : ℕ) / b + 1) = b * ((v : ℕ) / b) + b := by ring
      simp [pepsPartner_right_bond a b (v : ℕ) ha hb (by omega) ]
  · by_cases h3 : (v : ℕ) % b + 1 = b
    · rw [if_pos h3, if_pos h3]
    · rw [if_neg h3, if_neg h3]
      refine congrArg _ (hbond ⟨⟨5 * (v : ℕ) + 3,
          pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
          pepsSite_leg a b v 3 (by omega)⟩ ?_)
      simp [pepsPartner_down_bond a b (v : ℕ) ha hb (by omega) v.isLt]
  · by_cases h4 : (v : ℕ) % b = 0
    · rw [dif_pos h4, dif_pos h4]
    · rw [dif_neg h4, dif_neg h4]
      refine congrArg _ (hbond ⟨⟨5 * (v : ℕ) + 4,
          pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
          pepsSite_leg a b v 4 (by omega)⟩ ?_)
      simp [pepsPartner_up_bond a b (v : ℕ) ha hb h4]

theorem netContract_pepsNet_open_congr (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (y y' : OpenAssign (pepsNet a b d D T))
    (hphys : ∀ v : Fin (a * b),
      (y (pepsPhysLeg a b d D T v)).val = (y' (pepsPhysLeg a b d D T v)).val) :
    netContract (pepsNet a b d D T) y = netContract (pepsNet a b d D T) y' := by
  show (∑ e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val),
      ∏ v : Fin (a * b),
        (pepsNet a b d D T).tensor v (fun h => portValue (pepsNet a b d D T) y e h.val))
    = ∑ e : ∀ i : InternalEdge (pepsNet a b d D T), Fin ((pepsNet a b d D T).dims i.val),
      ∏ v : Fin (a * b),
        (pepsNet a b d D T).tensor v (fun h => portValue (pepsNet a b d D T) y' e h.val)
  refine congrArg _ (funext fun e => Finset.prod_congr rfl fun v _ => ?_)
  show pepsTensor a b d D T v (fun h => portValue (pepsNet a b d D T) y e h.val)
      = pepsTensor a b d D T v (fun h => portValue (pepsNet a b d D T) y' e h.val)
  refine pepsTensor_congr_ports a b d D T v _ _ ?_ ?_
  · show portValue (pepsNet a b d D T) y e (pepsPhysLegIdx a b v)
        = portValue (pepsNet a b d D T) y' e (pepsPhysLegIdx a b v)
    rw [portValue_of_partner_none _ e (pepsPhysLegIdx a b v)
        (pepsPartner_pepsPhysLegIdx_none a b v),
      portValue_of_partner_none _ e (pepsPhysLegIdx a b v)
        (pepsPartner_pepsPhysLegIdx_none a b v)]
    exact Fin.ext (hphys v)
  · intro h hsome
    exact portValue_ext_congr_of_partner_some y y' e hsome

theorem pepsEnc_physLeg (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) (v : Fin (a * b)) :
    (pepsEnc a b d D T x (pepsPhysLeg a b d D T v)).cast (pepsNet_dims_physLeg a b d D T v)
      = x (pepsP a b v).1 (pepsP a b v).2 := by
  have h1 := pepsPort_phys a b d D T x (pepsEdgeAssign a b d D T) v
  have h2 : portValue (pepsNet a b d D T) (pepsEnc a b d D T x) (pepsEdgeAssign a b d D T)
        (pepsPhysLegIdx a b v) = pepsEnc a b d D T x (pepsPhysLeg a b d D T v) :=
    portValue_of_partner_none _ _ _ (pepsPartner_pepsPhysLegIdx_none a b v)
  exact (congrArg (Fin.cast _) h2.symm).trans h1

theorem peps_site_coord_idx (a b : ℕ) (v : Fin (a * b)) :
    ((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ) = (v : ℕ) := by
  rw [pepsP_fst, pepsP_snd]
  have h := peps_divmod (v : ℕ) b
  have h' : (v : ℕ) / b * b = b * ((v : ℕ) / b) := Nat.mul_comm _ _
  omega

theorem peps_site_idx_coord (a b : ℕ) (hb : 0 < b) (i : Fin a) (c : Fin b) :
    pepsP a b ⟨(i : ℕ) * b + (c : ℕ), peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩ = (i, c) := by
  refine Prod.ext ?_ ?_
  · refine Fin.ext ?_
    show ((i : ℕ) * b + (c : ℕ)) / b = (i : ℕ)
    rw [Nat.mul_comm (i : ℕ) b, Nat.add_comm (b * (i : ℕ)) (c : ℕ),
      Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt c.isLt]
    omega
  · refine Fin.ext ?_
    show ((i : ℕ) * b + (c : ℕ)) % b = (c : ℕ)
    rw [Nat.mul_comm (i : ℕ) b, Nat.add_comm (b * (i : ℕ)) (c : ℕ),
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt]

noncomputable def pepsOpenDecode (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (y : OpenAssign (pepsNet a b d D T)) : Fin a → Fin b → Fin d :=
  fun i c =>
    (y (pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
      peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩)).cast
      (pepsNet_dims_physLeg a b d D T _)

theorem pepsOpenDecode_enc (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) :
    pepsOpenDecode a b d D T (pepsEnc a b d D T x) = x := by
  by_cases hex : Nonempty (Fin (a * b))
  · obtain ⟨v₀⟩ := hex
    have hb : 0 < b := (peps_pos_of_v a b v₀).2
    funext i c
    show ((pepsEnc a b d D T x (pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ), _⟩)).cast
        (pepsNet_dims_physLeg a b d D T _)) = x i c
    rw [pepsEnc_physLeg a b d D T x ⟨(i : ℕ) * b + (c : ℕ),
      peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩,
      peps_site_idx_coord a b hb i c]
  · funext i c
    exfalso
    rcases Nat.eq_zero_or_pos a with ha | ha
    · exact absurd i.isLt (by omega)
    · exact absurd c.isLt (by
        have hb0 : b = 0 := by
          by_contra hpos
          exact hex ⟨⟨0, Nat.mul_pos ha (Nat.pos_of_ne_zero hpos)⟩⟩
        omega)

theorem netContract_pepsNet_eval (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (y : OpenAssign (pepsNet a b d D T)) :
    netContract (pepsNet a b d D T) y
      = pepsAmplitude T (pepsOpenDecode a b d D T y) := by
  by_cases hex : Nonempty (Fin (a * b))
  · obtain ⟨v₀⟩ := hex
    have hb : 0 < b := (peps_pos_of_v a b v₀).2
    rw [netContract_pepsNet_open_congr a b d D T y
      (pepsEnc a b d D T (pepsOpenDecode a b d D T y)) ?_, netContract_pepsNet_eq]
    intro v
    have h := pepsEnc_physLeg a b d D T (pepsOpenDecode a b d D T y) v
    have hcoord := peps_site_coord_idx a b v
    have hleg : pepsPhysLeg a b d D T
        ⟨((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ), by
          have hv := v.isLt
          omega⟩ = pepsPhysLeg a b d D T v :=
      Subtype.ext (Fin.ext (by
        show 5 * (((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ)) = 5 * (v : ℕ)
        omega))
    have hval : (pepsEnc a b d D T (pepsOpenDecode a b d D T y)
          (pepsPhysLeg a b d D T v)).val
        = (pepsOpenDecode a b d D T y (pepsP a b v).1 (pepsP a b v).2).val := by
      rw [← h]
      simp
    exact (calc (pepsEnc a b d D T (pepsOpenDecode a b d D T y)
          (pepsPhysLeg a b d D T v)).val
        = (pepsOpenDecode a b d D T y (pepsP a b v).1 (pepsP a b v).2).val := hval
      _ = (y (pepsPhysLeg a b d D T v)).val := by
          show (Fin.cast _ (y (pepsPhysLeg a b d D T
              ⟨((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ), _⟩))).val
              = (y (pepsPhysLeg a b d D T v)).val
          rw [Fin.val_cast]
          exact congrArg (fun o : OpenLeg (pepsNet a b d D T) => (y o).val) hleg).symm
  · have hab : a * b = 0 := by
      by_contra hc
      exact hex ⟨⟨0, Nat.pos_of_ne_zero hc⟩⟩
    have hz : a = 0 ∨ b = 0 := Nat.mul_eq_zero.mp hab
    have hnv : (pepsNet a b d D T).nv = 0 := hab
    have hnh : (pepsNet a b d D T).nh = 0 := pepsNh_of_zero hz
    have hnc : netContract (pepsNet a b d D T) y = 1 :=
      netContract_of_empty_net hnv hnh y
    haveI hempty : IsEmpty (Fin a × Fin b) := ⟨fun p =>
      match hz with
      | Or.inl h => absurd p.1.isLt (by omega)
      | Or.inr h => absurd p.2.isLt (by omega)⟩
    have hemp : pepsAmplitude T (pepsOpenDecode a b d D T y) = 1 := by
      rw [pepsAmplitude_eq]
      have h1 : ∀ γ : Fin a × Fin b → Fin D × Fin D,
          ∏ p : Fin a × Fin b, pepsFactor T (pepsOpenDecode a b d D T y) γ p = 1 :=
        fun _ => by rw [Finset.univ_eq_empty]; exact Finset.prod_empty
      rw [Finset.sum_congr rfl (fun γ _ => h1 γ), Finset.sum_const, Finset.card_univ,
        Fintype.card_unique]
      simp
    rw [hnc, hemp]

theorem netContract_pepsNet_permPush (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (x : Fin a → Fin b → Fin d) (π : Fin (pepsNh a b) ≃ Fin (pepsNh a b)) :
    netContract (permNet (pepsNet a b d D T) π)
        (openPush (pepsNet a b d D T) π (pepsEnc a b d D T x)) = pepsAmplitude T x := by
  rw [netContract_permPush, netContract_pepsNet_eq]

def pepsPhysMap (a b : ℕ) (σ : Fin (a * b) ≃ Fin (a * b)) (j : Fin (pepsNh a b)) :
    Fin (pepsNh a b) :=
  if h : (j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0 then
    ⟨5 * ((σ ⟨(j : ℕ) / 5,
        Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ : Fin (a * b)) : ℕ),
      pepsLeg_lt_nh a b ((σ ⟨(j : ℕ) / 5,
        Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ : Fin (a * b)) : ℕ) 0
        (σ ⟨(j : ℕ) / 5,
          Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩).isLt (by omega)⟩
  else j

theorem pepsPhysMap_val (a b : ℕ) (σ : Fin (a * b) ≃ Fin (a * b)) (j : Fin (pepsNh a b)) :
    (pepsPhysMap a b σ j : ℕ)
      = if h : (j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0 then
          5 * ((σ ⟨(j : ℕ) / 5,
            Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ : Fin (a * b)) : ℕ)
        else (j : ℕ) := by
  by_cases h : (j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0
  · simp only [pepsPhysMap, dif_pos h]
  · simp only [pepsPhysMap, dif_neg h]

theorem pepsPhysMap_phys (a b : ℕ) (σ : Fin (a * b) ≃ Fin (a * b)) (v : Fin (a * b)) :
    pepsPhysMap a b σ (pepsPhysLegIdx a b v) = pepsPhysLegIdx a b (σ v) := by
  have h : (pepsPhysLegIdx a b v : ℕ) < 5 * a * b ∧ (pepsPhysLegIdx a b v : ℕ) % 5 = 0 :=
    ⟨pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega), Nat.mul_mod_right 5 _⟩
  have hw : (⟨(pepsPhysLegIdx a b v : ℕ) / 5,
      Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ : Fin (a * b)) = v := by
    refine Fin.ext ?_
    have hd := Nat.div_add_mod (pepsPhysLegIdx a b v : ℕ) 5
    have hm := h.2
    show (pepsPhysLegIdx a b v : ℕ) / 5 = (v : ℕ)
    rw [pepsPhysLegIdx_val]
    omega
  have harg : ((σ ⟨(pepsPhysLegIdx a b v : ℕ) / 5,
      Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ : Fin (a * b)) : ℕ)
      = ((σ v : Fin (a * b)) : ℕ) :=
    congrArg (fun w : Fin (a * b) => (σ w : ℕ)) hw
  simp only [pepsPhysMap, dif_pos h]
  refine Fin.ext ?_
  show 5 * ((σ ⟨(pepsPhysLegIdx a b v : ℕ) / 5,
      Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ : Fin (a * b)) : ℕ)
      = 5 * ((σ v : Fin (a * b)) : ℕ)
  exact congrArg (fun t : ℕ => 5 * t) harg

theorem pepsPhysMap_nonphys (a b : ℕ) (σ : Fin (a * b) ≃ Fin (a * b))
    (j : Fin (pepsNh a b)) (h : ¬((j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0)) :
    pepsPhysMap a b σ j = j := by
  simp only [pepsPhysMap, dif_neg h]

def pepsPhysLegPerm (a b : ℕ) (ρ : Fin (a * b) ≃ Fin (a * b)) :
    Fin (pepsNh a b) ≃ Fin (pepsNh a b) where
  toFun j := pepsPhysMap a b ρ j
  invFun j := pepsPhysMap a b ρ.symm j
  left_inv j := by
    by_cases h : (j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0
    · obtain ⟨k, hk⟩ : ∃ k : Fin (a * b), (j : ℕ) = 5 * (k : ℕ) :=
        ⟨⟨(j : ℕ) / 5, Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩,
          by have hd := Nat.div_add_mod (j : ℕ) 5
             show (j : ℕ) = 5 * ((j : ℕ) / 5)
             omega⟩
      have hj : j = pepsPhysLegIdx a b k := Fin.ext hk
      rw [hj]
      show pepsPhysMap a b ρ.symm (pepsPhysMap a b ρ (pepsPhysLegIdx a b k))
          = pepsPhysLegIdx a b k
      rw [pepsPhysMap_phys a b ρ k, pepsPhysMap_phys a b ρ.symm (ρ k), ρ.symm_apply_apply]
    · show pepsPhysMap a b ρ.symm (pepsPhysMap a b ρ j) = j
      rw [pepsPhysMap_nonphys a b ρ j h, pepsPhysMap_nonphys a b ρ.symm j h]
  right_inv j := by
    by_cases h : (j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0
    · obtain ⟨k, hk⟩ : ∃ k : Fin (a * b), (j : ℕ) = 5 * (k : ℕ) :=
        ⟨⟨(j : ℕ) / 5, Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩,
          by have hd := Nat.div_add_mod (j : ℕ) 5
             show (j : ℕ) = 5 * ((j : ℕ) / 5)
             omega⟩
      have hj : j = pepsPhysLegIdx a b k := Fin.ext hk
      rw [hj]
      show pepsPhysMap a b ρ (pepsPhysMap a b ρ.symm (pepsPhysLegIdx a b k))
          = pepsPhysLegIdx a b k
      rw [pepsPhysMap_phys a b ρ.symm k, pepsPhysMap_phys a b ρ (ρ.symm k),
        ρ.apply_symm_apply]
    · show pepsPhysMap a b ρ (pepsPhysMap a b ρ.symm j) = j
      rw [pepsPhysMap_nonphys a b ρ.symm j h, pepsPhysMap_nonphys a b ρ j h]

theorem pepsPhysLegPerm_apply (a b : ℕ) (ρ : Fin (a * b) ≃ Fin (a * b))
    (j : Fin (pepsNh a b)) : pepsPhysLegPerm a b ρ j = pepsPhysMap a b ρ j := rfl

def pepsBoundaryLeg (a b : ℕ) : Type :=
  {j : Fin (pepsNh a b) // pepsPartner a b j = none ∧ ¬((j : ℕ) < 5 * a * b ∧ (j : ℕ) % 5 = 0)}

instance (a b : ℕ) : Fintype (pepsBoundaryLeg a b) := Subtype.fintype _

instance (a b : ℕ) : DecidableEq (pepsBoundaryLeg a b) := Subtype.instDecidableEq

instance (a b D : ℕ) : Fintype (∀ _o : pepsBoundaryLeg a b, Fin D) := Pi.instFintype

theorem pepsBoundaryLeg_dims (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (o : pepsBoundaryLeg a b) :
    (pepsNet a b d D T).dims o.val = D := by
  show pepsDim a b d D (o.val : ℕ) = D
  exact pepsDim_of_not_phys a b d D o.property.2

noncomputable def pepsBoundaryRead (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (y : OpenAssign (pepsNet a b d D T)) : ∀ _o : pepsBoundaryLeg a b, Fin D :=
  fun o => (y ⟨o.val, o.property.1⟩).cast (pepsBoundaryLeg_dims a b d D T o)

noncomputable def pepsOpenCombine (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : (Fin a → Fin b → Fin d) × (∀ _o : pepsBoundaryLeg a b, Fin D)) :
    OpenAssign (pepsNet a b d D T) :=
  fun o =>
    if h : (o.val : ℕ) < 5 * a * b ∧ (o.val : ℕ) % 5 = 0 then
      (p.1
        (pepsP a b ⟨(o.val : ℕ) / 5,
          Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩).1
        (pepsP a b ⟨(o.val : ℕ) / 5,
          Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩).2).cast
        (by
          show d = pepsDim a b d D (o.val : ℕ)
          rw [pepsDim, if_pos h])
    else
      (p.2 ⟨o.val, o.property, h⟩).cast
        (by
          show D = pepsDim a b d D (o.val : ℕ)
          rw [pepsDim, if_neg h])

theorem pepsOpenDecode_site (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (y : OpenAssign (pepsNet a b d D T)) (v : Fin (a * b)) :
    (pepsOpenDecode a b d D T y (pepsP a b v).1 (pepsP a b v).2).val
      = (y (pepsPhysLeg a b d D T v)).val := by
  simp only [pepsOpenDecode, Fin.val_cast]
  have hleg : pepsPhysLeg a b d D T ⟨((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ),
      by have hc := peps_site_coord_idx a b v
         have hv := v.isLt
         omega⟩ = pepsPhysLeg a b d D T v := by
    refine Subtype.ext (Fin.ext ?_)
    show (5 : ℕ) * (((pepsP a b v).1 : ℕ) * b + ((pepsP a b v).2 : ℕ)) = 5 * (v : ℕ)
    have hc := peps_site_coord_idx a b v
    omega
  exact congrArg (fun l : OpenLeg (pepsNet a b d D T) => (y l).val) hleg

theorem pepsOpenCombine_factor (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (y : OpenAssign (pepsNet a b d D T)) :
    pepsOpenCombine a b d D T (pepsOpenDecode a b d D T y, pepsBoundaryRead a b d D T y) = y := by
  funext o
  by_cases h : (o.val : ℕ) < 5 * a * b ∧ (o.val : ℕ) % 5 = 0
  · simp only [pepsOpenCombine, dif_pos h]
    refine Fin.ext ?_
    simp only [Fin.val_cast]
    rw [pepsOpenDecode_site a b d D T y ⟨(o.val : ℕ) / 5,
      Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩]
    have hleg : pepsPhysLeg a b d D T ⟨(o.val : ℕ) / 5,
        Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact h.1)⟩ = o := by
      refine Subtype.ext (Fin.ext ?_)
      show (5 : ℕ) * ((o.val : ℕ) / 5) = (o.val : ℕ)
      have hd := Nat.div_add_mod (o.val : ℕ) 5
      have hm := h.2
      omega
    exact congrArg (fun l : OpenLeg (pepsNet a b d D T) => (y l).val) hleg
  · simp only [pepsOpenCombine, dif_neg h]
    refine Fin.ext ?_
    simp only [Fin.val_cast, pepsBoundaryRead]
    rfl

theorem pepsOpenDecode_combine (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : (Fin a → Fin b → Fin d) × (∀ _o : pepsBoundaryLeg a b, Fin D)) :
    pepsOpenDecode a b d D T (pepsOpenCombine a b d D T p) = p.1 := by
  by_cases hex : Nonempty (Fin (a * b))
  · obtain ⟨v₀⟩ := hex
    have hb : 0 < b := (peps_pos_of_v a b v₀).2
    funext i c
    refine Fin.ext ?_
    simp only [pepsOpenDecode, Fin.val_cast]
    have hphys : ((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
          peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ) < 5 * a * b
        ∧ ((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
            peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ) % 5 = 0 := by
      show ((5 : ℕ) * ((i : ℕ) * b + (c : ℕ))) < 5 * a * b
        ∧ ((5 : ℕ) * ((i : ℕ) * b + (c : ℕ))) % 5 = 0
      exact ⟨pepsLeg_lt a b ((i : ℕ) * b + (c : ℕ)) 0
        (peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt) (by omega), Nat.mul_mod_right 5 _⟩
    simp only [pepsOpenCombine, dif_pos hphys, Fin.val_cast]
    have hv : (⟨((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
            peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ) / 5,
          Nat.div_lt_of_lt_mul (by rw [← Nat.mul_assoc]; exact hphys.1)⟩ : Fin (a * b))
        = ⟨(i : ℕ) * b + (c : ℕ), peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩ := by
      refine Fin.ext ?_
      have hidx : ((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
            peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ)
          = 5 * ((i : ℕ) * b + (c : ℕ)) := rfl
      have hd := Nat.div_add_mod ((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
            peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ) 5
      have hm : ((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
            peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ) % 5 = 0 :=
        Nat.mul_mod_right 5 _
      show ((pepsPhysLeg a b d D T ⟨(i : ℕ) * b + (c : ℕ),
          peps_ib_lt a b (i : ℕ) (c : ℕ) i.isLt c.isLt⟩).val : ℕ) / 5
          = (i : ℕ) * b + (c : ℕ)
      omega
    refine Eq.trans
      (congrArg (fun u : Fin (a * b) => (p.1 (pepsP a b u).1 (pepsP a b u).2).val) hv) ?_
    (try simp only [])
    rw [peps_site_idx_coord a b hb i c]
  · funext i c
    exfalso
    rcases Nat.eq_zero_or_pos a with ha | ha
    · exact absurd i.isLt (by omega)
    · exact absurd c.isLt (by
        have hb0 : b = 0 := by
          by_contra hpos
          exact hex ⟨⟨0, Nat.mul_pos ha (Nat.pos_of_ne_zero hpos)⟩⟩
        omega)

theorem pepsBoundaryRead_combine (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (p : (Fin a → Fin b → Fin d) × (∀ _o : pepsBoundaryLeg a b, Fin D)) :
    pepsBoundaryRead a b d D T (pepsOpenCombine a b d D T p) = p.2 := by
  funext o
  refine Fin.ext ?_
  simp only [Fin.val_cast, pepsBoundaryRead, pepsOpenCombine, dif_neg o.property.2]
  rfl

noncomputable def pepsOpenFactorEquiv (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    OpenAssign (pepsNet a b d D T)
      ≃ (Fin a → Fin b → Fin d) × (∀ _o : pepsBoundaryLeg a b, Fin D) where
  toFun y := (pepsOpenDecode a b d D T y, pepsBoundaryRead a b d D T y)
  invFun := pepsOpenCombine a b d D T
  left_inv := pepsOpenCombine_factor a b d D T
  right_inv p := Prod.ext (pepsOpenDecode_combine a b d D T p)
    (pepsBoundaryRead_combine a b d D T p)

theorem netInner_pepsNet_eq (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    netInner (pepsNet a b d D T) (netContract (pepsNet a b d D T))
        (netContract (pepsNet a b d D T))
      = (Fintype.card (∀ _o : pepsBoundaryLeg a b, Fin D) : ℂ)
          * ∑ x : Fin a → Fin b → Fin d, conj (pepsAmplitude T x) * pepsAmplitude T x := by
  have key : ∀ y : OpenAssign (pepsNet a b d D T),
      conj (netContract (pepsNet a b d D T) y) * netContract (pepsNet a b d D T) y
        = conj (pepsAmplitude T (pepsOpenDecode a b d D T y))
            * pepsAmplitude T (pepsOpenDecode a b d D T y) := fun y => by
    rw [netContract_pepsNet_eval]
  show ∑ y : OpenAssign (pepsNet a b d D T),
      conj (netContract (pepsNet a b d D T) y) * netContract (pepsNet a b d D T) y = _
  rw [Finset.sum_congr rfl (fun y _ => key y),
    Fintype.sum_equiv (pepsOpenFactorEquiv a b d D T)
      (fun y => conj (pepsAmplitude T (pepsOpenDecode a b d D T y))
        * pepsAmplitude T (pepsOpenDecode a b d D T y))
      (fun q => conj (pepsAmplitude T q.1) * pepsAmplitude T q.1)
      (fun _ => rfl),
    Fintype.sum_prod_type]
  have hconst : ∀ x : Fin a → Fin b → Fin d,
      ∑ _β : (∀ _o : pepsBoundaryLeg a b, Fin D), conj (pepsAmplitude T x) * pepsAmplitude T x
        = (Fintype.card (∀ _o : pepsBoundaryLeg a b, Fin D) : ℂ)
            * (conj (pepsAmplitude T x) * pepsAmplitude T x) := by
    intro x
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun x _ => hconst x), ← Finset.mul_sum]

theorem netInner_pepsNet_perm (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (π : Fin (pepsNh a b) ≃ Fin (pepsNh a b)) :
    netInner (permNet (pepsNet a b d D T) π)
        (netContract (permNet (pepsNet a b d D T) π))
        (netContract (permNet (pepsNet a b d D T) π))
      = (Fintype.card (∀ _o : pepsBoundaryLeg a b, Fin D) : ℂ)
          * ∑ x : Fin a → Fin b → Fin d, conj (pepsAmplitude T x) * pepsAmplitude T x := by
  rw [netInner_state_perm, netInner_pepsNet_eq]

def pepsCfgReindex (a b d : ℕ) (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    (Fin a → Fin b → Fin d) ≃ (Fin a → Fin b → Fin d) :=
  ((Equiv.curry (Fin a) (Fin b) (Fin d)).symm.trans
    (Equiv.arrowCongr σ (Equiv.refl (Fin d)))).trans (Equiv.curry (Fin a) (Fin b) (Fin d))

theorem pepsCfgReindex_apply (a b d : ℕ) (σ : Fin a × Fin b ≃ Fin a × Fin b)
    (x : Fin a → Fin b → Fin d) (i : Fin a) (j : Fin b) :
    pepsCfgReindex a b d σ x i j = x (σ.symm (i, j)).1 (σ.symm (i, j)).2 := rfl

def pepsSiteUpdate (a b d : ℕ) (x : Fin a → Fin b → Fin d)
    (z : Fin a × Fin b) (y : Fin d) : Fin a → Fin b → Fin d :=
  Function.update x z.1 (Function.update (x z.1) z.2 y)

theorem sum_site_reindex {a b d : ℕ} (g : (Fin a → Fin b → Fin d) → ℂ)
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d, g (pepsCfgReindex a b d σ x)
      = ∑ x : Fin a → Fin b → Fin d, g x :=
  Fintype.sum_equiv (pepsCfgReindex a b d σ) _ _ (fun _ => rfl)

theorem pepsInner_reindex {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d,
        conj (pepsAmplitude T (pepsCfgReindex a b d σ x))
          * pepsAmplitude T (pepsCfgReindex a b d σ x)
      = ∑ x : Fin a → Fin b → Fin d, conj (pepsAmplitude T x) * pepsAmplitude T x :=
  sum_site_reindex (fun x => conj (pepsAmplitude T x) * pepsAmplitude T x) σ

theorem pepsObsExpectation_reindex {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (z : Fin a × Fin b) (O : Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d,
        conj (pepsAmplitude T (pepsCfgReindex a b d σ x))
          * ∑ y : Fin d, O (pepsCfgReindex a b d σ x z.1 z.2) y
              * pepsAmplitude T (pepsSiteUpdate a b d (pepsCfgReindex a b d σ x) z y)
      = ∑ x : Fin a → Fin b → Fin d,
          conj (pepsAmplitude T x)
            * ∑ y : Fin d, O (x z.1 z.2) y
                * pepsAmplitude T (pepsSiteUpdate a b d x z y) :=
  sum_site_reindex
    (fun x => conj (pepsAmplitude T x)
      * ∑ y : Fin d, O (x z.1 z.2) y * pepsAmplitude T (pepsSiteUpdate a b d x z y)) σ

theorem pepsTwoPointExpectation_reindex {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (z w : Fin a × Fin b) (O P : Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d,
        conj (pepsAmplitude T (pepsCfgReindex a b d σ x))
          * ∑ y : Fin d, ∑ u : Fin d,
              O (pepsCfgReindex a b d σ x z.1 z.2) y
                * P (pepsCfgReindex a b d σ x w.1 w.2) u
                * pepsAmplitude T (pepsSiteUpdate a b d
                    (pepsSiteUpdate a b d (pepsCfgReindex a b d σ x) z y) w u)
      = ∑ x : Fin a → Fin b → Fin d,
          conj (pepsAmplitude T x)
            * ∑ y : Fin d, ∑ u : Fin d,
                O (x z.1 z.2) y * P (x w.1 w.2) u
                  * pepsAmplitude T (pepsSiteUpdate a b d
                      (pepsSiteUpdate a b d x z y) w u) :=
  sum_site_reindex
    (fun x => conj (pepsAmplitude T x)
      * ∑ y : Fin d, ∑ u : Fin d,
          O (x z.1 z.2) y * P (x w.1 w.2) u
            * pepsAmplitude T (pepsSiteUpdate a b d (pepsSiteUpdate a b d x z y) w u)) σ

theorem pepsThreePointExpectation_reindex {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (z w v : Fin a × Fin b) (O P Q : Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d,
        conj (pepsAmplitude T (pepsCfgReindex a b d σ x))
          * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
              O (pepsCfgReindex a b d σ x z.1 z.2) y
                * P (pepsCfgReindex a b d σ x w.1 w.2) u
                * Q (pepsCfgReindex a b d σ x v.1 v.2) t
                * pepsAmplitude T (pepsSiteUpdate a b d
                    (pepsSiteUpdate a b d
                      (pepsSiteUpdate a b d (pepsCfgReindex a b d σ x) z y) w u) v t)
      = ∑ x : Fin a → Fin b → Fin d,
          conj (pepsAmplitude T x)
            * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
                O (x z.1 z.2) y * P (x w.1 w.2) u * Q (x v.1 v.2) t
                  * pepsAmplitude T (pepsSiteUpdate a b d
                      (pepsSiteUpdate a b d
                        (pepsSiteUpdate a b d x z y) w u) v t) :=
  sum_site_reindex
    (fun x => conj (pepsAmplitude T x)
      * ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
          O (x z.1 z.2) y * P (x w.1 w.2) u * Q (x v.1 v.2) t
            * pepsAmplitude T (pepsSiteUpdate a b d
                (pepsSiteUpdate a b d (pepsSiteUpdate a b d x z y) w u) v t)) σ

noncomputable def obsChainSum {C S : Type} {d : ℕ}
    (read : C → S → Fin d) (upd : C → S → Fin d → C) (F : C → ℂ) :
    List (S × Matrix (Fin d) (Fin d) ℂ) → C → C → ℂ
  | [], _, x' => F x'
  | (z, O) :: rest, x, x' =>
      ∑ y : Fin d, O (read x z) y * obsChainSum read upd F rest x (upd x' z y)

theorem obsChainSum_nil {C S : Type} {d : ℕ} (read : C → S → Fin d)
    (upd : C → S → Fin d → C) (F : C → ℂ) (x x' : C) :
    obsChainSum read upd F [] x x' = F x' := rfl

theorem obsChainSum_cons {C S : Type} {d : ℕ} (read : C → S → Fin d)
    (upd : C → S → Fin d → C) (F : C → ℂ) (z : S) (O : Matrix (Fin d) (Fin d) ℂ)
    (rest : List (S × Matrix (Fin d) (Fin d) ℂ)) (x x' : C) :
    obsChainSum read upd F ((z, O) :: rest) x x'
      = ∑ y : Fin d, O (read x z) y * obsChainSum read upd F rest x (upd x' z y) := rfl

theorem obsChainSum_pair {C S : Type} {d : ℕ} (read : C → S → Fin d)
    (upd : C → S → Fin d → C) (F : C → ℂ) (z w : S)
    (O P : Matrix (Fin d) (Fin d) ℂ) (x x' : C) :
    obsChainSum read upd F [(z, O), (w, P)] x x'
      = ∑ y : Fin d, ∑ u : Fin d,
          O (read x z) y * P (read x w) u * F (upd (upd x' z y) w u) := by
  simp only [obsChainSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun u _ => by ring

theorem obsChainSum_triple {C S : Type} {d : ℕ} (read : C → S → Fin d)
    (upd : C → S → Fin d → C) (F : C → ℂ) (z w v : S)
    (O P Q : Matrix (Fin d) (Fin d) ℂ) (x x' : C) :
    obsChainSum read upd F [(z, O), (w, P), (v, Q)] x x'
      = ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d,
          O (read x z) y * P (read x w) u * Q (read x v) t
            * F (upd (upd (upd x' z y) w u) v t) := by
  simp only [obsChainSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => by ring

theorem obsChainSum_quad {C S : Type} {d : ℕ} (read : C → S → Fin d)
    (upd : C → S → Fin d → C) (F : C → ℂ) (z w v r : S)
    (O P Q R : Matrix (Fin d) (Fin d) ℂ) (x x' : C) :
    obsChainSum read upd F [(z, O), (w, P), (v, Q), (r, R)] x x'
      = ∑ y : Fin d, ∑ u : Fin d, ∑ t : Fin d, ∑ s : Fin d,
          O (read x z) y * P (read x w) u * Q (read x v) t * R (read x r) s
            * F (upd (upd (upd (upd x' z y) w u) v t) r s) := by
  simp only [obsChainSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring

def cfgSiteRead {n d : ℕ} (c : Fin n → Fin d) (z : Fin n) : Fin d := c z

def cfgSiteUpdate {n d : ℕ} (c : Fin n → Fin d) (z : Fin n) (y : Fin d) :
    Fin n → Fin d := Function.update c z y

def pepsSiteRead {a b d : ℕ} (c : Fin a → Fin b → Fin d) (z : Fin a × Fin b) : Fin d :=
  c z.1 z.2

theorem mpsChainedExpectation_reindex {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (mpsAmplitude A (fun i => x (e.symm i)))
          * obsChainSum cfgSiteRead cfgSiteUpdate (mpsAmplitude A) prog
              (fun i => x (e.symm i)) (fun i => x (e.symm i))
      = ∑ x : Fin n → Fin d,
          conj (mpsAmplitude A x)
            * obsChainSum cfgSiteRead cfgSiteUpdate (mpsAmplitude A) prog x x :=
  sum_config_reindex
    (fun x => conj (mpsAmplitude A x)
      * obsChainSum cfgSiteRead cfgSiteUpdate (mpsAmplitude A) prog x x) e

theorem perChainedExpectation_reindex {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A (fun i => x (e.symm i)))
          * obsChainSum cfgSiteRead cfgSiteUpdate (periodicMpsAmplitude A) prog
              (fun i => x (e.symm i)) (fun i => x (e.symm i))
      = ∑ x : Fin n → Fin d,
          conj (periodicMpsAmplitude A x)
            * obsChainSum cfgSiteRead cfgSiteUpdate (periodicMpsAmplitude A) prog x x :=
  sum_config_reindex
    (fun x => conj (periodicMpsAmplitude A x)
      * obsChainSum cfgSiteRead cfgSiteUpdate (periodicMpsAmplitude A) prog x x) e

theorem pepsChainedExpectation_reindex {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (prog : List ((Fin a × Fin b) × Matrix (Fin d) (Fin d) ℂ))
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d,
        conj (pepsAmplitude T (pepsCfgReindex a b d σ x))
          * obsChainSum pepsSiteRead (pepsSiteUpdate a b d) (pepsAmplitude T) prog
              (pepsCfgReindex a b d σ x) (pepsCfgReindex a b d σ x)
      = ∑ x : Fin a → Fin b → Fin d,
          conj (pepsAmplitude T x)
            * obsChainSum pepsSiteRead (pepsSiteUpdate a b d) (pepsAmplitude T) prog x x :=
  sum_site_reindex
    (fun x => conj (pepsAmplitude T x)
      * obsChainSum pepsSiteRead (pepsSiteUpdate a b d) (pepsAmplitude T) prog x x) σ

theorem mpsTwoPointExpectation_reindex_of_chained {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z w : Fin n)
    (O P : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (mpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, ∑ u : Fin d, O ((fun i => x (e.symm i)) z) y
              * P ((fun i => x (e.symm i)) w) u
              * mpsAmplitude A (Function.update (Function.update (fun i => x (e.symm i)) z y) w u)
      = ∑ x : Fin n → Fin d,
          conj (mpsAmplitude A x)
            * ∑ y : Fin d, ∑ u : Fin d, O (x z) y * P (x w) u
              * mpsAmplitude A (Function.update (Function.update x z y) w u) := by
  have h := mpsChainedExpectation_reindex A [(z, O), (w, P)] e
  simp only [obsChainSum_pair] at h
  exact h

theorem perTwoPointExpectation_reindex_of_chained {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z w : Fin n)
    (O P : Matrix (Fin d) (Fin d) ℂ) (e : Fin n ≃ Fin n) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A (fun i => x (e.symm i)))
          * ∑ y : Fin d, ∑ u : Fin d, O ((fun i => x (e.symm i)) z) y
              * P ((fun i => x (e.symm i)) w) u
              * periodicMpsAmplitude A
                  (Function.update (Function.update (fun i => x (e.symm i)) z y) w u)
      = ∑ x : Fin n → Fin d,
          conj (periodicMpsAmplitude A x)
            * ∑ y : Fin d, ∑ u : Fin d, O (x z) y * P (x w) u
              * periodicMpsAmplitude A (Function.update (Function.update x z y) w u) := by
  have h := perChainedExpectation_reindex A [(z, O), (w, P)] e
  simp only [obsChainSum_pair] at h
  exact h

theorem pepsTwoPointExpectation_reindex_of_chained {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ)
    (z w : Fin a × Fin b) (O P : Matrix (Fin d) (Fin d) ℂ)
    (σ : Fin a × Fin b ≃ Fin a × Fin b) :
    ∑ x : Fin a → Fin b → Fin d,
        conj (pepsAmplitude T (pepsCfgReindex a b d σ x))
          * ∑ y : Fin d, ∑ u : Fin d,
              O (pepsCfgReindex a b d σ x z.1 z.2) y
                * P (pepsCfgReindex a b d σ x w.1 w.2) u
                * pepsAmplitude T (pepsSiteUpdate a b d
                    (pepsSiteUpdate a b d (pepsCfgReindex a b d σ x) z y) w u)
      = ∑ x : Fin a → Fin b → Fin d,
          conj (pepsAmplitude T x)
            * ∑ y : Fin d, ∑ u : Fin d,
                O (x z.1 z.2) y * P (x w.1 w.2) u
                  * pepsAmplitude T (pepsSiteUpdate a b d
                      (pepsSiteUpdate a b d x z y) w u) := by
  have h := pepsChainedExpectation_reindex T [((z : Fin a × Fin b), O), (w, P)] σ
  simp only [obsChainSum_pair] at h
  exact h

noncomputable def rowScaleBy {d : ℕ} (O W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun u y => (∑ v : Fin d, O u v) * W u y

theorem rowScaleBy_apply {d : ℕ} (O W : Matrix (Fin d) (Fin d) ℂ) (u y : Fin d) :
    rowScaleBy O W u y = (∑ v : Fin d, O u v) * W u y := rfl

theorem rowScaleBy_of_rowSums_eq_one {d : ℕ} (O W : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ u : Fin d, ∑ v : Fin d, O u v = 1) : rowScaleBy O W = W := by
  funext u y
  show (∑ v : Fin d, O u v) * W u y = W u y
  rw [h u, one_mul]

noncomputable def siteObsW {n d : ℕ} :
    List (Fin n × Matrix (Fin d) (Fin d) ℂ) → Fin n → Option (Matrix (Fin d) (Fin d) ℂ)
  | [], _ => none
  | (z, O) :: rest, w =>
      if z = w then
        match siteObsW rest w with
        | none => some O
        | some W₀ => some (rowScaleBy O W₀)
      else siteObsW rest w

theorem siteObsW_nil {n d : ℕ} (w : Fin n) :
    siteObsW ([] : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) w = none := rfl

theorem siteObsW_cons_self {n d : ℕ} (z : Fin n) (O : Matrix (Fin d) (Fin d) ℂ)
    (rest : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) :
    siteObsW ((z, O) :: rest) z =
      match siteObsW rest z with
      | none => some O
      | some W₀ => some (rowScaleBy O W₀) := by
  show (if z = z then
      match siteObsW rest z with
      | none => some O
      | some W₀ => some (rowScaleBy O W₀) else siteObsW rest z) = _
  rw [if_pos rfl]

theorem siteObsW_cons_of_ne {n d : ℕ} (z : Fin n) (O : Matrix (Fin d) (Fin d) ℂ)
    (rest : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) {w : Fin n} (hw : w ≠ z) :
    siteObsW ((z, O) :: rest) w = siteObsW rest w := by
  show (if z = w then
      match siteObsW rest w with
      | none => some O
      | some W₀ => some (rowScaleBy O W₀) else siteObsW rest w) = _
  rw [if_neg (Ne.symm hw)]

theorem siteObsW_single {n d : ℕ} (z : Fin n) (O : Matrix (Fin d) (Fin d) ℂ) :
    siteObsW [(z, O)] z = some O := by
  rw [siteObsW_cons_self, siteObsW_nil]

theorem siteObsW_single_of_ne {n d : ℕ} (z w : Fin n) (O : Matrix (Fin d) (Fin d) ℂ)
    (hw : w ≠ z) : siteObsW [(z, O)] w = none := by
  rw [siteObsW_cons_of_ne z O [] hw, siteObsW_nil]

noncomputable def obsMix {d D : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) : Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun u => Matrix.of fun l r => ∑ y : Fin d, W u y * M y l r

theorem obsMix_apply {d D : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) (u : Fin d) (l r : Fin D) :
    obsMix W M u l r = ∑ y : Fin d, W u y * M y l r := rfl

theorem obsMix_one {d D : ℕ} (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    obsMix 1 M = M := by
  funext u l r
  have key : ∀ y : Fin d, (1 : Matrix (Fin d) (Fin d) ℂ) u y * M y l r
      = if u = y then M u l r else 0 := by
    intro y
    by_cases hy : u = y
    · rw [if_pos hy]
      have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) u y = 1 := by
        rw [hy]
        exact Matrix.one_apply_eq y
      rw [h1, one_mul, hy]
    · rw [if_neg hy]
      have h0 : (1 : Matrix (Fin d) (Fin d) ℂ) u y = 0 := Matrix.one_apply_ne hy
      rw [h0, zero_mul]
  show (∑ y : Fin d, (1 : Matrix (Fin d) (Fin d) ℂ) u y * M y l r) = M u l r
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_ite_eq]
  simp

theorem perObsTensor_self_eq_obsMix {n d D : ℕ}
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) : perObsTensor A z O z = obsMix O (A z) :=
  perObsTensor_self A z O

theorem perED_obsMix_eq_perEO {d D : ℕ} (O : Matrix (Fin d) (Fin d) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) : perED (obsMix O M) M = perEO O M := rfl

theorem perAmp_weightUpdate_eq {n d D : ℕ} [NeZero n] [NeZero D]
    (F : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (W : Matrix (Fin d) (Fin d) ℂ) (x x' : Fin n → Fin d) :
    ∑ y : Fin d, W (x z) y * periodicMpsAmplitude F (Function.update x' z y)
      = periodicMpsAmplitude
          (Function.update F z
            (Matrix.of fun _u l r => ∑ y : Fin d, W (x z) y * F z y l r)) x' := by
  simp only [periodicMpsAmplitude]
  have hket : ∀ (y : Fin d) (β : Fin n → Fin D),
      ∏ i : Fin n, F i (Function.update x' z y i) (β i)
          (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        = F z y (β z) (β ⟨((z : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
            * ∏ i ∈ Finset.univ.erase z, F i (x' i) (β i)
                (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) := by
    intro y β
    rw [prod_univ_eq_mul_erase, Function.update_self]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun i hi => ?_)
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have hobs : ∀ β : Fin n → Fin D,
      ∏ i : Fin n, (Function.update F z
          (Matrix.of fun _u l r => ∑ y : Fin d, W (x z) y * F z y l r)) i (x' i) (β i)
          (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        = (∑ y : Fin d, W (x z) y
              * F z y (β z) (β ⟨((z : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩))
            * ∏ i ∈ Finset.univ.erase z, F i (x' i) (β i)
                (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩) := by
    intro β
    rw [prod_univ_eq_mul_erase]
    refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun i hi => ?_)
    · rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  simp only [hket]
  simp only [Finset.mul_sum]
  rw [sum_swap_fintype (F := fun (y : Fin d) (β : Fin n → Fin D) =>
    W (x z) y * (F z y (β z) (β ⟨((z : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
      * ∏ i ∈ Finset.univ.erase z, F i (x' i) (β i)
          (β ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩)))]
  simp only [hobs]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]

noncomputable def perProgBra {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) (x : Fin n → Fin d) :
    Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun z => match siteObsW prog z with
    | none => A z
    | some W => Matrix.of fun _u l r => ∑ y : Fin d, W (x z) y * A z y l r

theorem perProgBra_cons {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (z : Fin n) (O : Matrix (Fin d) (Fin d) ℂ)
    (rest : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) (x : Fin n → Fin d) :
    Function.update (perProgBra A rest x) z
        (Matrix.of fun _u l r =>
          ∑ y : Fin d, O (x z) y * perProgBra A rest x z y l r)
      = perProgBra A ((z, O) :: rest) x := by
  funext i
  by_cases hi : i = z
  · rw [hi]
    simp only [perProgBra, Function.update_self, siteObsW_cons_self]
    cases hW : siteObsW rest z with
    | none => rfl
    | some W₀ =>
        funext u l r
        show ∑ y : Fin d, O (x z) y * (∑ v : Fin d, W₀ (x z) v * A z v l r)
            = ∑ y : Fin d, rowScaleBy O W₀ (x z) y * A z y l r
        simp only [Finset.mul_sum]
        rw [sum_swap_fintype (F := fun (y v : Fin d) =>
          O (x z) y * (W₀ (x z) v * A z v l r))]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [rowScaleBy_apply, mul_assoc]
        exact (Finset.sum_mul Finset.univ (fun c => O (x z) c)
          (W₀ (x z) v * A z v l r)).symm
  · rw [Function.update_of_ne hi]
    simp only [perProgBra, siteObsW_cons_of_ne z O rest hi]

theorem perChained_amp_eq {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) (x x' : Fin n → Fin d) :
    obsChainSum cfgSiteRead cfgSiteUpdate (periodicMpsAmplitude A) prog x x'
      = periodicMpsAmplitude (perProgBra A prog x) x' := by
  induction prog generalizing x' with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨z, O⟩ := e
      rw [obsChainSum_cons]
      simp only [cfgSiteRead, cfgSiteUpdate]
      rw [Finset.sum_congr rfl (fun y _ => by rw [ih (Function.update x' z y)]),
        perAmp_weightUpdate_eq (perProgBra A rest x) z O x x', perProgBra_cons]

noncomputable def perProgFamily {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) :
    Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun z => match siteObsW prog z with
    | none => A z
    | some W => obsMix W (A z)

theorem perProgBra_amp_eq {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) (x : Fin n → Fin d) :
    periodicMpsAmplitude (perProgBra A prog x) x
      = periodicMpsAmplitude (perProgFamily A prog) x := by
  simp only [periodicMpsAmplitude, perProgBra, perProgFamily]
  refine Finset.sum_congr rfl fun β _ => Finset.prod_congr rfl fun i _ => ?_
  cases hW : siteObsW prog i with
  | none => rfl
  | some W => rfl

theorem perChainedExpectation_eq_trace {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (prog : List (Fin n × Matrix (Fin d) (Fin d) ℂ)) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A x)
          * obsChainSum cfgSiteRead cfgSiteUpdate (periodicMpsAmplitude A) prog x x
      = (chainProd (fun k : ℕ =>
          perED (perProgFamily A prog ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
            (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)) n).trace := by
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [perChained_amp_eq A prog x x, perProgBra_amp_eq A prog x])]
  exact perInner_eq_trace (perProgFamily A prog) A

theorem perProgFamily_single {n d D : ℕ}
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) :
    perProgFamily A [(z, O)] = perObsTensor A z O := by
  funext i
  by_cases hi : i = z
  · rw [hi]
    show (match siteObsW [(z, O)] z with
        | none => A z
        | some W => obsMix W (A z)) = perObsTensor A z O z
    rw [siteObsW_single]
    exact (perObsTensor_self_eq_obsMix A z O).symm
  · show (match siteObsW [(z, O)] i with
        | none => A i
        | some W => obsMix W (A i)) = perObsTensor A z O i
    rw [siteObsW_single_of_ne z i O hi]
    exact (perObsTensor_of_ne A z O hi).symm

theorem perObsExpectation_eq_trace_of_chained {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (z : Fin n)
    (O : Matrix (Fin d) (Fin d) ℂ) :
    ∑ x : Fin n → Fin d,
        conj (periodicMpsAmplitude A x)
          * ∑ y : Fin d, O (x z) y * periodicMpsAmplitude A (Function.update x z y)
      = (chainProd (perObsChain A z O) n).trace := by
  have hstep : ∀ x : Fin n → Fin d,
      obsChainSum cfgSiteRead cfgSiteUpdate (periodicMpsAmplitude A) [(z, O)] x x
        = ∑ y : Fin d, O (x z) y
            * periodicMpsAmplitude A (Function.update x z y) := fun _ => rfl
  have h := perChainedExpectation_eq_trace A [(z, O)]
  rw [Finset.sum_congr rfl (fun x _ => by rw [hstep x])] at h
  refine Eq.trans h ?_
  refine congrArg Matrix.trace (chainProd_congr n fun k _ => ?_)
  rw [perProgFamily_single]
  by_cases hz : (k % n) = (z : ℕ)
  · have hke : (⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩ : Fin n) = z := Fin.ext hz
    show perED (perObsTensor A z O ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
      = (if (k % n) = (z : ℕ) then perEO O (A z)
          else perE (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))
    rw [if_pos hz, hke, perObsTensor_self_eq_obsMix, perED_obsMix_eq_perEO]
  · show perED (perObsTensor A z O ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
        (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩)
      = (if (k % n) = (z : ℕ) then perEO O (A z)
          else perE (A ⟨k % n, Nat.mod_lt k (NeZero.pos n)⟩))
    rw [if_neg hz, perObsTensor_of_ne A z O
      (fun h => hz (congrArg (fun i : Fin n => (i : ℕ)) h))]
    exact perED_self _

theorem netBondDimension_eq_sup_paired (N : TensorNet) :
    netBondDimension N =
      Finset.univ.sup fun h : {h : Fin N.nh // N.partner h ≠ none} => N.dims h.val := by
  classical
  refine le_antisymm ?_ ?_
  · rw [netBondDimension]
    refine Finset.sup_le fun i _ => ?_
    obtain ⟨k, hk, -⟩ := i.property
    have hne : N.partner i.val ≠ none := by
      rw [hk]
      simp
    exact Finset.le_sup
      (f := fun h : {h : Fin N.nh // N.partner h ≠ none} => N.dims h.val)
      (Finset.mem_univ (⟨i.val, hne⟩ : {h : Fin N.nh // N.partner h ≠ none}))
  · refine Finset.sup_le fun h _ => ?_
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists.mp h.property
    rw [netBondDimension]
    rcases Nat.lt_trichotomy (h.val : ℕ) (k : ℕ) with hlt | heq | hgt
    · exact Finset.le_sup (f := fun i : InternalEdge N => N.dims i.val)
        (Finset.mem_univ (⟨h.val, ⟨k, hk.symm, hlt⟩⟩ : InternalEdge N))
    · exact absurd (Fin.ext heq) (N.no_self_loop h.val k hk.symm)
    · rw [N.dims_match h.val k hk.symm]
      exact Finset.le_sup (f := fun i : InternalEdge N => N.dims i.val)
        (Finset.mem_univ (⟨k, ⟨h.val, N.involution h.val k hk.symm, hgt⟩⟩ : InternalEdge N))

theorem netBondDimension_permNet (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    netBondDimension (permNet N π) = netBondDimension N := by
  rw [netBondDimension_eq_sup_paired, netBondDimension_eq_sup_paired]
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.sup_le fun h _ => ?_)
  · have hd : (permNet N π).dims j.val = N.dims (π.symm j.val) := by
      have h' := permNet_dims N π (π.symm j.val)
      rwa [π.apply_symm_apply] at h'
    rw [hd]
    have hne : N.partner (π.symm j.val) ≠ none := by
      intro hcon
      apply j.property
      have h2 := permNet_partner N π (π.symm j.val)
      rw [π.apply_symm_apply, hcon, Option.map_none] at h2
      exact h2
    exact Finset.le_sup
      (f := fun h : {h : Fin N.nh // N.partner h ≠ none} => N.dims h.val)
      (Finset.mem_univ (⟨π.symm j.val, hne⟩ :
        {h : Fin N.nh // N.partner h ≠ none}))
  · rw [(permNet_dims N π h.val).symm]
    have hne : (permNet N π).partner (π h.val) ≠ none := by
      rw [permNet_partner N π h.val]
      intro hcon
      exact h.property (Option.map_eq_none_iff.mp hcon)
    exact Finset.le_sup
      (f := fun j : {j : Fin (permNet N π).nh // (permNet N π).partner j ≠ none} =>
        (permNet N π).dims j.val)
      (Finset.mem_univ (⟨π h.val, hne⟩ :
        {j : Fin (permNet N π).nh // (permNet N π).partner j ≠ none}))

theorem netBondDimension_mpsNet_eq (n d D : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    netBondDimension (mpsNet n d D A) = D := by
  refine le_antisymm (netBondDimension_mpsNet_le n d D A) ?_
  rw [netBondDimension]
  have hz : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
  have hd : (mpsNet n d D A).dims (bondEdge n d D A ⟨0, by omega⟩).val = D := by
    show mpsDim n d D (2 * ((0 : Fin (n + 1)) : ℕ)) = D
    rw [mpsDim_bond n d D (by omega)]
  calc D = (mpsNet n d D A).dims (bondEdge n d D A ⟨0, by omega⟩).val := hd.symm
    _ ≤ Finset.univ.sup
          fun i : InternalEdge (mpsNet n d D A) => (mpsNet n d D A).dims i.val :=
        Finset.le_sup
          (f := fun i : InternalEdge (mpsNet n d D A) => (mpsNet n d D A).dims i.val)
          (Finset.mem_univ (bondEdge n d D A ⟨0, by omega⟩))

theorem netBondDimension_perNet_eq {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    netBondDimension (perNet n d D A) = D := by
  refine le_antisymm (netBondDimension_perNet_le A) ?_
  rw [netBondDimension]
  have hz : ((0 : Fin n) : ℕ) = 0 := rfl
  have hd : (perNet n d D A).dims (perBondEdge n d D A ⟨0, by omega⟩).val = D := by
    show perDim n d D (2 * ((0 : Fin n) : ℕ)) = D
    rw [perDim_bond n d D (by omega)]
  calc D = (perNet n d D A).dims (perBondEdge n d D A ⟨0, by omega⟩).val := hd.symm
    _ ≤ Finset.univ.sup
          fun i : InternalEdge (perNet n d D A) => (perNet n d D A).dims i.val :=
        Finset.le_sup
          (f := fun i : InternalEdge (perNet n d D A) => (perNet n d D A).dims i.val)
          (Finset.mem_univ (perBondEdge n d D A ⟨0, by omega⟩))

theorem netBondDimension_pepsNet_eq (a b d D : ℕ) [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) :
    netBondDimension (pepsNet a b d D T) = if a = 0 ∨ b = 0 then 0 else D := by
  by_cases hz : a = 0 ∨ b = 0
  · rw [if_pos hz]
    have hempty : IsEmpty (InternalEdge (pepsNet a b d D T)) := by
      refine ⟨fun i => ?_⟩
      obtain ⟨j, ⟨k, hk, -⟩⟩ := i
      have hnone : (pepsNet a b d D T).partner j = none := by
        show pepsPartner a b j = none
        simp only [pepsPartner]
        rw [dif_pos hz]
      rw [hnone] at hk
      simp at hk
    have huniv : (Finset.univ : Finset (InternalEdge (pepsNet a b d D T))) = ∅ := by
      simp
    rw [netBondDimension, huniv, Finset.sup_empty]
    rfl
  · rw [if_neg hz]
    have ha : 0 < a := Nat.pos_of_ne_zero (fun h => hz (Or.inl h))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun h => hz (Or.inr h))
    have hnh := pepsNh_of_pos ha hb
    have hb1 : (5 * a * b : ℕ) < (pepsNet a b d D T).nh := by
      show (5 * a * b : ℕ) < pepsNh a b
      omega
    have hb2 : (5 * a * b + 1 : ℕ) < (pepsNet a b d D T).nh := by
      show (5 * a * b + 1 : ℕ) < pepsNh a b
      omega
    have hb3 : (5 * a * b : ℕ) < (5 * a * b + 1 : ℕ) := by omega
    have hpart : (pepsNet a b d D T).partner
        (⟨5 * a * b, hb1⟩ : Fin (pepsNet a b d D T).nh) = some ⟨5 * a * b + 1, hb2⟩ := by
      show pepsPartner a b ⟨5 * a * b, hb1⟩ = _
      have h := pepsPartner_dummy_even a b 0 ha hb (by omega)
      simpa using! h
    have hdims : (pepsNet a b d D T).dims
        (⟨5 * a * b, hb1⟩ : Fin (pepsNet a b d D T).nh) = D := by
      show pepsDim a b d D (5 * a * b) = D
      rw [pepsDim, if_neg (fun h => Nat.lt_irrefl _ h.1)]
    refine le_antisymm (Finset.sup_le fun i _ => (pepsNet_dims_internal a b d D T i).le) ?_
    calc D = (pepsNet a b d D T).dims
          (⟨5 * a * b, hb1⟩ : Fin (pepsNet a b d D T).nh) := hdims.symm
      _ ≤ Finset.univ.sup
            fun i : InternalEdge (pepsNet a b d D T) => (pepsNet a b d D T).dims i.val :=
          Finset.le_sup
            (f := fun i : InternalEdge (pepsNet a b d D T) => (pepsNet a b d D T).dims i.val)
            (Finset.mem_univ
              ⟨⟨5 * a * b, hb1⟩, ⟨⟨5 * a * b + 1, hb2⟩, hpart, Fin.mk_lt_mk.mpr hb3⟩⟩)

theorem netContract_mpsNet_zero (d D : ℕ) [NeZero D]
    (A : Fin 0 → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (y : OpenAssign (mpsNet 0 d D A)) :
    netContract (mpsNet 0 d D A) y = 1 := by
  rw [netContract_mpsNet_eval]
  have h : mpsAmplitude A (openDecode 0 d D A y) = 1 := by
    show (∑ α : Fin (0 - 1) → Fin D, ∏ i : Fin 0,
        A i (openDecode 0 d D A y i) (mpsLeftIdx α i) (mpsRightIdx α i)) = 1
    simp
  rw [h]

theorem netInner_mpsNet_zero_dim {n D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin 0 → Matrix (Fin D) (Fin D) ℂ) :
    netInner (mpsNet n 0 D A) (netContract (mpsNet n 0 D A)) (netContract (mpsNet n 0 D A))
      = 0 := by
  rw [netInner_mpsNet_eq]
  have hempty : IsEmpty (Fin n → Fin 0) :=
    ⟨fun f => absurd (Fin.isLt (f ⟨0, NeZero.pos n⟩)) (Nat.not_lt_zero _)⟩
  simp

theorem finPowEnc_one_symm_apply {d : ℕ} (i : Fin (d ^ 1)) :
    (finPowEnc d 1).symm i = fun _ => i.cast (Nat.pow_one d) := by
  rw [Equiv.symm_apply_eq]
  refine Fin.ext ?_
  show (i : ℕ) = (∑ k : Fin 1, (((fun _ => i.cast (Nat.pow_one d)) k : Fin d) : ℕ)
      * d ^ (k : ℕ))
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.pow_zero, Nat.mul_one]
  rfl

theorem splitJoin_two_one_eq {d : ℕ} (a b : Fin d) :
    splitJoin 2 1 d (fun _ => a) (fun _ => b)
      = fun k : Fin 2 => if k = 0 then a else b := by
  funext k
  have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by have := k.isLt; omega
  rcases hk with h | h
  · have hk0 : k = 0 := Fin.ext (by simpa using! h)
    subst hk0
    simp [splitJoin]
  · have hk1 : k = 1 := Fin.ext (by simpa using! h)
    subst hk1
    simp [splitJoin]

theorem cutMatrix_two_one_apply (d : ℕ) (ψ : (Fin 2 → Fin d) → ℂ)
    (i : Fin (d ^ 1)) (j : Fin (d ^ (2 - 1))) :
    cutMatrix 2 d ψ 1 i j
      = ψ (fun k : Fin 2 =>
          if k = 0 then i.cast (Nat.pow_one d)
          else j.cast (by rw [show (2 : ℕ) - 1 = 1 from rfl, Nat.pow_one])) := by
  simp only [cutMatrix, Matrix.of_apply]
  rw [finPowEnc_one_symm_apply, finPowEnc_one_symm_apply, splitJoin_two_one_eq]

theorem netBondDimension_mpsNet_ge_sup_cutRank {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : (Fin n → Fin d) → ℂ)
    (hrep : IsMpsRepresentation A ψ) :
    max 1 ((Finset.range n).sup fun c => cutRank n d ψ c)
      ≤ netBondDimension (mpsNet n d D A) := by
  have h1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
  have h2 : (Finset.range n).sup (fun c => cutRank n d ψ c) ≤ D :=
    Finset.sup_le fun c hc => cutRank_le_of_isMps A ψ hrep c (Finset.mem_range.mp hc)
  rw [netBondDimension_mpsNet_eq]
  omega

theorem exists_mpsNet_minimalBond {n d : ℕ} (hn : 1 ≤ n)
    (ψ : (Fin n → Fin d) → ℂ) (hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    ∃ (D : ℕ) (_hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
      IsMpsRepresentation A ψ ∧ LeftCanonical A ∧
        D = max 1 ((Finset.range n).sup fun c => cutRank n d ψ c) ∧
        netBondDimension (mpsNet n d D A) = D := by
  obtain ⟨D, hD, A, hrep, hcan, hDsup⟩ := (g2 n d ψ hnorm).2.1 hn
  exact ⟨D, hD, A, hrep, hcan, hDsup, netBondDimension_mpsNet_eq n d D A⟩

theorem netBondDimension_min_eq_sup_cutRank {n d : ℕ} (hn : 1 ≤ n)
    (ψ : (Fin n → Fin d) → ℂ) (hnorm : ∑ x, Complex.normSq (ψ x) = 1) :
    (∃ (D : ℕ) (_hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
        IsMpsRepresentation A ψ ∧
          netBondDimension (mpsNet n d D A)
            = max 1 ((Finset.range n).sup fun c => cutRank n d ψ c))
      ∧ (∀ (D : ℕ) (_hD : NeZero D) (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ),
          IsMpsRepresentation A ψ →
            max 1 ((Finset.range n).sup fun c => cutRank n d ψ c)
              ≤ netBondDimension (mpsNet n d D A)) := by
  obtain ⟨D, hD, A, hrep, _hcan, hDsup, hnet⟩ := exists_mpsNet_minimalBond hn ψ hnorm
  refine ⟨⟨D, hD, A, hrep, ?_⟩, ?_⟩
  · rw [hnet, hDsup]
  · intro D _hD A hrep
    exact netBondDimension_mpsNet_ge_sup_cutRank A ψ hrep

theorem finPowEnc_symm_val {d k : ℕ} (i : Fin (d ^ k)) (m : Fin k) :
    (((finPowEnc d k).symm i m : Fin d) : ℕ) = (i : ℕ) / d ^ (m : ℕ) % d :=
  rfl

theorem finPowEnc_symm_apply {d k : ℕ} [NeZero d] (i : Fin (d ^ k)) (m : Fin k) :
    (finPowEnc d k).symm i m
      = ⟨(i : ℕ) / d ^ (m : ℕ) % d, Nat.mod_lt _ (NeZero.pos d)⟩ :=
  rfl

theorem finPowEnc_symm_zero {d k : ℕ} [NeZero d] :
    (finPowEnc d k).symm 0 = fun _ => 0 := by
  funext m
  have h : (((finPowEnc d k).symm 0 m : Fin d) : ℕ) = ((0 : Fin d) : ℕ) := by
    rw [finPowEnc_symm_val]
    simp
  exact Fin.ext h

theorem cutMatrix_apply (n d : ℕ) (ψ : (Fin n → Fin d) → ℂ) (c : ℕ)
    (i : Fin (d ^ c)) (j : Fin (d ^ (n - c))) :
    cutMatrix n d ψ c i j
      = ψ (fun k : Fin n =>
          if h : (k : ℕ) < c then (finPowEnc d c).symm i ⟨(k : ℕ), h⟩
          else (finPowEnc d (n - c)).symm j ⟨(k : ℕ) - c, by omega⟩) :=
  rfl

theorem cutMatrix_apply_digits {d : ℕ} [NeZero d] {n : ℕ}
    (ψ : (Fin n → Fin d) → ℂ) (c : ℕ) (i : Fin (d ^ c)) (j : Fin (d ^ (n - c))) :
    cutMatrix n d ψ c i j
      = ψ (fun k : Fin n =>
          if _h : (k : ℕ) < c
          then ⟨(i : ℕ) / d ^ (k : ℕ) % d, Nat.mod_lt _ (NeZero.pos d)⟩
          else ⟨(j : ℕ) / d ^ ((k : ℕ) - c) % d, Nat.mod_lt _ (NeZero.pos d)⟩) := by
  rw [cutMatrix_apply]
  refine congrArg ψ (funext fun k => ?_)
  by_cases h : (k : ℕ) < c
  · simp only [dif_pos h]
    exact finPowEnc_symm_apply i ⟨(k : ℕ), h⟩
  · simp only [dif_neg h]
    exact finPowEnc_symm_apply j ⟨(k : ℕ) - c, by omega⟩

theorem cutMatrix_prod_eq_vecMulVec {n d : ℕ} (g : Fin n → Fin d → ℂ) (c : ℕ)
    (hc : c ≤ n) :
    cutMatrix n d (fun x => ∏ k, g k (x k)) c
      = Matrix.vecMulVec
          (fun i : Fin (d ^ c) => ∏ k : Fin c,
            g ⟨(k : ℕ), by omega⟩ ((finPowEnc d c).symm i k))
          (fun j : Fin (d ^ (n - c)) => ∏ k : Fin (n - c),
            g ⟨c + (k : ℕ), by omega⟩ ((finPowEnc d (n - c)).symm j k)) := by
  ext i j
  rw [cutMatrix_apply, Matrix.vecMulVec_apply,
    prod_split_fin (fun k : Fin n =>
      g k (if h : (k : ℕ) < c then (finPowEnc d c).symm i ⟨(k : ℕ), h⟩
        else (finPowEnc d (n - c)).symm j ⟨(k : ℕ) - c, by omega⟩)) c hc]
  have hL : ∀ k : Fin c,
      (fun k : Fin n =>
          g k (if h : (k : ℕ) < c then (finPowEnc d c).symm i ⟨(k : ℕ), h⟩
            else (finPowEnc d (n - c)).symm j ⟨(k : ℕ) - c, by omega⟩))
        ⟨(k : ℕ), by omega⟩
      = g ⟨(k : ℕ), by omega⟩ ((finPowEnc d c).symm i k) := by
    intro k
    simp only [dif_pos k.isLt]
  have hR : ∀ m : Fin (n - c),
      (fun k : Fin n =>
          g k (if h : (k : ℕ) < c then (finPowEnc d c).symm i ⟨(k : ℕ), h⟩
            else (finPowEnc d (n - c)).symm j ⟨(k : ℕ) - c, by omega⟩))
        ⟨c + (m : ℕ), by omega⟩
      = g ⟨c + (m : ℕ), by omega⟩ ((finPowEnc d (n - c)).symm j m) := by
    intro m
    have hnl : ¬((c + (m : ℕ) : ℕ) < c) := by omega
    simp only [dif_neg hnl]
    have hidx : (⟨(c + (m : ℕ)) - c, by omega⟩ : Fin (n - c)) = m :=
      Fin.ext (by show c + (m : ℕ) - c = (m : ℕ); omega)
    rw [hidx]
  rw [Finset.prod_congr rfl (fun k _ => hL k), Finset.prod_congr rfl (fun m _ => hR m)]

theorem cutRank_prod_le_one {n d : ℕ} (g : Fin n → Fin d → ℂ) (c : ℕ) (hc : c ≤ n) :
    cutRank n d (fun x => ∏ k, g k (x k)) c ≤ 1 := by
  rw [cutRank_eq_matrixRank, cutMatrix_prod_eq_vecMulVec g c hc]
  exact Matrix.rank_vecMulVec_le _ _

theorem matrixSingularValues_sq_of_gram_smul {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ)
    {t : ℝ}
    (hG : (Matrix.conjTranspose A * A) * (Matrix.conjTranspose A * A)
      = (t : ℂ) • (Matrix.conjTranspose A * A)) {i : ℕ}
    (hi : i < Matrix.rank A) :
    (matrixSingularValues A i) ^ 2 = t := by
  have hcard : i < Fintype.card (Fin k) := by
    have h1 : i < Module.finrank ℂ (LinearMap.range A.toEuclideanLin) := by
      rw [← rank_eq_finrank_range_toEuclideanLin A]
      exact hi
    have h2 := A.toEuclideanLin.finrank_range_le
    rw [finrank_euclideanSpace, Fintype.card_fin] at h2
    rw [Fintype.card_fin]
    omega
  have hpos : 0 < matrixSingularValues A i := by
    rw [matrixSingularValues_pos_iff_lt_finrank_range,
      ← rank_eq_finrank_range_toEuclideanLin A]
    exact hi
  obtain ⟨v, hv⟩ :=
    (matrixSingularValues_sq_hasEigenvalue_gram A hcard).exists_hasEigenvector
  have hvne : v ≠ 0 := hv.2
  set G : Matrix (Fin k) (Fin k) ℂ := Matrix.conjTranspose A * A with hGdef
  set σ : ℂ := ((matrixSingularValues A i : ℝ) : ℂ) with hσdef
  have hvs : G.toEuclideanLin v = σ ^ 2 • v := hv.apply_eq_smul
  have hmul : (G * G).toEuclideanLin
      = G.toEuclideanLin ∘ₗ G.toEuclideanLin := by
    rw [Matrix.toLpLin_mul_same]
  have hop : (G.toEuclideanLin ∘ₗ G.toEuclideanLin) v = ((t : ℂ) * σ ^ 2) • v := by
    rw [← hmul, hG, map_smul, LinearMap.smul_apply, hvs, smul_smul]
  have hop' : (G.toEuclideanLin ∘ₗ G.toEuclideanLin) v = (σ ^ 2 * σ ^ 2) • v := by
    rw [LinearMap.comp_apply, hvs, map_smul, hvs, smul_smul]
  have hμt : σ ^ 2 * σ ^ 2 = (t : ℂ) * σ ^ 2 := by
    have hz : ((t : ℂ) * σ ^ 2 - σ ^ 2 * σ ^ 2) • v = 0 := by
      rw [sub_smul, ← hop, ← hop', sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hvne
  have hσne : σ ≠ 0 := by
    rw [hσdef]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have hμeq : σ ^ 2 = (t : ℂ) := by
    have hz : σ ^ 2 * (σ ^ 2 - (t : ℂ)) = 0 := by
      linear_combination hμt
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (pow_ne_zero 2 hσne)
    · exact sub_eq_zero.mp h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow]
  exact hμeq

theorem matrixSingularValues_eq_sqrt_of_gram_smul {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ)
    {t : ℝ}
    (hG : (Matrix.conjTranspose A * A) * (Matrix.conjTranspose A * A)
      = (t : ℂ) • (Matrix.conjTranspose A * A)) {i : ℕ}
    (hi : i < Matrix.rank A) :
    matrixSingularValues A i = Real.sqrt t := by
  rw [← Real.sqrt_sq (matrixSingularValues_nonneg A i),
    matrixSingularValues_sq_of_gram_smul A hG hi]

theorem schmidtTailSq_eq_sub_mul_of_gram_smul {n d : ℕ} (ψ : (Fin n → Fin d) → ℂ)
    (c D : ℕ) {t : ℝ}
    (hG : (Matrix.conjTranspose (cutMatrix n d ψ c) * cutMatrix n d ψ c)
        * (Matrix.conjTranspose (cutMatrix n d ψ c) * cutMatrix n d ψ c)
      = (t : ℂ)
          • (Matrix.conjTranspose (cutMatrix n d ψ c) * cutMatrix n d ψ c)) :
    schmidtTailSq n d ψ c D = ((cutRank n d ψ c - D : ℕ) : ℝ) * t := by
  rw [schmidtTailSq_eq_sum ψ c D, support_matrixSingularValues_cutMatrix ψ c]
  have hval : ∀ i ∈ (Finset.range (cutRank n d ψ c)).filter (fun i => D ≤ i),
      (matrixSingularValues (cutMatrix n d ψ c) i) ^ 2 = t := by
    intro i hi
    refine matrixSingularValues_sq_of_gram_smul (cutMatrix n d ψ c) hG ?_
    rw [← cutRank_eq_matrixRank]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  rw [Finset.sum_congr rfl (fun i hi => hval i hi), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hcard : ((Finset.range (cutRank n d ψ c)).filter (fun i => D ≤ i)).card
      = cutRank n d ψ c - D := by
    have hset : (Finset.range (cutRank n d ψ c)).filter (fun i => D ≤ i)
        = Finset.Ico D (cutRank n d ψ c) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hset, Nat.card_Ico]
  exact_mod_cast hcard

theorem twoSiteTrunc_error_eq_of_gram_smul {d D : ℕ} [NeZero D]
    (ψ : (Fin 2 → Fin d) → ℂ) (hD : D ≤ Fintype.card (Fin (d ^ (2 - 1)))) {t : ℝ}
    (hG : (Matrix.conjTranspose (cutMatrix 2 d ψ 1) * cutMatrix 2 d ψ 1)
        * (Matrix.conjTranspose (cutMatrix 2 d ψ 1) * cutMatrix 2 d ψ 1)
      = (t : ℂ)
          • (Matrix.conjTranspose (cutMatrix 2 d ψ 1) * cutMatrix 2 d ψ 1)) :
    ∑ x, Complex.normSq (mpsAmplitude (g10a_twoTensor d D ψ hD) x - ψ x)
      = ((cutRank 2 d ψ 1 - D : ℕ) : ℝ) * t :=
  (g10a_twoTensor_error ψ hD).trans (schmidtTailSq_eq_sub_mul_of_gram_smul ψ 1 D hG)

private theorem norm_dot_two_sq_le (a0 a1 b0 b1 : ℂ) :
    ‖a0 * b0 + a1 * b1‖ ^ 2
      ≤ (Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1) := by
  have hkey : ∀ x y u v : ℝ, (x * u + y * v) ^ 2 ≤ (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) := by
    intro x y u v
    have hsq : (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) - (x * u + y * v) ^ 2
        = (x * v - y * u) ^ 2 := by ring
    linarith [sq_nonneg (x * v - y * u)]
  have htri : ‖a0 * b0 + a1 * b1‖ ≤ ‖a0‖ * ‖b0‖ + ‖a1‖ * ‖b1‖ := by
    refine le_trans (Complex.norm_add_le' _ _) ?_
    rw [Complex.norm_mul, Complex.norm_mul]
  have hnn1 : 0 ≤ ‖a0 * b0 + a1 * b1‖ := Complex.norm_nonneg _
  have hnn2 : 0 ≤ ‖a0‖ * ‖b0‖ + ‖a1‖ * ‖b1‖ :=
    add_nonneg (mul_nonneg (Complex.norm_nonneg _) (Complex.norm_nonneg _))
      (mul_nonneg (Complex.norm_nonneg _) (Complex.norm_nonneg _))
  have hstep := sq_le_sq' (by linarith) htri
  rw [← Complex.sq_norm a0, ← Complex.sq_norm a1, ← Complex.sq_norm b0, ← Complex.sq_norm b1]
  exact le_trans hstep (hkey ‖a0‖ ‖a1‖ ‖b0‖ ‖b1‖)

private theorem prodTwo_normSq_le :
    ∀ (m : ℕ) (u : Fin (m + 1) → Fin 2 → ℂ),
      Complex.normSq (∏ k, u k 0) + Complex.normSq (∏ k, u k 1)
        ≤ ∏ k, (∑ a : Fin 2, Complex.normSq (u k a))
  | 0, u => by
      simp [Fin.sum_univ_two]
  | m + 1, u => by
      have hp0 : (∏ k : Fin (m + 2), u k 0)
          = (∏ k : Fin (m + 1), u k.castSucc 0) * u (Fin.last (m + 1)) 0 :=
        Fin.prod_univ_castSucc _
      have hp1 : (∏ k : Fin (m + 2), u k 1)
          = (∏ k : Fin (m + 1), u k.castSucc 1) * u (Fin.last (m + 1)) 1 :=
        Fin.prod_univ_castSucc _
      have hIH := prodTwo_normSq_le m (fun k => u k.castSucc)
      have hsum : (∑ a : Fin 2, Complex.normSq (u (Fin.last (m + 1)) a))
          = Complex.normSq (u (Fin.last (m + 1)) 0)
            + Complex.normSq (u (Fin.last (m + 1)) 1) :=
        Fin.sum_univ_two _
      have hprod : (∏ k : Fin (m + 2), (∑ a : Fin 2, Complex.normSq (u k a)))
          = (∏ k : Fin (m + 1), (∑ a : Fin 2, Complex.normSq (u k.castSucc a)))
            * (∑ a : Fin 2, Complex.normSq (u (Fin.last (m + 1)) a)) :=
        Fin.prod_univ_castSucc _
      have hn0 := Complex.normSq_nonneg (u (Fin.last (m + 1)) 0)
      have hn1 := Complex.normSq_nonneg (u (Fin.last (m + 1)) 1)
      have hp0n := Complex.normSq_nonneg (∏ k : Fin (m + 1), u k.castSucc 0)
      have hp1n := Complex.normSq_nonneg (∏ k : Fin (m + 1), u k.castSucc 1)
      have hstep1 : Complex.normSq (∏ k : Fin (m + 1), u k.castSucc 0)
            * Complex.normSq (u (Fin.last (m + 1)) 0)
            + Complex.normSq (∏ k : Fin (m + 1), u k.castSucc 1)
              * Complex.normSq (u (Fin.last (m + 1)) 1)
          ≤ (Complex.normSq (∏ k : Fin (m + 1), u k.castSucc 0)
              + Complex.normSq (∏ k : Fin (m + 1), u k.castSucc 1))
            * (∑ a : Fin 2, Complex.normSq (u (Fin.last (m + 1)) a)) := by
        rw [hsum]
        nlinarith [hp0n, hp1n, hn0, hn1]
      rw [hp0, hp1, Complex.normSq_mul, Complex.normSq_mul, hprod]
      exact le_trans hstep1
        (mul_le_mul_of_nonneg_right hIH
          (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))

theorem abs_prodTwo_add_le {n : ℕ} (hn : 2 ≤ n) (w : Fin n → Fin 2 → ℂ) :
    ‖∏ k, w k 0 + ∏ k, w k 1‖
      ≤ Real.sqrt (∏ k, (∑ a : Fin 2, Complex.normSq (w k a))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hp0 : (∏ k : Fin (m + 2), w k 0)
      = (∏ k : Fin (m + 1), w k.castSucc 0) * w (Fin.last (m + 1)) 0 :=
    Fin.prod_univ_castSucc _
  have hp1 : (∏ k : Fin (m + 2), w k 1)
      = (∏ k : Fin (m + 1), w k.castSucc 1) * w (Fin.last (m + 1)) 1 :=
    Fin.prod_univ_castSucc _
  have hIH := prodTwo_normSq_le m (fun k => w k.castSucc)
  have hsum : (∑ a : Fin 2, Complex.normSq (w (Fin.last (m + 1)) a))
      = Complex.normSq (w (Fin.last (m + 1)) 0)
        + Complex.normSq (w (Fin.last (m + 1)) 1) :=
    Fin.sum_univ_two _
  have hprod : (∏ k : Fin (m + 2), (∑ a : Fin 2, Complex.normSq (w k a)))
      = (∏ k : Fin (m + 1), (∑ a : Fin 2, Complex.normSq (w k.castSucc a)))
        * (∑ a : Fin 2, Complex.normSq (w (Fin.last (m + 1)) a)) :=
    Fin.prod_univ_castSucc _
  have hnnS : 0 ≤ ∏ k : Fin (m + 2), (∑ a : Fin 2, Complex.normSq (w k a)) :=
    Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hdot := norm_dot_two_sq_le (∏ k : Fin (m + 1), w k.castSucc 0)
    (∏ k : Fin (m + 1), w k.castSucc 1) (w (Fin.last (m + 1)) 0)
    (w (Fin.last (m + 1)) 1)
  rw [Real.le_sqrt (Complex.norm_nonneg _) hnnS, hp0, hp1]
  calc ‖(∏ k : Fin (m + 1), w k.castSucc 0) * w (Fin.last (m + 1)) 0
        + (∏ k : Fin (m + 1), w k.castSucc 1) * w (Fin.last (m + 1)) 1‖ ^ 2
      ≤ (Complex.normSq (∏ k : Fin (m + 1), w k.castSucc 0)
          + Complex.normSq (∏ k : Fin (m + 1), w k.castSucc 1))
        * (∑ a : Fin 2, Complex.normSq (w (Fin.last (m + 1)) a)) := by
          rw [hsum]
          exact hdot
    _ ≤ (∏ k : Fin (m + 1), (∑ a : Fin 2, Complex.normSq (w k.castSucc a)))
        * (∑ a : Fin 2, Complex.normSq (w (Fin.last (m + 1)) a)) :=
        mul_le_mul_of_nonneg_right hIH
          (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    _ = ∏ k : Fin (m + 2), (∑ a : Fin 2, Complex.normSq (w k a)) := hprod.symm

private theorem normSq_prod_finset {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∏ i ∈ s, f i) = ∏ i ∈ s, Complex.normSq (f i) := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun _ _ => (Complex.normSq_eq_norm_sq _).symm

theorem sum_prod_normSq_eq {n : ℕ} (w : Fin n → Fin 2 → ℂ) :
    ∑ x : Fin n → Fin 2, Complex.normSq (∏ k, w k (x k))
      = ∏ k, (∑ a : Fin 2, Complex.normSq (w k a)) := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
      (fun (k : Fin n) (a : Fin 2) => Complex.normSq (w k a)),
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun _ _ => normSq_prod_finset _ _

theorem sum_two_support {n : ℕ} {M : Type*} [AddCommMonoid M] (z o : Fin n → Fin 2)
    (hzo : z ≠ o) (f : (Fin n → Fin 2) → M) (hf : ∀ x, x ≠ z → x ≠ o → f x = 0) :
    ∑ x, f x = f z + f o := by
  classical
  have hsplit : ∀ x : Fin n → Fin 2,
      f x = (if x = z then f z else 0) + (if x = o then f o else 0) := by
    intro x
    by_cases hxz : x = z
    · rw [hxz, if_pos rfl, if_neg hzo, add_zero]
    · by_cases hxo : x = o
      · rw [hxo, if_neg (fun he => hxz (hxo.trans he)), if_pos rfl, zero_add]
      · rw [if_neg hxz, if_neg hxo, hf x hxz hxo]
        simp
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ z (fun _ => f z),
    Finset.sum_ite_eq' Finset.univ o (fun _ => f o)]
  simp

theorem twoValue_prod_normSq_ge_half {n : ℕ} (hn : 2 ≤ n) {c : ℂ}
    (hc : Complex.normSq c = 1 / 2) {ψ : (Fin n → Fin 2) → ℂ}
    (hz : ψ (fun _ => 0) = c) (ho : ψ (fun _ => 1) = c)
    (hrest : ∀ x : Fin n → Fin 2, x ≠ (fun _ => 0) → x ≠ (fun _ => 1) → ψ x = 0)
    (w : Fin n → Fin 2 → ℂ) :
    1 / 2 ≤ ∑ x : Fin n → Fin 2, Complex.normSq (ψ x - ∏ k, w k (x k)) := by
  classical
  obtain ⟨k0⟩ : Nonempty (Fin n) := ⟨0, by omega⟩
  have hzo : (fun _ => 0 : Fin n → Fin 2) ≠ (fun _ => 1) := by
    intro h
    have hk := congrFun h k0
    simp at hk
  have hφz : ∏ k, w k ((fun _ => 0 : Fin n → Fin 2) k) = ∏ k, w k 0 := rfl
  have hφo : ∏ k, w k ((fun _ => 1 : Fin n → Fin 2) k) = ∏ k, w k 1 := rfl
  have hinner : ∑ x : Fin n → Fin 2, conj (ψ x) * ∏ k, w k (x k)
      = conj c * (∏ k, w k 0 + ∏ k, w k 1) := by
    have key : ∑ x : Fin n → Fin 2, conj (ψ x) * ∏ k, w k (x k)
        = conj (ψ (fun _ => 0)) * ∏ k, w k ((fun _ => 0 : Fin n → Fin 2) k)
          + conj (ψ (fun _ => 1)) * ∏ k, w k ((fun _ => 1 : Fin n → Fin 2) k) :=
      sum_two_support (fun _ => 0) (fun _ => 1) hzo
        (fun x => conj (ψ x) * ∏ k, w k (x k))
        (fun x hx0 hx1 => by
          (try simp only [])
          rw [hrest x hx0 hx1]
          simp)
    rw [key, hz, ho, hφz, hφo]
    ring
  have hnormψ : ∑ x : Fin n → Fin 2, Complex.normSq (ψ x) = 1 := by
    have key : ∑ x : Fin n → Fin 2, Complex.normSq (ψ x)
        = Complex.normSq (ψ (fun _ => 0)) + Complex.normSq (ψ (fun _ => 1)) :=
      sum_two_support (fun _ => 0) (fun _ => 1) hzo
        (fun x => Complex.normSq (ψ x))
        (fun x hx0 hx1 => by
          (try simp only [])
          rw [hrest x hx0 hx1]
          simp)
    rw [key, hz, ho, hc]
    ring
  have hnormφ : ∑ x : Fin n → Fin 2, Complex.normSq (∏ k, w k (x k))
      = ∏ k, (∑ a : Fin 2, Complex.normSq (w k a)) :=
    sum_prod_normSq_eq w
  have hconjre : ∀ x : Fin n → Fin 2,
      (ψ x * conj (∏ k, w k (x k))).re = (conj (ψ x) * ∏ k, w k (x k)).re := by
    intro x
    have h := Complex.conj_re (ψ x * conj (∏ k, w k (x k)))
    rw [map_mul, Complex.conj_conj] at h
    exact h.symm
  have hexp : ∀ x : Fin n → Fin 2,
      Complex.normSq (ψ x - ∏ k, w k (x k))
        = Complex.normSq (ψ x) + Complex.normSq (∏ k, w k (x k))
          - 2 * (conj (ψ x) * ∏ k, w k (x k)).re := by
    intro x
    have step := Complex.normSq_add (ψ x) (-(∏ k, w k (x k)))
    rw [← sub_eq_add_neg, Complex.normSq_neg] at step
    have hcn : conj (-(∏ k, w k (x k))) = -(conj (∏ k, w k (x k))) := map_neg _ _
    rw [hcn, mul_neg, Complex.neg_re] at step
    rw [step, hconjre x]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hnormψ, hnormφ]
  have hresum : ∑ x : Fin n → Fin 2, (conj (ψ x) * ∏ k, w k (x k)).re
      = (conj c * (∏ k, w k 0 + ∏ k, w k 1)).re := by
    rw [← Complex.re_sum, hinner]
  have hre_le : ∑ x : Fin n → Fin 2, 2 * (conj (ψ x) * ∏ k, w k (x k)).re
      ≤ 2 * (‖c‖ * Real.sqrt (∏ k, (∑ a : Fin 2, Complex.normSq (w k a)))) := by
    have h0 : ∑ x : Fin n → Fin 2, (conj (ψ x) * ∏ k, w k (x k)).re
        ≤ ‖c‖ * Real.sqrt (∏ k, (∑ a : Fin 2, Complex.normSq (w k a))) := by
      rw [hresum]
      have h1 := Complex.re_le_norm (conj c * (∏ k, w k 0 + ∏ k, w k 1))
      rw [Complex.norm_mul, Complex.norm_conj] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_left (abs_prodTwo_add_le hn w)
        (Complex.norm_nonneg _))
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ 2)
  have hsqc : ‖c‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm]
    exact hc
  have hnnS : 0 ≤ ∏ k, (∑ a : Fin 2, Complex.normSq (w k a)) :=
    Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hsqS : Real.sqrt (∏ k, (∑ a : Fin 2, Complex.normSq (w k a))) ^ 2
      = ∏ k, (∑ a : Fin 2, Complex.normSq (w k a)) := Real.sq_sqrt hnnS
  have hfin : 1 / 2
      ≤ 1 + ∏ k, (∑ a : Fin 2, Complex.normSq (w k a))
        - 2 * (‖c‖ * Real.sqrt (∏ k, (∑ a : Fin 2, Complex.normSq (w k a)))) := by
    nlinarith [sq_nonneg
      (Real.sqrt (∏ k, (∑ a : Fin 2, Complex.normSq (w k a))) - ‖c‖)]
  linarith

theorem mpsAmplitude_bond1_eq_prod {n d : ℕ} (A : Fin n → Fin d → Matrix (Fin 1) (Fin 1) ℂ)
    (x : Fin n → Fin d) : mpsAmplitude A x = ∏ k, A k (x k) 0 0 := by
  have hA : A = fun i y => Matrix.of fun _ _ => A i y 0 0 := by
    funext i y
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.of_apply]
    rw [Fin.eq_zero a, Fin.eq_zero b]
  rw [hA, mpsAmplitude_product]
  rfl

private theorem normSq_sub_re (z w : ℂ) :
    Complex.normSq (z - w) = Complex.normSq z + Complex.normSq w - 2 * (conj z * w).re := by
  have step := Complex.normSq_add z (-w)
  rw [← sub_eq_add_neg, Complex.normSq_neg] at step
  have hcn : conj (-(w : ℂ)) = -conj w := map_neg _ _
  rw [hcn, mul_neg, Complex.neg_re] at step
  have hcr : (z * conj w).re = (conj z * w).re := by
    have h := Complex.conj_re (conj z * w)
    rw [map_mul, Complex.conj_conj] at h
    exact h
  rw [step, hcr]
  ring

private theorem ortho_family_conj {α : Type*} [Fintype α] {r : ℕ} (u : Fin r → α → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0) (i j : Fin r) :
    ∑ x, u i x * conj (u j x) = if i = j then 1 else 0 := by
  have hmap : conj (∑ x, conj (u i x) * u j x) = ∑ x, u i x * conj (u j x) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_mul, Complex.conj_conj]
  rw [← hmap, hu i j]
  by_cases hij : i = j
  · rw [if_pos hij, map_one]
  · rw [if_neg hij, map_zero]

private theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    ∑ i, p i * q i ≤ Real.sqrt (∑ i, p i ^ 2) * Real.sqrt (∑ i, q i ^ 2) := by
  classical
  by_cases hQ0 : ∑ i, q i ^ 2 = 0
  · have hq0 : ∀ i, q i = 0 := fun i =>
      sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => sq_nonneg (q x))).mp hQ0 i (Finset.mem_univ i))
    rw [Finset.sum_eq_zero fun i _ => by rw [hq0 i, mul_zero], hQ0, Real.sqrt_zero, mul_zero]
  · have hPnn : 0 ≤ ∑ i, p i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hQnn : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hQpos : 0 < ∑ i, q i ^ 2 := lt_of_le_of_ne hQnn fun h => hQ0 h.symm
    have hsnn : 0 ≤ ∑ i, p i * q i := Finset.sum_nonneg fun _ _ => mul_nonneg (hp _) (hq _)
    have hQne : (∑ i, q i ^ 2) ≠ 0 := ne_of_gt hQpos
    have hexp : ∑ i, (p i - (∑ i', p i' * q i') / (∑ i', q i' ^ 2) * q i) ^ 2
        = (∑ i, p i ^ 2) - (∑ i, p i * q i) ^ 2 / (∑ i, q i ^ 2) := by
      have hterm : ∀ i, (p i - (∑ i', p i' * q i') / (∑ i', q i' ^ 2) * q i) ^ 2
          = p i * p i - 2 * ((∑ i', p i' * q i') / (∑ i', q i' ^ 2)) * (p i * q i)
            + ((∑ i', p i' * q i') / (∑ i', q i' ^ 2)) ^ 2 * (q i * q i) := by
        intro i; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        show ∑ i, p i * p i = ∑ i, p i ^ 2 from Finset.sum_congr rfl fun i _ => by ring,
        show ∑ i, q i * q i = ∑ i', q i' ^ 2 from Finset.sum_congr rfl fun i _ => by ring]
      field_simp
      ring
    have hnn : 0 ≤ ∑ i, (p i - (∑ i', p i' * q i') / (∑ i', q i' ^ 2) * q i) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [hexp] at hnn
    have hkey : (∑ i, p i * q i) ^ 2 ≤ (∑ i, p i ^ 2) * (∑ i, q i ^ 2) :=
      (div_le_iff₀ hQpos).1 (by linarith)
    have hfin := Real.le_sqrt_of_sq_le hkey
    rwa [Real.sqrt_mul' _ hQnn] at hfin

private theorem norm_sum_conj_mul_le {α : Type*} [Fintype α] (f g : α → ℂ) :
    ‖∑ x, conj (f x) * g x‖
      ≤ Real.sqrt (∑ x, Complex.normSq (f x)) * Real.sqrt (∑ x, Complex.normSq (g x)) := by
  have htri : ‖∑ x, conj (f x) * g x‖ ≤ ∑ x, ‖conj (f x) * g x‖ := norm_sum_le _ _
  have hterm : ∀ x, ‖conj (f x) * g x‖
      = Real.sqrt (Complex.normSq (f x)) * Real.sqrt (Complex.normSq (g x)) := by
    intro x
    rw [Complex.norm_mul, Complex.norm_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg (f x)),
      Real.sqrt_sq (norm_nonneg (g x))]
  refine le_trans htri ?_
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  calc ∑ x, Real.sqrt (Complex.normSq (f x)) * Real.sqrt (Complex.normSq (g x))
      ≤ Real.sqrt (∑ x, (Real.sqrt (Complex.normSq (f x))) ^ 2)
          * Real.sqrt (∑ x, (Real.sqrt (Complex.normSq (g x))) ^ 2) :=
        sum_mul_le_sqrt_mul_sqrt _ _ (fun _ => Real.sqrt_nonneg _)
          (fun _ => Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ x, Complex.normSq (f x)) * Real.sqrt (∑ x, Complex.normSq (g x)) := by
        rw [Finset.sum_congr rfl
            (fun x _ => Real.sq_sqrt (Complex.normSq_nonneg _)),
          Finset.sum_congr rfl
            (fun x _ => Real.sq_sqrt (Complex.normSq_nonneg _))]

private theorem ortho_inner_coeff {α : Type*} [Fintype α] {r : ℕ}
    (v : Fin r → α → ℂ) (q : Fin r → ℂ) (g : α → ℂ) :
    (∑ x, conj (∑ i, q i * v i x) * g x) = ∑ i, conj (q i) * (∑ x, conj (v i x) * g x) := by
  have hterm : ∀ x, conj (∑ i, q i * v i x) * g x
      = ∑ i, conj (q i) * (conj (v i x) * g x) := by
    intro x
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    (Finset.mul_sum Finset.univ (fun x => conj (v i x) * g x) (conj (q i))).symm

theorem schmidt_family_normSq_eq {α : Type*} [Fintype α] {r : ℕ}
    (v : Fin r → α → ℂ) (q : Fin r → ℂ)
    (hv : ∀ i j, ∑ x, conj (v i x) * v j x = if i = j then 1 else 0) :
    ∑ x, Complex.normSq (∑ i, q i * v i x) = ∑ i, Complex.normSq (q i) := by
  have hexp : ∀ x, Complex.normSq (∑ i, q i * v i x)
      = ∑ i, ∑ j, (q i * conj (q j) * (v i x * conj (v j x))).re := by
    intro x
    have hz : Complex.normSq (∑ i, q i * v i x)
        = ((∑ i, q i * v i x) * conj (∑ i, q i * v i x)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re]
    rw [hz, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun j _ => by
        refine congrArg Complex.re ?_
        rw [map_mul]
        ring
  have hrow : ∀ i j, ∑ x, (q i * conj (q j) * (v i x * conj (v j x))).re
      = (q i * conj (q j) * (if i = j then 1 else 0)).re := by
    intro i j
    rw [← Complex.re_sum, ← Finset.mul_sum, ortho_family_conj v hv i j]
  have hval : ∀ i j, (q i * conj (q j) * (if i = j then 1 else 0)).re
      = if i = j then Complex.normSq (q i) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, mul_one, Complex.mul_conj, Complex.ofReal_re, if_pos rfl]
    · rw [if_neg hij, mul_zero, Complex.zero_re, if_neg hij]
  rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun x j => (q i * conj (q j) * (v i x * conj (v j x))).re))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hrow i j))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval i j))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_ite_eq Finset.univ i
    (fun _ => Complex.normSq (q i)))]
  simp

theorem ortho_sum_normSq_le {α : Type*} [Fintype α] {r : ℕ}
    (u : Fin r → α → ℂ) (a : α → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0) :
    ∑ i, Complex.normSq (∑ x, conj (u i x) * a x) ≤ ∑ x, Complex.normSq (a x) := by
  classical
  have hparseq : ∑ x, Complex.normSq (∑ i, (∑ x', conj (u i x') * a x') * u i x)
      = ∑ i, Complex.normSq (∑ x', conj (u i x') * a x') :=
    schmidt_family_normSq_eq u (fun i => ∑ x', conj (u i x') * a x') hu
  have hinner : (∑ x, conj (∑ i, (∑ x', conj (u i x') * a x') * u i x) * a x)
      = ((∑ i, Complex.normSq (∑ x', conj (u i x') * a x') : ℝ) : ℂ) := by
    rw [ortho_inner_coeff u (fun i => ∑ x', conj (u i x') * a x') a]
    rw [Finset.sum_congr rfl (fun i _ => by rw [mul_comm, Complex.mul_conj]),
      ← Complex.ofReal_sum]
  have hSnn : 0 ≤ ∑ i, Complex.normSq (∑ x', conj (u i x') * a x') :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hTnn : 0 ≤ ∑ x, Complex.normSq (a x) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hcs := norm_sum_conj_mul_le
    (fun x => ∑ i, (∑ x', conj (u i x') * a x') * u i x) a
  rw [hparseq] at hcs
  rw [hinner, Complex.norm_of_nonneg hSnn] at hcs
  by_cases hS0 : ∑ i, Complex.normSq (∑ x', conj (u i x') * a x') = 0
  · rw [hS0]
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · have hsqrt : (Real.sqrt (∑ i, Complex.normSq (∑ x', conj (u i x') * a x'))
        * Real.sqrt (∑ x, Complex.normSq (a x))) ^ 2
        = (∑ i, Complex.normSq (∑ x', conj (u i x') * a x'))
          * (∑ x, Complex.normSq (a x)) := by
      rw [mul_pow, Real.sq_sqrt hSnn, Real.sq_sqrt hTnn]
    have hSpos : 0 < ∑ i, Complex.normSq (∑ x', conj (u i x') * a x') :=
      lt_of_le_of_ne hSnn fun h => hS0 h.symm
    have hXnn : 0 ≤ Real.sqrt (∑ i, Complex.normSq (∑ x', conj (u i x') * a x'))
        * Real.sqrt (∑ x, Complex.normSq (a x)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hkey2 : (∑ i, Complex.normSq (∑ x', conj (u i x') * a x'))
            * (∑ i, Complex.normSq (∑ x', conj (u i x') * a x'))
        ≤ (∑ i, Complex.normSq (∑ x', conj (u i x') * a x'))
          * (∑ x, Complex.normSq (a x)) := by
      nlinarith [hcs, hsqrt, hXnn, hSnn]
    nlinarith [hkey2, hSpos]

theorem schmidt_pair_normSq_eq {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    (c : Fin r → ℂ) (u : Fin r → α → ℂ) (v : Fin r → β → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ y, conj (v i y) * v j y = if i = j then 1 else 0) :
    ∑ p : α × β, Complex.normSq (∑ i, c i * u i p.1 * v i p.2) = ∑ i, Complex.normSq (c i) := by
  have hrow : ∀ x : α, ∑ y : β, Complex.normSq (∑ i, c i * u i x * v i y)
      = ∑ i, Complex.normSq (c i) * Complex.normSq (u i x) := by
    intro x
    rw [schmidt_family_normSq_eq v (fun i => c i * u i x) hv]
    exact Finset.sum_congr rfl fun i _ => Complex.normSq_mul (c i) (u i x)
  have hunorm : ∀ i, ∑ x, Complex.normSq (u i x) = 1 := by
    intro i
    have h := hu i i
    rw [if_pos rfl] at h
    have hc : ((∑ x, Complex.normSq (u i x) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum,
        Finset.sum_congr rfl (fun x _ => by
          rw [(Complex.mul_conj (u i x)).symm, mul_comm]), h]
    exact Complex.ofReal_inj.mp (hc.trans rfl)
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl (fun x _ => hrow x), Finset.sum_comm,
    show (∑ i : Fin r, ∑ x : α, Complex.normSq (c i) * Complex.normSq (u i x))
        = ∑ i : Fin r, Complex.normSq (c i) * ∑ x : α, Complex.normSq (u i x) from
      Finset.sum_congr rfl fun i _ =>
        (Finset.mul_sum Finset.univ (fun x => Complex.normSq (u i x))
          (Complex.normSq (c i))).symm,
    Finset.sum_congr rfl (fun i _ => by rw [hunorm i, mul_one])]

theorem schmidt_prod_error_ge_of_top {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    (c : Fin r → ℂ) (u : Fin r → α → ℂ) (v : Fin r → β → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ y, conj (v i y) * v j y = if i = j then 1 else 0)
    (j : Fin r) (hmax : ∀ i, Complex.normSq (c i) ≤ Complex.normSq (c j))
    (a : α → ℂ) (b : β → ℂ) :
    (∑ i, Complex.normSq (c i)) - Complex.normSq (c j)
      ≤ ∑ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2) - a p.1 * b p.2) := by
  classical
  have hexp : ∀ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2) - a p.1 * b p.2)
      = Complex.normSq (∑ i, c i * u i p.1 * v i p.2) + Complex.normSq (a p.1 * b p.2)
        - 2 * (conj (∑ i, c i * u i p.1 * v i p.2) * (a p.1 * b p.2)).re :=
    fun p => normSq_sub_re _ _
  have hnorm : Complex.normSq (c j) = ‖c j‖ ^ 2 := (Complex.sq_norm (c j)).symm
  have hnormsqrt : ∀ z : ℂ, ‖z‖ = Real.sqrt (Complex.normSq z) := by
    intro z
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (Complex.norm_nonneg _)]
  have hσc : ∀ i, ‖c i‖ ≤ ‖c j‖ := by
    intro i
    rw [hnormsqrt (c i), hnormsqrt (c j)]
    exact Real.sqrt_le_sqrt (hmax i)
  have hφ : ∑ p : α × β, Complex.normSq (a p.1 * b p.2)
      = (∑ x, Complex.normSq (a x)) * (∑ y, Complex.normSq (b y)) := by
    rw [Fintype.sum_prod_type]
    (try simp only [])
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        show Complex.normSq (a ((x, y) : α × β).1 * b (x, y).2)
            = Complex.normSq (a x) * Complex.normSq (b y)
        rw [Complex.normSq_mul],
      show (∑ x : α, ∑ y : β, Complex.normSq (a x) * Complex.normSq (b y))
          = ∑ x : α, Complex.normSq (a x) * ∑ y : β, Complex.normSq (b y) from
        Finset.sum_congr rfl fun x _ =>
          (Finset.mul_sum Finset.univ (fun y => Complex.normSq (b y))
            (Complex.normSq (a x))).symm,
      show (∑ x : α, Complex.normSq (a x) * ∑ y : β, Complex.normSq (b y))
          = (∑ x : α, Complex.normSq (a x)) * ∑ y : β, Complex.normSq (b y) from
        (Finset.sum_mul Finset.univ (fun x => Complex.normSq (a x))
          (∑ y : β, Complex.normSq (b y))).symm]
  have hcoef : ∀ i : Fin r, (∑ p : α × β, conj (u i p.1 * v i p.2) * (a p.1 * b p.2))
      = (∑ x, conj (u i x) * a x) * (∑ y, conj (v i y) * b y) := by
    intro i
    rw [Fintype.sum_prod_type]
    (try simp only [])
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        show conj (u i x * v i y) * (a x * b y)
            = conj (u i x) * a x * (conj (v i y) * b y)
        rw [map_mul]
        ring,
      show (∑ x : α, ∑ y : β, conj (u i x) * a x * (conj (v i y) * b y))
          = ∑ x : α, conj (u i x) * a x * ∑ y : β, conj (v i y) * b y from
        Finset.sum_congr rfl fun x _ =>
          (Finset.mul_sum Finset.univ (fun y => conj (v i y) * b y)
            (conj (u i x) * a x)).symm,
      show (∑ x : α, conj (u i x) * a x * ∑ y : β, conj (v i y) * b y)
          = (∑ x : α, conj (u i x) * a x) * ∑ y : β, conj (v i y) * b y from
        (Finset.sum_mul Finset.univ (fun x => conj (u i x) * a x)
          (∑ y : β, conj (v i y) * b y)).symm]
  have hassoc : ∀ p : α × β, (conj (∑ i, c i * u i p.1 * v i p.2) * (a p.1 * b p.2)).re
      = (conj (∑ i, c i * (u i p.1 * v i p.2)) * (a p.1 * b p.2)).re := fun p =>
    congrArg Complex.re (congrArg (fun z => conj z * (a p.1 * b p.2))
      (Finset.sum_congr rfl fun i _ => mul_assoc _ _ _))
  have hsplitcross : (∑ p : α × β, conj (∑ i, c i * (u i p.1 * v i p.2)) * (a p.1 * b p.2))
      = ∑ i, conj (c i) * (∑ p : α × β, conj (u i p.1 * v i p.2) * (a p.1 * b p.2)) :=
    ortho_inner_coeff (fun (i : Fin r) (p : α × β) => u i p.1 * v i p.2) c
      (fun p => a p.1 * b p.2)
  have hcross : ∑ p : α × β, (conj (∑ i, c i * u i p.1 * v i p.2) * (a p.1 * b p.2)).re
      = (∑ i, conj (c i) * (∑ x, conj (u i x) * a x) * (∑ y, conj (v i y) * b y)).re := by
    rw [Finset.sum_congr rfl (fun p _ => hassoc p), ← Complex.re_sum, hsplitcross]
    exact congrArg Complex.re (Finset.sum_congr rfl fun i _ => by
      rw [hcoef i, mul_assoc])
  have hBessP := ortho_sum_normSq_le u a hu
  have hBessQ := ortho_sum_normSq_le v b hv
  have hchain : ‖∑ i, conj (c i) * (∑ x, conj (u i x) * a x) * (∑ y, conj (v i y) * b y)‖
      ≤ ‖c j‖ * Real.sqrt (∑ x, Complex.normSq (a x))
          * Real.sqrt (∑ y, Complex.normSq (b y)) := by
    have htri : ‖∑ i, conj (c i) * (∑ x, conj (u i x) * a x)
          * (∑ y, conj (v i y) * b y)‖
        ≤ ∑ i, ‖conj (c i) * (∑ x, conj (u i x) * a x) * (∑ y, conj (v i y) * b y)‖ :=
      norm_sum_le _ _
    have hterm : ∀ i : Fin r, ‖conj (c i) * (∑ x, conj (u i x) * a x)
          * (∑ y, conj (v i y) * b y)‖
        = ‖c i‖ * (‖(∑ x, conj (u i x) * a x)‖ * ‖(∑ y, conj (v i y) * b y)‖) := by
      intro i
      rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_conj]
      ring
    have hcs := sum_mul_le_sqrt_mul_sqrt
      (fun i : Fin r => ‖(∑ x, conj (u i x) * a x)‖)
      (fun i : Fin r => ‖(∑ y, conj (v i y) * b y)‖)
      (fun _ => Complex.norm_nonneg _) (fun _ => Complex.norm_nonneg _)
    have hsq1 : (∑ i : Fin r, ‖(∑ x, conj (u i x) * a x)‖ ^ 2)
        = ∑ i, Complex.normSq (∑ x, conj (u i x) * a x) :=
      Finset.sum_congr rfl fun i _ => Complex.sq_norm _
    have hsq2 : (∑ i : Fin r, ‖(∑ y, conj (v i y) * b y)‖ ^ 2)
        = ∑ i, Complex.normSq (∑ y, conj (v i y) * b y) :=
      Finset.sum_congr rfl fun i _ => Complex.sq_norm _
    (try simp only [] at hcs)
    rw [hsq1, hsq2] at hcs
    calc ‖∑ i, conj (c i) * (∑ x, conj (u i x) * a x) * (∑ y, conj (v i y) * b y)‖
        ≤ ∑ i, ‖c j‖ * (‖(∑ x, conj (u i x) * a x)‖ * ‖(∑ y, conj (v i y) * b y)‖) :=
          le_trans htri
            (Finset.sum_le_sum fun i _ => by
              rw [hterm i]
              exact mul_le_mul_of_nonneg_right (hσc i)
                (mul_nonneg (Complex.norm_nonneg _) (Complex.norm_nonneg _)))
      _ = ‖c j‖ * ∑ i, (‖(∑ x, conj (u i x) * a x)‖ * ‖(∑ y, conj (v i y) * b y)‖) :=
          (Finset.mul_sum Finset.univ
            (fun i : Fin r => ‖(∑ x, conj (u i x) * a x)‖ * ‖(∑ y, conj (v i y) * b y)‖)
            (‖c j‖)).symm
      _ ≤ ‖c j‖ * Real.sqrt (∑ x, Complex.normSq (a x))
            * Real.sqrt (∑ y, Complex.normSq (b y)) :=
          le_trans (mul_le_mul_of_nonneg_left
            (le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hBessP)
              (Real.sqrt_le_sqrt hBessQ) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
            (Complex.norm_nonneg _)) (le_of_eq (mul_assoc _ _ _).symm)
  have hre : ∑ p : α × β, (conj (∑ i, c i * u i p.1 * v i p.2) * (a p.1 * b p.2)).re
      ≤ ‖c j‖ * Real.sqrt (∑ x, Complex.normSq (a x))
          * Real.sqrt (∑ y, Complex.normSq (b y)) := by
    rw [hcross]
    exact le_trans (Complex.re_le_norm _) hchain
  have hA2nn : 0 ≤ ∑ x, Complex.normSq (a x) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hB2nn : 0 ≤ ∑ y, Complex.normSq (b y) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hX : (Real.sqrt (∑ x, Complex.normSq (a x))
      * Real.sqrt (∑ y, Complex.normSq (b y))) ^ 2
      = (∑ x, Complex.normSq (a x)) * (∑ y, Complex.normSq (b y)) := by
    rw [mul_pow, Real.sq_sqrt hA2nn, Real.sq_sqrt hB2nn]
  have hfin : (∑ i, Complex.normSq (c i)) - ‖c j‖ ^ 2
      ≤ (∑ i, Complex.normSq (c i))
          + (∑ x, Complex.normSq (a x)) * (∑ y, Complex.normSq (b y))
        - 2 * (‖c j‖ * Real.sqrt (∑ x, Complex.normSq (a x))
            * Real.sqrt (∑ y, Complex.normSq (b y))) := by
    nlinarith [sq_nonneg (Real.sqrt (∑ x, Complex.normSq (a x))
      * Real.sqrt (∑ y, Complex.normSq (b y)) - ‖c j‖), hX]
  rw [Finset.sum_congr rfl (fun p _ => hexp p), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, schmidt_pair_normSq_eq c u v hu hv, hφ]
  rw [← Finset.mul_sum]
  linarith [hre, hfin, hnorm]

theorem schmidt_trunc_error_eq {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    (c : Fin r → ℂ) (u : Fin r → α → ℂ) (v : Fin r → β → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ y, conj (v i y) * v j y = if i = j then 1 else 0) (j : Fin r) :
    ∑ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2) - c j * u j p.1 * v j p.2)
      = (∑ i, Complex.normSq (c i)) - Complex.normSq (c j) := by
  have hzero : ∀ p : α × β,
      (∑ i, c i * u i p.1 * v i p.2) - c j * u j p.1 * v j p.2
        = ∑ i, (if i = j then 0 else c i) * u i p.1 * v i p.2 := by
    intro p
    have hsplit : ∀ i : Fin r, c i * u i p.1 * v i p.2
        = (if i = j then 0 else c i) * u i p.1 * v i p.2
          + (if i = j then c i * u i p.1 * v i p.2 else 0) := by
      intro i
      by_cases h : i = j
      · rw [if_pos h, if_pos h, zero_mul, zero_mul, zero_add]
      · rw [if_neg h, if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ j (fun i => c i * u i p.1 * v i p.2)]
    simp
  have hsum : (∑ i, Complex.normSq (c i))
      = (∑ i, Complex.normSq ((fun i => if i = j then 0 else c i) i))
        + Complex.normSq (c j) := by
    have hsplit : ∀ i : Fin r, Complex.normSq (c i)
        = Complex.normSq ((fun i => if i = j then 0 else c i) i)
          + (if i = j then Complex.normSq (c j) else 0) := by
      intro i
      by_cases h : i = j
      · subst h
        simp
      · (try simp only [])
        rw [if_neg h, if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ j (fun _ => Complex.normSq (c j))]
    simp
  rw [Finset.sum_congr rfl (fun p _ => by rw [hzero p])]
  rw [schmidt_pair_normSq_eq (fun i => if i = j then 0 else c i) u v hu hv]
  linarith [hsum]

private theorem bessel_weight_ratio {r : ℕ} (T : Finset (Fin r)) (jmin : Fin r)
    (μ B : Fin r → ℝ) (hμnn : ∀ i, 0 ≤ μ i)
    (hmin : ∀ j ∈ T, μ jmin ≤ μ j) (hmax : ∀ i ∉ T, μ i ≤ μ jmin)
    (hB1 : ∀ i, B i ≤ 1) (hBnn : ∀ i, 0 ≤ B i)
    (hcount : (∑ i, B i) ≤ (T.card : ℝ)) :
    (∑ i, μ i * B i) ≤ ∑ i ∈ T, μ i := by
  have hjmnn : 0 ≤ μ jmin := hμnn jmin
  have hpt : ∀ i : Fin r, μ i * B i = μ i - μ i * (1 - B i) := fun i => by ring
  have hTform : (∑ i ∈ T, μ i * B i)
      = (∑ i ∈ T, μ i) - ∑ i ∈ T, μ i * (1 - B i) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib]
  have hone : ∀ i ∈ T, μ jmin * (1 - B i) ≤ μ i * (1 - B i) := fun i hi =>
    mul_le_mul_of_nonneg_right (hmin i hi) (by have := hB1 i; linarith)
  have hsplit : ∑ i ∈ T, ((1 : ℝ) - B i)
      = (∑ i ∈ T, (1 : ℝ)) - ∑ i ∈ T, B i := by
    have hlam : ∀ i : Fin r, (1 : ℝ) - B i
        = (fun _ => (1 : ℝ)) i - (fun i => B i) i := fun _ => rfl
    rw [Finset.sum_congr rfl (fun i _ => hlam i), Finset.sum_sub_distrib]
  have hcard1 : (∑ i ∈ T, (1 : ℝ)) = (T.card : ℝ) := by simp
  have hL1 : μ jmin * ((T.card : ℝ) - ∑ i ∈ T, B i)
      ≤ ∑ i ∈ T, μ i * (1 - B i) := by
    rw [← hcard1, ← hsplit, Finset.mul_sum T (fun i => (1 : ℝ) - B i) (μ jmin)]
    exact Finset.sum_le_sum hone
  have htwo : ∀ i ∈ Tᶜ, μ i * B i ≤ μ jmin * B i := fun i hi =>
    mul_le_mul_of_nonneg_right (hmax i (Finset.mem_compl.mp hi)) (hBnn i)
  have hL2 : ∑ i ∈ Tᶜ, μ i * B i ≤ μ jmin * (∑ i ∈ Tᶜ, B i) := by
    rw [Finset.mul_sum (Tᶜ) (fun i => B i) (μ jmin)]
    exact Finset.sum_le_sum htwo
  have hcountT : (∑ i ∈ T, B i) + (∑ i ∈ Tᶜ, B i) ≤ (T.card : ℝ) := by
    rw [Finset.sum_add_sum_compl T (fun i => B i)]
    exact hcount
  have hAB : μ jmin * ((T.card : ℝ) - ∑ i ∈ T, B i) - μ jmin * (∑ i ∈ Tᶜ, B i)
      ≥ 0 := by
    rw [← mul_sub]
    exact mul_nonneg hjmnn (by linarith)
  calc (∑ i, μ i * B i)
      = (∑ i ∈ T, μ i * B i) + ∑ i ∈ Tᶜ, μ i * B i :=
        (Finset.sum_add_sum_compl T (fun i => μ i * B i)).symm
    _ = ((∑ i ∈ T, μ i) - ∑ i ∈ T, μ i * (1 - B i)) + ∑ i ∈ Tᶜ, μ i * B i := by
        rw [hTform]
    _ ≤ ((∑ i ∈ T, μ i) - μ jmin * ((T.card : ℝ) - ∑ i ∈ T, B i))
        + μ jmin * (∑ i ∈ Tᶜ, B i) :=
        add_le_add (sub_le_sub_left hL1 _) hL2
    _ ≤ ∑ i ∈ T, μ i := by linarith

theorem schmidt_orthoFeet_error_ge_of_topset {α β : Type*} [Fintype α] [Fintype β]
    {r D : ℕ}
    (c : Fin r → ℂ) (u : Fin r → α → ℂ) (v : Fin r → β → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ y, conj (v i y) * v j y = if i = j then 1 else 0)
    (T : Finset (Fin r)) (hcard : T.card = D) (jmin : Fin r)
    (hmin : ∀ j ∈ T, Complex.normSq (c jmin) ≤ Complex.normSq (c j))
    (hmax : ∀ i ∉ T, Complex.normSq (c i) ≤ Complex.normSq (c jmin))
    (l : Fin D → α → ℂ) (t : Fin D → β → ℂ)
    (ht : ∀ a b, ∑ y, conj (t a y) * t b y = if a = b then 1 else 0) :
    (∑ i, Complex.normSq (c i)) - ∑ i ∈ T, Complex.normSq (c i)
      ≤ ∑ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2)
          - ∑ a, l a p.1 * t a p.2) := by
  classical
  have hexp : ∀ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2)
        - ∑ a, l a p.1 * t a p.2)
      = Complex.normSq (∑ i, c i * u i p.1 * v i p.2)
        + Complex.normSq (∑ a, l a p.1 * t a p.2)
        - 2 * (conj (∑ i, c i * u i p.1 * v i p.2)
            * (∑ a, l a p.1 * t a p.2)).re :=
    fun p => normSq_sub_re _ _
  have hφrow : ∀ x : α, ∑ y : β, Complex.normSq (∑ a, l a x * t a y)
      = ∑ a, Complex.normSq (l a x) := fun x =>
    schmidt_family_normSq_eq t (fun a => l a x) ht
  have hφnorm : ∑ p : α × β, Complex.normSq (∑ a, l a p.1 * t a p.2)
      = ∑ a, ∑ x : α, Complex.normSq (l a x) := by
    rw [Fintype.sum_prod_type]
    (try simp only [])
    rw [Finset.sum_congr rfl (fun x _ => hφrow x), Finset.sum_comm]
  have hinner : ∀ (a : Fin D) (x : α),
      (∑ y : β, conj (∑ i, c i * u i x * v i y) * t a y)
        = conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) := by
    intro a x
    have key1 : (∑ y : β, conj (∑ i, c i * u i x * v i y) * t a y)
        = ∑ i : Fin r, conj (c i * u i x) * (∑ y, conj (v i y) * t a y) := by
      rw [Finset.sum_congr rfl (fun y _ => by
          rw [map_sum, Finset.sum_mul Finset.univ
            (fun i => conj (c i * u i x * v i y)) (t a y)]),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : ∀ y : β, conj (c i * u i x * v i y) * t a y
          = conj (c i * u i x) * (conj (v i y) * t a y) := by
        intro y
        rw [map_mul]
        ring
      rw [Finset.sum_congr rfl (fun y _ => hterm y),
        ← Finset.mul_sum Finset.univ (fun y => conj (v i y) * t a y)
          (conj (c i * u i x))]
    have hτ : ∀ i : Fin r,
        (∑ y, conj (v i y) * t a y) = conj (∑ y, conj (t a y) * v i y) := by
      intro i
      rw [map_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [map_mul, Complex.conj_conj]; ring
    have hterm : ∀ i : Fin r, conj (c i * u i x) * (∑ y, conj (v i y) * t a y)
        = conj (c i * (∑ y, conj (t a y) * v i y) * u i x) := by
      intro i
      have hA : c i * (∑ y, conj (t a y) * v i y) * u i x
          = (c i * u i x) * (∑ y, conj (t a y) * v i y) := by ring
      have hB : conj (c i * u i x) * conj (∑ y, conj (t a y) * v i y)
          = conj ((c i * u i x) * (∑ y, conj (t a y) * v i y)) :=
        (map_mul (starRingEnd ℂ) _ _).symm
      rw [hτ i, hA, ← hB]
    rw [key1, Finset.sum_congr rfl (fun i _ => hterm i), map_sum]
  have hcross : (∑ p : α × β, conj (∑ i, c i * u i p.1 * v i p.2)
          * (∑ a, l a p.1 * t a p.2))
      = ∑ a, ∑ x : α, l a x * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) := by
    rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum Finset.univ
        (fun a => l a p.1 * t a p.2) (conj (∑ i, c i * u i p.1 * v i p.2)))]
    have hswap : (∑ p : α × β, ∑ a : Fin D, conj (∑ i, c i * u i p.1 * v i p.2)
          * (l a p.1 * t a p.2))
        = ∑ a : Fin D, ∑ p : α × β, conj (∑ i, c i * u i p.1 * v i p.2)
          * (l a p.1 * t a p.2) :=
      Finset.sum_comm (f := fun (p : α × β) (a : Fin D) =>
        conj (∑ i, c i * u i p.1 * v i p.2) * (l a p.1 * t a p.2))
    rw [hswap]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hterm2 : ∀ y : β, conj (∑ i, c i * u i x * v i y) * (l a x * t a y)
        = l a x * (conj (∑ i, c i * u i x * v i y) * t a y) := fun y => by ring
    rw [Finset.sum_congr rfl (fun y _ => hterm2 y),
      ← Finset.mul_sum Finset.univ
        (fun y => conj (∑ i, c i * u i x * v i y) * t a y) (l a x), hinner a x]
  have hhn : ∀ a : Fin D, ∑ x : α,
        Complex.normSq (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)
      = ∑ i, Complex.normSq (c i)
          * Complex.normSq (∑ y, conj (t a y) * v i y) := by
    intro a
    rw [schmidt_family_normSq_eq u (fun i => c i * (∑ y, conj (t a y) * v i y)) hu]
    exact Finset.sum_congr rfl fun i _ => Complex.normSq_mul _ _
  have hvar : ∀ a : Fin D, (∑ x : α, Complex.normSq (l a x))
      - 2 * (∑ x : α, l a x
          * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re
      ≥ -∑ x : α,
          Complex.normSq (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) := by
    intro a
    have hnn : 0 ≤ ∑ x : α, Complex.normSq
        ((∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) - l a x) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hper : ∀ x : α, Complex.normSq
        ((∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) - l a x)
        = Complex.normSq (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)
          + Complex.normSq (l a x)
          - 2 * (l a x
              * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re := by
      intro x
      have hstep := normSq_sub_re
        (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) (l a x)
      have hre : (conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x) * l a x).re
          = (l a x * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re := by
        rw [mul_comm (conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)) (l a x)]
      rw [hstep, hre]
    rw [Finset.sum_congr rfl (fun x _ => hper x), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum Finset.univ
        (fun x => (l a x
          * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re) (2 : ℝ),
      ← Complex.re_sum] at hnn
    linarith
  have hμ : (∑ i, Complex.normSq (c i))
      - ∑ i, Complex.normSq (c i)
          * (∑ a : Fin D, Complex.normSq (∑ y, conj (t a y) * v i y))
      ≤ ∑ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2)
          - ∑ a, l a p.1 * t a p.2) := by
    have hre : (∑ p : α × β, (conj (∑ i, c i * u i p.1 * v i p.2)
          * (∑ a, l a p.1 * t a p.2)).re)
        = (∑ a : Fin D, ∑ x : α, l a x
            * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re := by
      rw [← Complex.re_sum, hcross]
    rw [Finset.sum_congr rfl (fun p _ => hexp p), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, schmidt_pair_normSq_eq c u v hu hv, hφnorm,
      ← Finset.mul_sum Finset.univ
        (fun (p : α × β) => (conj (∑ i, c i * u i p.1 * v i p.2)
          * (∑ a, l a p.1 * t a p.2)).re) (2 : ℝ), hre, Complex.re_sum]
    have hdistr : 2 * (∑ a : Fin D, (∑ x : α, l a x
            * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re)
        = ∑ a : Fin D, 2 * ((∑ x : α, l a x
            * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re) := by
      rw [Finset.mul_sum Finset.univ
        (fun a => (∑ x : α, l a x
          * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re) (2 : ℝ)]
    rw [hdistr]
    have hbracket : (∑ a : Fin D, ∑ x : α, Complex.normSq (l a x))
        - (∑ a : Fin D, 2 * ((∑ x : α, l a x
            * conj (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)).re))
        ≥ -(∑ a : Fin D, ∑ x : α,
            Complex.normSq (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun a _ => hvar a
    have hconv : (∑ a : Fin D, ∑ x : α,
          Complex.normSq (∑ i, c i * (∑ y, conj (t a y) * v i y) * u i x))
        = ∑ i, Complex.normSq (c i)
          * (∑ a : Fin D, Complex.normSq (∑ y, conj (t a y) * v i y)) := by
      rw [Finset.sum_congr rfl (fun a _ => hhn a), Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← Finset.mul_sum Finset.univ
          (fun a => Complex.normSq (∑ y, conj (t a y) * v i y))
          (Complex.normSq (c i))]
    linarith
  have hvnorm : ∀ i : Fin r, (∑ y, Complex.normSq (v i y) : ℝ) = 1 := by
    intro i
    have h := hv i i
    rw [if_pos rfl] at h
    have hc : ((∑ y, Complex.normSq (v i y) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum,
        Finset.sum_congr rfl (fun y _ => by
          rw [(Complex.mul_conj (v i y)).symm, mul_comm]), h]
    exact Complex.ofReal_inj.mp (hc.trans rfl)
  have htnorm : ∀ a : Fin D, (∑ y, Complex.normSq (t a y) : ℝ) = 1 := by
    intro a
    have h := ht a a
    rw [if_pos rfl] at h
    have hc : ((∑ y, Complex.normSq (t a y) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum,
        Finset.sum_congr rfl (fun y _ => by
          rw [(Complex.mul_conj (t a y)).symm, mul_comm]), h]
    exact Complex.ofReal_inj.mp (hc.trans rfl)
  have hτconj : ∀ (a : Fin D) (i : Fin r),
      Complex.normSq (∑ y, conj (t a y) * v i y)
        = Complex.normSq (∑ y, conj (v i y) * t a y) := by
    intro a i
    have hc : (∑ y, conj (v i y) * t a y) = conj (∑ y, conj (t a y) * v i y) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_mul]
      have hcc : conj (conj (t a y)) = t a y := by simp
      rw [hcc]
      ring
    rw [hc, Complex.normSq_conj]
  have hB1 : ∀ i : Fin r,
      (∑ a : Fin D, Complex.normSq (∑ y, conj (t a y) * v i y)) ≤ 1 := by
    intro i
    have hb := ortho_sum_normSq_le t (v i) ht
    rw [hvnorm i] at hb
    exact hb
  have hcountB : (∑ i : Fin r, ∑ a : Fin D,
      Complex.normSq (∑ y, conj (t a y) * v i y))
      ≤ (Fintype.card (Fin D) : ℝ) := by
    have hper : ∀ a : Fin D,
        (∑ i : Fin r, Complex.normSq (∑ y, conj (t a y) * v i y)) ≤ 1 := by
      intro a
      have hb := ortho_sum_normSq_le v (t a) hv
      rw [htnorm a] at hb
      exact le_trans (Finset.sum_le_sum fun i _ => (hτconj a i).le) hb
    calc (∑ i : Fin r, ∑ a : Fin D, Complex.normSq (∑ y, conj (t a y) * v i y))
        = ∑ a : Fin D, ∑ i : Fin r,
            Complex.normSq (∑ y, conj (t a y) * v i y) := Finset.sum_comm
      _ ≤ ∑ a : Fin D, (1 : ℝ) := Finset.sum_le_sum fun a _ => hper a
      _ = (Fintype.card (Fin D) : ℝ) := by simp
  have hcountcard : (∑ i : Fin r, ∑ a : Fin D,
      Complex.normSq (∑ y, conj (t a y) * v i y)) ≤ (T.card : ℝ) := by
    rw [hcard]
    have h2 : (Fintype.card (Fin D) : ℝ) = (D : ℝ) := by simp
    rw [h2] at hcountB
    exact hcountB
  have hratio := bessel_weight_ratio T jmin
    (fun i => Complex.normSq (c i))
    (fun i => ∑ a : Fin D, Complex.normSq (∑ y, conj (t a y) * v i y))
    (fun i => Complex.normSq_nonneg _) hmin hmax hB1
    (fun i => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) hcountcard
  linarith

theorem schmidt_multiTrunc_error_eq {α β : Type*} [Fintype α] [Fintype β] {r D : ℕ}
    (c : Fin r → ℂ) (u : Fin r → α → ℂ) (v : Fin r → β → ℂ)
    (hu : ∀ i j, ∑ x, conj (u i x) * u j x = if i = j then 1 else 0)
    (hv : ∀ i j, ∑ y, conj (v i y) * v j y = if i = j then 1 else 0)
    (e : Fin D → Fin r) (he : Function.Injective e) :
    ∑ p : α × β, Complex.normSq ((∑ i, c i * u i p.1 * v i p.2)
        - ∑ a : Fin D, c (e a) * u (e a) p.1 * v (e a) p.2)
      = ∑ i, Complex.normSq
          (if i ∈ Finset.image e Finset.univ then (0 : ℂ) else c i) := by
  have hkept : ∀ p : α × β, (∑ a : Fin D, c (e a) * u (e a) p.1 * v (e a) p.2)
      = ∑ i, (if i ∈ Finset.image e Finset.univ then c i else 0)
          * u i p.1 * v i p.2 := by
    intro p
    rw [← Finset.sum_image (f := fun i => c i * u i p.1 * v i p.2)
      (s := Finset.univ) (g := e) (he.injOn),
      ← Finset.sum_add_sum_compl (Finset.image e Finset.univ)
        (fun i => (if i ∈ Finset.image e Finset.univ then c i else 0)
          * u i p.1 * v i p.2)]
    have hzero : ∀ i ∈ (Finset.image e Finset.univ)ᶜ,
        ((if i ∈ Finset.image e Finset.univ then c i else 0) * u i p.1 * v i p.2)
          = 0 := by
      intro i hi
      rw [if_neg (Finset.mem_compl.mp hi), zero_mul, zero_mul]
    have hpos : ∀ i ∈ Finset.image e Finset.univ,
        ((if i ∈ Finset.image e Finset.univ then c i else 0) * u i p.1 * v i p.2)
          = c i * u i p.1 * v i p.2 := by
      intro i hi
      rw [if_pos hi]
    rw [Finset.sum_eq_zero hzero, Finset.sum_congr rfl hpos, add_zero]
  have hzero : ∀ p : α × β,
      (∑ i, c i * u i p.1 * v i p.2)
        - ∑ a : Fin D, c (e a) * u (e a) p.1 * v (e a) p.2
      = ∑ i, (if i ∈ Finset.image e Finset.univ then (0 : ℂ) else c i)
          * u i p.1 * v i p.2 := by
    intro p
    rw [hkept p, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ Finset.image e Finset.univ
    · rw [if_pos hi, if_pos hi, sub_self, zero_mul, zero_mul]
    · rw [if_neg hi, if_neg hi, zero_mul, zero_mul, sub_zero]
  rw [Finset.sum_congr rfl (fun p _ => by rw [hzero p]),
    schmidt_pair_normSq_eq
      (fun i => if i ∈ Finset.image e Finset.univ then (0 : ℂ) else c i) u v hu hv]

section PositionDesc

theorem fin_cast_val {m n : ℕ} (h : m = n) (x : Fin m) : (x.cast h).val = x.val := rfl

theorem fin_cast_cast {m n : ℕ} (h : m = n) (x : Fin m) :
    (x.cast h).cast h.symm = x := Fin.ext rfl

theorem fin_cast_cast' {m n : ℕ} (h : m = n) (x : Fin n) :
    (x.cast h.symm).cast h = x := Fin.ext rfl

theorem mpsSite_legs {n : ℕ} (i : ℕ) (hi : i < n) {j : Fin (3 * n + 2)}
    (hj : mpsSite n j = ⟨i, by omega⟩) :
    (j : ℕ) = 2 * i ∨ (j : ℕ) = 2 * i + 3 ∨ (j : ℕ) = 2 * (n + 1) + i := by
  simp only [mpsSite] at hj
  by_cases h1 : (j : ℕ) = 1
  · rw [if_pos h1] at hj
    have hval : n = i := congrArg Fin.val hj
    omega
  · rw [if_neg h1] at hj
    by_cases h2 : (j : ℕ) = 2 * n
    · rw [if_pos h2] at hj
      have hval : n + 1 = i := congrArg Fin.val hj
      omega
    · rw [if_neg h2] at hj
      by_cases h3 : (j : ℕ) < 2 * (n + 1)
      · rw [dif_pos h3] at hj
        by_cases h4 : (j : ℕ) % 2 = 0
        · rw [dif_pos h4] at hj
          left
          have hval : (j : ℕ) / 2 = i := congrArg Fin.val hj
          omega
        · rw [dif_neg h4] at hj
          right
          left
          have hval : ((j : ℕ) - 3) / 2 = i := congrArg Fin.val hj
          omega
      · rw [dif_neg h3] at hj
        right
        right
        have hval : (j : ℕ) - (2 * (n + 1)) = i := congrArg Fin.val hj
        omega

def mpsSitePos (n d D : ℕ) (i : ℕ) (hi : i < n) (l : Fin D) (r : Fin D) (x : Fin d) :
    ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨i, by omega⟩},
      Fin (mpsDim n d D h.val.val) :=
  fun h =>
    if hL : h.val.val = 2 * i then
      l.cast (by rw [hL]; exact (mpsDim_bond n d D (by omega : 2 * i < 2 * (n + 1))).symm)
    else if hR : h.val.val = 2 * i + 3 then
      r.cast (by rw [hR]; exact (mpsDim_bond n d D (by omega : 2 * i + 3 < 2 * (n + 1))).symm)
    else
      x.cast (by
        have he : h.val.val = 2 * (n + 1) + i := by
          rcases mpsSite_legs i hi h.property with h2 | h2 | h2 <;> omega
        rw [he]
        exact (mpsDim_phys n d D i (by omega)).symm)

theorem mpsSitePos_left_leg (n d D : ℕ) (i : ℕ) (hi : i < n) (l : Fin D) (r : Fin D)
    (x : Fin d) :
    mpsSitePos n d D i hi l r x ⟨⟨2 * i, by omega⟩, by rw [mpsSite_left n i hi]⟩
      = l.cast ((mpsDim_bond n d D (by omega : 2 * i < 2 * (n + 1))).symm) := by
  simp only [mpsSitePos]
  rw [dif_pos trivial]

theorem mpsSitePos_right_leg (n d D : ℕ) (i : ℕ) (hi : i < n) (l : Fin D) (r : Fin D)
    (x : Fin d) :
    mpsSitePos n d D i hi l r x ⟨⟨2 * i + 3, by omega⟩, by rw [mpsSite_right n i hi]⟩
      = r.cast ((mpsDim_bond n d D (by omega : 2 * i + 3 < 2 * (n + 1))).symm) := by
  simp only [mpsSitePos]
  rw [dif_neg (by omega), dif_pos trivial]

theorem mpsSitePos_phys_leg (n d D : ℕ) (i : ℕ) (hi : i < n) (l : Fin D) (r : Fin D)
    (x : Fin d) :
    mpsSitePos n d D i hi l r x ⟨⟨2 * (n + 1) + i, by omega⟩, by rw [mpsSite_phys n i hi]⟩
      = x.cast ((mpsDim_phys n d D i (by omega)).symm) := by
  simp only [mpsSitePos]
  rw [dif_neg (by omega), dif_neg (by omega)]

def mpsSitePosEquiv (n d D : ℕ) (i : ℕ) (hi : i < n) :
    (∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨i, by omega⟩},
      Fin (mpsDim n d D h.val.val)) ≃ (Fin D × Fin D) × Fin d where
  toFun a :=
    ⟨⟨(a ⟨⟨2 * i, by omega⟩, by rw [mpsSite_left n i hi]⟩).cast
        (mpsDim_bond n d D (by omega : 2 * i < 2 * (n + 1))),
      (a ⟨⟨2 * i + 3, by omega⟩, by rw [mpsSite_right n i hi]⟩).cast
        (mpsDim_bond n d D (by omega : 2 * i + 3 < 2 * (n + 1)))⟩,
      (a ⟨⟨2 * (n + 1) + i, by omega⟩, by rw [mpsSite_phys n i hi]⟩).cast
        (mpsDim_phys n d D i (by omega))⟩
  invFun t := mpsSitePos n d D i hi t.1.1 t.1.2 t.2
  left_inv a := by
    funext h
    by_cases hL : h.val.val = 2 * i
    · have hE : h = ⟨⟨2 * i, by omega⟩, by rw [mpsSite_left n i hi]⟩ :=
        Subtype.ext (Fin.ext hL)
      simp only [mpsSitePos]
      rw [dif_pos hL]
      apply Fin.ext
      exact (congrArg (fun h' => (a h').val) hE).symm
    · by_cases hR : h.val.val = 2 * i + 3
      · have hE : h = ⟨⟨2 * i + 3, by omega⟩, by rw [mpsSite_right n i hi]⟩ :=
          Subtype.ext (Fin.ext hR)
        simp only [mpsSitePos]
        rw [dif_neg hL, dif_pos hR]
        apply Fin.ext
        exact (congrArg (fun h' => (a h').val) hE).symm
      · have he : h.val.val = 2 * (n + 1) + i := by
          rcases mpsSite_legs i hi h.property with h2 | h2 | h2 <;> omega
        have hE : h = ⟨⟨2 * (n + 1) + i, by omega⟩, by rw [mpsSite_phys n i hi]⟩ :=
          Subtype.ext (Fin.ext he)
        simp only [mpsSitePos]
        rw [dif_neg hL, dif_neg hR]
        apply Fin.ext
        exact (congrArg (fun h' => (a h').val) hE).symm
  right_inv t := by
    obtain ⟨⟨l, r⟩, x⟩ := t
    show (((mpsSitePos n d D i hi l r x ⟨⟨2 * i, by omega⟩, by rw [mpsSite_left n i hi]⟩).cast _,
          (mpsSitePos n d D i hi l r x ⟨⟨2 * i + 3, by omega⟩, by rw [mpsSite_right n i hi]⟩).cast _),
          (mpsSitePos n d D i hi l r x
            ⟨⟨2 * (n + 1) + i, by omega⟩, by rw [mpsSite_phys n i hi]⟩).cast _) = ((l, r), x)
    rw [mpsSitePos_left_leg, mpsSitePos_right_leg, mpsSitePos_phys_leg,
      fin_cast_cast', fin_cast_cast', fin_cast_cast']

theorem mpsTensor_site_read {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : ℕ) (hi : i < n) (l : Fin D) (r : Fin D) (x : Fin d) :
    (mpsNet n d D A).tensor ⟨i, by show i < n + 2; omega⟩ (mpsSitePosEquiv n d D i hi |>.symm ((l, r), x))
      = A ⟨i, hi⟩ x l r := by
  show mpsTensor n d D A ⟨i, by omega⟩ (mpsSitePos n d D i hi l r x) = _
  rw [mpsTensor, dif_pos hi]
  show A ⟨i, hi⟩
      (Fin.cast (mpsDim_phys n d D i (by omega))
        (mpsSitePos n d D i hi l r x
          ⟨⟨2 * (n + 1) + i, by omega⟩, by rw [mpsSite_phys n i hi]⟩))
      (Fin.cast (mpsDim_bond n d D (by omega : 2 * i < 2 * (n + 1)))
        (mpsSitePos n d D i hi l r x
          ⟨⟨2 * i, by omega⟩, by rw [mpsSite_left n i hi]⟩))
      (Fin.cast (mpsDim_bond n d D (by omega : 2 * i + 3 < 2 * (n + 1)))
        (mpsSitePos n d D i hi l r x
          ⟨⟨2 * i + 3, by omega⟩, by rw [mpsSite_right n i hi]⟩))
      = A ⟨i, hi⟩ x l r
  rw [mpsSitePos_phys_leg, mpsSitePos_left_leg, mpsSitePos_right_leg,
    fin_cast_cast', fin_cast_cast', fin_cast_cast']

theorem mpsTensor_site_read' {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : ℕ) (hi : i < n) (t : (Fin D × Fin D) × Fin d) :
    (mpsNet n d D A).tensor ⟨i, by show i < n + 2; omega⟩ (mpsSitePosEquiv n d D i hi |>.symm t)
      = A ⟨i, hi⟩ t.2 t.1.1 t.1.2 := by
  obtain ⟨⟨l, r⟩, x⟩ := t
  exact mpsTensor_site_read A i hi l r x

theorem tensorSumNorm_mpsNet_site {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (i : ℕ) (hi : i < n) :
    tensorSumNorm (mpsNet n d D A) ⟨i, by show i < n + 2; omega⟩
      = ∑ l : Fin D, ∑ r : Fin D, ∑ x : Fin d, ‖A ⟨i, hi⟩ x l r‖ := by
  show ∑ a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨i, by omega⟩},
      Fin (mpsDim n d D h.val.val), ‖(mpsNet n d D A).tensor ⟨i, by show i < n + 2; omega⟩ a‖ = _
  have hvals : ∀ a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨i, by omega⟩},
      Fin (mpsDim n d D h.val.val),
      ‖(mpsNet n d D A).tensor ⟨i, by show i < n + 2; omega⟩ a‖
        = ‖A ⟨i, hi⟩ ((mpsSitePosEquiv n d D i hi) a).2
            ((mpsSitePosEquiv n d D i hi) a).1.1
            ((mpsSitePosEquiv n d D i hi) a).1.2‖ := by
    intro a
    rw [← (mpsSitePosEquiv n d D i hi).symm_apply_apply a, Equiv.apply_symm_apply,
      mpsTensor_site_read' A i hi ((mpsSitePosEquiv n d D i hi) a)]
  rw [Fintype.sum_equiv (mpsSitePosEquiv n d D i hi)
    (fun a => ‖(mpsNet n d D A).tensor ⟨i, by show i < n + 2; omega⟩ a‖)
    (fun t => ‖A ⟨i, hi⟩ t.2 t.1.1 t.1.2‖) hvals,
    Fintype.sum_prod_type, Fintype.sum_prod_type]

theorem mpsSite_capL_leg {n : ℕ} {j : Fin (3 * n + 2)}
    (hj : mpsSite n j = ⟨n, by omega⟩) : (j : ℕ) = 1 := by
  simp only [mpsSite] at hj
  by_cases h1 : (j : ℕ) = 1
  · exact h1
  · rw [if_neg h1] at hj
    by_cases h2 : (j : ℕ) = 2 * n
    · rw [if_pos h2] at hj
      have hval : n + 1 = n := congrArg Fin.val hj
      omega
    · rw [if_neg h2] at hj
      by_cases h3 : (j : ℕ) < 2 * (n + 1)
      · rw [dif_pos h3] at hj
        by_cases h4 : (j : ℕ) % 2 = 0
        · rw [dif_pos h4] at hj
          have hval : (j : ℕ) / 2 = n := congrArg Fin.val hj
          omega
        · rw [dif_neg h4] at hj
          have hval : ((j : ℕ) - 3) / 2 = n := congrArg Fin.val hj
          omega
      · rw [dif_neg h3] at hj
        have hval : (j : ℕ) - (2 * (n + 1)) = n := congrArg Fin.val hj
        omega

theorem mpsSite_capR_leg {n : ℕ} {j : Fin (3 * n + 2)}
    (hj : mpsSite n j = ⟨n + 1, by omega⟩) : (j : ℕ) = 2 * n := by
  simp only [mpsSite] at hj
  by_cases h1 : (j : ℕ) = 1
  · rw [if_pos h1] at hj
    have hval : n = n + 1 := congrArg Fin.val hj
    omega
  · rw [if_neg h1] at hj
    by_cases h2 : (j : ℕ) = 2 * n
    · exact h2
    · rw [if_neg h2] at hj
      by_cases h3 : (j : ℕ) < 2 * (n + 1)
      · rw [dif_pos h3] at hj
        by_cases h4 : (j : ℕ) % 2 = 0
        · rw [dif_pos h4] at hj
          have hval : (j : ℕ) / 2 = n + 1 := congrArg Fin.val hj
          omega
        · rw [dif_neg h4] at hj
          have hval : ((j : ℕ) - 3) / 2 = n + 1 := congrArg Fin.val hj
          omega
      · rw [dif_neg h3] at hj
        have hval : (j : ℕ) - (2 * (n + 1)) = n + 1 := congrArg Fin.val hj
        omega

def mpsCapLPos (n d D : ℕ) (k : Fin D) :
    ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n, by omega⟩},
      Fin (mpsDim n d D h.val.val) :=
  fun h => k.cast (by
    have h1 := mpsSite_capL_leg h.property
    rw [h1]
    exact (mpsDim_bond n d D (by omega : 1 < 2 * (n + 1))).symm)

def mpsCapLPosEquiv (n d D : ℕ) :
    (∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n, by omega⟩},
      Fin (mpsDim n d D h.val.val)) ≃ Fin D where
  toFun a :=
    (a ⟨⟨1, by omega⟩, by rw [mpsSite_capL n]⟩).cast
      (mpsDim_bond n d D (by omega : 1 < 2 * (n + 1)))
  invFun k := mpsCapLPos n d D k
  left_inv a := by
    funext h
    have he : h.val.val = 1 := mpsSite_capL_leg h.property
    have hE : h = ⟨⟨1, by omega⟩, by rw [mpsSite_capL n]⟩ := Subtype.ext (Fin.ext he)
    rw [hE]
    rfl
  right_inv k := by
    show (mpsCapLPos n d D k ⟨⟨1, by omega⟩, by rw [mpsSite_capL n]⟩).cast
      (mpsDim_bond n d D (by omega : 1 < 2 * (n + 1))) = k
    rfl

theorem mpsCapLTensor_read {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) :
    (mpsNet n d D A).tensor ⟨n, by show n < n + 2; omega⟩ (mpsCapLPosEquiv n d D |>.symm k)
      = if (k : ℕ) = 0 then (1 : ℂ) else 0 := by
  show mpsTensor n d D A ⟨n, by omega⟩ (mpsCapLPos n d D k) = _
  rw [mpsTensor, dif_neg (by show ¬(n < n); omega), dif_pos (by show n = n; omega)]
  show (if (mpsCapLPos n d D k ⟨⟨1, by omega⟩, by rw [mpsSite_capL n]⟩).val = 0
      then (1 : ℂ) else 0) = if (k : ℕ) = 0 then (1 : ℂ) else 0
  have hval : (mpsCapLPos n d D k ⟨⟨1, by omega⟩, by rw [mpsSite_capL n]⟩).val = (k : ℕ) := rfl
  rw [hval]

theorem tensorSumNorm_mpsNet_capL {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    tensorSumNorm (mpsNet n d D A) ⟨n, by show n < n + 2; omega⟩ = 1 := by
  show ∑ a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n, by omega⟩},
      Fin (mpsDim n d D h.val.val), ‖(mpsNet n d D A).tensor ⟨n, by show n < n + 2; omega⟩ a‖ = 1
  have hvals : ∀ a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n, by omega⟩},
      Fin (mpsDim n d D h.val.val),
      ‖(mpsNet n d D A).tensor ⟨n, by show n < n + 2; omega⟩ a‖
        = ‖if ((mpsCapLPosEquiv n d D) a : ℕ) = 0 then (1 : ℂ) else 0‖ := by
    intro a
    rw [← (mpsCapLPosEquiv n d D).symm_apply_apply a, Equiv.apply_symm_apply,
      mpsCapLTensor_read A ((mpsCapLPosEquiv n d D) a)]
  rw [Fintype.sum_equiv (mpsCapLPosEquiv n d D)
    (fun a => ‖(mpsNet n d D A).tensor ⟨n, by show n < n + 2; omega⟩ a‖)
    (fun k => ‖if (k : ℕ) = 0 then (1 : ℂ) else 0‖) hvals]
  rw [Finset.sum_eq_single_of_mem (0 : Fin D) (Finset.mem_univ 0) ?_]
  · rw [if_pos (by simp), norm_one]
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext (h.trans (Fin.val_zero D).symm))), norm_zero]

def mpsCapRPos (n d D : ℕ) (k : Fin D) :
    ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n + 1, by omega⟩},
      Fin (mpsDim n d D h.val.val) :=
  fun h => k.cast (by
    have h2 := mpsSite_capR_leg h.property
    rw [h2]
    exact (mpsDim_bond n d D (by omega : 2 * n < 2 * (n + 1))).symm)

def mpsCapRPosEquiv (n d D : ℕ) :
    (∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n + 1, by omega⟩},
      Fin (mpsDim n d D h.val.val)) ≃ Fin D where
  toFun a :=
    (a ⟨⟨2 * n, by omega⟩, by rw [mpsSite_capR n]⟩).cast
      (mpsDim_bond n d D (by omega : 2 * n < 2 * (n + 1)))
  invFun k := mpsCapRPos n d D k
  left_inv a := by
    funext h
    have he : h.val.val = 2 * n := mpsSite_capR_leg h.property
    have hE : h = ⟨⟨2 * n, by omega⟩, by rw [mpsSite_capR n]⟩ := Subtype.ext (Fin.ext he)
    rw [hE]
    rfl
  right_inv k := by
    show (mpsCapRPos n d D k ⟨⟨2 * n, by omega⟩, by rw [mpsSite_capR n]⟩).cast
      (mpsDim_bond n d D (by omega : 2 * n < 2 * (n + 1))) = k
    rfl

theorem mpsCapRTensor_read {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) :
    (mpsNet n d D A).tensor ⟨n + 1, by show n + 1 < n + 2; omega⟩ (mpsCapRPosEquiv n d D |>.symm k)
      = if (k : ℕ) = 0 then (1 : ℂ) else 0 := by
  show mpsTensor n d D A ⟨n + 1, by omega⟩ (mpsCapRPos n d D k) = _
  rw [mpsTensor, dif_neg (by show ¬(n + 1 < n); omega), dif_neg (by show ¬(n + 1 = n); omega)]
  show (if (mpsCapRPos n d D k ⟨⟨2 * n, by omega⟩, by rw [mpsSite_capR n]⟩).val = 0
      then (1 : ℂ) else 0) = if (k : ℕ) = 0 then (1 : ℂ) else 0
  have hval : (mpsCapRPos n d D k ⟨⟨2 * n, by omega⟩, by rw [mpsSite_capR n]⟩).val = (k : ℕ) := rfl
  rw [hval]

theorem tensorSumNorm_mpsNet_capR {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    tensorSumNorm (mpsNet n d D A) ⟨n + 1, by show n + 1 < n + 2; omega⟩ = 1 := by
  show ∑ a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n + 1, by omega⟩},
      Fin (mpsDim n d D h.val.val), ‖(mpsNet n d D A).tensor ⟨n + 1, by show n + 1 < n + 2; omega⟩ a‖ = 1
  have hvals : ∀ a : ∀ h : {h : Fin (3 * n + 2) // mpsSite n h = ⟨n + 1, by omega⟩},
      Fin (mpsDim n d D h.val.val),
      ‖(mpsNet n d D A).tensor ⟨n + 1, by show n + 1 < n + 2; omega⟩ a‖
        = ‖if ((mpsCapRPosEquiv n d D) a : ℕ) = 0 then (1 : ℂ) else 0‖ := by
    intro a
    rw [← (mpsCapRPosEquiv n d D).symm_apply_apply a, Equiv.apply_symm_apply,
      mpsCapRTensor_read A ((mpsCapRPosEquiv n d D) a)]
  rw [Fintype.sum_equiv (mpsCapRPosEquiv n d D)
    (fun a => ‖(mpsNet n d D A).tensor ⟨n + 1, by show n + 1 < n + 2; omega⟩ a‖)
    (fun k => ‖if (k : ℕ) = 0 then (1 : ℂ) else 0‖) hvals]
  rw [Finset.sum_eq_single_of_mem (0 : Fin D) (Finset.mem_univ 0) ?_]
  · rw [if_pos (by simp), norm_one]
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext (h.trans (Fin.val_zero D).symm))), norm_zero]

theorem prod_tensorSumNorm_mpsNet_eq {n d D : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∏ v : Fin (n + 2), tensorSumNorm (mpsNet n d D A) v
      = ∏ i : Fin n,
          (∑ l : Fin D, ∑ r : Fin D, ∑ x : Fin d, ‖A ⟨(i : ℕ), i.isLt⟩ x l r‖) := by
  have hcapL : tensorSumNorm (mpsNet n d D A) (Fin.castSucc (Fin.last n)) = 1 :=
    tensorSumNorm_mpsNet_capL A
  have hcapR : tensorSumNorm (mpsNet n d D A) (Fin.last (n + 1)) = 1 :=
    tensorSumNorm_mpsNet_capR A
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, hcapL, hcapR, mul_one, mul_one]
  exact Finset.prod_congr rfl fun i _ => tensorSumNorm_mpsNet_site A (i : ℕ) i.isLt

theorem perSite_legs {n : ℕ} [NeZero n] (v : Fin n) {j : Fin (3 * n)}
    (hj : perSite n j = v) :
    (j : ℕ) = 2 * (v : ℕ) ∨ (j : ℕ) = 2 * (((v : ℕ) + 1) % n) + 1
      ∨ (j : ℕ) = 2 * n + (v : ℕ) := by
  simp only [perSite] at hj
  by_cases h3 : (j : ℕ) < 2 * n
  · rw [dif_pos h3] at hj
    by_cases h4 : (j : ℕ) % 2 = 0
    · rw [if_pos h4] at hj
      left
      have hval : (j : ℕ) / 2 = (v : ℕ) := congrArg Fin.val hj
      omega
    · rw [if_neg h4] at hj
      have hval : ((j : ℕ) / 2 + n - 1) % n = (v : ℕ) := congrArg Fin.val hj
      have hk : (j : ℕ) / 2 < n := by omega
      right
      left
      have hlt : (v : ℕ) + 1 < n ∨ (v : ℕ) + 1 = n := by omega
      rcases hlt with hlt | hlt
      · have hvm : ((v : ℕ) + 1) % n = (v : ℕ) + 1 := Nat.mod_eq_of_lt hlt
        rcases Nat.eq_zero_or_pos ((j : ℕ) / 2) with h0 | h0
        · rw [h0, Nat.zero_add] at hval
          rw [Nat.mod_eq_of_lt (show n - 1 < n by omega)] at hval
          omega
        · have hkn : (j : ℕ) / 2 + n - 1 = ((j : ℕ) / 2 - 1) + n := by omega
          rw [hkn, Nat.add_mod, Nat.mod_self, Nat.add_zero,
            Nat.mod_eq_of_lt (show (j : ℕ) / 2 - 1 < n by omega),
            Nat.mod_eq_of_lt (show (j : ℕ) / 2 - 1 < n by omega)] at hval
          rw [hvm]
          omega
      · have hvm : ((v : ℕ) + 1) % n = 0 := by rw [hlt, Nat.mod_self]
        rcases Nat.eq_zero_or_pos ((j : ℕ) / 2) with h0 | h0
        · rw [h0, Nat.zero_add] at hval
          rw [Nat.mod_eq_of_lt (show n - 1 < n by omega)] at hval
          rw [hvm]
          omega
        · have hkn : (j : ℕ) / 2 + n - 1 = ((j : ℕ) / 2 - 1) + n := by omega
          rw [hkn, Nat.add_mod, Nat.mod_self, Nat.add_zero,
            Nat.mod_eq_of_lt (show (j : ℕ) / 2 - 1 < n by omega),
            Nat.mod_eq_of_lt (show (j : ℕ) / 2 - 1 < n by omega)] at hval
          rw [hvm]
          omega
  · rw [dif_neg h3] at hj
    right
    right
    have hval : (j : ℕ) - 2 * n = (v : ℕ) := congrArg Fin.val hj
    omega

def perSitePos (n d D : ℕ) [NeZero n] (v : Fin n) (l : Fin D) (r : Fin D) (x : Fin d) :
    ∀ h : {h : Fin (3 * n) // perSite n h = v}, Fin (perDim n d D h.val.val) :=
  fun h =>
    if hL : h.val.val = 2 * (v : ℕ) then
      l.cast (by rw [hL]; exact (perDim_bond n d D (by omega : 2 * (v : ℕ) < 2 * n)).symm)
    else if hR : h.val.val = 2 * (((v : ℕ) + 1) % n) + 1 then
      r.cast (by
        rw [hR]
        exact (perDim_bond n d D (by
          have := Nat.mod_lt ((v : ℕ) + 1) (NeZero.pos n)
          omega)).symm)
    else
      x.cast (by
        have he : h.val.val = 2 * n + (v : ℕ) := by
          rcases perSite_legs v h.property with h2 | h2 | h2 <;> omega
        rw [he]
        exact (perDim_phys n d D (by omega)).symm)

theorem perSitePos_left_leg (n d D : ℕ) [NeZero n] (v : Fin n) (l : Fin D) (r : Fin D) (x : Fin d) :
    perSitePos n d D v l r x ⟨⟨2 * (v : ℕ), by omega⟩, by rw [perSite_left n (v : ℕ) v.isLt]⟩
      = l.cast ((perDim_bond n d D (by omega : 2 * (v : ℕ) < 2 * n)).symm) := by
  simp only [perSitePos]
  rw [dif_pos trivial]

theorem perSitePos_right_leg (n d D : ℕ) [NeZero n] (v : Fin n) (l : Fin D) (r : Fin D) (x : Fin d) :
    perSitePos n d D v l r x
        ⟨⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩,
          by rw [perSite_right' n (v : ℕ) v.isLt (NeZero.pos n)]⟩
      = r.cast ((perDim_bond n d D (by
          have := Nat.mod_lt ((v : ℕ) + 1) (NeZero.pos n)
          show 2 * (((v : ℕ) + 1) % n) + 1 < 2 * n
          omega)).symm) := by
  simp only [perSitePos]
  rw [dif_neg (by
        show 2 * (((v : ℕ) + 1) % n) + 1 ≠ 2 * (v : ℕ)
        have := Nat.mod_lt ((v : ℕ) + 1) (NeZero.pos n)
        omega), dif_pos trivial]

theorem perSitePos_phys_leg (n d D : ℕ) [NeZero n] (v : Fin n) (l : Fin D) (r : Fin D) (x : Fin d) :
    perSitePos n d D v l r x ⟨⟨2 * n + (v : ℕ), by omega⟩, by rw [perSite_phys n (v : ℕ) v.isLt]⟩
      = x.cast ((perDim_phys n d D (by
          show ¬(2 * n + (v : ℕ) < 2 * n)
          omega)).symm) := by
  simp only [perSitePos]
  rw [dif_neg (by show 2 * n + (v : ℕ) ≠ 2 * (v : ℕ); omega),
    dif_neg (by
      show 2 * n + (v : ℕ) ≠ 2 * (((v : ℕ) + 1) % n) + 1
      have := Nat.mod_lt ((v : ℕ) + 1) (NeZero.pos n)
      omega)]

def perSitePosEquiv (n d D : ℕ) [NeZero n] (v : Fin n) :
    (∀ h : {h : Fin (3 * n) // perSite n h = v}, Fin (perDim n d D h.val.val))
      ≃ (Fin D × Fin D) × Fin d where
  toFun a :=
    ⟨⟨(a ⟨⟨2 * (v : ℕ), by omega⟩, by rw [perSite_left n (v : ℕ) v.isLt]⟩).cast
        (perDim_bond n d D (by omega : 2 * (v : ℕ) < 2 * n)),
      (a ⟨⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩,
          by rw [perSite_right' n (v : ℕ) v.isLt (NeZero.pos n)]⟩).cast
        (perDim_bond n d D (by
          have := Nat.mod_lt ((v : ℕ) + 1) (NeZero.pos n)
          show 2 * (((v : ℕ) + 1) % n) + 1 < 2 * n
          omega))⟩,
      (a ⟨⟨2 * n + (v : ℕ), by omega⟩, by rw [perSite_phys n (v : ℕ) v.isLt]⟩).cast
        (perDim_phys n d D (by
          show ¬(2 * n + (v : ℕ) < 2 * n)
          omega))⟩
  invFun t := perSitePos n d D v t.1.1 t.1.2 t.2
  left_inv a := by
    funext h
    by_cases hL : h.val.val = 2 * (v : ℕ)
    · have hE : h = ⟨⟨2 * (v : ℕ), by omega⟩, by rw [perSite_left n (v : ℕ) v.isLt]⟩ :=
        Subtype.ext (Fin.ext hL)
      simp only [perSitePos]
      rw [dif_pos hL]
      apply Fin.ext
      exact (congrArg (fun h' => (a h').val) hE).symm
    · by_cases hR : h.val.val = 2 * (((v : ℕ) + 1) % n) + 1
      · have hE : h = ⟨⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩,
            by rw [perSite_right' n (v : ℕ) v.isLt (NeZero.pos n)]⟩ :=
          Subtype.ext (Fin.ext hR)
        simp only [perSitePos]
        rw [dif_neg hL, dif_pos hR]
        apply Fin.ext
        exact (congrArg (fun h' => (a h').val) hE).symm
      · have he : h.val.val = 2 * n + (v : ℕ) := by
          rcases perSite_legs v h.property with h2 | h2 | h2 <;> omega
        have hE : h = ⟨⟨2 * n + (v : ℕ), by omega⟩, by rw [perSite_phys n (v : ℕ) v.isLt]⟩ :=
          Subtype.ext (Fin.ext he)
        simp only [perSitePos]
        rw [dif_neg hL, dif_neg hR]
        apply Fin.ext
        exact (congrArg (fun h' => (a h').val) hE).symm
  right_inv t := by
    obtain ⟨⟨l, r⟩, x⟩ := t
    show (((perSitePos n d D v l r x
          ⟨⟨2 * (v : ℕ), by omega⟩, by rw [perSite_left n (v : ℕ) v.isLt]⟩).cast _,
        (perSitePos n d D v l r x
          ⟨⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩,
            by rw [perSite_right' n (v : ℕ) v.isLt (NeZero.pos n)]⟩).cast _),
        (perSitePos n d D v l r x
          ⟨⟨2 * n + (v : ℕ), by omega⟩, by rw [perSite_phys n (v : ℕ) v.isLt]⟩).cast _)
      = ((l, r), x)
    rw [perSitePos_left_leg, perSitePos_right_leg, perSitePos_phys_leg,
      fin_cast_cast', fin_cast_cast', fin_cast_cast']

theorem perTensor_read {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (v : Fin n) (l : Fin D) (r : Fin D)
    (x : Fin d) :
    (perNet n d D A).tensor v (perSitePosEquiv n d D v |>.symm ((l, r), x))
      = A v x l r := by
  show perTensor n d D A v (perSitePos n d D v l r x) = _
  show A v
      (Fin.cast (perDim_phys n d D (by show ¬(2 * n + (v : ℕ) < 2 * n); omega))
        (perSitePos n d D v l r x
          ⟨⟨2 * n + (v : ℕ), by omega⟩, by rw [perSite_phys n (v : ℕ) v.isLt]⟩))
      (Fin.cast (perDim_bond n d D (by show 2 * (v : ℕ) < 2 * n; have := v.isLt; omega))
        (perSitePos n d D v l r x
          ⟨⟨2 * (v : ℕ), by omega⟩, by rw [perSite_left n (v : ℕ) v.isLt]⟩))
      (Fin.cast (perDim_bond n d D (by
          have := Nat.mod_lt ((v : ℕ) + 1) (NeZero.pos n)
          show 2 * (((v : ℕ) + 1) % n) + 1 < 2 * n
          omega))
        (perSitePos n d D v l r x
          ⟨⟨2 * (((v : ℕ) + 1) % n) + 1, perLeg_bound n v⟩,
            by rw [perSite_right' n (v : ℕ) v.isLt (NeZero.pos n)]⟩))
      = A v x l r
  rw [perSitePos_phys_leg, perSitePos_left_leg, perSitePos_right_leg,
    fin_cast_cast', fin_cast_cast', fin_cast_cast']

theorem perTensor_read' {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (v : Fin n)
    (t : (Fin D × Fin D) × Fin d) :
    (perNet n d D A).tensor v (perSitePosEquiv n d D v |>.symm t)
      = A v t.2 t.1.1 t.1.2 := by
  obtain ⟨⟨l, r⟩, x⟩ := t
  exact perTensor_read A v l r x

theorem tensorSumNorm_perNet_site {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (v : Fin n) :
    tensorSumNorm (perNet n d D A) v = ∑ l : Fin D, ∑ r : Fin D, ∑ x : Fin d, ‖A v x l r‖ := by
  show ∑ a : ∀ h : {h : Fin (3 * n) // perSite n h = v},
      Fin (perDim n d D h.val.val), ‖(perNet n d D A).tensor v a‖ = _
  have hvals : ∀ a : ∀ h : {h : Fin (3 * n) // perSite n h = v},
      Fin (perDim n d D h.val.val),
      ‖(perNet n d D A).tensor v a‖
        = ‖A v ((perSitePosEquiv n d D v) a).2
            ((perSitePosEquiv n d D v) a).1.1 ((perSitePosEquiv n d D v) a).1.2‖ := by
    intro a
    rw [← (perSitePosEquiv n d D v).symm_apply_apply a, Equiv.apply_symm_apply,
      perTensor_read' A v ((perSitePosEquiv n d D v) a)]
  rw [Fintype.sum_equiv (perSitePosEquiv n d D v)
    (fun a => ‖(perNet n d D A).tensor v a‖)
    (fun t => ‖A v t.2 t.1.1 t.1.2‖) hvals,
    Fintype.sum_prod_type, Fintype.sum_prod_type]

theorem pepsSite_legs_mem {a b : ℕ} (v : Fin (a * b)) {j : Fin (pepsNh a b)}
    (hj : pepsSite a b j = v) :
    (∃ r, r < 5 ∧ (j : ℕ) = 5 * (v : ℕ) + r) ∨ 5 * a * b ≤ (j : ℕ) := by
  simp only [pepsSite] at hj
  by_cases hz : a = 0 ∨ b = 0
  · rcases hz with h | h
    · subst h
      exact absurd v.isLt (by omega)
    · subst h
      exact absurd v.isLt (by omega)
  · rw [dif_neg hz] at hj
    by_cases hreg : (j : ℕ) < 5 * a * b
    · rw [dif_pos hreg] at hj
      left
      have hval : (j : ℕ) / 5 = (v : ℕ) := congrArg Fin.val hj
      refine ⟨(j : ℕ) % 5, Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (j : ℕ) 5
      omega
    · rw [dif_neg hreg] at hj
      right
      omega

def pepsDummyLegs (a b : ℕ) (v : Fin (a * b)) : Type :=
  {j : Fin (pepsNh a b) // 5 * a * b ≤ (j : ℕ) ∧ pepsSite a b j = v}

instance (a b : ℕ) (v : Fin (a * b)) : Fintype (pepsDummyLegs a b v) :=
  Subtype.fintype _

instance (a b : ℕ) (v : Fin (a * b)) : DecidableEq (pepsDummyLegs a b v) :=
  fun x y =>
    if h : x.val = y.val then isTrue (Subtype.ext h)
    else isFalse (fun hc => h (congrArg Subtype.val hc))

def pepsSitePos (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    ∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v}, Fin (pepsDim a b d D h.val.val) :=
  fun h =>
    if h0 : h.val.val = 5 * (v : ℕ) then
      x.cast (by
        rw [h0]
        exact (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
          (pepsLeg_mod (v : ℕ) 0 (by omega))).symm)
    else if h1 : h.val.val = 5 * (v : ℕ) + 1 then
      l.cast (by
        rw [h1]
        exact (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega)).symm)
    else if h2 : h.val.val = 5 * (v : ℕ) + 2 then
      r.cast (by
        rw [h2]
        exact (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega)).symm)
    else if h3 : h.val.val = 5 * (v : ℕ) + 3 then
      dn.cast (by
        rw [h3]
        exact (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega)).symm)
    else if h4 : h.val.val = 5 * (v : ℕ) + 4 then
      up.cast (by
        rw [h4]
        exact (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega)).symm)
    else
      (m ⟨h.val, ⟨by
          rcases pepsSite_legs_mem v h.property with ⟨r, hr, he⟩ | hge
          · omega
          · exact hge, h.property⟩⟩).cast (by
        rcases pepsSite_legs_mem v h.property with ⟨r, hr, he⟩ | hge
        · omega
        · exact (pepsDim_dummy a b d D hge).symm)

theorem pepsSitePos_phys_leg (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    pepsSitePos a b d D v x l r dn up m
        ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩,
          pepsSite_leg a b v 0 (by omega)⟩
      = x.cast (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
          (pepsLeg_mod (v : ℕ) 0 (by omega))).symm := by
  simp only [pepsSitePos]
  rw [dif_pos trivial]

theorem pepsSitePos_left_leg (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    pepsSitePos a b d D v x l r dn up m
        ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
          pepsSite_leg a b v 1 (by omega)⟩
      = l.cast (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega)).symm := by
  simp only [pepsSitePos]
  rw [dif_neg (by omega), dif_pos trivial]

theorem pepsSitePos_right_leg (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    pepsSitePos a b d D v x l r dn up m
        ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
          pepsSite_leg a b v 2 (by omega)⟩
      = r.cast (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega)).symm := by
  simp only [pepsSitePos]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos trivial]

theorem pepsSitePos_down_leg (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    pepsSitePos a b d D v x l r dn up m
        ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
          pepsSite_leg a b v 3 (by omega)⟩
      = dn.cast (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega)).symm := by
  simp only [pepsSitePos]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos trivial]

theorem pepsSitePos_up_leg (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    pepsSitePos a b d D v x l r dn up m
        ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
          pepsSite_leg a b v 4 (by omega)⟩
      = up.cast (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega)).symm := by
  simp only [pepsSitePos]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
    dif_pos trivial]

theorem pepsSitePos_dummy_leg (a b d D : ℕ) (v : Fin (a * b)) (x : Fin d) (l r dn up : Fin D)
    (m : ∀ _h : pepsDummyLegs a b v, Fin D) (h' : pepsDummyLegs a b v) :
    pepsSitePos a b d D v x l r dn up m ⟨h'.val, h'.property.2⟩
      = (m h').cast (pepsDim_dummy a b d D h'.property.1).symm := by
  have hlt0 := pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega)
  have hlt1 := pepsLeg_lt a b (v : ℕ) 1 v.isLt (by omega)
  have hlt2 := pepsLeg_lt a b (v : ℕ) 2 v.isLt (by omega)
  have hlt3 := pepsLeg_lt a b (v : ℕ) 3 v.isLt (by omega)
  have hlt4 := pepsLeg_lt a b (v : ℕ) 4 v.isLt (by omega)
  have hge := h'.property.1
  simp only [pepsSitePos]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
    dif_neg (by omega)]
  rfl

def pepsSitePosEquiv (a b d D : ℕ) (v : Fin (a * b)) :
    (∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v}, Fin (pepsDim a b d D h.val.val))
      ≃ (Fin d × Fin D × Fin D × Fin D × Fin D) × (∀ _h : pepsDummyLegs a b v, Fin D) where
  toFun α :=
    ⟨⟨(α ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩,
              pepsSite_leg a b v 0 (by omega)⟩).cast
          (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
            (pepsLeg_mod (v : ℕ) 0 (by omega))),
      (α ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
          pepsSite_leg a b v 1 (by omega)⟩).cast
        (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega)),
      (α ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
          pepsSite_leg a b v 2 (by omega)⟩).cast
        (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega)),
      (α ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
          pepsSite_leg a b v 3 (by omega)⟩).cast
        (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega)),
      (α ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
          pepsSite_leg a b v 4 (by omega)⟩).cast
        (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))⟩,
      fun h => (α ⟨h.val, h.property.2⟩).cast (pepsDim_dummy a b d D h.property.1)⟩
  invFun t := pepsSitePos a b d D v t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2 t.2
  left_inv α := by
    funext h
    by_cases h0 : h.val.val = 5 * (v : ℕ)
    · have hE : h = ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩,
          pepsSite_leg a b v 0 (by omega)⟩ := Subtype.ext (Fin.ext h0)
      simp only [pepsSitePos]
      rw [dif_pos h0]
      apply Fin.ext
      exact (congrArg (fun h' => (α h').val) hE).symm
    · by_cases h1 : h.val.val = 5 * (v : ℕ) + 1
      · have hE : h = ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
            pepsSite_leg a b v 1 (by omega)⟩ := Subtype.ext (Fin.ext h1)
        simp only [pepsSitePos]
        rw [dif_neg h0, dif_pos h1]
        apply Fin.ext
        exact (congrArg (fun h' => (α h').val) hE).symm
      · by_cases h2 : h.val.val = 5 * (v : ℕ) + 2
        · have hE : h = ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
              pepsSite_leg a b v 2 (by omega)⟩ := Subtype.ext (Fin.ext h2)
          simp only [pepsSitePos]
          rw [dif_neg h0, dif_neg h1, dif_pos h2]
          apply Fin.ext
          exact (congrArg (fun h' => (α h').val) hE).symm
        · by_cases h3 : h.val.val = 5 * (v : ℕ) + 3
          · have hE : h = ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
                pepsSite_leg a b v 3 (by omega)⟩ := Subtype.ext (Fin.ext h3)
            simp only [pepsSitePos]
            rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_pos h3]
            apply Fin.ext
            exact (congrArg (fun h' => (α h').val) hE).symm
          · by_cases h4 : h.val.val = 5 * (v : ℕ) + 4
            · have hE : h = ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
                  pepsSite_leg a b v 4 (by omega)⟩ := Subtype.ext (Fin.ext h4)
              simp only [pepsSitePos]
              rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
              apply Fin.ext
              exact (congrArg (fun h' => (α h').val) hE).symm
            · have hge : 5 * a * b ≤ h.val.val := by
                rcases pepsSite_legs_mem v h.property with ⟨r, hr, he⟩ | hge
                · omega
                · exact hge
              simp only [pepsSitePos]
              rw [dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]
              apply Fin.ext
              rfl
  right_inv t := by
    obtain ⟨⟨x, l, r, dn, up⟩, m⟩ := t
    show ((⟨(pepsSitePos a b d D v x l r dn up m
              ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩,
                pepsSite_leg a b v 0 (by omega)⟩).cast
            (pepsDim_phys a b d D (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
              (pepsLeg_mod (v : ℕ) 0 (by omega))),
          (pepsSitePos a b d D v x l r dn up m
              ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
                pepsSite_leg a b v 1 (by omega)⟩).cast
            (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega)),
          (pepsSitePos a b d D v x l r dn up m
              ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
                pepsSite_leg a b v 2 (by omega)⟩).cast
            (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega)),
          (pepsSitePos a b d D v x l r dn up m
              ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
                pepsSite_leg a b v 3 (by omega)⟩).cast
            (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega)),
          (pepsSitePos a b d D v x l r dn up m
              ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
                pepsSite_leg a b v 4 (by omega)⟩).cast
            (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))⟩ :
          Fin d × Fin D × Fin D × Fin D × Fin D),
        fun h' => (pepsSitePos a b d D v x l r dn up m ⟨h'.val, h'.property.2⟩).cast
          (pepsDim_dummy a b d D h'.property.1))
      = ((⟨x, l, r, dn, up⟩ : Fin d × Fin D × Fin D × Fin D × Fin D), m)
    rw [pepsSitePos_phys_leg, pepsSitePos_left_leg, pepsSitePos_right_leg,
        pepsSitePos_down_leg, pepsSitePos_up_leg]
    have hdummy : (fun h' : pepsDummyLegs a b v =>
          (pepsSitePos a b d D v x l r dn up m ⟨h'.val, h'.property.2⟩).cast
            (pepsDim_dummy a b d D h'.property.1)) = m := by
      funext h'
      rw [pepsSitePos_dummy_leg]
      exact fin_cast_cast' _ _
    rw [hdummy, fin_cast_cast', fin_cast_cast', fin_cast_cast', fin_cast_cast', fin_cast_cast']

theorem pepsTensor_read {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) (v : Fin (a * b))
    (x : Fin d) (l r dn up : Fin D) (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    (pepsNet a b d D T).tensor v (pepsSitePosEquiv a b d D v |>.symm ((x, l, r, dn, up), m))
      = T (pepsP a b v).1 (pepsP a b v).2 x
          (if ((pepsP a b v).1 : ℕ) = 0 then 0 else l)
          (if ((pepsP a b v).1 : ℕ) + 1 = a then 0 else r)
          (if ((pepsP a b v).2 : ℕ) + 1 = b then 0 else dn)
          (if ((pepsP a b v).2 : ℕ) = 0 then 0 else up) := by
  show pepsTensor a b d D T v (pepsSitePos a b d D v x l r dn up m) = _
  simp only [pepsTensor]
  show T (pepsP a b v).1 (pepsP a b v).2
      (Fin.cast (pepsDim_phys a b d D
          (pepsLeg_lt a b (v : ℕ) 0 v.isLt (by omega))
          (pepsLeg_mod (v : ℕ) 0 (by omega)))
        (pepsSitePos a b d D v x l r dn up m
          ⟨⟨5 * (v : ℕ), pepsLeg_lt_nh a b (v : ℕ) 0 v.isLt (by omega)⟩,
            pepsSite_leg a b v 0 (by omega)⟩))
      (if hL : ((pepsP a b v).1 : ℕ) = 0 then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 1 (by omega) (by omega))
          (pepsSitePos a b d D v x l r dn up m
            ⟨⟨5 * (v : ℕ) + 1, pepsLeg_lt_nh a b (v : ℕ) 1 v.isLt (by omega)⟩,
              pepsSite_leg a b v 1 (by omega)⟩))
      (if ((pepsP a b v).1 : ℕ) + 1 = a then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 2 (by omega) (by omega))
          (pepsSitePos a b d D v x l r dn up m
            ⟨⟨5 * (v : ℕ) + 2, pepsLeg_lt_nh a b (v : ℕ) 2 v.isLt (by omega)⟩,
              pepsSite_leg a b v 2 (by omega)⟩))
      (if ((pepsP a b v).2 : ℕ) + 1 = b then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 3 (by omega) (by omega))
          (pepsSitePos a b d D v x l r dn up m
            ⟨⟨5 * (v : ℕ) + 3, pepsLeg_lt_nh a b (v : ℕ) 3 v.isLt (by omega)⟩,
              pepsSite_leg a b v 3 (by omega)⟩))
      (if hU : ((pepsP a b v).2 : ℕ) = 0 then 0
        else Fin.cast (pepsDim_bond_leg a b d D (v : ℕ) 4 (by omega) (by omega))
          (pepsSitePos a b d D v x l r dn up m
            ⟨⟨5 * (v : ℕ) + 4, pepsLeg_lt_nh a b (v : ℕ) 4 v.isLt (by omega)⟩,
              pepsSite_leg a b v 4 (by omega)⟩))
      = _
  rw [pepsSitePos_phys_leg, pepsSitePos_left_leg, pepsSitePos_right_leg,
      pepsSitePos_down_leg, pepsSitePos_up_leg, fin_cast_cast', fin_cast_cast',
      fin_cast_cast', fin_cast_cast', fin_cast_cast']
  by_cases hL : ((pepsP a b v).1 : ℕ) = 0
  · rw [dif_pos hL, if_pos hL]
    by_cases hUp : ((pepsP a b v).2 : ℕ) = 0
    · rw [dif_pos hUp, if_pos hUp]
    · rw [dif_neg hUp, if_neg hUp]
  · rw [dif_neg hL, if_neg hL]
    by_cases hUp : ((pepsP a b v).2 : ℕ) = 0
    · rw [dif_pos hUp, if_pos hUp]
    · rw [dif_neg hUp, if_neg hUp]

theorem pepsTensor_read' {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) (v : Fin (a * b))
    (t : Fin d × Fin D × Fin D × Fin D × Fin D) (m : ∀ _h : pepsDummyLegs a b v, Fin D) :
    (pepsNet a b d D T).tensor v (pepsSitePosEquiv a b d D v |>.symm (t, m))
      = T (pepsP a b v).1 (pepsP a b v).2 t.1
          (if ((pepsP a b v).1 : ℕ) = 0 then 0 else t.2.1)
          (if ((pepsP a b v).1 : ℕ) + 1 = a then 0 else t.2.2.1)
          (if ((pepsP a b v).2 : ℕ) + 1 = b then 0 else t.2.2.2.1)
          (if ((pepsP a b v).2 : ℕ) = 0 then 0 else t.2.2.2.2) := by
  obtain ⟨x, l, r, dn, up⟩ := t
  exact pepsTensor_read T v x l r dn up m

theorem tensorSumNorm_pepsNet_site {a b d D : ℕ} [NeZero D]
    (T : Fin a → Fin b → Fin d → Fin D → Fin D → Fin D → Fin D → ℂ) (v : Fin (a * b)) :
    tensorSumNorm (pepsNet a b d D T) v
      = ∑ x : Fin d, ∑ l : Fin D, ∑ r : Fin D, ∑ dn : Fin D, ∑ up : Fin D,
          ∑ _m : ∀ _h : pepsDummyLegs a b v, Fin D,
            ‖T (pepsP a b v).1 (pepsP a b v).2 x
              (if ((pepsP a b v).1 : ℕ) = 0 then 0 else l)
              (if ((pepsP a b v).1 : ℕ) + 1 = a then 0 else r)
              (if ((pepsP a b v).2 : ℕ) + 1 = b then 0 else dn)
              (if ((pepsP a b v).2 : ℕ) = 0 then 0 else up)‖ := by
  show ∑ u : ∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v},
      Fin (pepsDim a b d D h.val.val), ‖(pepsNet a b d D T).tensor v u‖ = _
  have hvals : ∀ u : ∀ h : {h : Fin (pepsNh a b) // pepsSite a b h = v},
      Fin (pepsDim a b d D h.val.val),
      ‖(pepsNet a b d D T).tensor v u‖
        = ‖T (pepsP a b v).1 (pepsP a b v).2
            ((pepsSitePosEquiv a b d D v) u).1.1
            (if ((pepsP a b v).1 : ℕ) = 0 then 0 else
              ((pepsSitePosEquiv a b d D v) u).1.2.1)
            (if ((pepsP a b v).1 : ℕ) + 1 = a then 0 else
              ((pepsSitePosEquiv a b d D v) u).1.2.2.1)
            (if ((pepsP a b v).2 : ℕ) + 1 = b then 0 else
              ((pepsSitePosEquiv a b d D v) u).1.2.2.2.1)
            (if ((pepsP a b v).2 : ℕ) = 0 then 0 else
              ((pepsSitePosEquiv a b d D v) u).1.2.2.2.2)‖ := by
    intro u
    rw [← (pepsSitePosEquiv a b d D v).symm_apply_apply u, Equiv.apply_symm_apply,
      pepsTensor_read' T v ((pepsSitePosEquiv a b d D v) u).1
        ((pepsSitePosEquiv a b d D v) u).2]
  rw [Fintype.sum_equiv (pepsSitePosEquiv a b d D v)
    (fun u => ‖(pepsNet a b d D T).tensor v u‖)
    (fun t => ‖T (pepsP a b v).1 (pepsP a b v).2 t.1.1
        (if ((pepsP a b v).1 : ℕ) = 0 then 0 else t.1.2.1)
        (if ((pepsP a b v).1 : ℕ) + 1 = a then 0 else t.1.2.2.1)
        (if ((pepsP a b v).2 : ℕ) + 1 = b then 0 else t.1.2.2.2.1)
        (if ((pepsP a b v).2 : ℕ) = 0 then 0 else t.1.2.2.2.2)‖) hvals]
  simp only [Fintype.sum_prod_type]

theorem frontier1 (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    (∀ y : OpenAssign (permNet N π),
      netContract (permNet N π) y = netContract N (openPull N π y))
    ∧ (∀ ψ φ : OpenAssign N → ℂ,
      netInner (permNet N π) (fun y => ψ (openPull N π y)) (fun y => φ (openPull N π y))
        = netInner N ψ φ) :=
  ⟨netContract_permNet N π, netInner_perm N π⟩

end PositionDesc

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
