/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.FiniteTensorTableCodec
open Qatlib
open Qatlib.Concepts.TensorNetwork.CanonicalMPS
open Qatlib.Concepts.TensorNetwork.GaugeInvariance
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
open scoped BigOperators

structure TableTensorNet (N : TensorNet) where

  num : (v : Fin N.nv) → (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) → GaussianRat

def tableDecode (N : TensorNet) (T : TableTensorNet N) : TensorNet :=
  { N with tensor := fun v a => gaussianRatComplex (T.num v a) }

theorem tableDecode_tensor (N : TensorNet) (T : TableTensorNet N) (v : Fin N.nv)
    (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    (tableDecode N T).tensor v a = gaussianRatComplex (T.num v a) := rfl

theorem tableDecode_graph (N : TensorNet) (T : TableTensorNet N) :
    (tableDecode N T).nv = N.nv ∧ (tableDecode N T).nh = N.nh
      ∧ (tableDecode N T).dims = N.dims ∧ (tableDecode N T).site = N.site
      ∧ (tableDecode N T).partner = N.partner := ⟨rfl, rfl, rfl, rfl, rfl⟩

noncomputable def tableEncode (N : TensorNet)
    (h : ∀ (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      ∃ q : GaussianRat, N.tensor v a = gaussianRatComplex q) :
    TableTensorNet N where
  num v a := Classical.choose (h v a)

theorem tableEncode_decode_tensor (N : TensorNet)
    (h : ∀ (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
      ∃ q : GaussianRat, N.tensor v a = gaussianRatComplex q)
    (v : Fin N.nv) (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    (tableDecode N (tableEncode N h)).tensor v a = N.tensor v a := by
  rw [tableDecode_tensor]
  exact (Classical.choose_spec (h v a)).symm

def tablePermute (N : TensorNet) (T : TableTensorNet N) (π : Fin N.nh ≃ Fin N.nh) :
    TableTensorNet (permNet N π) where
  num v a := T.num v (fun g : {g : Fin N.nh // N.site g = v} =>
    (a ⟨π g.val, (permNet_site N π g.val).trans g.property⟩).cast
      (permNet_dims N π g.val))

theorem tablePermute_num (N : TensorNet) (T : TableTensorNet N) (π : Fin N.nh ≃ Fin N.nh)
    (v : Fin N.nv)
    (a : ∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = v},
      Fin ((permNet N π).dims h.val)) :
    (tablePermute N T π).num v a
      = T.num v (fun g : {g : Fin N.nh // N.site g = v} =>
          (a ⟨π g.val, (permNet_site N π g.val).trans g.property⟩).cast
            (permNet_dims N π g.val)) := rfl

def tablePosPull (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (v : Fin N.nv) :
    (∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = v},
      Fin ((permNet N π).dims h.val)) →
      (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :=
  fun a g => (a ⟨π g.val, (permNet_site N π g.val).trans g.property⟩).cast
      (permNet_dims N π g.val)

def tablePosPush (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (v : Fin N.nv) :
    (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) →
      (∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = v},
        Fin ((permNet N π).dims h.val)) :=
  fun b h' => b ⟨π.symm h'.val, h'.property⟩

theorem tablePosPull_push (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (v : Fin N.nv)
    (b : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    tablePosPull N π v (tablePosPush N π v b) = b := by
  funext g
  apply Fin.ext
  have hg : (⟨π.symm (π g.val),
      ((permNet_site N π g.val).trans g.property : N.site (π.symm (π ↑g)) = v)⟩ :
      {h : Fin N.nh // N.site h = v}) = g := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply π g.val
  show (b ⟨π.symm (π g.val), (permNet_site N π g.val).trans g.property⟩).val = (b g).val
  rw [hg]

theorem tablePosPush_pull (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (v : Fin N.nv)
    (a : ∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = v},
      Fin ((permNet N π).dims h.val)) :
    tablePosPush N π v (tablePosPull N π v a) = a := by
  funext h'
  apply Fin.ext
  have hmid : N.site (π.symm h'.val) = v := h'.property
  have hh : (⟨π (π.symm h'.val),
      (permNet_site N π (π.symm h'.val)).trans hmid⟩ :
      {h : Fin (permNet N π).nh // (permNet N π).site h = v}) = h' := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply π h'.val
  show (a ⟨π (π.symm h'.val),
      (permNet_site N π (π.symm h'.val)).trans hmid⟩).val = (a h').val
  rw [hh]

def tablePosEquiv (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) (v : Fin N.nv) :
    (∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = v},
      Fin ((permNet N π).dims h.val)) ≃
      (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) where
  toFun := tablePosPull N π v
  invFun := tablePosPush N π v
  left_inv := tablePosPush_pull N π v
  right_inv := tablePosPull_push N π v

theorem tableDecode_permNet (N : TensorNet) (T : TableTensorNet N) (π : Fin N.nh ≃ Fin N.nh) :
    tableDecode (permNet N π) (tablePermute N T π) = permNet (tableDecode N T) π := rfl

theorem openPull_tableDecode (N : TensorNet) (T : TableTensorNet N) (π : Fin N.nh ≃ Fin N.nh)
    (y : OpenAssign (permNet N π)) :
    openPull (tableDecode N T) π y = openPull N π y := rfl

theorem netContract_tablePermute (N : TensorNet) (T : TableTensorNet N)
    (π : Fin N.nh ≃ Fin N.nh) (y : OpenAssign (permNet N π)) :
    netContract (tableDecode (permNet N π) (tablePermute N T π)) y
      = netContract (tableDecode N T) (openPull N π y) :=
  netContract_permNet (tableDecode N T) π y

theorem netContract_tablePermute_push (N : TensorNet) (T : TableTensorNet N)
    (π : Fin N.nh ≃ Fin N.nh) (y : OpenAssign N) :
    netContract (tableDecode (permNet N π) (tablePermute N T π)) (openPush N π y)
      = netContract (tableDecode N T) y :=
  netContract_permPush (tableDecode N T) π y

def grHeight (q : GaussianRat) : ℕ :=
  max (max q.1.num.natAbs q.1.den) (max q.2.num.natAbs q.2.den)

def tableHeight (N : TensorNet) (T : TableTensorNet N) : ℕ :=
  Finset.univ.sup fun v : Fin N.nv =>
    Finset.univ.sup fun a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val) =>
      grHeight (T.num v a)

theorem grHeight_le_tableHeight (N : TensorNet) (T : TableTensorNet N) (v : Fin N.nv)
    (a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)) :
    grHeight (T.num v a) ≤ tableHeight N T :=
  (Finset.le_sup (f := fun a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val) =>
      grHeight (T.num v a)) (Finset.mem_univ a)).trans
    (Finset.le_sup (f := fun v : Fin N.nv =>
      Finset.univ.sup fun a : ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val) =>
        grHeight (T.num v a)) (Finset.mem_univ v))

theorem tableHeight_permute (N : TensorNet) (T : TableTensorNet N) (π : Fin N.nh ≃ Fin N.nh) :
    tableHeight (permNet N π) (tablePermute N T π) = tableHeight N T := by
  apply le_antisymm
  · refine Finset.sup_le fun v _ => Finset.sup_le fun a _ => ?_
    have hr : (tablePermute N T π).num v a = T.num v (tablePosPull N π v a) := rfl
    rw [hr]
    refine le_trans (Finset.le_sup (f := fun b :
        ∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val) =>
          grHeight (T.num v b)) (Finset.mem_univ (tablePosPull N π v a))) ?_
    exact Finset.le_sup (f := fun w : Fin N.nv =>
      Finset.univ.sup fun b : ∀ h : {h : Fin N.nh // N.site h = w}, Fin (N.dims h.val) =>
        grHeight (T.num w b)) (Finset.mem_univ v)
  · refine Finset.sup_le fun v _ => Finset.sup_le fun b _ => ?_
    have hr : T.num v b = (tablePermute N T π).num v (tablePosPush N π v b) := by
      rw [tablePermute_num]
      congr 1
      funext g
      have hg : (⟨π.symm (π g.val),
          ((permNet_site N π g.val).trans g.property : N.site (π.symm (π ↑g)) = v)⟩ :
          {h : Fin N.nh // N.site h = v}) = g := by
        apply Subtype.ext
        exact Equiv.symm_apply_apply π g.val
      apply Fin.ext
      show (b g).val = (b ⟨π.symm (π g.val),
          (permNet_site N π g.val).trans g.property⟩).val
      rw [hg]
    rw [hr]
    refine le_trans (Finset.le_sup (f := fun c :
        ∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = v},
          Fin ((permNet N π).dims h.val) =>
          grHeight ((tablePermute N T π).num v c))
        (Finset.mem_univ (tablePosPush N π v b))) ?_
    exact Finset.le_sup (f := fun w : Fin (permNet N π).nv =>
      Finset.univ.sup fun c :
          ∀ h : {h : Fin (permNet N π).nh // (permNet N π).site h = w},
            Fin ((permNet N π).dims h.val) =>
        grHeight ((tablePermute N T π).num w c)) (Finset.mem_univ v)

theorem permNet_dims_tableDecode (N : TensorNet) (T : TableTensorNet N)
    (π : Fin N.nh ≃ Fin N.nh) (h : Fin N.nh) :
    (permNet (tableDecode N T) π).dims (π h) = (tableDecode N T).dims h :=
  permNet_dims (tableDecode N T) π h

theorem card_openLeg_permNet (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    Fintype.card (OpenLeg (permNet N π)) = Fintype.card (OpenLeg N) :=
  Fintype.card_congr (permOpenLeg N π).symm

theorem netBondDimension_tablePermute (N : TensorNet) (T : TableTensorNet N)
    (π : Fin N.nh ≃ Fin N.nh) :
    netBondDimension (tableDecode (permNet N π) (tablePermute N T π))
      = netBondDimension (tableDecode N T) := by
  rw [tableDecode_permNet]
  exact netBondDimension_permNet (tableDecode N T) π

def grBitSize (q : GaussianRat) : ℕ :=
  q.1.num.natAbs.log2 + q.1.den.log2 + q.2.num.natAbs.log2 + q.2.den.log2 + 6

def tableBitSize (N : TensorNet) (T : TableTensorNet N) : ℕ :=
  ∑ v : Fin N.nv, ∑ a : (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val)),
    grBitSize (T.num v a)

def tableReadCount (N : TensorNet) : ℕ :=
  ∑ v : Fin N.nv,
    Fintype.card (∀ h : {h : Fin N.nh // N.site h = v}, Fin (N.dims h.val))

theorem tableBitSize_permute (N : TensorNet) (T : TableTensorNet N)
    (π : Fin N.nh ≃ Fin N.nh) :
    tableBitSize (permNet N π) (tablePermute N T π) = tableBitSize N T := by
  apply Finset.sum_congr rfl
  intro v _
  exact Fintype.sum_equiv (tablePosEquiv N π v) _ _ (fun _ => rfl)

theorem tableReadCount_permute (N : TensorNet) (π : Fin N.nh ≃ Fin N.nh) :
    tableReadCount (permNet N π) = tableReadCount N := by
  apply Finset.sum_congr rfl
  intro v _
  exact Fintype.card_congr (tablePosEquiv N π v)

theorem tableDecode_empty_contract (N : TensorNet) (T : TableTensorNet N)
    (hnv : N.nv = 0) (hnh : N.nh = 0) (y : OpenAssign N) :
    netContract (tableDecode N T) y = 1 :=
  netContract_of_empty_net (N := tableDecode N T) hnv hnh y

theorem tableDecode_zero_bond_contract (N : TensorNet) (T : TableTensorNet N)
    (hd : ∃ i : InternalEdge N, N.dims i.val = 0) (y : OpenAssign N) :
    netContract (tableDecode N T) y = 0 :=
  netContract_of_isEmpty_internal (N := tableDecode N T) hd y

theorem frontier1 (N : TensorNet) (T : TableTensorNet N) (π : Fin N.nh ≃ Fin N.nh) :
    tableDecode (permNet N π) (tablePermute N T π) = permNet (tableDecode N T) π
    ∧ (∀ y : OpenAssign (permNet N π),
        netContract (tableDecode (permNet N π) (tablePermute N T π)) y
          = netContract (tableDecode N T) (openPull N π y))
    ∧ (∀ h : Fin N.nh,
        (permNet (tableDecode N T) π).dims (π h) = (tableDecode N T).dims h)
    ∧ tableHeight (permNet N π) (tablePermute N T π) = tableHeight N T
    ∧ netBondDimension (tableDecode (permNet N π) (tablePermute N T π))
        = netBondDimension (tableDecode N T) :=
  ⟨tableDecode_permNet N T π, netContract_tablePermute N T π,
    permNet_dims_tableDecode N T π, tableHeight_permute N T π,
    netBondDimension_tablePermute N T π⟩

theorem netContract_allOpen (N : TensorNet) (hno : ∀ j : Fin N.nh, N.partner j = none)
    (ext : OpenAssign N) :
    netContract N ext = ∏ v : Fin N.nv,
      N.tensor v (fun h : {h : Fin N.nh // N.site h = v} => ext ⟨h.val, hno h.val⟩) := by
  have hIE : IsEmpty (InternalEdge N) := ⟨fun i => by
    obtain ⟨k, hk, _⟩ := i.2
    rw [hno i.val] at hk
    simp at hk⟩
  rw [netContract, Fintype.sum_unique]
  refine Finset.prod_congr rfl fun v _ => congrArg (N.tensor v) (funext fun h => ?_)
  exact portValue_of_partner_none ext default h.val (hno h.val)

def prodNet : TensorNet where
  nv := 2
  nh := 2
  dims := fun _ => 2
  site := fun j => ⟨(j : ℕ), by omega⟩
  partner := fun _ => none
  involution := by intro j k hj; cases hj
  no_self_loop := by intro j k hj; cases hj
  dims_match := by intro j k hj; cases hj
  tensor := fun _ _ => 0

def prodTable (g : Fin 2 → Fin 2 → GaussianRat) : TableTensorNet prodNet where
  num v a := g v (a ⟨v, by
    show (prodNet).site v = v
    rfl⟩)

theorem prodTable_num (g : Fin 2 → Fin 2 → GaussianRat) (v : Fin (prodNet).nv)
    (a : ∀ h : {h : Fin (prodNet).nh // (prodNet).site h = v}, Fin ((prodNet).dims h.val)) :
    (prodTable g).num v a = g v (a ⟨v, by
      show (prodNet).site v = v
      rfl⟩) := rfl

def prodAssign (y : Fin 2 → Fin 2) : OpenAssign prodNet := fun o => y o.val

theorem prod_contract (g : Fin 2 → Fin 2 → GaussianRat) (y : Fin 2 → Fin 2) :
    netContract (tableDecode prodNet (prodTable g)) (prodAssign y)
      = gaussianRatComplex (g 0 (y 0)) * gaussianRatComplex (g 1 (y 1)) := by
  rw [show netContract (tableDecode prodNet (prodTable g)) (prodAssign y)
        = ∏ v : Fin (tableDecode prodNet (prodTable g)).nv,
            (tableDecode prodNet (prodTable g)).tensor v
              (fun h : {h : Fin (prodNet).nh // (prodNet).site h = v} =>
                (prodAssign y) ⟨h.val, rfl⟩)
        from netContract_allOpen _ (fun _ => rfl) _]
  show (∏ v : Fin 2, (tableDecode prodNet (prodTable g)).tensor v
      (fun h : {h : Fin (prodNet).nh // (prodNet).site h = v} =>
        (prodAssign y) ⟨h.val, rfl⟩))
    = gaussianRatComplex (g 0 (y 0)) * gaussianRatComplex (g 1 (y 1))
  rw [Fin.prod_univ_two, tableDecode_tensor, tableDecode_tensor, prodTable_num,
    prodTable_num]
  rfl

def prodSwap : Fin 2 ≃ Fin 2 := Equiv.swap (⟨0, by omega⟩ : Fin 2) ⟨1, by omega⟩

theorem prod_perm_contract (g : Fin 2 → Fin 2 → GaussianRat) (y : Fin 2 → Fin 2) :
    netContract (tableDecode (permNet prodNet prodSwap)
        (tablePermute prodNet (prodTable g) prodSwap))
      (openPush prodNet prodSwap (prodAssign y))
      = gaussianRatComplex (g 0 (y 0)) * gaussianRatComplex (g 1 (y 1)) :=
  (netContract_tablePermute_push prodNet (prodTable g) prodSwap
    (prodAssign y)).trans (prod_contract g y)

def bellSite (j : Fin 4) : Fin 2 :=
  if (j : ℕ) = 0 ∨ (j : ℕ) = 1 then 0 else 1

def bellPartner (j : Fin 4) : Option (Fin 4) :=
  if (j : ℕ) = 1 then some 2
  else if (j : ℕ) = 2 then some 1
  else none

def bellNet : TensorNet where
  nv := 2
  nh := 4
  dims := fun _ => 2
  site := bellSite
  partner := bellPartner
  involution := by
    intro j k hj
    fin_cases j <;> fin_cases k <;> simp [bellPartner] at hj ⊢
  no_self_loop := by
    intro j k hj
    fin_cases j <;> fin_cases k <;> simp [bellPartner] at hj ⊢
  dims_match := by
    intro j k hj
    fin_cases j <;> fin_cases k <;> simp [bellPartner] at hj ⊢
  tensor := fun _ _ => 0

theorem bell_partner_one : bellPartner (⟨1, by omega⟩ : Fin 4) = some ⟨2, by omega⟩ := by
  simp [bellPartner]

theorem bell_partner_two : bellPartner (⟨2, by omega⟩ : Fin 4) = some ⟨1, by omega⟩ := by
  simp [bellPartner]

theorem bell_site_zero (v : Fin (bellNet).nv) (hv : (v : ℕ) = 0) :
    (bellNet).site (⟨0, by omega⟩ : Fin 4) = v := by
  apply Fin.ext
  show (0 : ℕ) = (v : ℕ)
  omega

theorem bell_site_one (v : Fin (bellNet).nv) (hv : (v : ℕ) = 0) :
    (bellNet).site (⟨1, by omega⟩ : Fin 4) = v := by
  apply Fin.ext
  show (0 : ℕ) = (v : ℕ)
  omega

theorem bell_site_two (v : Fin (bellNet).nv) (hv : (v : ℕ) = 1) :
    (bellNet).site (⟨2, by omega⟩ : Fin 4) = v := by
  apply Fin.ext
  show (1 : ℕ) = (v : ℕ)
  omega

theorem bell_site_three (v : Fin (bellNet).nv) (hv : (v : ℕ) = 1) :
    (bellNet).site (⟨3, by omega⟩ : Fin 4) = v := by
  apply Fin.ext
  show (1 : ℕ) = (v : ℕ)
  omega

theorem bell_internal_val (i : InternalEdge bellNet) : (i.val : ℕ) = 1 := by
  have hkey : ∀ (j k : Fin 4), bellPartner j = some k → (j : ℕ) < (k : ℕ) → (j : ℕ) = 1 := by
    intro j k hk hlt
    fin_cases j <;> fin_cases k <;> simp [bellPartner] at hk hlt ⊢
  obtain ⟨k, hk, hlt⟩ := i.2
  exact hkey i.val k hk hlt

def bellEdgeEquiv :
    (∀ i : InternalEdge bellNet, Fin ((bellNet).dims i.val)) ≃ Fin 2 where
  toFun e := e ⟨(⟨1, by omega⟩ : Fin 4),
    ⟨(⟨2, by omega⟩ : Fin 4), bell_partner_one, by decide⟩⟩
  invFun k i := k.cast (by rfl)
  left_inv := by
    intro e
    funext i
    have hi : i = ⟨(⟨1, by omega⟩ : Fin 4),
        ⟨(⟨2, by omega⟩ : Fin 4), bell_partner_one, by decide⟩⟩ := by
      apply Subtype.ext
      apply Fin.ext
      exact bell_internal_val i
    subst hi
    rfl
  right_inv := by
    intro k
    rfl

def bellTable : TableTensorNet bellNet where
  num v a :=
    if hv : (v : ℕ) = 0 then
      if a ⟨(⟨0, by omega⟩ : Fin 4), bell_site_zero v hv⟩
          = a ⟨(⟨1, by omega⟩ : Fin 4), bell_site_one v hv⟩ then (1, 0) else (0, 0)
    else
      if a ⟨(⟨2, by omega⟩ : Fin 4),
            bell_site_two v (by have hn : (bellNet).nv = 2 := rfl; have := v.isLt; omega)⟩
          = a ⟨(⟨3, by omega⟩ : Fin 4),
            bell_site_three v (by have hn : (bellNet).nv = 2 := rfl; have := v.isLt; omega)⟩ then
        (1, 0) else (0, 0)

theorem bell_partner_zero :
    (tableDecode bellNet bellTable).partner (⟨0, by omega⟩ : Fin 4) = none := by
  show bellPartner (⟨0, by omega⟩ : Fin 4) = none
  simp [bellPartner]

theorem bell_partner_three :
    (tableDecode bellNet bellTable).partner (⟨3, by omega⟩ : Fin 4) = none := by
  show bellPartner (⟨3, by omega⟩ : Fin 4) = none
  simp [bellPartner]

theorem bell_partner_one' : (tableDecode bellNet bellTable).partner (⟨1, by omega⟩ : Fin 4)
    = some (⟨2, by omega⟩ : Fin 4) := bell_partner_one

theorem bell_partner_two' : (tableDecode bellNet bellTable).partner (⟨2, by omega⟩ : Fin 4)
    = some (⟨1, by omega⟩ : Fin 4) := bell_partner_two

theorem bellTable_num_zero (v : Fin (bellNet).nv) (hv : (v : ℕ) = 0)
    (a : ∀ h : {h : Fin (bellNet).nh // (bellNet).site h = v}, Fin ((bellNet).dims h.val)) :
    (bellTable).num v a =
      (if a ⟨(⟨0, by omega⟩ : Fin 4), bell_site_zero v hv⟩
          = a ⟨(⟨1, by omega⟩ : Fin 4), bell_site_one v hv⟩ then (1, 0) else (0, 0)) := by
  show dite ((v : ℕ) = 0) _ _ = _
  rw [dif_pos hv]

theorem bellTable_num_one (v : Fin (bellNet).nv) (hv : ¬(v : ℕ) = 0)
    (a : ∀ h : {h : Fin (bellNet).nh // (bellNet).site h = v}, Fin ((bellNet).dims h.val)) :
    (bellTable).num v a =
      (if a ⟨(⟨2, by omega⟩ : Fin 4),
            bell_site_two v (by have hn : (bellNet).nv = 2 := rfl; have := v.isLt; omega)⟩
          = a ⟨(⟨3, by omega⟩ : Fin 4),
            bell_site_three v (by have hn : (bellNet).nv = 2 := rfl; have := v.isLt; omega)⟩ then
        (1, 0) else (0, 0)) := by
  show dite ((v : ℕ) = 0) _ _ = _
  rw [dif_neg hv]

def bellAssign (p q : Fin 2) : OpenAssign bellNet := fun o =>
  if (o.val : ℕ) = 0 then p else q

theorem bell_contract (p q : Fin 2) :
    netContract (tableDecode bellNet bellTable) (bellAssign p q)
      = if p = q then (1 : ℂ) else 0 := by
  have hsum : netContract (tableDecode bellNet bellTable) (bellAssign p q)
      = ∑ k : Fin 2, ∏ v : Fin 2, (tableDecode bellNet bellTable).tensor v
        (fun h : {h : Fin (bellNet).nh // (bellNet).site h = v} =>
          portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) h.val) := by
    rw [netContract]
    exact Fintype.sum_equiv bellEdgeEquiv _ _ (fun e => by rw [Equiv.symm_apply_apply]; rfl)
  rw [hsum]
  have hfin : ∀ k : Fin 2,
      (∏ v : Fin 2, (tableDecode bellNet bellTable).tensor v
        (fun h : {h : Fin (bellNet).nh // (bellNet).site h = v} =>
          portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) h.val))
      = (if p = k then (1 : ℂ) else 0) * (if k = q then (1 : ℂ) else 0) := by
    intro k
    have hfun0 : ∀ h : {h : Fin (bellNet).nh // (bellNet).site h = (0 : Fin 2)},
        portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) h.val =
          if (h.val : ℕ) = 0 then p else k := by
      intro h
      fin_cases h
      · show portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) (⟨0, by omega⟩ : Fin 4) = p
        rw [portValue_of_partner_none (N := tableDecode bellNet bellTable) _ _ _
          bell_partner_zero]
        rfl
      · show portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) (⟨1, by omega⟩ : Fin 4) =
          if (1 : ℕ) = 0 then p else k
        rw [portValue_of_partner_eq (N := tableDecode bellNet bellTable) _ _
          (⟨1, by omega⟩ : Fin 4) (⟨2, by omega⟩ : Fin 4) bell_partner_one' (by decide)]
        rfl
    have hfun1 : ∀ h : {h : Fin (bellNet).nh // (bellNet).site h = (1 : Fin 2)},
        portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) h.val =
          if (h.val : ℕ) = 2 then k else q := by
      intro h
      fin_cases h
      · show portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) (⟨2, by omega⟩ : Fin 4) =
          if (2 : ℕ) = 2 then k else q
        rw [portValue_of_partner_eq_rev (N := tableDecode bellNet bellTable) _ _
          (⟨2, by omega⟩ : Fin 4) (⟨1, by omega⟩ : Fin 4) bell_partner_two' (by decide)
          bell_partner_one' (by rfl)]
        rfl
      · show portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) (⟨3, by omega⟩ : Fin 4) = q
        rw [portValue_of_partner_none (N := tableDecode bellNet bellTable) _ _ _
          bell_partner_three]
        rfl
    rw [Fin.prod_univ_two]
    show (tableDecode bellNet bellTable).tensor (0 : Fin 2)
        (fun h : {h : Fin (bellNet).nh // (bellNet).site h = (0 : Fin 2)} =>
          portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) h.val)
        * (tableDecode bellNet bellTable).tensor (1 : Fin 2)
        (fun h : {h : Fin (bellNet).nh // (bellNet).site h = (1 : Fin 2)} =>
          portValue (tableDecode bellNet bellTable) (bellAssign p q)
            (bellEdgeEquiv.symm k) h.val)
      = (if p = k then (1 : ℂ) else 0) * (if k = q then (1 : ℂ) else 0)
    rw [tableDecode_tensor, tableDecode_tensor,
      bellTable_num_zero (0 : Fin 2) (by decide),
      bellTable_num_one (1 : Fin 2) (by decide),
      hfun0 ⟨(⟨0, by omega⟩ : Fin 4), bell_site_zero (0 : Fin 2) (by decide)⟩,
      hfun0 ⟨(⟨1, by omega⟩ : Fin 4), bell_site_one (0 : Fin 2) (by decide)⟩,
      hfun1 ⟨(⟨2, by omega⟩ : Fin 4), bell_site_two (1 : Fin 2) (by decide)⟩,
      hfun1 ⟨(⟨3, by omega⟩ : Fin 4), bell_site_three (1 : Fin 2) (by decide)⟩]
    fin_cases k <;> fin_cases p <;> fin_cases q <;> simp [gaussianRatComplex]
  rw [Fin.sum_univ_two, hfin 0, hfin 1]
  fin_cases p <;> fin_cases q <;> simp

def chainSite (j : Fin 7) : Fin 3 :=
  if (j : ℕ) ≤ 1 then 0 else if (j : ℕ) ≤ 4 then 1 else 2

def chainPartner (j : Fin 7) : Option (Fin 7) :=
  if (j : ℕ) = 1 then some 3
  else if (j : ℕ) = 3 then some 1
  else if (j : ℕ) = 4 then some 5
  else if (j : ℕ) = 5 then some 4
  else none

def chainNet : TensorNet where
  nv := 3
  nh := 7
  dims := fun _ => 2
  site := chainSite
  partner := chainPartner
  involution := by
    intro j k hj
    fin_cases j <;> fin_cases k <;> simp [chainPartner] at hj ⊢
  no_self_loop := by
    intro j k hj
    fin_cases j <;> fin_cases k <;> simp [chainPartner] at hj ⊢
  dims_match := by
    intro j k hj
    fin_cases j <;> fin_cases k <;> simp [chainPartner] at hj ⊢
  tensor := fun _ _ => 0

theorem chain_partner_one : chainPartner (⟨1, by omega⟩ : Fin 7)
    = some (⟨3, by omega⟩ : Fin 7) := by
  simp [chainPartner]

theorem chain_partner_three : chainPartner (⟨3, by omega⟩ : Fin 7)
    = some (⟨1, by omega⟩ : Fin 7) := by
  simp [chainPartner]

theorem chain_partner_four : chainPartner (⟨4, by omega⟩ : Fin 7)
    = some (⟨5, by omega⟩ : Fin 7) := by
  simp [chainPartner]

theorem chain_partner_five : chainPartner (⟨5, by omega⟩ : Fin 7)
    = some (⟨4, by omega⟩ : Fin 7) := by
  simp [chainPartner]

theorem chain_site_zero (v : Fin (chainNet).nv) (hv : (v : ℕ) = 0) :
    (chainNet).site (⟨0, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (0 : ℕ) = (v : ℕ)
  omega

theorem chain_site_one (v : Fin (chainNet).nv) (hv : (v : ℕ) = 0) :
    (chainNet).site (⟨1, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (0 : ℕ) = (v : ℕ)
  omega

theorem chain_site_two (v : Fin (chainNet).nv) (hv : (v : ℕ) = 1) :
    (chainNet).site (⟨2, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (1 : ℕ) = (v : ℕ)
  omega

theorem chain_site_three (v : Fin (chainNet).nv) (hv : (v : ℕ) = 1) :
    (chainNet).site (⟨3, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (1 : ℕ) = (v : ℕ)
  omega

theorem chain_site_four (v : Fin (chainNet).nv) (hv : (v : ℕ) = 1) :
    (chainNet).site (⟨4, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (1 : ℕ) = (v : ℕ)
  omega

theorem chain_site_five (v : Fin (chainNet).nv) (hv : (v : ℕ) = 2) :
    (chainNet).site (⟨5, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (2 : ℕ) = (v : ℕ)
  omega

theorem chain_site_six (v : Fin (chainNet).nv) (hv : (v : ℕ) = 2) :
    (chainNet).site (⟨6, by omega⟩ : Fin 7) = v := by
  apply Fin.ext
  show (2 : ℕ) = (v : ℕ)
  omega

theorem chain_internal_val (i : InternalEdge chainNet) :
    (i.val : ℕ) = 1 ∨ (i.val : ℕ) = 4 := by
  have hkey : ∀ (j k : Fin 7), chainPartner j = some k → (j : ℕ) < (k : ℕ) →
      (j : ℕ) = 1 ∨ (j : ℕ) = 4 := by
    intro j k hk hlt
    fin_cases j <;> fin_cases k <;> simp [chainPartner] at hk hlt ⊢
  obtain ⟨k, hk, hlt⟩ := i.2
  exact hkey i.val k hk hlt

def chainEdgeEquiv :
    (∀ i : InternalEdge chainNet, Fin ((chainNet).dims i.val)) ≃ Fin 2 × Fin 2 where
  toFun e :=
    (e ⟨(⟨1, by omega⟩ : Fin 7),
        ⟨(⟨3, by omega⟩ : Fin 7), chain_partner_one, by change (1 : ℕ) < 3; decide⟩⟩,
      e ⟨(⟨4, by omega⟩ : Fin 7),
        ⟨(⟨5, by omega⟩ : Fin 7), chain_partner_four, by change (4 : ℕ) < 5; decide⟩⟩)
  invFun p i := if (i.val : ℕ) = 1 then p.1 else p.2
  left_inv := by
    intro e
    funext i
    rcases chain_internal_val i with h | h
    · (try dsimp only)
      rw [if_pos h]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      exact h.symm
    · (try dsimp only)
      rw [if_neg (by omega)]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      exact h.symm
  right_inv := by
    intro p
    rfl

def chainTable : TableTensorNet chainNet where
  num v a :=
    if hv : (v : ℕ) = 0 then
      if (a ⟨(⟨0, by omega⟩ : Fin 7), chain_site_zero v hv⟩ : ℕ) = 0 then
        (if (a ⟨(⟨1, by omega⟩ : Fin 7), chain_site_one v hv⟩ : ℕ) = 0
          then (1, 0) else (0, 0))
      else (1, 0)
    else if hv1 : (v : ℕ) = 1 then
      (if (a ⟨(⟨2, by omega⟩ : Fin 7), chain_site_two v hv1⟩ : ℕ) = 0 ∧
        (a ⟨(⟨3, by omega⟩ : Fin 7), chain_site_three v hv1⟩ : ℕ) =
          (a ⟨(⟨4, by omega⟩ : Fin 7), chain_site_four v hv1⟩ : ℕ) then (1, 0) else (0, 0))
      else if (a ⟨(⟨6, by omega⟩ : Fin 7),
          chain_site_six v (by have := v.isLt; change (v : ℕ) < 3 at this; omega)⟩ : ℕ) = 0 then
        (if (a ⟨(⟨5, by omega⟩ : Fin 7),
            chain_site_five v (by have := v.isLt; change (v : ℕ) < 3 at this; omega)⟩ : ℕ) = 1
          then (1, 0) else (0, 0))
      else (1, 0)

theorem chain_partner_zero :
    (tableDecode chainNet chainTable).partner (⟨0, by omega⟩ : Fin 7) = none := by
  show chainPartner (⟨0, by omega⟩ : Fin 7) = none
  simp [chainPartner]

theorem chain_partner_two :
    (tableDecode chainNet chainTable).partner (⟨2, by omega⟩ : Fin 7) = none := by
  show chainPartner (⟨2, by omega⟩ : Fin 7) = none
  simp [chainPartner]

theorem chain_partner_six :
    (tableDecode chainNet chainTable).partner (⟨6, by omega⟩ : Fin 7) = none := by
  show chainPartner (⟨6, by omega⟩ : Fin 7) = none
  simp [chainPartner]

theorem chain_partner_one' : (tableDecode chainNet chainTable).partner (⟨1, by omega⟩ : Fin 7)
    = some (⟨3, by omega⟩ : Fin 7) := chain_partner_one

theorem chain_partner_three' : (tableDecode chainNet chainTable).partner (⟨3, by omega⟩ : Fin 7)
    = some (⟨1, by omega⟩ : Fin 7) := chain_partner_three

theorem chain_partner_four' : (tableDecode chainNet chainTable).partner (⟨4, by omega⟩ : Fin 7)
    = some (⟨5, by omega⟩ : Fin 7) := chain_partner_four

theorem chain_partner_five' : (tableDecode chainNet chainTable).partner (⟨5, by omega⟩ : Fin 7)
    = some (⟨4, by omega⟩ : Fin 7) := chain_partner_five

theorem chainTable_num_zero (v : Fin (chainNet).nv) (hv : (v : ℕ) = 0)
    (a : ∀ h : {h : Fin (chainNet).nh // (chainNet).site h = v}, Fin ((chainNet).dims h.val)) :
    (chainTable).num v a =
      (if (a ⟨(⟨0, by omega⟩ : Fin 7), chain_site_zero v hv⟩ : ℕ) = 0 then
        (if (a ⟨(⟨1, by omega⟩ : Fin 7), chain_site_one v hv⟩ : ℕ) = 0
          then (1, 0) else (0, 0))
      else (1, 0)) := by
  show dite ((v : ℕ) = 0) _ _ = _
  rw [dif_pos hv]

theorem chainTable_num_one (v : Fin (chainNet).nv) (hv : (v : ℕ) = 1)
    (a : ∀ h : {h : Fin (chainNet).nh // (chainNet).site h = v}, Fin ((chainNet).dims h.val)) :
    (chainTable).num v a =
      (if (a ⟨(⟨2, by omega⟩ : Fin 7),
            chain_site_two v hv⟩ : ℕ)
            = 0 ∧
        (a ⟨(⟨3, by omega⟩ : Fin 7),
            chain_site_three v hv⟩ : ℕ)
            =
          (a ⟨(⟨4, by omega⟩ : Fin 7),
            chain_site_four v hv⟩ : ℕ)
        then (1, 0) else (0, 0)) := by
  show dite ((v : ℕ) = 0) _ _ = _
  rw [dif_neg (by omega), dif_pos hv]

theorem chainTable_num_two (v : Fin (chainNet).nv) (hv0 : ¬(v : ℕ) = 0) (hv1 : ¬(v : ℕ) = 1)
    (a : ∀ h : {h : Fin (chainNet).nh // (chainNet).site h = v}, Fin ((chainNet).dims h.val)) :
    (chainTable).num v a =
      (if (a ⟨(⟨6, by omega⟩ : Fin 7),
            chain_site_six v (by have hn : (chainNet).nv = 3 := rfl; have := v.isLt; omega)⟩ : ℕ)
            = 0 then
        (if (a ⟨(⟨5, by omega⟩ : Fin 7),
              chain_site_five v (by have hn : (chainNet).nv = 3 := rfl; have := v.isLt; omega)⟩ : ℕ)
              = 1 then (1, 0) else (0, 0))
      else (1, 0)) := by
  show dite ((v : ℕ) = 0) _ _ = _
  rw [dif_neg hv0, dif_neg hv1]

def chainExt (y : Fin 3 → Fin 2) : OpenAssign chainNet := fun o =>
  if (o.val : ℕ) = 0 then y 0 else if (o.val : ℕ) = 2 then y 1 else y 2

theorem chain_contract (y : Fin 3 → Fin 2) :
    netContract (tableDecode chainNet chainTable) (chainExt y)
      = if (y 1 : ℕ) = 0 then
          (if (y 0 : ℕ) = 1 then (1 : ℂ) else 0) + (if (y 2 : ℕ) = 1 then (1 : ℂ) else 0)
        else 0 := by
  have hsum : netContract (tableDecode chainNet chainTable) (chainExt y)
      = ∑ p : Fin 2 × Fin 2, ∏ v : Fin 3, (tableDecode chainNet chainTable).tensor v
        (fun h : {h : Fin (chainNet).nh // (chainNet).site h = v} =>
          portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) h.val) := by
    rw [netContract]
    exact Fintype.sum_equiv chainEdgeEquiv _ _ (fun e => by rw [Equiv.symm_apply_apply]; rfl)
  rw [hsum]
  have hfin : ∀ p : Fin 2 × Fin 2,
      (∏ v : Fin 3, (tableDecode chainNet chainTable).tensor v
        (fun h : {h : Fin (chainNet).nh // (chainNet).site h = v} =>
          portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) h.val))
      = (if (y 0 : ℕ) = 0 then (if (p.1 : ℕ) = 0 then (1 : ℂ) else 0) else 1)
        * (if (y 1 : ℕ) = 0 ∧ (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)
        * (if (y 2 : ℕ) = 0 then (if (p.2 : ℕ) = 1 then (1 : ℂ) else 0) else 1) := by
    intro p
    have hfun0 : ∀ h : {h : Fin (chainNet).nh // (chainNet).site h = (0 : Fin 3)},
        portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) h.val =
          if (h.val : ℕ) = 0 then y 0 else p.1 := by
      intro h
      fin_cases h
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨0, by omega⟩ : Fin 7) = y 0
        rw [portValue_of_partner_none (N := tableDecode chainNet chainTable) _ _ _
          chain_partner_zero]
        rfl
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨1, by omega⟩ : Fin 7) =
          if (1 : ℕ) = 0 then y 0 else p.1
        rw [portValue_of_partner_eq (N := tableDecode chainNet chainTable) _ _
          (⟨1, by omega⟩ : Fin 7) (⟨3, by omega⟩ : Fin 7) chain_partner_one' (by decide)]
        rfl
    have hfun1 : ∀ h : {h : Fin (chainNet).nh // (chainNet).site h = (1 : Fin 3)},
        portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) h.val =
          if (h.val : ℕ) = 3 then p.1
          else if (h.val : ℕ) = 4 then p.2 else y 1 := by
      intro h
      fin_cases h
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨2, by omega⟩ : Fin 7) =
          if (2 : ℕ) = 3 then p.1 else if (2 : ℕ) = 4 then p.2 else y 1
        rw [portValue_of_partner_none (N := tableDecode chainNet chainTable) _ _ _
          chain_partner_two]
        rfl
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨3, by omega⟩ : Fin 7) =
          if (3 : ℕ) = 3 then p.1 else if (3 : ℕ) = 4 then p.2 else y 1
        rw [portValue_of_partner_eq_rev (N := tableDecode chainNet chainTable) _ _
          (⟨3, by omega⟩ : Fin 7) (⟨1, by omega⟩ : Fin 7) chain_partner_three' (by decide)
          chain_partner_one' (by rfl)]
        rfl
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨4, by omega⟩ : Fin 7) =
          if (4 : ℕ) = 3 then p.1 else if (4 : ℕ) = 4 then p.2 else y 1
        rw [portValue_of_partner_eq (N := tableDecode chainNet chainTable) _ _
          (⟨4, by omega⟩ : Fin 7) (⟨5, by omega⟩ : Fin 7) chain_partner_four' (by decide)]
        rfl
    have hfun2 : ∀ h : {h : Fin (chainNet).nh // (chainNet).site h = (2 : Fin 3)},
        portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) h.val =
          if (h.val : ℕ) = 5 then p.2 else y 2 := by
      intro h
      fin_cases h
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨5, by omega⟩ : Fin 7) =
          if (5 : ℕ) = 5 then p.2 else y 2
        rw [portValue_of_partner_eq_rev (N := tableDecode chainNet chainTable) _ _
          (⟨5, by omega⟩ : Fin 7) (⟨4, by omega⟩ : Fin 7) chain_partner_five' (by decide)
          chain_partner_four' (by rfl)]
        rfl
      · show portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) (⟨6, by omega⟩ : Fin 7) =
          if (6 : ℕ) = 5 then p.2 else y 2
        rw [portValue_of_partner_none (N := tableDecode chainNet chainTable) _ _ _
          chain_partner_six]
        rfl
    rw [Fin.prod_univ_three]
    show (tableDecode chainNet chainTable).tensor (0 : Fin 3)
        (fun h : {h : Fin (chainNet).nh // (chainNet).site h = (0 : Fin 3)} =>
          portValue (tableDecode chainNet chainTable) (chainExt y)
            (chainEdgeEquiv.symm p) h.val)
        * (tableDecode chainNet chainTable).tensor (1 : Fin 3)
          (fun h : {h : Fin (chainNet).nh // (chainNet).site h = (1 : Fin 3)} =>
            portValue (tableDecode chainNet chainTable) (chainExt y)
              (chainEdgeEquiv.symm p) h.val)
        * (tableDecode chainNet chainTable).tensor (2 : Fin 3)
          (fun h : {h : Fin (chainNet).nh // (chainNet).site h = (2 : Fin 3)} =>
            portValue (tableDecode chainNet chainTable) (chainExt y)
              (chainEdgeEquiv.symm p) h.val)
      = (if (y 0 : ℕ) = 0 then (if (p.1 : ℕ) = 0 then (1 : ℂ) else 0) else 1)
        * (if (y 1 : ℕ) = 0 ∧ (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)
        * (if (y 2 : ℕ) = 0 then (if (p.2 : ℕ) = 1 then (1 : ℂ) else 0) else 1)
    rw [tableDecode_tensor, tableDecode_tensor, tableDecode_tensor,
      chainTable_num_zero (0 : Fin 3) (by decide),
      chainTable_num_one (1 : Fin 3) (by decide),
      chainTable_num_two (2 : Fin 3) (by decide) (by decide),
      hfun0 ⟨(⟨0, by omega⟩ : Fin 7), chain_site_zero (0 : Fin 3) (by decide)⟩,
      hfun0 ⟨(⟨1, by omega⟩ : Fin 7), chain_site_one (0 : Fin 3) (by decide)⟩,
      hfun1 ⟨(⟨2, by omega⟩ : Fin 7), chain_site_two (1 : Fin 3) (by decide)⟩,
      hfun1 ⟨(⟨3, by omega⟩ : Fin 7), chain_site_three (1 : Fin 3) (by decide)⟩,
      hfun1 ⟨(⟨4, by omega⟩ : Fin 7), chain_site_four (1 : Fin 3) (by decide)⟩,
      hfun2 ⟨(⟨5, by omega⟩ : Fin 7), chain_site_five (2 : Fin 3) (by decide)⟩,
      hfun2 ⟨(⟨6, by omega⟩ : Fin 7), chain_site_six (2 : Fin 3) (by decide)⟩]
    have hy0 : (y 0 : ℕ) = 0 ∨ (y 0 : ℕ) = 1 := by have := (y 0).isLt; omega
    have hy1 : (y 1 : ℕ) = 0 ∨ (y 1 : ℕ) = 1 := by have := (y 1).isLt; omega
    have hy2 : (y 2 : ℕ) = 0 ∨ (y 2 : ℕ) = 1 := by have := (y 2).isLt; omega
    rcases p with ⟨a, b⟩; fin_cases a <;> fin_cases b <;>
      rcases hy0 with v0 | v0 <;> rcases hy1 with v1 | v1 <;> rcases hy2 with v2 | v2 <;>
      simp [gaussianRatComplex, chainNet, v0, v1, v2]
  simp only [hfin, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hy0 : (y 0 : ℕ) = 0 ∨ (y 0 : ℕ) = 1 := by have := (y 0).isLt; omega
  have hy1 : (y 1 : ℕ) = 0 ∨ (y 1 : ℕ) = 1 := by have := (y 1).isLt; omega
  have hy2 : (y 2 : ℕ) = 0 ∨ (y 2 : ℕ) = 1 := by have := (y 2).isLt; omega
  rcases hy0 with v0 | v0 <;> rcases hy1 with v1 | v1 <;> rcases hy2 with v2 | v2 <;>
    simp [v0, v1, v2]

theorem chain_contract_eq_mpsAmplitude (y : Fin 3 → Fin 2) :
    netContract (tableDecode chainNet chainTable) (chainExt y)
      = @mpsAmplitude 3 2 2 _ shortChainTensors y := by
  rw [chain_contract, short_chain_consumer]

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.FiniteTensorTableCodec
