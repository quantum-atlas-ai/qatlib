/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

def bxor {n : ℕ} (a b : Reg n) : Reg n := fun i => Bool.xor (a i) (b i)

@[simp] theorem bxor_apply {n : ℕ} (a b : Reg n) (i : Fin n) :
    bxor a b i = Bool.xor (a i) (b i) := rfl

theorem bxor_comm {n : ℕ} (a b : Reg n) : bxor a b = bxor b a := by
  funext i; simp [bxor, Bool.xor_comm]

theorem bxor_assoc {n : ℕ} (a b c : Reg n) :
    bxor (bxor a b) c = bxor a (bxor b c) := by
  funext i; simp [bxor]

theorem bxor_self {n : ℕ} (a : Reg n) : bxor a a = ZeroStr n := by
  funext i; simp [bxor, ZeroStr]

theorem bxor_bxor_cancel {n : ℕ} (v w : Reg n) : bxor (bxor v w) w = v := by
  funext i
  simp only [bxor_apply]
  cases v i <;> cases w i <;> rfl

theorem bxor_zero {n : ℕ} (v : Reg n) : bxor v (ZeroStr n) = v := by
  funext i; simp [bxor, ZeroStr]

theorem bxor_zero_left {n : ℕ} (v : Reg n) : bxor (ZeroStr n) v = v := by
  funext i; simp [bxor, ZeroStr]

structure RevStep (Γ : Type) where

  op : Γ ≃ Γ

  cost : ℕ

def seqCost {Γ : Type} : List (RevStep Γ) → ℕ
  | [] => 0
  | s :: ss => s.cost + seqCost ss

def runOps {Γ : Type} : List (RevStep Γ) → Γ → Γ
  | [], x => x
  | s :: ss, x => runOps ss (s.op x)

@[simp] theorem seqCost_append {Γ : Type} (a b : List (RevStep Γ)) :
    seqCost (a ++ b) = seqCost a + seqCost b := by
  induction a with
  | nil => simp [seqCost]
  | cons s ss ih => simp [seqCost, ih, Nat.add_assoc]

theorem runOps_append {Γ : Type} (a b : List (RevStep Γ)) (x : Γ) :
    runOps (a ++ b) x = runOps b (runOps a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons s ss ih => simp [runOps, ih]

theorem runOps_reverse_map_symm {Γ : Type} (s : List (RevStep Γ)) (x : Γ) :
    runOps (s.reverse.map (fun t => ⟨t.op.symm, t.cost⟩)) (runOps s x) = x := by
  induction s generalizing x with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, runOps] at ih ⊢
    rw [runOps_append]
    simp only [runOps]
    rw [ih]
    exact t.op.symm_apply_apply x

structure RevBasis (Γ : Type) where

  mem : (Γ ≃ Γ) → Prop

  inv_mem : ∀ g, mem g → mem g.symm

def AllIn {Γ : Type} (B : RevBasis Γ) (s : List (RevStep Γ)) : Prop := ∀ t ∈ s, B.mem t.op

theorem allIn_reverse_symm {Γ : Type} (B : RevBasis Γ) {s : List (RevStep Γ)}
    (hs : AllIn B s) :
    AllIn B (s.reverse.map (fun t => ⟨t.op.symm, t.cost⟩)) := by
  intro t ht
  simp only [List.mem_map, List.mem_reverse] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact B.inv_mem u.op (hs u hu)

theorem allIn_append {Γ : Type} (B : RevBasis Γ) {a b : List (RevStep Γ)}
    (ha : AllIn B a) (hb : AllIn B b) : AllIn B (a ++ b) := by
  intro t ht
  rw [List.mem_append] at ht
  exact ht.elim (ha t) (hb t)

theorem allIn_singleton {Γ : Type} (B : RevBasis Γ) {t : RevStep Γ}
    (h : B.mem t.op) : AllIn B [t] := by
  intro u hu
  simp only [List.mem_singleton] at hu
  subst hu
  exact h

theorem seqCost_revMap {Γ : Type} (s : List (RevStep Γ)) :
    seqCost (s.reverse.map (fun t => ⟨t.op.symm, t.cost⟩)) = seqCost s := by
  induction s with
  | nil => rfl
  | cons t ts ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, seqCost_append]
    simp only [seqCost, ih, List.map_nil, Nat.add_zero]
    omega

def reverseSeq {Γ : Type} (s : List (RevStep Γ)) : List (RevStep Γ) :=
  s.reverse.map (fun t => ⟨t.op.symm, t.cost⟩)

theorem seqCost_reverseSeq {Γ : Type} (s : List (RevStep Γ)) :
    seqCost (reverseSeq s) = seqCost s :=
  seqCost_revMap s

theorem runOps_reverseSeq {Γ : Type} (s : List (RevStep Γ)) (x : Γ) :
    runOps (reverseSeq s) (runOps s x) = x :=
  runOps_reverse_map_symm s x

theorem allIn_reverseSeq {Γ : Type} (B : RevBasis Γ) {s : List (RevStep Γ)}
    (hs : AllIn B s) : AllIn B (reverseSeq s) :=
  allIn_reverse_symm B hs

theorem runOps_pair {Γ : Type} (a b : RevStep Γ) (y : Γ) :
    runOps [a, b] y = b.op (a.op y) := rfl

def Ftau {n m : ℕ} (F : Reg n → Reg m) : Reg n × Reg m → Reg n × Reg m :=
  fun p => (p.1, bxor p.2 (F p.1))

theorem Ftau_involutive {n m : ℕ} (F : Reg n → Reg m) :
    Function.Involutive (Ftau F) := by
  intro p
  simp only [Ftau, bxor_bxor_cancel]

def FtauEquiv {n m : ℕ} (F : Reg n → Reg m) : (Reg n × Reg m) ≃ (Reg n × Reg m) :=
  (Ftau_involutive F).toPerm

@[simp] theorem FtauEquiv_apply {n m : ℕ} (F : Reg n → Reg m) (p : Reg n × Reg m) :
    FtauEquiv F p = Ftau F p := rfl

abbrev Mem (n m w : ℕ) := Reg n × Reg m × Reg m × Reg w

def liftCore {n m w : ℕ}
    (C : (Reg n × (Reg m × Reg w)) ≃ (Reg n × (Reg m × Reg w))) : Mem n m w ≃ Mem n m w where
  toFun x := ((C (x.1, (x.2.2.1, x.2.2.2))).1, x.2.1, (C (x.1, (x.2.2.1, x.2.2.2))).2)
  invFun x := ((C.symm (x.1, (x.2.2.1, x.2.2.2))).1, x.2.1, (C.symm (x.1, (x.2.2.1, x.2.2.2))).2)
  left_inv x := by
    simp only [Prod.mk.eta]
    rw [C.symm_apply_apply]
  right_inv x := by
    simp only [Prod.mk.eta]
    rw [C.apply_symm_apply]

@[simp] theorem liftCore_apply {n m w : ℕ}
    (C : (Reg n × (Reg m × Reg w)) ≃ (Reg n × (Reg m × Reg w))) (x : Mem n m w) :
    liftCore C x = ((C (x.1, (x.2.2.1, x.2.2.2))).1, x.2.1,
      (C (x.1, (x.2.2.1, x.2.2.2))).2) := rfl

theorem liftCore_symm {n m w : ℕ}
    (C : (Reg n × (Reg m × Reg w)) ≃ (Reg n × (Reg m × Reg w))) :
    (liftCore C).symm = liftCore C.symm := by
  ext x <;> simp [liftCore]

def tauCopy {n m w : ℕ} (x : Mem n m w) : Mem n m w :=
  (x.1, bxor x.2.1 x.2.2.1, x.2.2.1, x.2.2.2)

theorem tauCopy_involutive {n m w : ℕ} : Function.Involutive (@tauCopy n m w) := by
  intro x
  simp only [tauCopy, bxor_bxor_cancel]

def tauCopyEquiv (n m w : ℕ) : Mem n m w ≃ Mem n m w := tauCopy_involutive.toPerm

@[simp] theorem tauCopyEquiv_apply {n m w : ℕ} (x : Mem n m w) :
    tauCopyEquiv n m w x = tauCopy x := rfl

def copyXY {n : ℕ} (p : Reg n × Reg n) : Reg n × Reg n := (p.1, bxor p.2 p.1)

theorem copyXY_involutive {n : ℕ} : Function.Involutive (@copyXY n) := by
  intro p; simp only [copyXY, bxor_bxor_cancel]

def copyXYEquiv (n : ℕ) : (Reg n × Reg n) ≃ (Reg n × Reg n) :=
  (copyXY_involutive (n := n)).toPerm

@[simp] theorem copyXYEquiv_apply {n : ℕ} (p : Reg n × Reg n) :
    copyXYEquiv n p = copyXY p := rfl

def copyYX {n : ℕ} (p : Reg n × Reg n) : Reg n × Reg n := (bxor p.1 p.2, p.2)

theorem copyYX_involutive {n : ℕ} : Function.Involutive (@copyYX n) := by
  intro p
  simp only [copyYX, bxor_bxor_cancel]

def copyYXEquiv (n : ℕ) : (Reg n × Reg n) ≃ (Reg n × Reg n) :=
  (copyYX_involutive (n := n)).toPerm

@[simp] theorem copyYXEquiv_apply {n : ℕ} (p : Reg n × Reg n) :
    copyYXEquiv n p = copyYX p := rfl

def swapPair (n : ℕ) : (Reg n × Reg n) ≃ (Reg n × Reg n) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

def relabelSeq {Γ Δ : Type} (e : Γ ≃ Δ) (s : List (RevStep Γ)) : List (RevStep Δ) :=
  s.map (fun t => ⟨e.symm.trans (t.op.trans e), t.cost⟩)

theorem seqCost_relabel {Γ Δ : Type} (e : Γ ≃ Δ) (s : List (RevStep Γ)) :
    seqCost (relabelSeq e s) = seqCost s := by
  induction s with
  | nil => rfl
  | cons t ts ih =>
    simp only [relabelSeq, List.map_cons, seqCost] at ih ⊢
    rw [ih]

theorem runOps_relabel {Γ Δ : Type} (e : Γ ≃ Δ) (s : List (RevStep Γ)) (x : Δ) :
    runOps (relabelSeq e s) x = e (runOps s (e.symm x)) := by
  induction s generalizing x with
  | nil => simp [relabelSeq, runOps, e.apply_symm_apply]
  | cons t ts ih =>
    simp only [relabelSeq, List.map_cons, runOps, Equiv.trans_apply] at ih ⊢
    rw [ih, e.symm_apply_apply]

abbrev CtrlMem (n : ℕ) := Bool × Reg n × Reg n

def lamTauAB {n : ℕ} (x : CtrlMem n) : CtrlMem n :=
  (x.1, x.2.1, if x.1 then bxor x.2.2 x.2.1 else x.2.2)

theorem lamTauAB_involutive {n : ℕ} : Function.Involutive (@lamTauAB n) := by
  intro x
  obtain ⟨a, ξ, η⟩ := x
  cases a <;> simp [lamTauAB, bxor_bxor_cancel]

def lamTauABEquiv (n : ℕ) : CtrlMem n ≃ CtrlMem n :=
  (lamTauAB_involutive (n := n)).toPerm

@[simp] theorem lamTauABEquiv_apply {n : ℕ} (x : CtrlMem n) :
    lamTauABEquiv n x = lamTauAB x := rfl

def lamTauBA {n : ℕ} (x : CtrlMem n) : CtrlMem n :=
  (x.1, if x.1 then bxor x.2.1 x.2.2 else x.2.1, x.2.2)

theorem lamTauBA_involutive {n : ℕ} : Function.Involutive (@lamTauBA n) := by
  intro x
  obtain ⟨a, ξ, η⟩ := x
  cases a <;> simp [lamTauBA, bxor_bxor_cancel]

def lamTauBAEquiv (n : ℕ) : CtrlMem n ≃ CtrlMem n :=
  (lamTauBA_involutive (n := n)).toPerm

@[simp] theorem lamTauBAEquiv_apply {n : ℕ} (x : CtrlMem n) :
    lamTauBAEquiv n x = lamTauBA x := rfl

def liftU {n : ℕ} (U : Reg n ≃ Reg n) : CtrlMem n ≃ CtrlMem n where
  toFun x := (x.1, x.2.1, U x.2.2)
  invFun x := (x.1, x.2.1, U.symm x.2.2)
  left_inv x := by obtain ⟨a, ξ, η⟩ := x; simp only [U.symm_apply_apply]
  right_inv x := by obtain ⟨a, ξ, η⟩ := x; simp only [U.apply_symm_apply]

@[simp] theorem liftU_apply {n : ℕ} (U : Reg n ≃ Reg n) (x : CtrlMem n) :
    liftU U x = (x.1, x.2.1, U x.2.2) := rfl

abbrev CtrlFunMem (k l n : ℕ) := Reg k × Reg n × Reg l

def ctrlFamily {k l n : ℕ} (U : Reg l → Reg n ≃ Reg n) :
    CtrlFunMem k l n ≃ CtrlFunMem k l n where
  toFun x := (x.1, U x.2.2 x.2.1, x.2.2)
  invFun x := (x.1, (U x.2.2).symm x.2.1, x.2.2)
  left_inv x := by obtain ⟨a, ξ, w⟩ := x; simp only [(U w).symm_apply_apply]
  right_inv x := by obtain ⟨a, ξ, w⟩ := x; simp only [(U w).apply_symm_apply]

@[simp] theorem ctrlFamily_apply {k l n : ℕ} (U : Reg l → Reg n ≃ Reg n)
    (x : CtrlFunMem k l n) :
    ctrlFamily U x = (x.1, U x.2.2 x.2.1, x.2.2) := rfl

def ctrlFamilyComp {k l n : ℕ} (U : Reg l → Reg n ≃ Reg n) (F : Reg k → Reg l) :
    CtrlFunMem k l n ≃ CtrlFunMem k l n where
  toFun x := (x.1, U (F x.1) x.2.1, x.2.2)
  invFun x := (x.1, (U (F x.1)).symm x.2.1, x.2.2)
  left_inv x := by obtain ⟨a, ξ, w⟩ := x; simp only [(U (F a)).symm_apply_apply]
  right_inv x := by obtain ⟨a, ξ, w⟩ := x; simp only [(U (F a)).apply_symm_apply]

@[simp] theorem ctrlFamilyComp_apply {k l n : ℕ} (U : Reg l → Reg n ≃ Reg n)
    (F : Reg k → Reg l) (x : CtrlFunMem k l n) :
    ctrlFamilyComp U F x = (x.1, U (F x.1) x.2.1, x.2.2) := rfl

def liftFun {k l n : ℕ} (C : (Reg k × Reg l) ≃ (Reg k × Reg l)) :
    CtrlFunMem k l n ≃ CtrlFunMem k l n where
  toFun x := ((C (x.1, x.2.2)).1, x.2.1, (C (x.1, x.2.2)).2)
  invFun x := ((C.symm (x.1, x.2.2)).1, x.2.1, (C.symm (x.1, x.2.2)).2)
  left_inv x := by simp only [Prod.mk.eta]; rw [C.symm_apply_apply]
  right_inv x := by simp only [Prod.mk.eta]; rw [C.apply_symm_apply]

@[simp] theorem liftFun_apply {k l n : ℕ} (C : (Reg k × Reg l) ≃ (Reg k × Reg l))
    (x : CtrlFunMem k l n) :
    liftFun C x = ((C (x.1, x.2.2)).1, x.2.1, (C (x.1, x.2.2)).2) := rfl

theorem liftFun_apply_inv {k l n : ℕ} (C : (Reg k × Reg l) ≃ (Reg k × Reg l))
    (x : CtrlFunMem k l n) :
    (liftFun (n := n) C).symm (liftFun (n := n) C x) = x :=
  (liftFun (n := n) C).symm_apply_apply x

abbrev FunMem (k l n w : ℕ) := Reg k × Reg n × Reg l × Reg w

def liftFunG {k l n w : ℕ}
    (C : (Reg k × (Reg l × Reg w)) ≃ (Reg k × (Reg l × Reg w))) :
    FunMem k l n w ≃ FunMem k l n w where
  toFun x := ((C (x.1, (x.2.2.1, x.2.2.2))).1, x.2.1,
    (C (x.1, (x.2.2.1, x.2.2.2))).2.1, (C (x.1, (x.2.2.1, x.2.2.2))).2.2)
  invFun x := ((C.symm (x.1, (x.2.2.1, x.2.2.2))).1, x.2.1,
    (C.symm (x.1, (x.2.2.1, x.2.2.2))).2.1, (C.symm (x.1, (x.2.2.1, x.2.2.2))).2.2)
  left_inv x := by
    obtain ⟨a, ξ, y, g⟩ := x
    simp only [C.symm_apply_apply]
  right_inv x := by
    obtain ⟨a, ξ, y, g⟩ := x
    simp only [C.apply_symm_apply]

@[simp] theorem liftFunG_apply {k l n w : ℕ}
    (C : (Reg k × (Reg l × Reg w)) ≃ (Reg k × (Reg l × Reg w))) (x : FunMem k l n w) :
    liftFunG C x = ((C (x.1, (x.2.2.1, x.2.2.2))).1, x.2.1,
      (C (x.1, (x.2.2.1, x.2.2.2))).2.1, (C (x.1, (x.2.2.1, x.2.2.2))).2.2) := rfl

def ctrlFun {k l n w : ℕ} (U : Reg l → Reg n ≃ Reg n) :
    FunMem k l n w ≃ FunMem k l n w where
  toFun x := (x.1, U x.2.2.1 x.2.1, x.2.2.1, x.2.2.2)
  invFun x := (x.1, (U x.2.2.1).symm x.2.1, x.2.2.1, x.2.2.2)
  left_inv x := by obtain ⟨a, ξ, y, g⟩ := x; simp only [(U y).symm_apply_apply]
  right_inv x := by obtain ⟨a, ξ, y, g⟩ := x; simp only [(U y).apply_symm_apply]

@[simp] theorem ctrlFun_apply {k l n w : ℕ} (U : Reg l → Reg n ≃ Reg n)
    (x : FunMem k l n w) :
    ctrlFun U x = (x.1, U x.2.2.1 x.2.1, x.2.2.1, x.2.2.2) := rfl

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
