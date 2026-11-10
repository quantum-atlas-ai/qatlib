/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.Lemma1Tau
import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.Lemma2Bijection
import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.Lemma7ControlledFunction
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath

abbrev CMem (n m w : ℕ) := Reg n × (Reg m × Reg w)

structure BGate (n m w : ℕ) where

  op : CMem n m w ≃ CMem n m w

  keepsIn : ∀ x, (op x).1 = x.1

def runGates {n m w : ℕ} : List (BGate n m w) → CMem n m w → CMem n m w
  | [], x => x
  | g :: gs, x => runGates gs (g.op x)

def runGatesEquiv {n m w : ℕ} : List (BGate n m w) → (CMem n m w ≃ CMem n m w)
  | [] => Equiv.refl _
  | g :: gs => g.op.trans (runGatesEquiv gs)

theorem runGates_eq {n m w : ℕ} (gs : List (BGate n m w)) (x : CMem n m w) :
    runGates gs x = runGatesEquiv gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih (g.op x)

theorem runGates_keepsIn {n m w : ℕ} (gs : List (BGate n m w)) (x : CMem n m w) :
    (runGates gs x).1 = x.1 := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [runGates, ih, g.keepsIn]

def Computes {n m w : ℕ} (F : Reg n → Reg m) (gs : List (BGate n m w)) : Prop :=
  ∀ u, (runGates gs (u, ZeroStr m, ZeroStr w)).2.1 = F u

theorem Computes.equiv {n m w : ℕ} {F : Reg n → Reg m} {gs : List (BGate n m w)}
    (h : Computes F gs) (u : Reg n) :
    (runGatesEquiv gs (u, ZeroStr m, ZeroStr w)).2.1 = F u := by
  rw [← runGates_eq]
  exact h u

theorem liftCore_trans {n m w : ℕ} (C D : CMem n m w ≃ CMem n m w) (x : Mem n m w) :
    liftCore (C.trans D) x = liftCore D (liftCore C x) := by
  obtain ⟨u, v, y, g⟩ := x
  rfl

theorem runOps_map_liftCore {n m w : ℕ} (gs : List (BGate n m w)) (x : Mem n m w) :
    runOps (gs.map (fun g => (⟨liftCore g.op, 1⟩ : RevStep (Mem n m w)))) x
      = liftCore (runGatesEquiv gs) x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runOps]
    rw [ih]
    show liftCore (runGatesEquiv gs) (liftCore g.op x) =
      liftCore (g.op.trans (runGatesEquiv gs)) x
    rw [liftCore_trans]

theorem seqCost_map_liftCore {n m w : ℕ} (gs : List (BGate n m w)) :
    seqCost (gs.map (fun g => (⟨liftCore g.op, 1⟩ : RevStep (Mem n m w)))) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, seqCost, ih, List.length_cons]
    exact Nat.add_comm 1 gs.length

theorem lemma1_compiled
    {n m w : ℕ} (F : Reg n → Reg m) (gs : List (BGate n m w))
    (hcomp : Computes F gs)
    (B : RevBasis (Mem n m w))
    (hB : ∀ g ∈ gs, B.mem (liftCore g.op))
    (hτ : B.mem (tauCopyEquiv n m w)) :
    ∃ s : List (RevStep (Mem n m w)),
      seqCost s = 2 * gs.length + m ∧ AllIn B s ∧
        ∀ (u : Reg n) (v : Reg m),
          runOps s (u, v, ZeroStr m, ZeroStr w) =
            (u, bxor v (F u), ZeroStr m, ZeroStr w) := by
  refine lemma1_tau_representable F (runGatesEquiv gs) ?_ ?_ B
    (gs.map (fun g => (⟨liftCore g.op, 1⟩ : RevStep (Mem n m w))))
    (fun x => runOps_map_liftCore gs x) ?_ hτ gs.length (seqCost_map_liftCore gs)
  · intro u
    rw [← runGates_eq]
    exact runGates_keepsIn gs (u, ZeroStr m, ZeroStr w)
  · intro u
    exact Computes.equiv hcomp u
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨g, hg, rfl⟩ := ht
    exact hB g hg

theorem liftFunG_trans {k l n w : ℕ} (C D : CMem k l w ≃ CMem k l w)
    (x : FunMem k l n w) :
    liftFunG (C.trans D) x = liftFunG D (liftFunG C x) := by
  obtain ⟨a, ξ, y, g⟩ := x
  rfl

theorem runOps_map_liftFunG {k l n w : ℕ} (gs : List (BGate k l w))
    (x : FunMem k l n w) :
    runOps (gs.map (fun g => (⟨liftFunG g.op, 1⟩ : RevStep (FunMem k l n w)))) x
      = liftFunG (runGatesEquiv gs) x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runOps]
    rw [ih]
    show liftFunG (runGatesEquiv gs) (liftFunG g.op x) =
      liftFunG (g.op.trans (runGatesEquiv gs)) x
    rw [liftFunG_trans]

theorem seqCost_map_liftFunG {k l n w : ℕ} (gs : List (BGate k l w)) :
    seqCost (gs.map (fun g => (⟨liftFunG g.op, 1⟩ : RevStep (FunMem k l n w)))) =
      gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, seqCost, ih, List.length_cons]
    exact Nat.add_comm 1 gs.length

theorem lemma7_compiled
    {k l n w : ℕ} (F : Reg k → Reg l) (U : Reg l → Reg n ≃ Reg n)
    (gs : List (BGate k l w)) (hcomp : Computes F gs)
    (B : RevBasis (FunMem k l n w))
    (hB : ∀ g ∈ gs, B.mem (liftFunG g.op))
    (hT : B.mem (ctrlFun U)) :
    ∃ s : List (RevStep (FunMem k l n w)),
      seqCost s = 2 * gs.length + 1 ∧ AllIn B s ∧
        ∀ (a : Reg k) (ξ : Reg n),
          runOps s (a, ξ, ZeroStr l, ZeroStr w) = (a, U (F a) ξ, ZeroStr l, ZeroStr w) := by
  have h := lemma7_controlled_function F U (runGatesEquiv gs)
    (fun a => by rw [← runGates_eq]; exact runGates_keepsIn gs (a, ZeroStr l, ZeroStr w))
    (fun a => Computes.equiv hcomp a)
    B (gs.map (fun g => (⟨liftFunG g.op, 1⟩ : RevStep (FunMem k l n w))))
    (fun x => runOps_map_liftFunG gs x) ?_ hT gs.length (seqCost_map_liftFunG gs)
  · obtain ⟨hcost, hall, hact, -⟩ := h
    exact ⟨_, hcost, hall, hact⟩
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨g, hg, rfl⟩ := ht
    exact hB g hg

abbrev L2Mem (n w : ℕ) := Mem n n w

def swapXYMem (n w : ℕ) : L2Mem n w ≃ L2Mem n w where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by obtain ⟨a, b, y, g⟩ := x; rfl
  right_inv x := by obtain ⟨a, b, y, g⟩ := x; rfl

def tauXYMem (n w : ℕ) (x : L2Mem n w) : L2Mem n w :=
  (x.1, (bxor x.2.1 x.1, x.2.2))

theorem tauXYMem_involutive (n w : ℕ) : Function.Involutive (@tauXYMem n w) := by
  intro x
  obtain ⟨a, b, y, g⟩ := x
  simp only [tauXYMem, bxor_bxor_cancel]

def tauXYEquiv (n w : ℕ) : L2Mem n w ≃ L2Mem n w := (tauXYMem_involutive n w).toPerm

theorem tauXYEquiv_apply (n w : ℕ) (x : L2Mem n w) :
    tauXYEquiv n w x = tauXYMem n w x := rfl

def tauYXMem (n w : ℕ) (x : L2Mem n w) : L2Mem n w :=
  (bxor x.1 x.2.1, (x.2.1, x.2.2))

theorem tauYXMem_involutive (n w : ℕ) : Function.Involutive (@tauYXMem n w) := by
  intro x
  obtain ⟨a, b, y, g⟩ := x
  simp only [tauYXMem, bxor_bxor_cancel]

def tauYXEquiv (n w : ℕ) : L2Mem n w ≃ L2Mem n w := (tauYXMem_involutive n w).toPerm

theorem tauYXEquiv_apply (n w : ℕ) (x : L2Mem n w) :
    tauYXEquiv n w x = tauYXMem n w x := rfl

theorem lemma2_compiled
    {n w : ℕ} (G : Reg n ≃ Reg n) (L L' : ℕ)
    (gsG : List (BGate n n w)) (hG : Computes (fun u => G u) gsG)
    (hGL : gsG.length = L)
    (gsGi : List (BGate n n w)) (hGi : Computes (fun u => G.symm u) gsGi)
    (hGiL : gsGi.length = L')
    (B : RevBasis (L2Mem n w))
    (hB : ∀ g ∈ gsG, B.mem (liftCore g.op))
    (hBi : ∀ g ∈ gsGi, B.mem (liftCore g.op))
    (hτ : B.mem (tauCopyEquiv n n w))
    (hswap : ∀ t : RevStep (L2Mem n w), B.mem t.op →
      B.mem ((swapXYMem n w).symm.trans (t.op.trans (swapXYMem n w))))
    (hτXY : B.mem (tauXYEquiv n w))
    (hτYX : B.mem (tauYXEquiv n w)) :
    ∃ s : List (RevStep (L2Mem n w)),
      seqCost s = 2 * L + 2 * L' + 4 * n ∧ AllIn B s ∧
        ∀ x : Reg n,
          runOps s (x, ZeroStr n, ZeroStr n, ZeroStr w) =
            (G x, ZeroStr n, ZeroStr n, ZeroStr w) := by
  obtain ⟨s1, hs1c, hs1in, hs1act⟩ := lemma1_compiled (fun u => G u) gsG hG B hB hτ
  obtain ⟨s2, hs2c, hs2in, hs2act⟩ := lemma1_compiled (fun u => G.symm u) gsGi hGi B hBi hτ
  let s2' : List (RevStep (L2Mem n w)) := relabelSeq (swapXYMem n w) s2
  have hs2'in : AllIn B s2' := by
    intro t ht
    simp only [s2', relabelSeq, List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact hswap u (hs2in u hu)
  have hs2'c : seqCost s2' = seqCost s2 := seqCost_relabel (swapXYMem n w) s2
  refine ⟨s1 ++ (s2' ++ [⟨tauYXEquiv n w, n⟩, ⟨tauXYEquiv n w, n⟩]), ?_, ?_, ?_⟩
  · rw [seqCost_append, seqCost_append, hs1c, hs2'c, hs2c]
    simp only [seqCost, Nat.add_zero]
    rw [hGL, hGiL]
    omega
  · refine allIn_append B hs1in (allIn_append B hs2'in ?_)
    exact allIn_append B (allIn_singleton B hτYX) (allIn_singleton B hτXY)
  · intro x
    have h1 : runOps s1 (x, ZeroStr n, ZeroStr n, ZeroStr w) =
        (x, G x, ZeroStr n, ZeroStr w) := by
      have h := hs1act x (ZeroStr n)
      simpa [bxor_zero_left] using h
    have h2 : runOps s2' (x, G x, ZeroStr n, ZeroStr w) =
        (ZeroStr n, G x, ZeroStr n, ZeroStr w) := by
      rw [show s2' = relabelSeq (swapXYMem n w) s2 from rfl, runOps_relabel]
      rw [show (swapXYMem n w).symm (x, G x, ZeroStr n, ZeroStr w) =
        (G x, x, ZeroStr n, ZeroStr w) from rfl]
      rw [hs2act (G x) x]
      simp only [Equiv.symm_apply_apply]
      rw [bxor_self]
      rfl
    have h3 : runOps [⟨tauYXEquiv n w, n⟩, ⟨tauXYEquiv n w, n⟩]
        (ZeroStr n, G x, ZeroStr n, ZeroStr w) =
          (G x, ZeroStr n, ZeroStr n, ZeroStr w) := by
      rw [runOps_pair]
      simp [tauYXEquiv_apply, tauXYEquiv_apply, tauYXMem, tauXYMem,
        bxor_zero_left, bxor_self]
    calc runOps (s1 ++ (s2' ++ [⟨tauYXEquiv n w, n⟩, ⟨tauXYEquiv n w, n⟩]))
          (x, ZeroStr n, ZeroStr n, ZeroStr w)
        = runOps (s2' ++ [⟨tauYXEquiv n w, n⟩, ⟨tauXYEquiv n w, n⟩])
            (runOps s1 (x, ZeroStr n, ZeroStr n, ZeroStr w)) := by rw [runOps_append]
      _ = runOps [⟨tauYXEquiv n w, n⟩, ⟨tauXYEquiv n w, n⟩]
            (runOps s2' (runOps s1 (x, ZeroStr n, ZeroStr n, ZeroStr w))) := by
            rw [runOps_append]
      _ = runOps [⟨tauYXEquiv n w, n⟩, ⟨tauXYEquiv n w, n⟩]
            (ZeroStr n, G x, ZeroStr n, ZeroStr w) := by rw [h1, h2]
      _ = _ := h3

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
