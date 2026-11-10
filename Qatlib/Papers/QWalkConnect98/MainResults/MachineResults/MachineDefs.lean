/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Basic

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

open Finset
open scoped BigOperators

set_option autoImplicit false

structure GraphInstance (d : ℕ) where

  V : Type

  [instFintype : Fintype V]

  [instDecEq : DecidableEq V]

  G : SimpleGraph V

  [instDecRel : DecidableRel G.Adj]

  regular : ∀ v : V, (G.neighborFinset v).card = d

  s : V

  t : V

def InstanceSize {d : ℕ} (I : GraphInstance d) : ℕ := @Fintype.card I.V I.instFintype

def InstanceConnected {d : ℕ} (I : GraphInstance d) : Prop := I.G.Reachable I.s I.t

structure QTM where

  space : ℕ → ℕ

  steps : ℕ → ℕ

  acceptProb : List Bool → ℝ

  acceptProb_nonneg : ∀ x, 0 ≤ acceptProb x

  acceptProb_le_one : ∀ x, acceptProb x ≤ 1

def LogSpace (M : QTM) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, M.space n ≤ c * (Nat.log2 (n + 1) + 1)

def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, f n ≤ (n + 2) ^ c

def PolyTime (M : QTM) : Prop := PolyBounded M.steps

def DecidesOneSided (M : QTM) (P : List Bool → Prop) (p : ℝ) : Prop :=
  (∀ x, P x → p ≤ M.acceptProb x) ∧ (∀ x, ¬ P x → M.acceptProb x = 0)

def InQRHL (P : List Bool → Prop) : Prop :=
  ∃ M : QTM, LogSpace M ∧ PolyTime M ∧ DecidesOneSided M P (1 / 2)

def Reduces (A B : List Bool → Prop) : Prop :=
  ∃ f : List Bool → List Bool, ∀ x, A x ↔ B (f x)

def InSL (A : List Bool → Prop) : Prop :=
  ∃ (d : ℕ) (decode : List Bool → GraphInstance d),
    3 ≤ d ∧ Reduces A (fun x => InstanceConnected (decode x))

structure ReversibleMachine (W : Type*) where

  space : ℕ → ℕ

  transform : List Bool → W ≃ W

  steps : List Bool → W → ℕ

def ReversibleMachine.LogSpace {W : Type*} (M : ReversibleMachine W) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, M.space n ≤ c * (Nat.log2 (n + 1) + 1)

structure USTCONMachine (d : ℕ) where

  space : ℕ → ℕ

  steps : GraphInstance d → ℕ

  acceptProb : GraphInstance d → ℝ

  acceptProb_nonneg : ∀ I, 0 ≤ acceptProb I

  acceptProb_le_one : ∀ I, acceptProb I ≤ 1

def USTCONMachine.LogSpace {d : ℕ} (M : USTCONMachine d) : Prop :=
  ∃ c : ℕ, ∀ I : GraphInstance d, M.space (InstanceSize I) ≤ c * (Nat.log2 (InstanceSize I + 1) + 1)

def USTCONMachine.PolyTime {d : ℕ} (M : USTCONMachine d) : Prop :=
  ∃ c : ℕ, ∀ I : GraphInstance d, M.steps I ≤ (InstanceSize I + 1) ^ c

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
