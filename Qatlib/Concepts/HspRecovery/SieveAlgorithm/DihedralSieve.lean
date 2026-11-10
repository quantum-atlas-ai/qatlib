/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Probability.Distributions.Uniform
import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralSummandExtraction
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm

open Qatlib

def zeroBitsGE (n t : ℕ) (k : ZMod (2 ^ n)) : Prop := k.val % 2 ^ t = 0

def windowAgree (n w t : ℕ) (k ℓ : ZMod (2 ^ n)) : Prop :=
  (k.val / 2 ^ t) % 2 ^ w = (ℓ.val / 2 ^ t) % 2 ^ w

instance instDecidableWindowAgree (n w t : ℕ) (k ℓ : ZMod (2 ^ n)) :
    Decidable (windowAgree n w t k ℓ) :=
  inferInstanceAs (Decidable ((k.val / 2 ^ t) % 2 ^ w = (ℓ.val / 2 ^ t) % 2 ^ w))

def sieveWindowWidth (n m j : ℕ) : ℕ := min m (n - 1 - m * j)

noncomputable def sievePairWith (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (L : List α) : List (α × α) := by
  set_option linter.unusedVariables false in
  match L with
  | [] => exact []
  | r :: rest =>
    match h : rest.find? (fun r' => decide (windowAgree n w t (label r) (label r'))) with
    | none => exact sievePairWith n label w t rest
    | some r' => exact (r, r') :: sievePairWith n label w t (rest.erase r')
termination_by L.length
decreasing_by
  · simp
  · have hm : r' ∈ rest := List.mem_of_find?_eq_some h
    have h1 := List.length_erase_add_one hm
    simp
    omega

noncomputable def sievePair (n w t : ℕ) (L : List (ZMod (2 ^ n))) :
    List (ZMod (2 ^ n) × ZMod (2 ^ n)) :=
  sievePairWith n (α := ZMod (2 ^ n)) id w t L

noncomputable def dihedralIdealRecordLaw (n : ℕ) : PMF (ZMod (2 ^ n)) :=
  PMF.uniformOfFintype' (ZMod (2 ^ n))

noncomputable def idealFreshRecords (n : ℕ) :
    ℕ → PMF (List (ZMod (2 ^ n)))
  | 0 => pure []
  | i + 1 =>
    (dihedralIdealRecordLaw n).bind fun r =>
      (idealFreshRecords n i).map fun L => r :: L

noncomputable def idealLayerAux (n : ℕ) :
    List (ZMod (2 ^ n) × ZMod (2 ^ n)) → PMF (List (ZMod (2 ^ n)))
  | [] => pure []
  | (r, r') :: ps =>
    (PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (idealLayerAux n ps).map fun tail =>
        if b = 1 then (r' - r) :: tail else tail

noncomputable def idealLayer (n m j : ℕ) (L : List (ZMod (2 ^ n))) :
    PMF (List (ZMod (2 ^ n))) :=
  idealLayerAux n (sievePair n (sieveWindowWidth n m j) (m * j) L)

noncomputable def idealSieveRec (n m : ℕ) :
    ℕ → List (ZMod (2 ^ n)) → PMF (List (ZMod (2 ^ n)))
  | 0, L => pure L
  | j + 1, L => (idealSieveRec n m j L).bind (idealLayer n m j)

noncomputable def idealReadout (n : ℕ) (s : ZMod (2 ^ n))
    (L : List (ZMod (2 ^ n))) : PMF (Option Bool) :=
  match L.find? (fun r => decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none => pure none
  | some r =>
    (parityReadout (dihedralQubitState (2 ^ n) s r)
      (normalized_dihedralQubitState (2 ^ n) s r)).map some

noncomputable def dihedralSieveRun (n m : ℕ) (s : ZMod (2 ^ n)) :
    PMF (Option Bool) × (ℕ × ℕ × ℕ) :=
  (((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)).bind
      (idealReadout n s),
    (24 * 2 ^ (3 * m), 48 * 2 ^ (3 * m) + 1, 48 * 2 ^ (3 * m) + 1))

noncomputable def actualFreshRecords (N : ℕ) [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) :
    ℕ → PMF (List (ZMod N × NormQ))
  | 0 => pure []
  | i + 1 =>
    (dihedralActualRecord N f).bind fun q =>
      (actualFreshRecords N f i).map fun L => (q.1, q.2.2) :: L

noncomputable def actualLayerAux (n : ℕ) :
    List ((ZMod (2 ^ n) × NormQ) × (ZMod (2 ^ n) × NormQ)) →
    PMF (List (ZMod (2 ^ n) × NormQ))
  | [] => pure []
  | ((k, χ), (ℓ, χ')) :: ps =>
    (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).bind fun q =>
      (actualLayerAux n ps).map fun tail =>
        if q.1 then (k - ℓ, q.2) :: tail else tail

noncomputable def actualLayer (n w t : ℕ)
    (L : List (ZMod (2 ^ n) × NormQ)) : PMF (List (ZMod (2 ^ n) × NormQ)) :=
  actualLayerAux n (sievePairWith n (α := ZMod (2 ^ n) × NormQ) Prod.fst w t L)

noncomputable def actualReadout (n : ℕ) (L : List (ZMod (2 ^ n) × NormQ)) :
    PMF (Option Bool) :=
  match L.find? (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none => pure none
  | some r => (parityReadout r.2.1 r.2.2).map some

noncomputable def actualSieveRec (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) :
    ℕ → List (ZMod (2 ^ n) × NormQ) → PMF (List (ZMod (2 ^ n) × NormQ))
  | 0, L => pure L
  | j + 1, L =>
    (actualSieveRec n m f j L).bind
      (actualLayer n (sieveWindowWidth n m j) (m * j))

noncomputable def dihedralSieveActual (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) : PMF (Option Bool) :=
  ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
      (actualSieveRec n m f m)).bind (actualReadout n)

end Qatlib.Concepts.HspRecovery.SieveAlgorithm
