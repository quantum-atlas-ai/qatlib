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

/-!
# Ideal and quantum dihedral sieve processes

This module defines the ideal label process and the process carrying actual normalized qubit
states for the dihedral sieve of [Kuperberg2005]. Records are paired by agreement on a bit
window, combined through random extraction, and searched for the distinguished parity-readout
label.

## Main definitions

* `sievePairWith`: greedy pairing according to a label window.
* `idealSieveRec`: successive ideal sieve layers.
* `dihedralSieveRun`: ideal output law with an attached resource triple.
* `dihedralSieveActual`: oracle record generation, quantum extraction layers, and final readout.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

open Qatlib.Concepts.HspRecovery.RecordExtract

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.SieveAlgorithm

open Qatlib

/-- The condition that the lowest `t` bits of the label's canonical representative vanish,
expressed as divisibility by `2 ^ t`. -/
def zeroBitsGE (n t : ℕ) (k : ZMod (2 ^ n)) : Prop := k.val % 2 ^ t = 0

/-- The condition that two label representatives agree on the `w`-bit window beginning at bit
position `t`. -/
def windowAgree (n w t : ℕ) (k ℓ : ZMod (2 ^ n)) : Prop :=
  (k.val / 2 ^ t) % 2 ^ w = (ℓ.val / 2 ^ t) % 2 ^ w

instance instDecidableWindowAgree (n w t : ℕ) (k ℓ : ZMod (2 ^ n)) :
    Decidable (windowAgree n w t k ℓ) :=
  inferInstanceAs (Decidable ((k.val / 2 ^ t) % 2 ^ w = (ℓ.val / 2 ^ t) % 2 ^ w))

/-- The window width `min m (n - 1 - m * j)` used at sieve layer `j`. -/
def sieveWindowWidth (n m j : ℕ) : ℕ := min m (n - 1 - m * j)

/-- The greedy list pairing that matches each available head with the first remaining record
whose label agrees on the selected window, discarding unmatched heads. -/
noncomputable def sievePairWith (n : ℕ) {α : Type} [DecidableEq α]
    (label : α → ZMod (2 ^ n)) (w t : ℕ) (L : List α) : List (α × α) := by
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

/-- Greedy window-agreement pairing specialized to lists of labels modulo `2 ^ n`. -/
noncomputable def sievePair (n w t : ℕ) (L : List (ZMod (2 ^ n))) :
    List (ZMod (2 ^ n) × ZMod (2 ^ n)) :=
  sievePairWith n (α := ZMod (2 ^ n)) id w t L

/-- The uniform probability law on labels modulo `2 ^ n`. -/
noncomputable def dihedralIdealRecordLaw (n : ℕ) : PMF (ZMod (2 ^ n)) :=
  PMF.uniformOfFintype' (ZMod (2 ^ n))

/-- The probability law of a list of the specified number of independent uniform labels modulo
`2 ^ n`. -/
noncomputable def idealFreshRecords (n : ℕ) :
    ℕ → PMF (List (ZMod (2 ^ n)))
  | 0 => pure []
  | i + 1 =>
    (dihedralIdealRecordLaw n).bind fun r =>
      (idealFreshRecords n i).map fun L => r :: L

/-- The ideal layer law that independently retains each pair's difference `r' - r` with
probability one half and otherwise discards that pair. -/
noncomputable def idealLayerAux (n : ℕ) :
    List (ZMod (2 ^ n) × ZMod (2 ^ n)) → PMF (List (ZMod (2 ^ n)))
  | [] => pure []
  | (r, r') :: ps =>
    (PMF.uniformOfFintype' (Fin 2)).bind fun b =>
      (idealLayerAux n ps).map fun tail =>
        if b = 1 then (r' - r) :: tail else tail

/-- The ideal sieve layer that pairs labels in the window of width `sieveWindowWidth n m j`
beginning at `m * j` and randomly retains their differences. -/
noncomputable def idealLayer (n m j : ℕ) (L : List (ZMod (2 ^ n))) :
    PMF (List (ZMod (2 ^ n))) :=
  idealLayerAux n (sievePair n (sieveWindowWidth n m j) (m * j) L)

/-- The successive ideal sieve layers, with zero layers returning the input list and each
successor applying the next indexed layer. -/
noncomputable def idealSieveRec (n m : ℕ) :
    ℕ → List (ZMod (2 ^ n)) → PMF (List (ZMod (2 ^ n)))
  | 0, L => pure L
  | j + 1, L => (idealSieveRec n m j L).bind (idealLayer n m j)

/-- The ideal readout law that returns `none` if the distinguished label `2 ^ (n - 1)` is absent
and otherwise returns its dihedral qubit's parity measurement wrapped in `some`. -/
noncomputable def idealReadout (n : ℕ) (s : ZMod (2 ^ n))
    (L : List (ZMod (2 ^ n))) : PMF (Option Bool) :=
  match L.find? (fun r => decide (r = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none => pure none
  | some r =>
    (parityReadout (dihedralQubitState (2 ^ n) s r)
      (normalized_dihedralQubitState (2 ^ n) s r)).map some

/-- The ideal run drawing `24 * 2 ^ (3 * m)` labels, applying `m` sieve layers, and reading out
parity. It is paired with resource triple `(24 * 2 ^ (3 * m), 48 * 2 ^ (3 * m) + 1, 48 * 2 ^
(3 * m) + 1)`. -/
noncomputable def dihedralSieveRun (n m : ℕ) (s : ZMod (2 ^ n)) :
    PMF (Option Bool) × (ℕ × ℕ × ℕ) :=
  (((idealFreshRecords n (24 * 2 ^ (3 * m))).bind (idealSieveRec n m m)).bind
      (idealReadout n s),
    (24 * 2 ^ (3 * m), 48 * 2 ^ (3 * m) + 1, 48 * 2 ^ (3 * m) + 1))

/-- The law of a list of independent actual oracle records, retaining each record's label and
normalized qubit state. -/
noncomputable def actualFreshRecords (N : ℕ) [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) :
    ℕ → PMF (List (ZMod N × NormQ))
  | 0 => pure []
  | i + 1 =>
    (dihedralActualRecord N f).bind fun q =>
      (actualFreshRecords N f i).map fun L => (q.1, q.2.2) :: L

/-- The actual extraction law for paired labeled qubits, retaining the difference label `k - ℓ`
and output state on the true branch and discarding the false branch. -/
noncomputable def actualLayerAux (n : ℕ) :
    List ((ZMod (2 ^ n) × NormQ) × (ZMod (2 ^ n) × NormQ)) →
    PMF (List (ZMod (2 ^ n) × NormQ))
  | [] => pure []
  | ((k, χ), (ℓ, χ')) :: ps =>
    (dihedralExtraction χ.1 χ'.1 χ.2 χ'.2).bind fun q =>
      (actualLayerAux n ps).map fun tail =>
        if q.1 then (k - ℓ, q.2) :: tail else tail

/-- The actual sieve layer that greedily pairs labeled qubits by the selected label window and
applies quantum extraction to each pair. -/
noncomputable def actualLayer (n w t : ℕ)
    (L : List (ZMod (2 ^ n) × NormQ)) : PMF (List (ZMod (2 ^ n) × NormQ)) :=
  actualLayerAux n (sievePairWith n (α := ZMod (2 ^ n) × NormQ) Prod.fst w t L)

/-- The readout law that measures the qubit of the first record labeled `2 ^ (n - 1)` and
returns `none` when no such record exists. -/
noncomputable def actualReadout (n : ℕ) (L : List (ZMod (2 ^ n) × NormQ)) :
    PMF (Option Bool) :=
  match L.find? (fun r => decide (r.1 = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)))) with
  | none => pure none
  | some r => (parityReadout r.2.1 r.2.2).map some

/-- The successive actual extraction layers, using window width `sieveWindowWidth n m j` and
offset `m * j` at layer `j`. -/
noncomputable def actualSieveRec (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) :
    ℕ → List (ZMod (2 ^ n) × NormQ) → PMF (List (ZMod (2 ^ n) × NormQ))
  | 0, L => pure L
  | j + 1, L =>
    (actualSieveRec n m f j L).bind
      (actualLayer n (sieveWindowWidth n m j) (m * j))

/-- The oracle-driven sieve output law obtained from `24 * 2 ^ (3 * m)` actual records, `m`
extraction layers, and the final distinguished-label readout. -/
noncomputable def dihedralSieveActual (n m : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg (2 ^ n) → S) : PMF (Option Bool) :=
  ((actualFreshRecords (2 ^ n) f (24 * 2 ^ (3 * m))).bind
      (actualSieveRec n m f m)).bind (actualReadout n)

end Qatlib.Concepts.HspRecovery.SieveAlgorithm
