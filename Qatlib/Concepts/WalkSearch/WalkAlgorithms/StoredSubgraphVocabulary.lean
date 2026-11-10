/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts
import Mathlib.Data.Finset.Prod
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

def storedEdges {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (U.product U).filter (fun p => adj p.1 p.2 = true)

def storedSetupQueries {n : ℕ} (U : Finset (Fin n)) : List (Fin n × Fin n) :=
  (U.product U).toList

def storedUpdateQueries {n : ℕ} (U : Finset (Fin n)) (v : Fin n) :
    List (Fin n × Fin n) := U.toList.map (fun a => (a, v))

def storedQueryAnswers {n : ℕ} (adj : Fin n → Fin n → Bool)
    (queries : List (Fin n × Fin n)) : List ((Fin n × Fin n) × Bool) :=
  queries.map (fun p => (p, adj p.1 p.2))

def storedReplay {n : ℕ} (answers : List ((Fin n × Fin n) × Bool)) :
    Finset (Fin n × Fin n) :=
  (answers.toFinset.filter (fun row => row.2 = true)).image Prod.fst

def storedReplayInsert {n : ℕ} (D : Finset (Fin n × Fin n))
    (answers : List ((Fin n × Fin n) × Bool)) : Finset (Fin n × Fin n) :=
  D ∪ (storedReplay answers ∪ (storedReplay answers).image Prod.swap)

def storedInsert {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (v : Fin n) : Finset (Fin n × Fin n) :=
  storedEdges adj U ∪
    ((U.filter (fun a => adj a v = true)).image (fun a => (a, v)) ∪
      (U.filter (fun a => adj a v = true)).image (fun a => (v, a)))

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
