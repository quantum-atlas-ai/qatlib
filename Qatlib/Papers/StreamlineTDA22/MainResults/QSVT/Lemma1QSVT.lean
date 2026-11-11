/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StreamlineTDA22.MainResults.Definitions
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionQSVTGeneralGily
import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.WalkSearch.Spectral.Approximation

set_option backward.isDefEq.respectTransparency false

/-!
# StreamlineTDA22 — Lemma 1 (QSVT projected unitary encoding)

Paper: *A streamlined quantum algorithm for topological data analysis with
exponentially fewer qubits*, arXiv:2209.12887, Lemma 1, p. 40.

Lemma 1 (paper text): for a degree-`d` odd polynomial `P_o` we can implement a
projected unitary encoding `U_o` with `Π_L U_o Π_R = P_o(A/α) := W P_o(Σ) V†`
(and, for a degree-`d` even polynomial, `U_e` with `Π_R U_e Π_R = P_e(A/α) :=
V P_e(Σ) V†`) using a QSVT circuit that makes `d` calls to `U, U†`, `2d` calls
to `C_{Π_L}NOT, C_{Π_R}NOT`, and uses `O(d)` other single- and two-qubit gates.

The algebraic corner is exactly the source-convention QSVT theorem of the
frozen library (`QuantumAlgorithm.Papers.QSingValue19.QsVtMain.sourceConventionQSVTGeneral`,
Gilyén–Su–Low–Wiebe 2019 Theorem 17 / Corollary 18, with phases in source
order).  The circuit ledger is formalised below by an explicit alternating
instruction list `qsvtWord`: one data query per phase angle (the query
direction alternates between `U` and `U†`), one phase gadget per angle (the
terminal phase is the identity and costs nothing), each phase gadget charged
the paper's two controlled projector applications (one `C_{Π_L}NOT` and one
`C_{Π_R}NOT`), and no further gates (`O(d) = 0 ≤ d`).  No native gate
synthesis, no phase-computation algorithm and no robustness bound is claimed —
those are outside Lemma 1's algebraic statement.
-/

set_option autoImplicit false

namespace Qatlib.Papers.StreamlineTDA22.MainResults.QSVT

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral

noncomputable section

variable {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

/-! ## The QSVT instruction list and its cost ledger -/

/-- A QSVT circuit step, at the paper's ledger granularity:
a data query in the forward or backward direction, a projector phase gadget
(on the currently active projector), or an arbitrary single- and two-qubit
gate macro. -/
inductive QsvtStep (H : Type*) where
  | queryForward : QsvtStep H
  | queryBackward : QsvtStep H
  | phaseHere (z : ℂ) : QsvtStep H
  | gate (M : Matrix H H ℂ) : QsvtStep H

/-- Evaluate a step list as a product of matrices.  A forward query flips the
active direction (`U` versus `U†`) and swaps the two projectors, exactly as in
`phasedAlternating`; `phaseHere z` multiplies by the phase gadget on the
currently active projector. -/
def evalWord (U P Q : Matrix H H ℂ) : List (QsvtStep H) → Matrix H H ℂ
  | [] => 1
  | .queryForward :: l => U * evalWord Uᴴ Q P l
  | .queryBackward :: l => Uᴴ * evalWord U Q P l
  | .phaseHere z :: l => phaseRotation Q z * evalWord U P Q l
  | .gate M :: l => M * evalWord U P Q l

/-- The alternating QSVT word for a phase list, with terminal base phase `1`
(identity, hence omitted as a gate).  One phase gadget and one data query are
emitted per angle; the direction and projector roles alternate. -/
def qsvtWord (U P Q : Matrix H H ℂ) : List ℂ → List (QsvtStep H)
  | [] => [.gate 1]
  | z :: zs => .phaseHere z :: .queryForward :: qsvtWord Uᴴ Q P zs

/-- The word evaluates to the phased alternating product with terminal base
`1`. -/
theorem evalWord_qsvtWord (U P Q : Matrix H H ℂ) (zs : List ℂ) :
    evalWord U P Q (qsvtWord U P Q zs) = phasedAlternating U P Q 1 zs := by
  induction zs generalizing U P Q with
  | nil => simp [evalWord, qsvtWord, phasedAlternating, phaseRotation_one]
  | cons z zs ih =>
    simp only [qsvtWord, evalWord, ih, phasedAlternating, Matrix.mul_assoc]

/-- Number of data queries in a step list. -/
def queryCount : List (QsvtStep H) → ℕ
  | [] => 0
  | .queryForward :: l => 1 + queryCount l
  | .queryBackward :: l => 1 + queryCount l
  | _ :: l => queryCount l

/-- Number of controlled-projector applications in a step list.  Following the
paper's ledger, each phase gadget is charged one `C_{Π_L}NOT` and one
`C_{Π_R}NOT`, i.e. two controlled-projector calls. -/
def controlledProjectorCount : List (QsvtStep H) → ℕ
  | [] => 0
  | .phaseHere _ :: l => 2 + controlledProjectorCount l
  | _ :: l => controlledProjectorCount l

/-- Number of additional single- and two-qubit gates in a step list. -/
def otherGateCount : List (QsvtStep H) → ℕ
  | [] => 0
  | .gate _ :: l => 1 + otherGateCount l
  | _ :: l => otherGateCount l

/-- The word uses exactly as many data queries as angles. -/
theorem qsvtWord_queryCount (U P Q : Matrix H H ℂ) (zs : List ℂ) :
    queryCount (qsvtWord U P Q zs) = zs.length := by
  induction zs generalizing U P Q with
  | nil => rfl
  | cons z zs ih =>
    simp only [qsvtWord, queryCount, ih, List.length_cons]
    omega

/-- The word uses exactly `2 d` controlled-projector applications, matching
Lemma 1's `2d` count. -/
theorem qsvtWord_controlledProjectorCount (U P Q : Matrix H H ℂ) (zs : List ℂ) :
    controlledProjectorCount (qsvtWord U P Q zs) = 2 * zs.length := by
  induction zs generalizing U P Q with
  | nil => rfl
  | cons z zs ih =>
    simp only [qsvtWord, controlledProjectorCount, ih, List.length_cons]
    ring

/-- The word uses no gate beyond the terminal identity, hence `O(d)` extra
single- and two-qubit gates. -/
theorem qsvtWord_otherGateCount (U P Q : Matrix H H ℂ) (zs : List ℂ) :
    otherGateCount (qsvtWord U P Q zs) = 1 := by
  induction zs generalizing U P Q with
  | nil => rfl
  | cons z zs ih =>
    simp only [qsvtWord, otherGateCount, ih]

/-! ## Lemma 1: the algebraic corner and the circuit ledger -/

/-- **Lemma 1** (paper p. 40).  For an exact normalized projected unitary
encoding `A = Π_L U Π_R`, every real polynomial `p` of exact degree `d > 0`
with parity `d` and `|p| ≤ 1` on `[-1,1]` admits a real phase list `Φ` of
length `d` such that

* the odd corner `Π_L U_Φ Π_R` equals the odd singular-value transform
  `W p(Σ) V†` applied to `A` (when `d` is odd), and
* the even corner `Π_R U_Φ Π_R` equals the even singular-value transform
  `V p(Σ) V†` applied to `A` (when `d` is even),

and the associated QSVT word makes `d` data queries, `2d`
controlled-projector calls and `O(d)` additional gates. -/
theorem lemma1_projectedUnitaryEncoding
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (h : ProjectedUnitaryEncoding A U L R)
    (p : Polynomial ℝ) (d : ℕ) (hd : 0 < d)
    (hdeg : p.degree = (d : WithBot ℕ))
    (hpar : HasRealParity d p)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ Φ : List ℝ, Φ.length = d ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) ∧
      (d % 2 = 1 →
        rangeProjector L * phasedAlternating U (rangeProjector R) (rangeProjector L) 1
            (Φ.map anglePhase) * rangeProjector R =
          L * oddSingularTransform A (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) * Rᴴ) ∧
      (d % 2 = 0 →
        rangeProjector R * phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) 1
            (Φ.map anglePhase) * rangeProjector R =
          R * rightSingularTransform A (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) * Rᴴ) ∧
      queryCount (qsvtWord U (rangeProjector R) (rangeProjector L) (Φ.map anglePhase)) = d ∧
      controlledProjectorCount
          (qsvtWord U (rangeProjector R) (rangeProjector L) (Φ.map anglePhase)) = 2 * d ∧
      otherGateCount
          (qsvtWord U (rangeProjector R) (rangeProjector L) (Φ.map anglePhase)) = 1 := by
  obtain ⟨Φ, hlen, hre, _hmin, hodd, heven⟩ :=
    sourceConventionQSVTGeneral.1 H I O A U L R p d h hd hdeg hpar hb
  refine ⟨Φ, hlen, hre, hodd, heven, ?_, ?_, ?_⟩
  · rw [qsvtWord_queryCount, List.length_map, hlen]
  · rw [qsvtWord_controlledProjectorCount, List.length_map, hlen]
  · rw [qsvtWord_otherGateCount]

end

end Qatlib.Papers.StreamlineTDA22.MainResults.QSVT
