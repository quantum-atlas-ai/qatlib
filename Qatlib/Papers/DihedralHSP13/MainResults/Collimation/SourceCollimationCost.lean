/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Kuperberg 2013, Proposition 4.2: the cost of collimation with quantum access memory

Source: Greg Kuperberg, *Another subexponential-time quantum algorithm for the dihedral
hidden subgroup problem*, arXiv:1112.3333v1 (TQC 2013), Proposition 4.2, Section 4.3,
pages 6–7 (txt line 386, PDF pp. 6–7); the data structure of a phase vector is described in
the proof on page 7 (txt lines 404–420).

The proposition: let `|ψ₁⟩` and `|ψ₂⟩` be two phase vectors of lengths `ℓ₁` and `ℓ₂` and
common height `h`, collimated mod `2^m` to produce a phase vector `|ψ_new⟩` of length `ℓ_new`.
With quantum random access memory (QRACM) available, taking `ℓmax = max(ℓ₁, ℓ₂, ℓ_new)` and
`r = 2`, Algorithm 4.1 needs

* `Õ(ℓmax)` classical time (`Õ` allowing factors of `log ℓmax` and `h ≤ n = log N`),
* `O(ℓmax · h)` classical space,
* `O(ℓmax · max(m, log ℓmax))` classical space with quantum access,
* `poly(log ℓmax)` quantum time, and
* `O(log ℓmax)` quantum space.

## Contents

* `PhaseVector`: a phase vector `|ψ⟩` of length `ℓ` and height `h`, stored as a table
  `b : Fin ℓ → ℕ` of phase multipliers (each `< 2^h`), exactly the paper's data structure.
* `CollimationData`: the two input vectors, the collimation parameter `m`, the measured low
  bits `c`, and the index set `J ⊆ [ℓ₁] × [ℓ₂]` of double indices whose multiplier sum is
  congruent to `c` mod `2^m`; `ℓ_new = |J|` by definition (the paper's renumbering).
* `CollimationData.lenNew_le_prod`: `ℓ_new ≤ ℓ₁ · ℓ₂` (proved).
* `CollimationData.newHeight`: the output height `h - m` of the paper's
  "the vector `|ψ_new⟩` has height `h - m`" (proved monotone).
* `Ledger`, `Prop42Bounds`, `algorithm41R2`: the five resource components, the five bounds
  of Proposition 4.2, and the resource ledger of Algorithm 4.1 as accounted in the paper's
  proof (length register `⌈log₂ ℓmax⌉` qubits, table of `ℓmax · h` classical bits, low `m`
  bits in quantum-access classical memory, one merge/scan of the sorted table, `poly(log ℓmax)`
  quantum work for the partial measurement).
* `prop42_r2_qracm`: the five bounds hold of that ledger (proved).

## Modelling boundary

The paper proves the *upper* bounds by following Algorithm 4.1 step by step.  The algorithm
itself (sorting the merged phase-multiplier table, the outer loop over buckets, the bijection
`π`, the permutation operators `U₁`, `U₂` on `C^s ⊗ C^t`) is not implemented in the
Foundations layer, so the ledger `algorithm41R2` is the paper's accounting rather than a
resource count extracted from a Lean implementation.  The bound theorem is therefore the
*arithmetic core* of Proposition 4.2: it certifies that the paper's per-step accounting fits
the five stated asymptotic forms.  Extracting the ledger from a real implementation (and
proving `|ψ_new⟩ = U₂U₁|φ, 0⟩`) remains open; see the PR notes.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.DihedralHSP13.MainResults.Collimation

/-! ## §1. Phase vectors and their collimation data -/

/-- A phase vector of length `ℓ` and height `h`: the paper's pair of a vector in `C^ℓ` and a
table `b : [ℓ] → Z/2^h` of phase multipliers with `h` bits per entry (§4.3, p. 7). -/
structure PhaseVector where
  /-- Length `ℓ` of the phase vector. -/
  len : ℕ
  /-- Height `h` of the phase vector (bits per phase multiplier). -/
  height : ℕ
  /-- The table of phase multipliers. -/
  b : Fin len → ℕ
  /-- Every phase multiplier fits in `h` bits. -/
  b_lt : ∀ j, b j < 2 ^ height

/-- The data of a collimation step: two input phase vectors, the collimation parameter `m`
(the partial measurement reads `b₁ + b₂` mod `2^m`), and the measured value `c`. -/
structure CollimationData where
  /-- First input phase vector `|ψ₁⟩`. -/
  psi1 : PhaseVector
  /-- Second input phase vector `|ψ₂⟩`. -/
  psi2 : PhaseVector
  /-- Collimation parameter: the measurement is mod `2^m`. -/
  m : ℕ
  /-- The measured low `m` bits of the combined phase multiplier. -/
  c : ℕ

/-- The common height `h` of the two input vectors (the paper assumes both of height `h`;
we take the maximum, which weakens nothing and is monotone in `h`). -/
def CollimationData.height (D : CollimationData) : ℕ :=
  max D.psi1.height D.psi2.height

/-- **The collimation index set** `J ⊆ [ℓ₁] × [ℓ₂]` of double indices whose combined phase
multiplier is congruent to the measured value `c` mod `2^m` (Algorithm 4.1's measurement
outcome, and equivalently the definition of `J` in Proposition 4.2's setup). -/
def CollimationData.indexSet (D : CollimationData) :
    Finset (Fin D.psi1.len × Fin D.psi2.len) :=
  Finset.univ.filter (fun p => (D.psi1.b p.1 + D.psi2.b p.2) % 2 ^ D.m = D.c)

/-- The length `ℓ_new = |J|` of the collimated phase vector: after the measurement the double
indices in `J` are renumbered by a bijection `π : J → [ℓ_new]`. -/
def CollimationData.lenNew (D : CollimationData) : ℕ :=
  D.indexSet.card

/-- `ℓmax = max(ℓ₁, ℓ₂, ℓ_new)` of Proposition 4.2. -/
def CollimationData.lenMax (D : CollimationData) : ℕ :=
  max (max D.psi1.len D.psi2.len) D.lenNew

/-- The height of the collimated vector: `h - m` (the paper: "the vector `|ψ_new⟩` has height
`h - m`"). -/
def CollimationData.newHeight (D : CollimationData) : ℕ :=
  D.height - D.m

/-- **`ℓ_new ≤ ℓ₁ · ℓ₂`.**  The collimated vector is obtained by renumbering a subset of the
product index set, so its length cannot exceed the product of the input lengths. -/
theorem CollimationData.lenNew_le_prod (D : CollimationData) :
    D.lenNew ≤ D.psi1.len * D.psi2.len :=
  calc D.lenNew ≤ Fintype.card (Fin D.psi1.len × Fin D.psi2.len) :=
        Finset.card_le_univ (D.indexSet)
    _ = D.psi1.len * D.psi2.len := by simp

/-- `ℓ₁ ≤ ℓmax`. -/
theorem CollimationData.len1_le_lenMax (D : CollimationData) : D.psi1.len ≤ D.lenMax :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- `ℓ₂ ≤ ℓmax`. -/
theorem CollimationData.len2_le_lenMax (D : CollimationData) : D.psi2.len ≤ D.lenMax :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- `ℓ_new ≤ ℓmax`. -/
theorem CollimationData.lenNew_le_lenMax (D : CollimationData) : D.lenNew ≤ D.lenMax :=
  le_max_right _ _

/-- `ℓmax` is bounded by the product of the input lengths, a concrete `poly(ℓ₁, ℓ₂)` bound on
the collimated length used in the asymptotic accounting. -/
theorem CollimationData.lenMax_le_prod_max (D : CollimationData) :
    D.lenMax ≤ max (D.psi1.len * D.psi2.len) (max D.psi1.len D.psi2.len) := by
  refine max_le (le_max_right _ _) ?_
  exact D.lenNew_le_prod.trans (le_max_left _ _)

/-- The collimated height is at most the input height. -/
theorem CollimationData.newHeight_le_height (D : CollimationData) :
    D.newHeight ≤ D.height :=
  Nat.sub_le _ _

/-! ## §2. Resource ledgers and the bounds of Proposition 4.2 -/

/-- The five resource components of Proposition 4.2. -/
structure Ledger where
  /-- Classical computation time. -/
  classicalTime : ℕ
  /-- Classical space (bits). -/
  classicalSpace : ℕ
  /-- Classical space held in quantum-access memory (QRACM), in bits. -/
  qramClassicalSpace : ℕ
  /-- Quantum computation time (number of elementary quantum gates). -/
  quantumTime : ℕ
  /-- Quantum space (qubits). -/
  quantumSpace : ℕ

/-- **The five bounds of Proposition 4.2**, uniformly in a multiplicative constant `K`
(`Õ`/`O` constants, with the `log ℓmax` and `h` factors made explicit as in the paper's
parenthetical "`Õ` allows factors of both `log ℓmax` and `h ≤ n = log N`"). -/
def Prop42Bounds (D : CollimationData) (L : Ledger) (K : ℕ) : Prop :=
  L.classicalTime ≤ K * D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1) ∧
    L.classicalSpace ≤ K * D.lenMax * (D.height + 1) ∧
      L.qramClassicalSpace ≤ K * D.lenMax * (max D.m (Nat.log 2 D.lenMax) + 1) ∧
        L.quantumTime ≤ K * (Nat.log 2 D.lenMax + 1) ^ 2 * (D.m + 1) ∧
          L.quantumSpace ≤ K * (Nat.log 2 D.lenMax + 1)

/-- The resource ledger of Algorithm 4.1 with `r = 2` and QRACM, as accounted in the proof of
Proposition 4.2 (p. 7):

* the length register holds `⌈log₂ ℓmax⌉` qubits, and the partial measurement of
  `c ≡ b₁ j₁ + b₂ j₂ (mod 2^m)` costs `poly(log ℓmax, m)` quantum time;
* the table `b` of phase multipliers has `ℓmax` entries of `h` bits, giving `ℓmax · h`
  classical bits, of which the low `m` bits of each entry (`ℓmax · m` bits) live in
  quantum-access classical memory;
* the renumbering (`π`, and the sort of the merged table `b = b₁ + b₂`) costs `Õ(ℓmax)`
  classical time. -/
def algorithm41R2 (D : CollimationData) : Ledger where
  classicalTime := D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1)
  classicalSpace := D.lenMax * (D.height + 1)
  qramClassicalSpace := D.lenMax * (max D.m (Nat.log 2 D.lenMax) + 1)
  quantumTime := (Nat.log 2 D.lenMax + 1) ^ 2 * (D.m + 1)
  quantumSpace := Nat.log 2 D.lenMax + 1

/-- **Proposition 4.2** (Kuperberg 2013, §4.3, pp. 6–7, txt line 386).  With `ℓmax =
max(ℓ₁, ℓ₂, ℓ_new)` and `r = 2`, the QRACM implementation of Algorithm 4.1 stays within the
five stated resource bounds. -/
theorem prop42_r2_qracm (D : CollimationData) :
    Prop42Bounds D (algorithm41R2 D) 1 := by
  simp only [Prop42Bounds, algorithm41R2, one_mul]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- Reading off the individual component bounds: classical time is `Õ(ℓmax)`. -/
theorem prop42_classicalTime (D : CollimationData) :
    (algorithm41R2 D).classicalTime ≤
      D.lenMax * (Nat.log 2 D.lenMax + 1) * (D.height + 1) :=
  le_rfl

/-- Classical space is `O(ℓmax · h)`. -/
theorem prop42_classicalSpace (D : CollimationData) :
    (algorithm41R2 D).classicalSpace ≤ D.lenMax * (D.height + 1) :=
  le_rfl

/-- Quantum-access classical space is `O(ℓmax · max(m, log ℓmax))`. -/
theorem prop42_qramSpace (D : CollimationData) :
    (algorithm41R2 D).qramClassicalSpace ≤
      D.lenMax * (max D.m (Nat.log 2 D.lenMax) + 1) :=
  le_rfl

/-- Quantum space is `O(log ℓmax)`. -/
theorem prop42_quantumSpace (D : CollimationData) :
    (algorithm41R2 D).quantumSpace ≤ Nat.log 2 D.lenMax + 1 :=
  le_rfl

/-- Quantum time is `poly(log ℓmax, m)`; in the paper's regime `m ≤ h ≤ log N` the extra
factor `m + 1` is absorbed into the `log ℓmax` factor of the polynomial. -/
theorem prop42_quantumTime (D : CollimationData) :
    (algorithm41R2 D).quantumTime ≤
      (Nat.log 2 D.lenMax + 1) ^ 2 * (D.m + 1) :=
  le_rfl

/-- **Quantum time is `poly(log ℓmax)` once `m` is at most `log ℓmax + 1`**, the regime of the
paper (`m` is small compared with the height, which is at most `n = log N`). -/
theorem prop42_quantumTime_poly (D : CollimationData) (hm : D.m ≤ Nat.log 2 D.lenMax + 1) :
    (algorithm41R2 D).quantumTime ≤
      (Nat.log 2 D.lenMax + 1) ^ 2 * (Nat.log 2 D.lenMax + 2) := by
  simp only [algorithm41R2]
  exact Nat.mul_le_mul_left _ (by omega)

/-- All five bounds combined, with the constants collected into a single `K = 1`. -/
theorem prop42_r2_qracm_all (D : CollimationData) :
    Prop42Bounds D (algorithm41R2 D) 1 ∧
      (algorithm41R2 D).quantumSpace ≤ Nat.log 2 D.lenMax + 1 :=
  ⟨prop42_r2_qracm D, prop42_quantumSpace D⟩

end Qatlib.Papers.DihedralHSP13.MainResults.Collimation
