/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QCodeDecoding22.MainResults.DecoderModel — source object layer

Leverrier--Zémor, *Efficient decoding up to a constant fraction of the code
length for asymptotically good quantum codes*, fixed **arXiv:2206.07571v2**
(PDF SHA-256 recorded on the review branch).  Paper file:
`assets/2206.07571v2.pdf`.

This module fixes the objects that the theorem layer of the `MainResults`
block refers to:

* `coordWeight` — the Hamming weight `|·|` on the square set `Q` (source §2).
* `Equivalent` — the source's notion of *equivalent* errors: two error
  vectors are equivalent when they differ by a stabilizer element (§2, p. 3).
* `CorrectsAllErrorsBelow` — the decoding guarantee of Theorem 2 / Theorem 29:
  every error of weight `< r` is mapped to an equivalent error.
* `QuantumTannerCode` / `PaperDecoder` — a quantum Tanner code `Q = (C0,C1)`
  on a left-right Cayley complex together with the sequential/parallel decoder
  of §2.  The field `isSequentialParallelDecoder : Prop` records that the
  decoding function is exactly the algorithm constructed in §2; it is a
  *specification* of the source object (the concrete implementation is not
  re-constructed here) and is only ever used as a hypothesis.
* `LiftedProductCode` / `LiftedProductDecoder` — the analogous objects for
  the Panteleev--Kalachev lifted product codes of §7.

Boundary (per the block metadata): no concrete code family construction, no
numerical threshold estimation, no fault-tolerant gate compilation, and no
higher-dimensional / subsystem / erasure-channel generalisation.

Every declaration in this file is fully elaborated; the model layer has no
proof holes and introduces no new logical primitives.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCodeDecoding22.MainResults

open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Classical

/-- Hamming weight of an error / decomposition vector, re-exported from the
frozen binary-Pauli layer. -/
abbrev coordWeight {ι : Type*} [Fintype ι] (v : ι → ZMod 2) : ℕ := bitWeight v

/-- Source §2: two errors `e`, `ê` are *equivalent* when their difference is
a stabilizer element (they act identically on the code space). -/
def Equivalent {ι : Type*} [Fintype ι]
    (stabilizer : Submodule (ZMod 2) (ι → ZMod 2)) (e ê : ι → ZMod 2) : Prop :=
  e + ê ∈ stabilizer

/-- Source Theorem 2 / Theorem 29 decoding guarantee: the decoder `D` corrects
every error of Hamming weight `< r`, i.e. maps it to an equivalent error. -/
def CorrectsAllErrorsBelow {ι : Type*} [Fintype ι]
    (stabilizer : Submodule (ZMod 2) (ι → ZMod 2))
    (D : (ι → ZMod 2) → Option (ι → ZMod 2)) (r : ℝ) : Prop :=
  ∀ e : ι → ZMod 2, (coordWeight e : ℝ) < r →
    ∃ ê : ι → ZMod 2, D e = some ê ∧ Equivalent stabilizer e ê

/-- The parameter regime of the source: `Δ ≥ 2` is the degree of the
left-right Cayley complex, `δ` is a lower bound on the minimum distances of
both component codes `CA`, `CB`, and `ε ∈ (0, 1/2)` is the analysis slack.
The source takes `Δ` large-but-fixed and constants `κ` depending only on `δ`
(and on `β` where stated). -/
structure Regime where
  Δ : ℕ
  hΔ : 2 ≤ Δ
  δ : ℝ
  hδ0 : 0 < δ
  hδ1 : δ ≤ 1
  ε : ℝ
  hε0 : 0 < ε
  hε1 : ε < 1 / 2

/-- `Δ^{1-2ε}` — the length scale appearing in Lemmas 11, 12, 15, 20, 23. -/
def Regime.D (R : Regime) : ℝ := (R.Δ : ℝ) ^ (1 - 2 * R.ε)

/-- `Δ^{1/2-ε}` — the robustness / normality scale of §5. -/
def Regime.w (R : Regime) : ℝ := (R.Δ : ℝ) ^ (1 / 2 - R.ε)

/-- `R.D = Δ^{1-2ε}` is strictly positive. -/
theorem Regime.D_pos (R : Regime) : 0 < R.D := by
  unfold Regime.D
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < R.Δ by have := R.hΔ; omega)) _

/-- `R.w = Δ^{1/2-ε}` is strictly positive. -/
theorem Regime.w_pos (R : Regime) : 0 < R.w := by
  unfold Regime.w
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < R.Δ by have := R.hΔ; omega)) _

/-- The source's Lemma 3 (expander mixing lemma) in the normalisation used in
§5: for a `Δ`-regular `2`-lifted Cayley graph with `V` vertices on each side,
the number `e` of edges between finite vertex sets `A`, `B` of sizes `a`, `b`
satisfies `e ≤ Δ² a b / V + 4 Δ √(a b)`.  This is the only spectral input
used by the decoder analysis (the complexes of Theorem 1 are Ramanujan). -/
def ExpanderMixingBound (Δ V : ℕ) (a b e : ℝ) : Prop :=
  e ≤ (Δ : ℝ) ^ 2 * a * b / (V : ℝ) + 4 * (Δ : ℝ) * Real.sqrt (a * b)

/-- A quantum Tanner code `Q = (C0, C1)` of §2 on a left-right Cayley complex
with `Δ`-regular component graphs and component codes of minimum distance at
least `δ`.  The code is a CSS code, recorded through its stabilizer group on
the square set `Q`. -/
structure QuantumTannerCode where
  Δ : ℕ
  hΔ : 2 ≤ Δ
  δ : ℝ
  hδ : 0 < δ
  Coord : Type
  instFintype : Fintype Coord
  instDecEq : DecidableEq Coord
  stabilizer : Submodule (ZMod 2) (Coord → ZMod 2)
  /-- The code is obtained from the left-right Cayley complex construction of
  Theorem 1 (Ramanujan component graphs `GA`, `GB`, `G◻0`, `G◻1`).  This is the
  provenance hypothesis under which the expander mixing input of §5 applies;
  it is only used as a hypothesis, never constructed. -/
  isRamanujanConstruction : Prop

attribute [instance] QuantumTannerCode.instFintype QuantumTannerCode.instDecEq

/-- Code length `n = |Q|` (source Theorem 2). -/
def QuantumTannerCode.n (Q : QuantumTannerCode) : ℕ := Fintype.card Q.Coord

/-- The sequential/parallel decoder of §2 for a quantum Tanner code.  The
field `isSequentialParallelDecoder` is the source specification "this is the
algorithm of §2" (sequential local decoding, interrupted by the two-round
parallel decoding procedure when stalled); it is used only as a hypothesis. -/
structure PaperDecoder (Q : QuantumTannerCode) where
  decode : (Q.Coord → ZMod 2) → Option (Q.Coord → ZMod 2)
  isSequentialParallelDecoder : Prop

/-- A Panteleev--Kalachev lifted product code (§7) with the same parameter
regime `Δ`, `δ`; its errors decompose into the five blocks
`eAB + e00 + e01 + e10 + e11` of §7.3. -/
structure LiftedProductCode where
  Δ : ℕ
  hΔ : 2 ≤ Δ
  δ : ℝ
  hδ : 0 < δ
  Coord : Type
  instFintype : Fintype Coord
  instDecEq : DecidableEq Coord
  stabilizer : Submodule (ZMod 2) (Coord → ZMod 2)
  -- the source's off-diagonal coordinate sets `C0×D1` and `C1×D0`
  offDiag0 : Finset Coord
  offDiag1 : Finset Coord

attribute [instance] LiftedProductCode.instFintype LiftedProductCode.instDecEq

/-- Length `n = |Q|`... for the lifted product code the length is `|A×B|`,
recorded as the number of `AB` coordinates. -/
def LiftedProductCode.n (L : LiftedProductCode) : ℕ := Fintype.card L.Coord

/-- The lifted product decoder of §7.3 (the §2 decoder applied after removing
the off-diagonal parts via Lemma 28). -/
structure LiftedProductDecoder (L : LiftedProductCode) where
  decode : (L.Coord → ZMod 2) → Option (L.Coord → ZMod 2)
  isLiftedProductDecoder : Prop

/-- Restriction of a vector to a coordinate set (zero outside). -/
def restrictTo {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ZMod 2) :
    ι → ZMod 2 :=
  fun i => if i ∈ s then v i else 0

end Qatlib.Papers.QCodeDecoding22.MainResults
