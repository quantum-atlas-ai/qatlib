/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneShotLDPC23.MainResults.Model.BinaryWeight

set_option backward.isDefEq.respectTransparency false

/-!
# OneShotLDPC23.MainResults.Model.TannerStructure — quantum Tanner code interface

Fixed paper: **arXiv:2306.12470v2**, §2 (codes and Tanner graphs) and §4.1–4.2.

A quantum Tanner code is a CSS code on a qubit register `Q` whose checks are
indexed by the four vertex classes `V00, V01, V10, V11` of the Tanner graph.
Because all four classes play the same role in §4's statements (only the
distinguished class matters for `V_ij`-weighting), we encode a vertex by a
single index type `V1` together with a class map

  `cls : V1 → VClass`.

The fields are the paper's data:

* `view v ⊆ Q` — the squares (qubits) incident to `v`, i.e. `Q(v)`;
* `sigma v : F₂^Q → F₂^κ` — the local syndrome map `σ_v`;
* `localCode v` — the local code `C1^⊥(v)` (column/row codewords combined);
* `localCode_support` — local codewords live on `Q(v)`;
* `reducedWeight` — the reduced weight `|e|_R` of §2 (min weight modulo the
  stabilizer group).

Everything about the *graph* (that every face meets two vertices, that views of
different `V01` vertices are disjoint, …) is deliberately **not** assumed here;
the statements of Lemmas 4.7/4.8 that need it carry it as explicit hypotheses.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Model

open scoped BigOperators

/-- The four vertex classes `V_ij` of a quantum Tanner code. -/
inductive VClass where
  | v00 | v01 | v10 | v11
  deriving DecidableEq, Repr

/-- A quantum Tanner code: the data of §2 that the §4 analysis refers to. -/
structure TannerCode (Q V1 κ : Type*) [Fintype Q] [Fintype V1] where
  /-- Vertex class of each vertex. -/
  cls : V1 → VClass
  /-- Squares (qubits) incident to a vertex: the paper's `Q(v)`. -/
  view : V1 → Finset Q
  /-- Local syndrome map `σ_v` of a vertex. -/
  sigma : V1 → BitVec Q → BitVec κ
  /-- The local code `C1^⊥(v)` at a vertex. -/
  localCode : V1 → Set (BitVec Q)
  /-- Local codewords are supported on `Q(v)`. -/
  localCode_support : ∀ v, localCode v ⊆ {x | ∀ i, i ∉ view v → x i = 0}
  /-- The reduced weight `|e|_R` of §2. -/
  reducedWeight : BitVec Q → ℝ

variable {Q V1 κ : Type*} [Fintype Q] [Fintype V1]

/-- The number of physical qubits `n = |Q|`, as a real number. -/
noncomputable def numQubits (_C : TannerCode Q V1 κ) : ℝ := (Fintype.card Q : ℝ)

/-- `e` is `V_ij`-weighted (Definition 4.6): its syndrome vanishes at every
vertex of class `V_ij`.  The §4 uses of the notition are all `V10`. -/
def V10Weighted (C : TannerCode Q V1 κ) (e : BitVec Q) : Prop :=
  ∀ v : V1, C.cls v = VClass.v10 → C.sigma v e = 0

/-- `Z` is an associated mismatch vector (Definition 4.6) for the error `e`. -/
def Associated (C : TannerCode Q V1 κ) (Z e : BitVec Q) : Prop :=
  ∀ v : V1, C.cls v = VClass.v10 → C.sigma v Z = C.sigma v e

/-- `Z` is a mismatch vector (Definition 4.4): a sum of local codewords. -/
def IsMismatchVector (C : TannerCode Q V1 κ) (Z : BitVec Q) : Prop :=
  ∃ ε : V1 → BitVec Q, (∀ v, ε v ∈ C.localCode v) ∧ Z = ∑ v : V1, ε v

/-- The flip set of §4.2 attached to a local codeword `x = c + r` at a vertex
`v`: `0` on `V10`, `x` on `V01`, `c` on `V11` and `r` on `V00`. -/
def flipSet (C : TannerCode Q V1 κ) (v : V1) (c r : BitVec Q) : BitVec Q :=
  match C.cls v with
  | VClass.v10 => 0
  | VClass.v01 => c + r
  | VClass.v11 => c
  | VClass.v00 => r

/-- Vertex support `|D|_V` of a syndrome-error vector `D` (Definition 4.3):
the number of vertices at which `D` is nonzero. -/
noncomputable def vertexSupport (D : V1 → BitVec κ) : ℕ := by
  classical
  exact (Finset.univ.filter fun v => D v ≠ 0).card

/-- Real-valued vertex support. -/
noncomputable def vertexSupportR (D : V1 → BitVec κ) : ℝ := (vertexSupport D : ℝ)

/-- The paper's error weight `|e|` (Hamming weight). -/
noncomputable def errWeight (e : BitVec Q) : ℝ := weightR e

/-- The paper's reduced error weight `|e|_R` (Definition 4.3 / §2). -/
noncomputable def redWeight (C : TannerCode Q V1 κ) (e : BitVec Q) : ℝ :=
  C.reducedWeight e

end Qatlib.Papers.OneShotLDPC23.MainResults.Model
