/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GndStatePrep20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5 (Reflector and projector) — arXiv:2002.12508v3, p.6 (Section 2)

`c001`.  The paper states:

> Lemma 5 (Reflector and projector). Given a Hermitian matrix `H` with its
> `(α,m,0)`-block-encoding `U_H`, with the guarantee that `μ ∈ ℝ` is separated
> from the spectrum of `H` by a gap of at least `Δ/2`, we can construct an
> `(1,m+2,ε)`-block-encoding of `R_{<μ}`, and an `(1,m+3,ε/2)`-block-encoding of
> `P_{<μ}`, both using `O(α/Δ · log(1/ε))` applications of `U_H` and `U_H†`, and
> `O(mα/Δ · log(1/ε))` other one- and two-qubit gates.

Route (paper Section 2):
1. The sign-polynomial approximation of Lemma 3 (from [23]) has degree
   `ℓ = O((1/δ) log(1/ε))` with `δ = Δ/(4α)`.  Applying it through QSVT
   (Theorem 1 of the paper, i.e. Gilyén–Su–Low–Wiebe) to the block-encoding of
   `(H − μI)/(α+|μ|)` gives the `(1,m+2,ε)`-block-encoding `REF(μ,δ,ε)` of
   `R_{<μ}` (this is the black box reused as `hR` below).
2. The projector circuit Eq. (2) (one Hadamard ancilla + controlled-`REF`) has
   compression `½(I + REF)`, so `‖P̃ − P_{<μ}‖ ≤ ½‖R̃ − R_{<μ}‖ ≤ ε/2`
   (paper p.6).  This half is proved here in
   `projectorBlockEncoding_of_reflector` and returned as the second conjunct.

The query and gate counts of step 1 are exactly those of the QSP polynomial
degree; they are not reproved here (the QSVT machinery is outside this paper's
own contribution).  `lemma5_query_gate_cost` records the arithmetic that, from
Lemma 3's degree bound, gives the paper's two `O` expressions.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GndStatePrep20.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators Classical

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding

/-- **Lemma 5 (Reflector and projector), paper p.6.**

Given the QSP-produced `(1,m+2,ε)`-block-encoding `hR` of the reflector
`R_{<μ} = Rmat` (built from the sign polynomial of Lemma 3 through QSVT, the
cited black box), and the projector circuit Eq. (2) whose compression is
`½(I + compress L U Rf)`, we obtain both
* the reflector block-encoding `Rmat` (returned unchanged), and
* an `(1,m+3,ε/2)`-block-encoding of the projector `Pmat = ½(I + Rmat)`.

The error-halving `‖P̃ − P‖ ≤ ε/2` is the content proved here; it is exactly the
paper's chain `‖P̃ − P_{<μ}‖ ≤ ½‖R̃ − R_{<μ}‖ ≤ ε/2` (p.6). -/
theorem lemma5_reflector_projector
    {Hsp I : Type*} [Fintype Hsp] [Fintype I] [DecidableEq Hsp] [DecidableEq I]
    {Rmat Pmat : Matrix I I ℂ} {U Up : Matrix Hsp Hsp ℂ}
    {L Lp Rf Rp : Matrix Hsp I ℂ} {ε : ℝ}
    (hR : BlockEncoding Rmat U L Rf 1 ε)
    (hUp : Up ∈ Matrix.unitaryGroup Hsp ℂ)
    (hLp : IsIsometry Lp) (hRp : IsIsometry Rp)
    (hPmat : Pmat = (1 / 2 : ℂ) • ((1 : Matrix I I ℂ) + Rmat))
    (hCircuit : compress Lp Up Rp = (1 / 2 : ℂ) • ((1 : Matrix I I ℂ) + compress L U Rf)) :
    BlockEncoding Rmat U L Rf 1 ε ∧ BlockEncoding Pmat Up Lp Rp 1 (ε / 2) :=
  ⟨hR, projectorBlockEncoding_of_reflector hUp hLp hRp hPmat hCircuit
    (by simpa only [one_smul] using hR.error_le)⟩

/-- **Query/gate accounting of Lemma 5 (paper p.6).**

The QSP polynomial of Lemma 3 has degree `ℓ` and uses `ℓ + 1` applications of
the encoded unitary per QSVT evaluation; each such application in turn calls
`U_H` (and `U_H†`) once.  Given Lemma 3's degree bound
`ℓ + 1 ≤ Cq · (α/Δ) · log(1/ε)`, the query complexity and the
`m`-fold tensor one-qubit and two-qubit gate count satisfy the paper's two `O` bounds
with constants `Cq` and `Cq`. -/
theorem lemma5_query_gate_cost
    {ℓ m : ℕ} {α Δ ε Cq : ℝ}
    (hCq : 0 ≤ Cq) (hm : 0 ≤ (m : ℝ))
    (hdeg : (ℓ + 1 : ℝ) ≤ Cq * (α / Δ) * Real.log (1 / ε)) :
    (ℓ + 1 : ℝ) ≤ Cq * (α / Δ) * Real.log (1 / ε) ∧
      (m : ℝ) * (ℓ + 1) ≤ Cq * (m : ℝ) * (α / Δ) * Real.log (1 / ε) := by
  refine ⟨hdeg, ?_⟩
  calc
    (m : ℝ) * (ℓ + 1) ≤ (m : ℝ) * (Cq * (α / Δ) * Real.log (1 / ε)) := by
      exact mul_le_mul_of_nonneg_left hdeg hm
    _ = Cq * (m : ℝ) * (α / Δ) * Real.log (1 / ε) := by ring

end Qatlib.Papers.GndStatePrep20.MainResults
