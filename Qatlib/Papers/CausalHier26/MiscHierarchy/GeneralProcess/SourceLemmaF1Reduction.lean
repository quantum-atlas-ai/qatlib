/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.GeneralProcess.SourceProp44GeneralError
import Mathlib.Data.Real.StarOrdered

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemmaF1Reduction — Lemma F.1 (general-process charge-block reduction)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Lemma F.1, p. 39
(txt lines 2105-2130), Eqs. (203)-(204).

**Statement.**  For every reduced general-process feasible point with `T_1 = 0`,
averaging over the independent amplitude-damping phase symmetries, entrywise
complex conjugation, and `A ↔ B` preserves feasibility and `x_c`.  In the bases
`(|1⟩,|4⟩,|13⟩,|16⟩)`, `(|3⟩,|15⟩)`, `(|9⟩,|12⟩)` the contributing `S` blocks are

```
[[r0-2r1+2r4, -r2, -r2, 0],
 [-r2, r1-r3+r5, 0, r2],
 [-r2, 0, r1-r3+r5, r2],
 [0, r2, r2, 2r3-r5]],
[[r1,r2],[r2,r3]],   [[r1,r2],[r2,r3]],
```

with `r0 + 2 r4 + r5 = 1`; the omitted charge sectors are orthogonal to the
off-diagonal support of `G_ε` and do not contribute to `x_c`.

**Modelling boundary.**  The raw general-process SDP and the exchange symmetries
are not rebuilt.  What the present file records is the normal form `GenSymBlock`
of Eq. (203), its trace normalization (204), the positive semidefiniteness of the
three displayed blocks, and the optimality conclusion `x_c ≤ s(ε + R_ε)` of the
Appendix F certificate (Eq. (215)-(220)).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.GeneralProcess

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model

/-- The general-process charge-block tuple `(r0,…,r5)` of Eq. (203), p. 39. -/
structure GenSymBlock where
  /-- Entry `r_0`. -/
  r0 : ℝ
  /-- Entry `r_1`. -/
  r1 : ℝ
  /-- Entry `r_2`. -/
  r2 : ℝ
  /-- Entry `r_3`. -/
  r3 : ℝ
  /-- Entry `r_4`. -/
  r4 : ℝ
  /-- Entry `r_5`. -/
  r5 : ℝ

/-- Eq. (203), p. 39: the first `4 × 4` contributing block of `S`. -/
def genSymS00 (B : GenSymBlock) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![B.r0 - 2 * B.r1 + 2 * B.r4, -B.r2, -B.r2, 0;
     -B.r2, B.r1 - B.r3 + B.r5, 0, B.r2;
     -B.r2, 0, B.r1 - B.r3 + B.r5, B.r2;
     0, B.r2, B.r2, 2 * B.r3 - B.r5]

/-- Eq. (203), p. 39: the `(3,15)` contributing `2 × 2` block of `S`. -/
def genSymS0m1 (B : GenSymBlock) : Matrix (Fin 2) (Fin 2) ℝ := !![B.r1, B.r2; B.r2, B.r3]

/-- Eq. (203), p. 39: the `(9,12)` contributing `2 × 2` block of `S`. -/
def genSymS02 (B : GenSymBlock) : Matrix (Fin 2) (Fin 2) ℝ := !![B.r1, B.r2; B.r2, B.r3]

/-- Eq. (204), p. 39: the trace normalization of a general-process block tuple. -/
def GenSymNormal (B : GenSymBlock) : Prop := B.r0 + 2 * B.r4 + B.r5 = 1

/-- The witness block used to establish that the general-process normal form is
nonempty: `r0 = 1`, all other parameters zero.  Its three blocks are the rank-one
`|1⟩⟨1|` projection and the zero matrices, all positive semidefinite. -/
def genSymBlockUnit : GenSymBlock :=
  ⟨1, 0, 0, 0, 0, 0⟩

/-- Fixed arXiv:2609.08639v1, Lemma F.1, Eq. (203)-(204), p. 39: the
general-process normal form is nonempty, trace-normalized, and its blocks are
positive semidefinite; moreover no general-process coherence value exceeds the
Appendix F certificate bound `s(ε + R_ε)`.

SOURCE: Lemma F.1, p. 39, Eqs. (203)-(204), and the certificate conclusion
Eq. (215)-(220).
PAPER PROOF: solving the linear system (205) gives (203); the trace equation gives
(204); the certificate operators `P_ε, Q_ε ⪰ 0` of Eq. (211) with
`H_ε = G_ε - (Q_ε - P_ε)` diagonal (Eq. (219)) give
`x_c = ⟨Q_ε - P_ε, T_c⟩ ≤ s(ε + R_ε)` (Eq. (220)).
LEAN GAP: the reduction of an arbitrary feasible point to the normal form (the
symmetry averaging and the linear system (205)), and the certificate construction
of Eq. (211), are not rebuilt; only the nonemptiness/PSD/normalization of the
normal form and the final bound (via Proposition 4.4's family bound) are proved.
CANDIDATE REUSE: `genXc_le` (`GeneralProcess/SourceProp44GeneralError.lean`) for
the bound; `Matrix.PosSemidef` for the blocks.
SUGGESTED TACTIC: for the bound, reuse `genXc_le`; for the reduction, formalize
the symmetry averaging as projection maps on the charge-block space. -/
theorem source_lemma_F1_general_block_reduction (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ B : GenSymBlock,
      GenSymNormal B ∧
      (genSymS00 B).PosSemidef ∧ (genSymS0m1 B).PosSemidef ∧ (genSymS02 B).PosSemidef ∧
      genXc ε t ≤ s ε * (ε + Rε ε) := by
  refine ⟨genSymBlockUnit, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GenSymNormal genSymBlockUnit
    norm_num
  · have h : genSymS00 genSymBlockUnit = Matrix.diagonal ![(1 : ℝ), 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [genSymS00, genSymBlockUnit, Matrix.diagonal]
    rw [h]
    exact Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> simp)
  · have h : genSymS0m1 genSymBlockUnit = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [genSymS0m1, genSymBlockUnit]
    rw [h]
    exact Matrix.PosSemidef.zero
  · have h : genSymS02 genSymBlockUnit = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [genSymS02, genSymBlockUnit]
    rw [h]
    exact Matrix.PosSemidef.zero
  · exact genXc_le ε t h0 h1 ht

end Qatlib.Papers.CausalHier26.MiscHierarchy.GeneralProcess
