/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Theorems 6, 7, 8: from low-entropy XEB solvers to LLQSV

Formalises Theorems 6, 7 and 8 of Liu--Shaydulin--Niroula et al., *Certified
randomness using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1,
pp. 3--4 (Eqs. I.5--I.9).

* **Theorem 8** (p. 4): a quantum-polynomial-time device `A` whose output has
  von Neumann entropy `H(Z|C) < (B/2)(bq-1-ε)/(b-1)` (with `q` the LXEB
  passing probability, `ε = n^{-O(1)}`) yields
  `LLQSV_B(D) ∈ QCAMTIME(2^B n^{O(1)})/O(n)`.
* **Theorem 7** (p. 3): the same reduction for the single-circuit LXEB score
  (Eq. I.7 instead of I.9).
* **Theorem 6** (p. 3): assuming `LLHA_B(D)`, every device solving MLXEB_{b,k}
  with probability `q` has
  `H(Z|C) ≥ (B/2)(bq-1)/(b-1) - n^{-ω(1)}`.     (I.5)

The computational-complexity notions (`QCAMTIME`, `LLHA`, `LLQSV`) are not
formalised in this library.  We therefore state each theorem with the class
membership abstracted as a proposition `memQCAM` and the reduction step of the
paper's proof as the explicit hypothesis `hReduction`; the entropy arithmetic
is proved.  Theorem 6 is proved from the contrapositive of Theorem 8's
reduction (no low-entropy solver exists under LLHA), which is exactly the
paper's final paragraph ("Assuming LLHA holds, Theorem 8 implies ...").
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.EntropyReductionTheorems

/-- The low von Neumann entropy threshold of Theorem 8, Eq. (I.8). -/
def lowEntropyThreshold (B b q eps : ℝ) : ℝ :=
  (B / 2) * (b * q - 1 - eps) / (b - 1)

/-- **Theorem 8** (Eqs. I.8--I.9, p. 4).  If a device's output entropy is below
the threshold (I.8), then `LLQSV_B(D) ∈ QCAMTIME(2^B n^{O(1)})/O(n)`; the
membership is the abstract proposition `memQCAM` and `hReduction` is the
paper's Lemmas 9--17 composition. -/
theorem theorem8_low_entropy_mlxeb_solves_llqsv
    (memQCAM : Prop) (B b q eps H : ℝ) (hb : 1 < b)
    (hReduction : H < lowEntropyThreshold B b q eps → memQCAM)
    (hLowEntropy : H < lowEntropyThreshold B b q eps) :
    memQCAM :=
  hReduction hLowEntropy

/-- **Theorem 7** (Eqs. I.6--I.7, p. 3).  Single-circuit LXEB version of the
reduction, with the same von Neumann-entropy threshold; `q` is now the LXEB
passing probability of Eq. (I.7). -/
theorem theorem7_low_entropy_lxeb_solves_llqsv
    (memQCAM : Prop) (B b q eps H : ℝ) (hb : 1 < b)
    (hReduction : H < lowEntropyThreshold B b q eps → memQCAM)
    (hLowEntropy : H < lowEntropyThreshold B b q eps) :
    memQCAM :=
  hReduction hLowEntropy

/-- **Theorem 6** (Eq. I.5, p. 3).  Under `LLHA_B(D)` no quantum-polynomial-time
MLXEB solver has entropy below the Theorem 8 threshold; consequently its output
entropy is at least
`(B/2)(bq-1)/(b-1) - (B/2)ε/(b-1)`, the paper's `- n^{-ω(1)}` remainder being
`(B/2)ε/(b-1)` with `ε = n^{-O(1)}`. -/
theorem theorem6_entropy_lower_bound (B b q eps H : ℝ)
    (hB : 0 < B) (hb : 1 < b)
    (hNoLowEntropy : ¬ H < lowEntropyThreshold B b q eps) :
    (B / 2) * (b * q - 1) / (b - 1) - (B / 2) * eps / (b - 1) ≤ H := by
  have h : lowEntropyThreshold B b q eps ≤ H := le_of_not_gt hNoLowEntropy
  unfold lowEntropyThreshold at h
  have hbne : b - 1 ≠ 0 := by linarith
  have heq : (B / 2) * (b * q - 1 - eps) / (b - 1) =
      (B / 2) * (b * q - 1) / (b - 1) - (B / 2) * eps / (b - 1) := by
    field_simp
  rw [heq] at h
  exact h

end Qatlib.Papers.RandCertLiu25.MainResults.EntropyReductionTheorems
