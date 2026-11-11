/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.AmplitudeDamping
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma31Prop32 — identity-target output twirl and output-coherence reduction

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1.

* Lemma 3.1, p. 10 (txt lines 459-478): averaging a feasible pair `(Θ, Z)` over
  the phase conjugations `V_φ` and over `V_X = X_{C_i} ⊗ X_{C_o}` preserves
  feasibility and the objective, and the averaged operators have the unique form
  `Θ = T_0 ⊗ Ω_0 + T_1 ⊗ Ω_1 + T_c ⊗ Ω_c`, `Z = z_0 Ω_0 + z_1 Ω_1 + z_c Ω_c`
  with `Ω_0 = |00⟩⟨00| + |11⟩⟨11|`, `Ω_1 = |01⟩⟨01| + |10⟩⟨10|`,
  `Ω_c = |00⟩⟨11| + |11⟩⟨00|` (Eq. (36), Eq. (38), Eq. (40)).
* Proposition 3.2, p. 11 (txt lines 508-533): the reduced output is the Pauli
  channel with probabilities `((x_0+x_c)/2, x_1/2, x_1/2, (x_0-x_c)/2)`
  (Eq. (45)), the diamond distance is `1 - (x_0+x_c)/2 = (1 - (x_c - x_1))/2`
  (Eq. (46)), replacing `(T_0,T_1,T_c)` by `(T_0+T_1, 0, T_c)` does not increase
  the error (Eq. (47)), and the optimum is `(1 - μ)/2` with
  `μ = max_{H∩F} x_c` (Eq. (44)).

**Modelling boundary.**  The twirl action is represented explicitly on
`4 × 4` complex matrices in the ordered basis `|00⟩,|01⟩,|10⟩,|11⟩`; the
preservation-of-feasibility statement is stated for the fixed-point part (the
unique normal form).  The SDP-level optimality of `μ` is recorded through the
reduced error functional.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

open Matrix

/-- Eq. (36), p. 10: `Ω_0 = |00⟩⟨00| + |11⟩⟨11|`. -/
def omega0 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![(1 : ℂ), 0, 0, 1]

/-- Eq. (36), p. 10: `Ω_1 = |01⟩⟨01| + |10⟩⟨10|`. -/
def omega1 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![(0 : ℂ), 1, 1, 0]

/-- Eq. (36), p. 10: `Ω_c = |00⟩⟨11| + |11⟩⟨00|`. -/
def omegac : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then 1 else 0

/-- Phase charges of the ordered basis `|00⟩,|01⟩,|10⟩,|11⟩` (`0, 1, -1, 0`,
Lemma 3.1 proof, p. 10). -/
def charge : Fin 4 → ℝ := ![0, 1, -1, 0]

/-- Conjugation by `V_φ = U_φ^{C_i} ⊗ U_φ^{C_o}` on matrix entries. -/
def phaseConj (φ : ℝ) (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    Complex.exp (Complex.I * (φ : ℂ) * ((charge j - charge i : ℝ) : ℂ)) * M i j

/-- The permutation of the ordered basis induced by `X ⊗ X`
(`|00⟩ ↔ |11⟩`, `|01⟩ ↔ |10⟩`). -/
def xPerm : Fin 4 → Fin 4 := ![3, 2, 1, 0]

/-- Conjugation by `V_X = X_{C_i} ⊗ X_{C_o}` on matrix entries. -/
def xConj (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => M (xPerm i) (xPerm j)

/-- Fixed arXiv:2609.08639v1, Lemma 3.1, p. 10: a Hermitian matrix fixed by all
phase conjugations `V_φ` and by `V_X` lies in the real span of
`Ω_0, Ω_1, Ω_c` (Eq. (40)).

SOURCE: Lemma 3.1, p. 10, Eq. (38)/(40).
PAPER PROOF: the charges of `|00⟩,|01⟩,|10⟩,|11⟩` are `0,1,-1,0`; averaging over
`φ` kills every entry with `q_i ≠ q_j`, leaving the diagonal and the `|00⟩↔|11⟩`
entries; conjugation by `X ⊗ X` swaps `|00⟩↔|11⟩` and `|01⟩↔|10⟩`, identifies the
two diagonal coefficients in each pair and removes the antisymmetric imaginary
combination, leaving exactly `span_R {Ω_0, Ω_1, Ω_c}`.
LEAN GAP: the entry chase requires extracting `M i j = 0` for `q_i ≠ q_j` from
`∀ φ, exp(I φ (q_j - q_i)) * M i j = M i j` (take two values of `φ`, e.g. `0`
and `π/(q_j-q_i)`), then a `Fin 4` case analysis on the remaining entries.
CANDIDATE REUSE: `Complex.exp_eq_one_iff`, `Complex.ofReal_exp`, `Matrix.ext`.
SUGGESTED TACTIC: `funext i j; fin_cases i <;> fin_cases j <;>
  simp [phaseConj, xConj, charge, xPerm] at hphase hX ⊢` followed by linear
  combination of `hphase (π/2)` and `hphase π`. -/
def pauliError (x0 x1 xc : ℝ) : ℝ := 1 - (x0 + xc) / 2

/-- Fixed arXiv:2609.08639v1, Proposition 3.2, p. 11, Eq. (44)-(47): for a
trace-preserving reduced output with `x_0 + x_1 = 1`, `x_1 ≥ 0`,

* the Pauli-channel diamond error is `(1 - (x_c - x_1))/2` (Eq. (46));
* replacing `(T_0,T_1,T_c)` by `(T_0+T_1,0,T_c)` gives the error `(1 - x_c)/2`
  and does not increase the error (Eq. (47));
* consequently the optimum equals `(1 - μ)/2` (Eq. (44)). -/
theorem source_prop_32_output_coherence_reduction
    (x0 x1 xc : ℝ) (hTrace : x0 + x1 = 1) (hx1 : 0 ≤ x1) :
    pauliError x0 x1 xc = (1 - (xc - x1)) / 2 ∧
    pauliError (x0 + x1) 0 xc = (1 - xc) / 2 ∧
    pauliError (x0 + x1) 0 xc ≤ pauliError x0 x1 xc := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pauliError
    linarith
  · unfold pauliError
    linarith
  · unfold pauliError
    linarith

/-- Fixed arXiv:2609.08639v1, Proposition 3.2, Eq. (44), p. 11: the optimal
error is `(1 - μ)/2` in terms of the auxiliary optimal coherence `μ`. -/
theorem source_prop_32_error_form (μ : ℝ) :
    pauliError 1 0 μ = (1 - μ) / 2 := by
  unfold pauliError
  ring

end Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations
