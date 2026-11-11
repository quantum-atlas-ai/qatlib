/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 1: the low-depth controlled-`Rz` circuit

Source: arXiv:1605.03590v2, Appendix B, Lemma 1 and Fig. 5 (p.11).

Fig. 5 shows a two-qubit circuit implementing `Λ(Rz(2θ))` with the top qubit as
control: two CNOTs with single-qubit `Rz` rotations in between.  We use the
convention `Rz(α) = diag(e^{iα/2}, e^{-iα/2})`; the labels `∓θ/2` of Fig. 5 then
correspond to the rotations `Rz(∓θ)`, i.e. the pair of angles appearing in the
definition of `lowDepthCircuit`.

The circuit is a concrete 4×4 complex matrix: `CNOT`, then `Rz(-θ)` on the target,
then `CNOT`, then `Rz(θ)` on the target.  We prove it equals the controlled gate
`Λ(Rz(2θ))` entrywise, following the proof of Lemma 1 (Eqs. (B3)--(B5)): the CNOTs
move the target into and out of the control basis, and the rotations contribute the
`±θ` phases precisely on the controlled branch.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.ReactionMech16.MainResults.Source

/-- Target flip of a CNOT with control `c`. -/
def cnotTarget (c t : Bool) : Bool := if c then !t else t

/-- Single-qubit rotation `Rz(α) = diag(e^{iα/2}, e^{-iα/2})` in the `Bool` basis. -/
noncomputable def rzGate (α : ℝ) : Matrix Bool Bool ℂ :=
  fun a b =>
    if a = b then
      (if a then Complex.exp (-(Complex.I * (((α / 2 : ℝ) : ℂ))))
       else Complex.exp (Complex.I * (((α / 2 : ℝ) : ℂ))))
    else 0

/-- CNOT with the first (control) qubit as control and the second as target. -/
noncomputable def cnotGate : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = cnotTarget q.1 q.2 then 1 else 0

/-- `Rz(α)` acting on the target (second) qubit. -/
noncomputable def targetRz (α : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => if p.1 = q.1 then rzGate α p.2 q.2 else 0

/-- Controlled `Rz(α)`: the first qubit is the control. -/
noncomputable def controlledRz (α : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if p.1 then rzGate α p.2 q.2 else if p.2 = q.2 then 1 else 0)
    else 0

/-- The Fig. 5 circuit: `CNOT`, `Rz(-θ)` on the target, `CNOT`, `Rz(θ)` on the
target. -/
noncomputable def lowDepthCircuit (θ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  targetRz θ * cnotGate * targetRz (-θ) * cnotGate

/-- Product of complex exponentials as one exponential (used to combine the rotation
phases in the circuit). -/
private lemma exp_mul_exp (x y : ℂ) :
    Complex.exp x * Complex.exp y = Complex.exp (x + y) := by
  rw [Complex.exp_add]

/-- arXiv:1605.03590v2, Lemma 1 (p.11): the Fig. 5 circuit implements
`Λ(Rz(2θ))`, with the topmost qubit as control. -/
theorem lemma1_low_depth_controlled_rz (θ : ℝ) :
    lowDepthCircuit θ = controlledRz (2 * θ) := by
  ext p q
  obtain ⟨c, t⟩ := p
  obtain ⟨c', t'⟩ := q
  cases c <;> cases t <;> cases c' <;> cases t' <;>
    simp only [lowDepthCircuit, cnotGate, targetRz, rzGate, controlledRz, cnotTarget,
      Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
      if_false, if_true, mul_one, mul_zero, zero_mul, add_zero, zero_add,
      Bool.not_false, Bool.not_true, exp_mul_exp,
      true_and, false_and, and_true, and_false]
  all_goals
    push_cast <;> ring_nf <;> simp

end Qatlib.Papers.ReactionMech16.MainResults.Source
