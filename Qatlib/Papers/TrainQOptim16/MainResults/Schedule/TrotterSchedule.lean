/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrainQOptim16.MainResults.IsingModel
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula

set_option backward.isDefEq.respectTransparency false

/-!
# QAOA schedules, the modified ansatz, and its Trotter–Suzuki implementation

Source: Wecker, Hastings, Troyer, *Training A Quantum Optimizer*,
fixed arXiv:1605.05370v1.

* Eq. (1), p. 1 / Eq. (3), p. 2: the modified ansatz
  `ΨF = exp(i(θpX HX + θpZ HZ)) ⋯ exp(i(θ1X HX + θ1Z HZ)) ΨI`;
* p. 3, Sec. III.B: the Trotter–Suzuki implementation
  `exp(i(θX HX + θZ HZ)) ≈ (exp(i θZ HZ/2n) exp(i θX HX/n) exp(i θZ HZ/2n))^n`,
  with the paper's choice `n = 4`;
* p. 5, Sec. IV: the notation `L(p,x,z)` for the linear annealing schedule
  `θjZ = z j/(p+1)`, `θjX = x (p+1-j)/(p+1)`.

Lean's `HamiltonianEvolution H t` is `exp(-i t H)`; the paper writes `exp(+i θ H)`.
`paperEvolution H θ := HamiltonianEvolution H (-θ)` is therefore the paper's
phase convention. `microStepTrotter` is `pfStrang` of the two generators
`-θZ/n • HZ` and `-θX/n • HX`, so its printed product form is recovered in
`printedStepFactor_eq_pfStrang`, and the shared second-order error theorem
`product_formula_strang_nested_commutator` gives `microStepTrotter_error`.

Boundary: these are the paper's ansatz and its per-substep Trotter factor; no
claim is made that the Trotter error is negligible for the paper's chosen
`n = 4`. The empirical training results are in `SourceClaims`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrainQOptim16.MainResults.Schedule

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-- A `p`-step schedule: the angles `θjX`, `θjZ` of Eq. (1). -/
structure Schedule (p : ℕ) where
  /-- The transverse-field angles `θjX`. -/
  thetaX : Fin p → ℝ
  /-- The diagonal-field angles `θjZ`. -/
  thetaZ : Fin p → ℝ

/-- The linear schedule `L(p,x,z)` of Sec. IV, p. 5:
`θjZ = z j/(p+1)` and `θjX = x (p+1-j)/(p+1)` for `j = 1,…,p`. -/
def linearAnnealSchedule (p : ℕ) (x z : ℝ) : Schedule p where
  thetaX j := x * ((p + 1 : ℝ) - ((j.val : ℝ) + 1)) / (p + 1 : ℝ)
  thetaZ j := z * ((j.val : ℝ) + 1) / (p + 1 : ℝ)

/-- The linear schedule's defining angle formulas (Sec. IV, p. 5). -/
theorem linearAnnealSchedule_theta (p : ℕ) (x z : ℝ) (j : Fin p) :
    (linearAnnealSchedule p x z).thetaZ j =
        z * ((j.val : ℝ) + 1) / (p + 1 : ℝ) ∧
      (linearAnnealSchedule p x z).thetaX j =
        x * ((p + 1 : ℝ) - ((j.val : ℝ) + 1)) / (p + 1 : ℝ) :=
  ⟨rfl, rfl⟩

/-- The paper's phase convention `exp(+i θ H)`, expressed through Lean's
`exp(-i t H)`. -/
def paperEvolution (D : ℕ) (H : Operator D) (θ : ℝ) : Operator D :=
  HamiltonianEvolution H (-θ)

/-- `paperEvolution H θ` really is `exp(-i (-θ) H)`. -/
theorem paperEvolution_def (D : ℕ) (H : Operator D) (θ : ℝ) :
    paperEvolution D H θ = HamiltonianEvolution H (-θ) := rfl

/-- Scaling the generator is the same as scaling the time: `exp(-i t (cH)) =
exp(-i (c t) H)`. -/
theorem hamiltonianEvolution_smul (D : ℕ) (H : Operator D) (c t : ℝ) :
    HamiltonianEvolution (c • H) t = HamiltonianEvolution H (c * t) := by
  unfold HamiltonianEvolution
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

/-- Reversing the sign of the generator reverses the time. -/
theorem hamiltonianEvolution_neg (D : ℕ) (H : Operator D) (t : ℝ) :
    HamiltonianEvolution (-H) t = HamiltonianEvolution H (-t) := by
  rw [show (-H) = (-1 : ℝ) • H by simp, hamiltonianEvolution_smul]
  congr 1
  ring

/-- The exact one-step evolution of the modified ansatz, Eq. (3), for a step
with angles `θX, θZ`: `exp(i(θX HX + θZ HZ))`. -/
def stepEvolution (D : ℕ) (HX HZ : Operator D) (θX θZ : ℝ) : Operator D :=
  paperEvolution D (θX • HX + θZ • HZ) 1

/-- The paper's full modified ansatz unitary, Eq. (3): the chronological product
of the `p` step evolutions. -/
def ansatzUnitary (D : ℕ) (HX HZ : Operator D) {p : ℕ} (s : Schedule p) : Operator D :=
  (List.ofFn fun j : Fin p => stepEvolution D HX HZ (s.thetaX j) (s.thetaZ j)).foldl
    (fun U V => V * U) 1

/-- Applying the ansatz unitary to the initial state `ΨI` (the ground state of
`HX`, Sec. I, p. 1). -/
def ansatzState (D : ℕ) (HX HZ : Operator D) {p : ℕ} (s : Schedule p)
    (ψI : Fin D → ℂ) : Fin D → ℂ :=
  ansatzUnitary D HX HZ s *ᵥ ψI

/-- The generator `-θZ/n • HZ` of the Strang factor: its sign matches the paper's
`exp(+i θZ HZ/2n)` convention. -/
def zGenerator (D : ℕ) (HZ : Operator D) (θZ : ℝ) (n : ℕ) : Operator D :=
  (-(θZ / (n : ℝ))) • HZ

/-- The generator `-θX/n • HX` of the Strang factor. -/
def xGenerator (D : ℕ) (HX : Operator D) (θX : ℝ) (n : ℕ) : Operator D :=
  (-(θX / (n : ℝ))) • HX

/-- One Strang micro-step, p. 3: the `n`-fold subdivision of a single ansatz step,
written through the shared `pfStrang` word. -/
def microStepTrotter (D : ℕ) (HX HZ : Operator D) (θX θZ : ℝ) (n : ℕ) :
    Operator D :=
  pfStrang (zGenerator D HZ θZ n) (xGenerator D HX θX n) 1

/-- The exact evolution of one micro-step: `exp(i(θX/n HX + θZ/n HZ))`. -/
def microStepExact (D : ℕ) (HX HZ : Operator D) (θX θZ : ℝ) (n : ℕ) :
    Operator D :=
  paperEvolution D ((θX / (n : ℝ)) • HX + (θZ / (n : ℝ)) • HZ) 1

/-- The paper's printed Trotter factor, p. 3, for one micro-step:
`exp(i θZ HZ/2n) exp(i θX HX/n) exp(i θZ HZ/2n)`. -/
def printedMicroStep (D : ℕ) (HX HZ : Operator D) (θX θZ : ℝ) (n : ℕ) :
    Operator D :=
  paperEvolution D ((θZ / (2 * (n : ℝ))) • HZ) 1 *
    paperEvolution D ((θX / (n : ℝ)) • HX) 1 *
    paperEvolution D ((θZ / (2 * (n : ℝ))) • HZ) 1

/-- The `n`-fold repetition of the printed micro-step, i.e. the parenthesized
factor of the paper's displayed Trotter formula (p. 3). -/
def printedStepFactor (D : ℕ) (HX HZ : Operator D) (θX θZ : ℝ) (n : ℕ) :
    Operator D :=
  (printedMicroStep D HX HZ θX θZ n) ^ n

/-- The paper's displayed Trotter formula: the `n`-th power of the printed
micro-step is exactly the Strang word used by `microStepTrotter`. -/
theorem printedStepFactor_eq_pfStrang (D : ℕ) (HX HZ : Operator D)
    (θX θZ : ℝ) (n : ℕ) (hn : 0 < n) :
    printedStepFactor D HX HZ θX θZ n = (microStepTrotter D HX HZ θX θZ n) ^ n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hz : HamiltonianEvolution (zGenerator D HZ θZ n) (1 / 2) =
      paperEvolution D ((θZ / (2 * (n : ℝ))) • HZ) 1 := by
    unfold zGenerator paperEvolution
    rw [hamiltonianEvolution_smul, hamiltonianEvolution_smul]
    congr 1
    field_simp [hn']
  have hx : HamiltonianEvolution (xGenerator D HX θX n) 1 =
      paperEvolution D ((θX / (n : ℝ)) • HX) 1 := by
    unfold xGenerator paperEvolution
    rw [hamiltonianEvolution_smul, hamiltonianEvolution_smul]
    congr 1
    field_simp [hn']
  unfold printedStepFactor printedMicroStep microStepTrotter pfStrang
  rw [hz, hx]

/-- Second-order Strang error of one printed micro-step, reusing the shared
`product_formula_strang_nested_commutator` from `TrotterFormula.LieStrang`. -/
theorem microStepTrotter_error (D : ℕ) (HX HZ : Operator D)
    (θX θZ : ℝ) (n : ℕ) (hHX : HX.IsHermitian) (hHZ : HZ.IsHermitian) :
    ‖microStepTrotter D HX HZ θX θZ n - microStepExact D HX HZ θX θZ n‖ ≤
      (1 / 12) * ‖pfComm (xGenerator D HX θX n)
          (pfComm (xGenerator D HX θX n) (zGenerator D HZ θZ n))‖ +
      (1 / 24) * ‖pfComm (zGenerator D HZ θZ n)
          (pfComm (zGenerator D HZ θZ n) (xGenerator D HX θX n))‖ := by
  have hA : (zGenerator D HZ θZ n).IsHermitian := by
    unfold zGenerator
    exact hHZ.smul (by show IsSelfAdjoint (-(θZ / (n : ℝ))); simp [IsSelfAdjoint])
  have hB : (xGenerator D HX θX n).IsHermitian := by
    unfold xGenerator
    exact hHX.smul (by show IsSelfAdjoint (-(θX / (n : ℝ))); simp [IsSelfAdjoint])
  have h := product_formula_strang_nested_commutator D (zGenerator D HZ θZ n)
    (xGenerator D HX θX n) 1 hA hB
  have hsum : zGenerator D HZ θZ n + xGenerator D HX θX n =
      -(((θX / (n : ℝ)) • HX) + ((θZ / (n : ℝ)) • HZ)) := by
    unfold zGenerator xGenerator
    rw [neg_add]
    simp only [neg_smul]
    abel
  have heq : HamiltonianEvolution
      (zGenerator D HZ θZ n + xGenerator D HX θX n) 1 =
      microStepExact D HX HZ θX θZ n := by
    unfold microStepExact paperEvolution
    rw [hsum, hamiltonianEvolution_neg]
  rw [heq] at h
  simpa [microStepTrotter, abs_one] using h

/-- The Trotterized ansatz unitary with the paper's `n` substeps per ansatz
step (Sec. III.B, p. 3). -/
def trotterizedAnsatzUnitary (D : ℕ) (HX HZ : Operator D) {p : ℕ} (s : Schedule p)
    (n : ℕ) : Operator D :=
  (List.ofFn fun j : Fin p =>
      printedStepFactor D HX HZ (s.thetaX j) (s.thetaZ j) n).foldl
    (fun U V => V * U) 1

/-- The Trotterized schedule is exactly the same word as the ansatz with each
step replaced by its printed Strang factor. -/
theorem trotterizedAnsatzUnitary_eq (D : ℕ) (HX HZ : Operator D)
    {p : ℕ} (s : Schedule p) (n : ℕ) (hn : 0 < n) :
    trotterizedAnsatzUnitary D HX HZ s n =
      (List.ofFn fun j : Fin p =>
        (microStepTrotter D HX HZ (s.thetaX j) (s.thetaZ j) n) ^ n).foldl
        (fun U V => V * U) 1 := by
  unfold trotterizedAnsatzUnitary
  congr 1
  rw [List.ofFn_inj]
  funext j
  exact printedStepFactor_eq_pfStrang D HX HZ (s.thetaX j) (s.thetaZ j) n hn

end Qatlib.Papers.TrainQOptim16.MainResults.Schedule
