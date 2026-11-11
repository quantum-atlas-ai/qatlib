/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.UniformHHLFilter
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
import Qatlib.Concepts.LchsSimulation.StaticLchs.ReadoutError
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.PSeries

/-!
# Finite Grid Gradient Readout

`GradientGrid` and `gradientWord` implement coordinate Fourier transforms, one diagonal phase
query, and inverse Fourier transforms for numerical gradient readout in the setting of
[Jordan2005Gradient]. The resource count treats each coordinate Fourier transform as one gate,
giving one phase query and `2 * d` gates.

Affine phases yield products of `qpeKernel` states, with exact basis-state readout at grid
frequencies. Kernel tails and phase perturbation bounds give a joint window probability of at
least `1 - 16*d/(M*w) - 4*pi*B` when the phase differs from its affine target by at most `B`;
`signedGridValue` converts sufficiently small circular windows into real-coordinate errors.

## Main statements

- `gradient_coordinate_qft_word_unitarity` establishes circuit unitarity and resource counts.
- `gradient_affine_actual_exact_readout` identifies exact affine readout.
- `gradient_offgrid_joint_window` bounds the joint off-grid window probability.
- `gradient_actual_phase_error_transport` transfers that bound through phase error.

## References

* [Jordan, 2005][Jordan2005Gradient], *Fast Quantum Algorithm for Numerical Gradient
  Estimation*.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Concepts.SignalPrimitive.GridGradient
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
/-- The finite `d`-coordinate grid with `M` labels per coordinate, represented by functions `Fin
d → Fin M`. -/
abbrev GradientGrid (d M : ℕ) := Fin d→Fin M
/-- The Fourier transform on coordinate `j`, acting as the identity on all other grid
coordinates. -/
noncomputable def coordinateQFT (d M : ℕ) (j : Fin d) :
    Matrix (GradientGrid d M) (GradientGrid d M) ℂ :=
  fun x y => if ∀ i : Fin d,i≠j → x i=y i then QFTMatrix M (x j) (y j) else 0
/-- The diagonal grid oracle whose entry at `x` is `exp (2*pi*I*φ x)`. -/
noncomputable def gradientPhase (d M : ℕ) (φ : GradientGrid d M→ℝ) :
    Matrix (GradientGrid d M) (GradientGrid d M) ℂ :=
  Matrix.diagonal (fun x => Complex.exp (2*Real.pi*Complex.I*(φ x:ℂ)))
/-- The circuit word applying one coordinate Fourier transform for each coordinate of
`GradientGrid d M`. -/
noncomputable def gradientQFTWord (d M : ℕ) : Circuit (GradientGrid d M) :=
  List.ofFn (fun j : Fin d => Step.gate (coordinateQFT d M j))
/-- The gradient circuit word consisting of coordinate Fourier transforms, one phase-oracle
query, and their adjoints in reverse order. -/
noncomputable def gradientWord (d M : ℕ) : Circuit (GradientGrid d M) :=
  gradientQFTWord d M ++ [.query] ++
    (gradientQFTWord d M).reverse.map (fun s => match s with
      | .gate U => .gate Uᴴ | .query => .query)
/-- The all-zero grid label, defined when `M` is positive. -/
def gradientZero (d M : ℕ) (hM : 0 < M) : GradientGrid d M := fun _ => ⟨0,hM⟩
/-- The output state obtained by running `gradientWord` with phase oracle `gradientPhase d M φ`
on the all-zero basis state. -/
noncomputable def gradientReadout (d M : ℕ) (hM : 0 < M) (φ : GradientGrid d M→ℝ) :
    QState (GradientGrid d M) := Run (gradientPhase d M φ) (gradientWord d M) (Ket (gradientZero d M hM))
/-- Decodes `z/M` as a signed real coordinate, retaining it when `2*z.val ≤ M` and subtracting
one otherwise. -/
noncomputable def signedGridValue (M : ℕ) (z : Fin M) : ℝ :=
  if 2*z.val≤M then (z.val:ℝ)/M else (z.val:ℝ)/M-1

/-- Each coordinate Fourier transform is unitary when the grid size `M` is positive. -/
theorem coordinateQFT_unitary (d M : ℕ) (j : Fin d) (hM : 0 < M) :
    coordinateQFT d M j ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ := by
  let e := Equiv.funSplitAt j (Fin M)
  have he : coordinateQFT d M j = Matrix.reindex e.symm e.symm
      (TensorGate (QFTMatrix M) (1 : Matrix ({i : Fin d // i ≠ j} → Fin M)
        ({i : Fin d // i ≠ j} → Fin M) ℂ)) := by
    ext x y
    change (if ∀ i, i ≠ j → x i = y i then _ else _) =
      QFTMatrix M (x j) (y j) * (1 : Matrix _ _ ℂ) (fun i : {i : Fin d // i ≠ j} => x i)
        (fun i : {i : Fin d // i ≠ j} => y i)
    have hh : (∀ i : Fin d, i ≠ j → x i = y i) ↔
        (fun i : {i : Fin d // i ≠ j} => x i) = (fun i : {i : Fin d // i ≠ j} => y i) := by
      constructor
      · intro h; funext i; exact h i i.property
      · intro h i hi; exact congrFun h ⟨i, hi⟩
    simp [Matrix.one_apply, hh]
  rw [he]
  exact unitaryGroup_reindex e.symm
    (tensorGate_unitary (qftMatrix_unitary hM) (Matrix.unitaryGroup _ ℂ).one_mem)

/-- A list containing only gate steps has zero oracle queries and gate count equal to its
length. -/
private theorem gradient_gate_list_resources {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Matrix I I ℂ)) :
    QueryCount (gs.map Step.gate) = 0 ∧ GateCount (gs.map Step.gate) = gs.length := by
  induction gs with
  | nil => simp
  | cons U gs ih => simp [ih]

/-- For positive `M`, the finite-grid gradient word has unitary gates, exactly one phase-oracle
query, and `2*d` coordinate Fourier gates, realizing the single-query circuit structure of
[Jordan2005Gradient]. -/
theorem gradient_coordinate_qft_word_unitarity (d M : ℕ) (hM : 0 < M) :
    IsUnitaryCircuit (gradientWord d M) ∧ QueryCount (gradientWord d M) = 1 ∧
      GateCount (gradientWord d M) = 2*d := by
  let gs := List.ofFn (coordinateQFT d M)
  have hf : gradientQFTWord d M = gs.map Step.gate := by
    simp [gradientQFTWord, gs, List.map_ofFn, Function.comp_def]
  have hb : (gradientQFTWord d M).reverse.map (fun s => match s with
      | .gate U => .gate Uᴴ | .query => .query) =
      (gs.reverse.map Matrix.conjTranspose).map Step.gate := by
    rw [hf]
    simp only [← List.map_reverse, List.map_map]
    rfl
  have hv : IsUnitaryCircuit (gradientQFTWord d M) := by
    intro U hU
    simp only [gradientQFTWord, List.mem_ofFn] at hU
    obtain ⟨j, hj⟩ := hU
    cases hj
    exact coordinateQFT_unitary d M j hM
  have hvi : IsUnitaryCircuit ((gs.reverse.map Matrix.conjTranspose).map Step.gate) := by
    intro U hU
    simp only [List.mem_map, List.mem_reverse] at hU
    obtain ⟨V, ⟨W, hW, rfl⟩, heq⟩ := hU
    cases heq
    have hW' : W ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ := by
      apply hv W
      rw [hf]
      exact List.mem_map.mpr ⟨W, hW, rfl⟩
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hW'
  have hfc := gradient_gate_list_resources gs
  have hbc := gradient_gate_list_resources (gs.reverse.map Matrix.conjTranspose)
  have hlen : gs.length = d := by simp [gs]
  refine ⟨?_, ?_, ?_⟩
  · simp only [gradientWord, hb, isUnitaryCircuit_append, isUnitaryCircuit_query]
    exact ⟨⟨hv, isUnitaryCircuit_nil⟩, hvi⟩
  · rw [gradientWord, hb, hf]
    simp only [queryCount_append, hfc.1, hbc.1, queryCount_query, queryCount_nil]
  · rw [gradientWord, hb, hf]
    simp only [gateCount_append, hfc.2, hbc.2, gateCount_query, gateCount_nil,
      List.length_map, List.length_reverse, hlen]
    omega

/-- Lifts a matrix on `Fin M` to coordinate `j` of the grid while preserving every other
coordinate. -/
noncomputable def coordinateGridGate (d M : ℕ) (j : Fin d)
    (U : Matrix (Fin M) (Fin M) ℂ) : Matrix (GradientGrid d M) (GradientGrid d M) ℂ :=
  fun x y => if ∀ i : Fin d, i ≠ j → x i = y i then U (x j) (y j) else 0

/-- Applying a lifted coordinate gate sums over replacements of coordinate `j`, weighted by the
corresponding row of `U`. -/
theorem coordinateGridGate_apply (d M : ℕ) (j : Fin d)
    (U : Matrix (Fin M) (Fin M) ℂ) (ψ : QState (GradientGrid d M))
    (x : GradientGrid d M) :
    ApplyGate (coordinateGridGate d M j U) ψ x =
      ∑ a : Fin M, U (x j) a * ψ (Function.update x j a) := by
  let e := Equiv.funSplitAt j (Fin M)
  let b : {i : Fin d // i ≠ j} → Fin M := fun i => x i
  change (∑ y, coordinateGridGate d M j U x y * ψ y) = _
  rw [← e.symm.sum_comp (fun y => coordinateGridGate d M j U x y * ψ y), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have hh (r : {i : Fin d // i ≠ j} → Fin M) :
      (∀ i : Fin d, i ≠ j → x i = e.symm (a, r) i) ↔ b = r := by
    constructor
    · intro h; funext i
      simpa [e, Equiv.funSplitAt_symm_apply, i.property] using! h i i.property
    · intro h i hi
      have := congrFun h ⟨i, hi⟩
      simpa [e, b, Equiv.funSplitAt_symm_apply, hi] using! this
  have he : e.symm (a, b) = Function.update x j a := by
    funext i
    by_cases hi : i = j
    · subst i; simp [e, Equiv.funSplitAt_symm_apply]
    · simp [e, b, Equiv.funSplitAt_symm_apply, hi]
  simp only [coordinateGridGate, hh]
  rw [Finset.sum_eq_single b]
  · simp [e, Equiv.funSplitAt_symm_apply, he]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

/-- The amplitude after a coordinate Fourier transform is the Fourier-weighted sum of amplitudes
obtained by varying that coordinate. -/
theorem coordinateQFT_apply (d M : ℕ) (j : Fin d) (ψ : QState (GradientGrid d M))
    (x : GradientGrid d M) :
    ApplyGate (coordinateQFT d M j) ψ x =
      ∑ a : Fin M, QFTMatrix M (x j) a * ψ (Function.update x j a) :=
  coordinateGridGate_apply d M j (QFTMatrix M) ψ x

/-- Taking the conjugate transpose commutes with lifting a matrix to a grid coordinate. -/
theorem coordinateGridGate_adjoint (d M : ℕ) (j : Fin d)
    (U : Matrix (Fin M) (Fin M) ℂ) :
    (coordinateGridGate d M j U)ᴴ = coordinateGridGate d M j Uᴴ := by
  ext x y
  have hh : (∀ i : Fin d, i ≠ j → y i = x i) ↔
      (∀ i : Fin d, i ≠ j → x i = y i) := by
    constructor <;> intro h i hi <;> exact (h i hi).symm
  simp only [Matrix.conjTranspose_apply, coordinateGridGate, hh]
  split_ifs <;> simp

/-- The grid state whose amplitude is the product of the supplied one-coordinate state
amplitudes. -/
def gridProductState {d M : ℕ} (v : Fin d → QState (Fin M)) : QState (GradientGrid d M) :=
  fun x => ∏ i, v i (x i)

/-- A lifted coordinate gate maps a product state to the product state with only its `j`th
factor transformed by `U`. -/
theorem coordinateGridGate_productState (d M : ℕ) (j : Fin d)
    (U : Matrix (Fin M) (Fin M) ℂ) (v : Fin d → QState (Fin M)) :
    ApplyGate (coordinateGridGate d M j U) (gridProductState v) =
      gridProductState (Function.update v j (ApplyGate (U) (v j))) := by
  funext x
  rw [coordinateGridGate_apply]
  have hp (a : Fin M) : gridProductState v (Function.update x j a) =
      v j a * ∏ i ∈ Finset.univ.erase j, v i (x i) := by
    unfold gridProductState
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp_rw [hp, ← mul_assoc]
  rw [← Finset.sum_mul]
  unfold gridProductState
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  change (ApplyGate (U) (v j)) (x j) * _ = _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- A coordinate Fourier transform changes only the corresponding factor of a grid product
state. -/
theorem coordinateQFT_productState (d M : ℕ) (j : Fin d) (v : Fin d → QState (Fin M)) :
    ApplyGate (coordinateQFT d M j) (gridProductState v) =
      gridProductState (Function.update v j (ApplyGate (QFTMatrix M) (v j))) :=
  coordinateGridGate_productState d M j (QFTMatrix M) v

/-- The adjoint coordinate Fourier transform changes only the corresponding product-state factor
by the adjoint Fourier matrix. -/
theorem coordinateQFT_adjoint_productState (d M : ℕ) (j : Fin d)
    (v : Fin d → QState (Fin M)) :
    ApplyGate (coordinateQFT d M j)ᴴ (gridProductState v) =
      gridProductState (Function.update v j (ApplyGate (QFTMatrix M)ᴴ (v j))) := by
  change ApplyGate (coordinateGridGate d M j (QFTMatrix M))ᴴ _ = _
  rw [coordinateGridGate_adjoint, coordinateGridGate_productState]

/-- Running Fourier gates on a duplicate-free coordinate list transforms exactly those
product-state factors indexed by the list. -/
theorem run_coordinateQFT_list (d M : ℕ) (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    (js : List (Fin d)) (hjs : js.Nodup) (v : Fin d → QState (Fin M)) :
    Run O (js.map (fun j => Step.gate (coordinateQFT d M j))) (gridProductState v) =
      gridProductState (fun j => if j ∈ js then ApplyGate (QFTMatrix M) (v j) else v j) := by
  induction js generalizing v with
  | nil => simp
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hjs
    simp only [List.map_cons, run_gate, coordinateQFT_productState]
    rw [ih hjs]
    congr 1
    funext i
    by_cases hi : i ∈ js
    · have hij : i ≠ j := by intro e; subst i; exact hj hi
      simp [hi, hij]
    · by_cases hij : i = j
      · subst i; simp [hi]
      · simp [hi, hij]

/-- Running adjoint Fourier gates on a duplicate-free coordinate list applies the adjoint
Fourier matrix exactly to the listed product-state factors. -/
theorem run_coordinateQFT_adjoint_list (d M : ℕ) (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    (js : List (Fin d)) (hjs : js.Nodup) (v : Fin d → QState (Fin M)) :
    Run O (js.map (fun j => Step.gate (coordinateQFT d M j)ᴴ)) (gridProductState v) =
      gridProductState (fun j => if j ∈ js then ApplyGate (QFTMatrix M)ᴴ (v j) else v j) := by
  induction js generalizing v with
  | nil => simp
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hjs
    simp only [List.map_cons, run_gate, coordinateQFT_adjoint_productState]
    rw [ih hjs]
    congr 1
    funext i
    by_cases hi : i ∈ js
    · have hij : i ≠ j := by intro e; subst i; exact hj hi
      simp [hi, hij]
    · by_cases hij : i = j
      · subst i; simp [hi]
      · simp [hi, hij]

/-- Running the complete coordinate Fourier word transforms every factor of a grid product state
by `QFTMatrix M`. -/
theorem run_gradientQFTWord_product (d M : ℕ)
    (O : Matrix (GradientGrid d M) (GradientGrid d M) ℂ) (v : Fin d → QState (Fin M)) :
    Run O (gradientQFTWord d M) (gridProductState v) =
      gridProductState (fun j => ApplyGate (QFTMatrix M) (v j)) := by
  have hw : gradientQFTWord d M = (List.finRange d).map (fun j => Step.gate (coordinateQFT d M j)) :=
    List.ofFn_eq_map
  rw [hw, run_coordinateQFT_list d M O _ (List.nodup_finRange d)]
  simp

/-- The product of the coordinate basis states associated with `q` is the grid basis state `Ket
q`. -/
theorem gridProductState_ket {d M : ℕ} (q : GradientGrid d M) :
    gridProductState (fun j => Ket (q j)) = Ket q := by
  funext x
  by_cases h : x = q
  · subst x; simp [gridProductState, Ket]
  · have hex : ∃ i, x i ≠ q i := by
      by_contra hh
      apply h
      funext i
      exact not_ne_iff.mp (not_exists.mp hh i)
    obtain ⟨i, hi⟩ := hex
    have hz : (∏ j : Fin d, Ket (q j) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ket, hi])
    simpa [gridProductState, Ket, h] using! hz

/-- Circuit execution commutes with complex scalar multiplication of the input state. -/
private theorem gradient_run_smul {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (a : ℂ) (ψ : QState I) :
    Run O C (a • ψ) = a • Run O C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [Run, ApplyGate, Matrix.mulVec_smul, ih]

/-- Running a list of unitary gates followed by their adjoints in reverse order restores the
input state. -/
private theorem gradient_run_inverse {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (gs : List (Matrix I I ℂ))
    (hgs : ∀ U ∈ gs, U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    Run O (gs.reverse.map (fun U => Step.gate Uᴴ))
      (Run O (gs.map Step.gate) ψ) = ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons U gs ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, run_append,
      run_gate, run_nil]
    rw [ih (fun V hV => hgs V (List.mem_cons_of_mem U hV))]
    rw [← applyGate_mul]
    have hU := hgs U List.mem_cons_self
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    rw [hU, applyGate_one]

/-- The Fourier transform of a basis state has amplitude `1/sqrt M` times the character `exp
(2*pi*I*q*x/M)`. -/
private theorem gradient_qft_ket (M : ℕ) (q x : Fin M) :
    ApplyGate (QFTMatrix M) (Ket q) x =
      (Real.sqrt (M : ℝ) : ℂ)⁻¹ *
        Complex.exp (2*Real.pi*Complex.I*(((q.val : ℝ)*(x.val : ℝ))/(M : ℝ))) := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, qftMatrix_apply, primRoot_zpow_eq_exp]
  congr 2
  push_cast
  ring

/-- For an affine phase with coordinate slopes `g`, the actual gradient readout is the product
of `qpeKernel M (g j)` states multiplied by the constant global phase. -/
theorem gradient_offgrid_actual_readout (d M : ℕ) (hM : 0 < M)
    (g : Fin d → ℝ) (c : ℝ) :
    gradientReadout d M hM (fun x => c+∑ j : Fin d, g j*(x j).val) =
      Complex.exp (2*Real.pi*Complex.I*(c:ℂ)) •
        gridProductState (fun j => qpeKernel M (g j)) := by
  let O := gradientPhase d M (fun x => c+∑ j : Fin d, g j*(x j).val)
  have hp : ApplyGate O (Run O (gradientQFTWord d M) (Ket (gradientZero d M hM))) =
      Complex.exp (2*Real.pi*Complex.I*(c:ℂ)) •
        gridProductState (fun j => offGridPhase M (g j)) := by
    rw [← gridProductState_ket (gradientZero d M hM), run_gradientQFTWord_product]
    funext x
    unfold gridProductState
    simp_rw [gradient_qft_ket]
    simp only [O, gradientPhase, ApplyGate, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul, gradientZero, Nat.cast_zero, zero_mul, zero_div, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one, offGridPhase]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    have he : (2*Real.pi*Complex.I*(↑(c+∑ j : Fin d, g j*(x j).val)) : ℂ) =
        2*Real.pi*Complex.I*(c:ℂ) +
          ∑ j : Fin d, 2*Real.pi*Complex.I*(↑((x j).val*g j) : ℂ) := by
      push_cast
      simp only [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, Complex.exp_add]
    push_cast
    ring
  have hb : (gradientQFTWord d M).reverse.map (fun s => match s with
      | .gate U => .gate Uᴴ | .query => .query) =
      (List.finRange d).reverse.map (fun j => Step.gate (coordinateQFT d M j)ᴴ) := by
    rw [show gradientQFTWord d M = (List.finRange d).map
      (fun j => Step.gate (coordinateQFT d M j)) from List.ofFn_eq_map]
    simp only [← List.map_reverse, List.map_map]
    rfl
  change Run O (gradientWord d M) (Ket (gradientZero d M hM)) = _
  rw [gradientWord, run_append, run_append, run_query, run_nil, hp, gradient_run_smul, hb,
    run_coordinateQFT_adjoint_list d M O _
      (by simpa only [List.nodup_reverse] using! List.nodup_finRange d)]
  simp only [List.mem_reverse, List.mem_finRange, if_true]
  rfl

/-- Circular phase distance is symmetric in its two arguments. -/
theorem gradient_phaseDistance_comm (x y : ℝ) : phaseDistance x y = phaseDistance y x := by
  have h (a b : ℝ) : phaseDistance a b ≤ phaseDistance b a := by
    calc
      _ ≤ |a-b-((-⌊b-a+1/2⌋:ℤ):ℝ)| := phaseDistance_le_integer_distance a b _
      _ = phaseDistance b a := by
        unfold phaseDistance
        rw [Int.cast_neg]
        have he : a-b-(-(⌊b-a+1/2⌋:ℤ):ℝ) = -(b-a-(⌊b-a+1/2⌋:ℤ)) := by ring
        rw [he, abs_neg]
  exact le_antisymm (h x y) (h y x)

/-- For an affine phase, the probability that every coordinate lies in its circular window
factors into the corresponding one-coordinate kernel probabilities. -/
theorem gradient_offgrid_window_product (d M : ℕ) (hM : 0 < M)
    (g : Fin d → ℝ) (c w : ℝ) :
    MeasureProb (gradientReadout d M hM (fun x => c+∑ j : Fin d, g j*(x j).val))
      (Finset.univ.filter (fun z => ∀ j : Fin d,
        phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w)) =
      ∏ j : Fin d, ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        phaseDistance (g j) (y.val/(M:ℝ)) ≤ w), ‖qpeKernel M (g j) y‖^2 := by
  rw [gradient_offgrid_actual_readout]
  let t := fun j : Fin d => Finset.univ.filter (fun y : Fin M =>
    phaseDistance (g j) (y.val/(M:ℝ)) ≤ w)
  have he : Finset.univ.filter (fun z : GradientGrid d M => ∀ j : Fin d,
      phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w) = Fintype.piFinset t := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, t]
    simp_rw [gradient_phaseDistance_comm]
  rw [he]
  simp only [MeasureProb, BornProb, Pi.smul_apply, smul_eq_mul, norm_mul,
    norm_exp_two_pi_I, one_mul, gridProductState, norm_prod, ← Finset.prod_pow]
  exact (Finset.prod_univ_sum t (fun j y => ‖qpeKernel M (g j) y‖^2)).symm

/-- An affine phase whose coordinate frequencies lie exactly on the grid yields `Ket q` up to
the constant global phase, giving the exact finite-grid readout case of
[Jordan2005Gradient]. -/
theorem gradient_affine_actual_exact_readout (d M : ℕ) (hM : 0 < M)
    (q : GradientGrid d M) (c : ℝ) :
    gradientReadout d M hM (fun x => c+∑ j : Fin d,(q j).val*(x j).val/(M:ℝ)) =
      Complex.exp (2*Real.pi*Complex.I*(c:ℂ)) • Ket q := by
  let O := gradientPhase d M (fun x => c+∑ j : Fin d,(q j).val*(x j).val/(M:ℝ))
  have hp : ApplyGate O (Run O (gradientQFTWord d M) (Ket (gradientZero d M hM))) =
      Complex.exp (2*Real.pi*Complex.I*(c:ℂ)) • Run O (gradientQFTWord d M) (Ket q) := by
    rw [← gridProductState_ket (gradientZero d M hM), ← gridProductState_ket q,
      run_gradientQFTWord_product, run_gradientQFTWord_product]
    funext x
    unfold gridProductState
    simp_rw [gradient_qft_ket]
    simp only [O, gradientPhase, ApplyGate, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul]
    simp only [gradientZero, Nat.cast_zero, zero_mul, zero_div, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    have he : (2*Real.pi*Complex.I*(↑(c + ∑ j : Fin d, ↑(q j).val * ↑(x j).val / (M:ℝ))) : ℂ) =
        2*Real.pi*Complex.I*(c:ℂ) +
          ∑ j : Fin d, 2*Real.pi*Complex.I*(↑((↑(q j).val*↑(x j).val)/(M:ℝ)) : ℂ) := by
      push_cast
      simp only [mul_add, Finset.mul_sum]
    rw [he, Complex.exp_add]
    push_cast
    ring
  let gs := List.ofFn (coordinateQFT d M)
  have hf : gradientQFTWord d M = gs.map Step.gate := by
    simp [gradientQFTWord, gs, List.map_ofFn, Function.comp_def]
  have hb : (gradientQFTWord d M).reverse.map (fun s => match s with
      | .gate U => .gate Uᴴ | .query => .query) = gs.reverse.map (fun U => Step.gate Uᴴ) := by
    rw [hf]
    simp only [← List.map_reverse, List.map_map]
    rfl
  change Run O (gradientWord d M) (Ket (gradientZero d M hM)) = _
  rw [gradientWord, run_append, run_append, run_query, run_nil, hp, gradient_run_smul, hb, hf]
  rw [gradient_run_inverse]
  intro U hU
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hU
  exact coordinateQFT_unitary d M j hM

/-- For `M ≥ 2` and window width `w ≥ 1/64`, the kernel probability outside the circular window
is at most `16/(M*w)`. -/
theorem gradient_phase_kernel_tail_wide (M : ℕ) (φ w : ℝ) (hM : 2 ≤ M)
    (hw : 0 < w) (hwide : 1/64 ≤ w) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
      w < phaseDistance φ ((y.val : ℝ)/(M : ℝ))), ‖qpeKernel M φ y‖^2) ≤
      16/((M : ℝ)*w) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  by_cases hhalf : w ≤ 1/2
  · refine (uniform_phase_kernel_derived_tail M φ w hM hw hhalf).trans ?_
    apply (div_le_div_iff₀ (by positivity : 0 < 4*(M:ℝ)*w^2)
      (by positivity : 0 < (M:ℝ)*w)).mpr
    nlinarith [mul_pos hMr hw]
  · have hs : Finset.univ.filter (fun y : Fin M =>
        w < phaseDistance φ ((y.val : ℝ)/(M : ℝ))) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      have hd := uniform_phaseDistance_le_half φ ((y.val : ℝ)/(M : ℝ))
      linarith
    rw [hs, Finset.sum_empty]
    positivity

/-- For positive `M` and `w` with `M*w ≤ 16`, the kernel probability outside the circular window
is at most `16/(M*w)`. -/
theorem gradient_phase_kernel_tail_small_budget (M : ℕ) (φ w : ℝ) (hM : 0 < M)
    (hw : 0 < w) (hbudget : (M : ℝ)*w ≤ 16) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
      w < phaseDistance φ ((y.val : ℝ)/(M : ℝ))), ‖qpeKernel M φ y‖^2) ≤
      16/((M : ℝ)*w) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have ht : (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
      w < phaseDistance φ ((y.val : ℝ)/(M : ℝ))), ‖qpeKernel M φ y‖^2) ≤ 1 := by
    calc
      _ ≤ ∑ y : Fin M, ‖qpeKernel M φ y‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun y _ _ => sq_nonneg _)
      _ = 1 := uniform_qpeKernel_normalized M φ hM
  exact ht.trans ((le_div_iff₀ (mul_pos hMr hw)).mpr (by simpa using! hbudget))

/-- If bad grid labels have injective integer distance bins within one of their scaled phase
distances and `M*w > 16`, their total kernel mass is at most the reciprocal of `floor
(M*w/2)`. -/
private theorem gradient_kernel_tail_injective (M : ℕ) (φ w : ℝ) (hM : 0 < M)
    (hw : 0 < w) (hbudget : 16 < (M:ℝ)*w) (s : Finset (Fin M)) (p : Fin M → ℕ)
    (hinj : Set.InjOn p s)
    (hbad : ∀ y ∈ s, w < phaseDistance φ ((y.val:ℝ)/(M:ℝ)))
    (hdist : ∀ y ∈ s, (p y:ℝ) ≤ (M:ℝ)*phaseDistance φ ((y.val:ℝ)/(M:ℝ)) ∧
      (M:ℝ)*phaseDistance φ ((y.val:ℝ)/(M:ℝ)) ≤ (p y:ℝ)+1) :
    (∑ y ∈ s, ‖qpeKernel M φ y‖^2) ≤ (⌊(M:ℝ)*w/2⌋₊:ℝ)⁻¹ := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  let L := ⌊(M:ℝ)*w/2⌋₊
  let N := max L (s.sup p)
  have hL : L ≠ 0 := by
    have hfloor := Nat.lt_floor_add_one ((M:ℝ)*w/2)
    intro heq
    change (M:ℝ)*w/2 < (L:ℝ)+1 at hfloor
    rw [heq, Nat.cast_zero, zero_add] at hfloor
    linarith
  have hp (y : Fin M) (hy : y ∈ s) : L < p y := by
    have hfloor := Nat.floor_le (show 0 ≤ (M:ℝ)*w/2 by positivity)
    have hd := (hdist y hy).2
    have hb := mul_lt_mul_of_pos_left (hbad y hy) hMr
    have hpr : (L:ℝ) < (p y:ℝ) := by dsimp [L]; linarith
    exact_mod_cast hpr
  have hkernel (y : Fin M) (hy : y ∈ s) : ‖qpeKernel M φ y‖^2 ≤ ((p y:ℝ)^2)⁻¹ := by
    have hp0 : 0 < (p y:ℝ) := by exact_mod_cast (show 0 < p y by have := hp y hy; omega)
    have hwindow : p y/(2*(M:ℝ)) < phaseDistance φ ((y.val:ℝ)/(M:ℝ)) := by
      apply (div_lt_iff₀ (by positivity : 0 < 2*(M:ℝ))).mpr
      have hd := (hdist y hy).1
      nlinarith
    have hb := uniform_qpeKernel_bad_label M φ (p y/(2*(M:ℝ))) y hM
      (by positivity) hwindow
    have he : 1/(2*(M:ℝ)*(p y/(2*(M:ℝ)))) = (p y:ℝ)⁻¹ := by field_simp
    rw [he] at hb
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [inv_pow] using! hs
  calc
    _ ≤ ∑ y ∈ s, ((p y:ℝ)^2)⁻¹ := Finset.sum_le_sum hkernel
    _ = ∑ k ∈ s.image p, ((k:ℝ)^2)⁻¹ :=
      (Finset.sum_image (f := fun k : ℕ => ((k:ℝ)^2)⁻¹) hinj).symm
    _ ≤ ∑ k ∈ Finset.Ioc L N, ((k:ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_Ioc.mpr ⟨hp y hy, (Finset.le_sup hy).trans (le_max_right _ _)⟩
      · intro k _ _; positivity
    _ ≤ (L:ℝ)⁻¹-(N:ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hL (le_max_left _ _)
    _ ≤ (L:ℝ)⁻¹ := sub_le_self _ (by positivity)

/-- For positive grid size and window width, the kernel probability outside the circular window
is at most `16/(M*w)`. -/
theorem gradient_phase_kernel_tail (M : ℕ) (φ w : ℝ) (hM : 0 < M) (hw : 0 < w) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
      w < phaseDistance φ ((y.val:ℝ)/(M:ℝ))), ‖qpeKernel M φ y‖^2) ≤
      16/((M:ℝ)*w) := by
  by_cases hbudget : (M:ℝ)*w ≤ 16
  · exact gradient_phase_kernel_tail_small_budget M φ w hM hw hbudget
  have hbudget' : 16 < (M:ℝ)*w := lt_of_not_ge hbudget
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  let k (y : Fin M) : ℤ := y.val + (M:ℤ)*⌊φ-(y.val:ℝ)/(M:ℝ)+1/2⌋
  have hkmod (y : Fin M) : k y % (M:ℤ) = (y.val:ℤ) := by
    dsimp [k]
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by exact_mod_cast y.isLt)]
  have hkinj : Function.Injective k := by
    intro y z he
    apply Fin.ext
    have hm := congrArg (fun a : ℤ => a % (M:ℤ)) he
    change k y % (M:ℤ) = k z % (M:ℤ) at hm
    rw [hkmod, hkmod] at hm
    exact_mod_cast hm
  let n (y : Fin M) : ℤ := k y-⌊(M:ℝ)*φ⌋
  let δ : ℝ := (M:ℝ)*φ-(⌊(M:ℝ)*φ⌋:ℤ)
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Int.floor_le _)
  have hδ1 : δ < 1 := Int.fract_lt_one _
  have he (y : Fin M) : (M:ℝ)*phaseDistance φ ((y.val:ℝ)/(M:ℝ)) = |δ-(n y:ℝ)| := by
    change (M:ℝ)*|φ-(y.val:ℝ)/(M:ℝ)-(⌊φ-(y.val:ℝ)/(M:ℝ)+1/2⌋:ℤ)| = _
    rw [show (M:ℝ)*|φ-(y.val:ℝ)/(M:ℝ)-(⌊φ-(y.val:ℝ)/(M:ℝ)+1/2⌋:ℤ)| =
      |(M:ℝ)*(φ-(y.val:ℝ)/(M:ℝ)-(⌊φ-(y.val:ℝ)/(M:ℝ)+1/2⌋:ℤ))| by
      rw [abs_mul, abs_of_pos hMr]]
    congr 1
    dsimp only [δ, n, k]
    push_cast
    have hdiv : (M:ℝ)*((y.val:ℝ)/(M:ℝ)) = (y.val:ℝ) := by field_simp
    rw [mul_sub, mul_sub, hdiv]
    ring
  let s := Finset.univ.filter (fun y : Fin M => w < phaseDistance φ ((y.val:ℝ)/(M:ℝ)))
  let p₀ (y : Fin M) := (-n y).toNat
  let p₁ (y : Fin M) := (n y-1).toNat
  have hpc₀ (y : Fin M) (hy : n y ≤ 0) : (p₀ y:ℝ) = -(n y:ℝ) := by
    have hc := Int.toNat_of_nonneg (show 0 ≤ -n y by omega)
    exact_mod_cast hc
  have hpc₁ (y : Fin M) (hy : ¬n y ≤ 0) : (p₁ y:ℝ) = (n y:ℝ)-1 := by
    have hc := Int.toNat_of_nonneg (show 0 ≤ n y-1 by omega)
    exact_mod_cast hc
  have htail₀ := gradient_kernel_tail_injective M φ w hM hw hbudget'
    (s.filter (fun y => n y ≤ 0)) p₀
    (by
      intro y hy z hz hp
      apply hkinj
      have hy' := (Finset.mem_filter.mp hy).2
      have hz' := (Finset.mem_filter.mp hz).2
      have hpr := congrArg (fun a : ℕ => (a:ℝ)) hp
      change (p₀ y:ℝ) = (p₀ z:ℝ) at hpr
      rw [hpc₀ y hy', hpc₀ z hz'] at hpr
      have hn : n y = n z := by exact_mod_cast (neg_injective hpr)
      dsimp [n] at hn
      omega)
    (fun y hy => (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2)
    (by
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      rw [he, hpc₀ y hy', abs_of_nonneg (by
        have hn : (n y:ℝ) ≤ 0 := by exact_mod_cast hy'
        linarith)]
      constructor <;> linarith)
  have htail₁ := gradient_kernel_tail_injective M φ w hM hw hbudget'
    (s.filter (fun y => ¬n y ≤ 0)) p₁
    (by
      intro y hy z hz hp
      apply hkinj
      have hy' := (Finset.mem_filter.mp hy).2
      have hz' := (Finset.mem_filter.mp hz).2
      have hpr := congrArg (fun a : ℕ => (a:ℝ)) hp
      change (p₁ y:ℝ) = (p₁ z:ℝ) at hpr
      rw [hpc₁ y hy', hpc₁ z hz'] at hpr
      have hn : n y = n z := by exact_mod_cast (show (n y:ℝ) = (n z:ℝ) by linarith)
      dsimp [n] at hn
      omega)
    (fun y hy => (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2)
    (by
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      rw [he, hpc₁ y hy', abs_of_nonpos (by
        have hn : (1:ℝ) ≤ (n y:ℝ) := by exact_mod_cast (show 1 ≤ n y by omega)
        linarith)]
      constructor <;> linarith)
  have hsum := Finset.sum_filter_add_sum_filter_not s (fun y => n y ≤ 0)
    (fun y => ‖qpeKernel M φ y‖^2)
  have hL := Nat.lt_floor_add_one ((M:ℝ)*w/2)
  have hLpos : 0 < (⌊(M:ℝ)*w/2⌋₊:ℝ) := by linarith
  calc
    _ = _ + _ := hsum.symm
    _ ≤ (⌊(M:ℝ)*w/2⌋₊:ℝ)⁻¹ + (⌊(M:ℝ)*w/2⌋₊:ℝ)⁻¹ := add_le_add htail₀ htail₁
    _ = 2/(⌊(M:ℝ)*w/2⌋₊:ℝ) := by ring
    _ ≤ 16/((M:ℝ)*w) := by
      apply (div_le_div_iff₀ hLpos (mul_pos hMr hw)).mpr
      linarith

/-- A finite product of numbers in `[0, 1]` is at least one minus the sum of their deficits from
one. -/
private theorem gradient_product_lower {I : Type} [DecidableEq I]
    (p : I → ℝ) (s : Finset I) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    1-(∑ i ∈ s, (1-p i)) ≤ ∏ i ∈ s, p i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h0 := hp0 i (Finset.mem_insert_self _ _)
    have h1 := hp1 i (Finset.mem_insert_self _ _)
    have hih := ih (fun j hj => hp0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => hp1 j (Finset.mem_insert_of_mem hj))
    have hs0 : 0 ≤ ∑ j ∈ s, (1-p j) := Finset.sum_nonneg
      (fun j hj => sub_nonneg.mpr (hp1 j (Finset.mem_insert_of_mem hj)))
    have hm := mul_le_mul_of_nonneg_left hih h0
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) hs0]

/-- For an affine phase, `M ≥ 2`, and positive `w`, the joint circular window has probability at
least `1 - 16*d/(M*w)`. -/
theorem gradient_offgrid_joint_window (d M : ℕ) (hM : 0 < M)
    (g : Fin d → ℝ) (c w : ℝ) (_hM2 : 2 ≤ M) (hw : 0 < w) :
    MeasureProb (gradientReadout d M hM (fun x => c+∑ j : Fin d, g j*(x j).val))
      (Finset.univ.filter (fun z => ∀ j : Fin d,
        phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w)) ≥ 1-16*(d:ℝ)/((M:ℝ)*w) := by
  rw [gradient_offgrid_window_product]
  let p := fun j : Fin d => ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
    phaseDistance (g j) (y.val/(M:ℝ)) ≤ w), ‖qpeKernel M (g j) y‖^2
  have hp0 (j : Fin d) : 0 ≤ p j := Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have hsplit (j : Fin d) : p j +
      (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        w < phaseDistance (g j) (y.val/(M:ℝ))), ‖qpeKernel M (g j) y‖^2) = 1 := by
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun y : Fin M => phaseDistance (g j) (y.val/(M:ℝ)) ≤ w)
      (fun y => ‖qpeKernel M (g j) y‖^2)
    simpa only [not_le, uniform_qpeKernel_normalized M (g j) hM] using! hs
  have hp1 (j : Fin d) : p j ≤ 1 := by
    have hn : 0 ≤ (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        w < phaseDistance (g j) (y.val/(M:ℝ))), ‖qpeKernel M (g j) y‖^2) :=
      Finset.sum_nonneg (fun y _ => sq_nonneg _)
    linarith [hsplit j]
  have herr (j : Fin d) : 1-p j ≤ 16/((M:ℝ)*w) := by
    linarith [hsplit j, gradient_phase_kernel_tail M (g j) w hM hw]
  have hsum : (∑ j : Fin d, (1-p j)) ≤ 16*(d:ℝ)/((M:ℝ)*w) := by
    calc
      _ ≤ ∑ _j : Fin d, 16/((M:ℝ)*w) := Finset.sum_le_sum (fun j _ => herr j)
      _ = _ := by simp; ring
  exact (sub_le_sub_left hsum 1).trans
    (gradient_product_lower p Finset.univ (fun j _ => hp0 j) (fun j _ => hp1 j))

/-- Every real-valued grid phase defines a unitary diagonal matrix. -/
theorem gradientPhase_unitary (d M : ℕ) (φ : GradientGrid d M → ℝ) :
    gradientPhase d M φ ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, gradientPhase,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext z
  change (starRingEnd ℂ) (Complex.exp _) * Complex.exp _ = 1
  rw [Complex.conj_mul']
  rw [norm_exp_two_pi_I]
  norm_num

/-- A uniform pointwise phase error at most nonnegative `B` gives operator norm error at most
`2*pi*B` between the diagonal phase matrices. -/
theorem gradientPhase_sub_norm_le (d M : ℕ) (φ ψ : GradientGrid d M → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (herror : ∀ z, |φ z - ψ z| ≤ B) :
    ‖gradientPhase d M φ - gradientPhase d M ψ‖ ≤ 2*Real.pi*B := by
  rw [gradientPhase, gradientPhase, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal,
    pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*Real.pi*B)]
  intro z
  have he (t : ℝ) : (2*Real.pi*Complex.I*(t:ℂ) : ℂ) =
      ((2*Real.pi*t:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he, he]
  calc
    _ ≤ |2*Real.pi*φ z - 2*Real.pi*ψ z| := norm_exp_mul_I_sub_le _ _
    _ = 2*Real.pi*|φ z-ψ z| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
    _ ≤ 2*Real.pi*B := mul_le_mul_of_nonneg_left (herror z) (by positivity)

/-- A uniform phase error at most nonnegative `B` changes the probability of any
gradient-readout event by at most `4*pi*B`. -/
theorem gradient_actual_phase_event_error (d M : ℕ) (hM : 0 < M)
    (φ ψ : GradientGrid d M → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ z, |φ z-ψ z| ≤ B) (S : Finset (GradientGrid d M)) :
    |MeasureProb (gradientReadout d M hM φ) S -
      MeasureProb (gradientReadout d M hM ψ) S| ≤ 4*Real.pi*B := by
  obtain ⟨hC, hq, _⟩ := gradient_coordinate_qft_word_unitarity d M hM
  have h := measureProb_run_sub_le_queryCount_of_le (gradientPhase d M φ)
    (gradientPhase d M ψ) (gradientWord d M) (Ket (gradientZero d M hM)) S
    (2*Real.pi*B) (gradientPhase_unitary d M φ) (gradientPhase_unitary d M ψ)
    hC (normalized_ket _) (gradientPhase_sub_norm_le d M φ ψ B hB herror)
  rw [hq] at h
  simpa only [Nat.cast_one, mul_one,
    show 2*(2*Real.pi*B) = 4*Real.pi*B by ring] using! h

/-- If the phase is uniformly within nonnegative `B` of an affine target, its joint circular
gradient window has probability at least `1 - 16*d/(M*w) - 4*pi*B` for `M ≥ 2` and positive
`w`. -/
theorem gradient_actual_phase_error_transport (d M : ℕ) (hM : 0 < M)
    (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
    (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
    (herror : ∀ x, |φ x-(c+∑ j : Fin d, g j*(x j).val)| ≤ B) :
    MeasureProb (gradientReadout d M hM φ)
      (Finset.univ.filter (fun z => ∀ j : Fin d,
        phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w)) ≥
        1-16*(d:ℝ)/((M:ℝ)*w)-4*Real.pi*B := by
  have he := gradient_actual_phase_event_error d M hM φ
    (fun x => c+∑ j : Fin d, g j*(x j).val) B hB herror
    (Finset.univ.filter (fun z => ∀ j : Fin d,
      phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w))
  have hi := gradient_offgrid_joint_window d M hM g c w hM2 hw
  linarith [(abs_le.mp he).1]

/-- When `|g| ≤ 1/4` and `w ≤ 1/8`, circular window membership implies signed decoding error
`|signedGridValue M z - g| ≤ w`. -/
theorem gradient_signed_decode_window (M : ℕ) (hM : 0 < M) (z : Fin M)
    (g w : ℝ) (hg : |g| ≤ 1/4) (hw : w ≤ 1/8)
    (hgood : phaseDistance ((z.val:ℝ)/(M:ℝ)) g ≤ w) :
    |signedGridValue M z-g| ≤ w := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  let a : ℝ := z.val/(M:ℝ)
  let n : ℤ := ⌊a-g+1/2⌋
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hMr).mpr
    exact_mod_cast z.isLt
  have hg' := abs_le.mp hg
  have hnlo := Int.floor_le (a-g+1/2)
  have hnhi := Int.lt_floor_add_one (a-g+1/2)
  change |a-g-(n:ℝ)| ≤ w at hgood
  have hgood' := abs_le.mp hgood
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by
    have hn : (-1:ℝ) < (n:ℝ) := by dsimp [n]; linarith
    exact_mod_cast hn
  have hn1 : (n:ℝ) ≤ 1 := by
    have hn : (n:ℝ) < 2 := by dsimp [n]; linarith
    have hi : n < 2 := by exact_mod_cast hn
    exact_mod_cast (show n ≤ 1 by omega)
  have hn : n = 0 ∨ n = 1 := by
    have h0 : 0 ≤ n := by exact_mod_cast hn0
    have h1 : n ≤ 1 := by exact_mod_cast hn1
    omega
  unfold signedGridValue
  split_ifs with hz
  · have ha : a ≤ 1/2 := by
      apply (div_le_iff₀ hMr).mpr
      have hz' : 2*(z.val:ℝ) ≤ (M:ℝ) := by exact_mod_cast hz
      linarith
    rcases hn with hn | hn
    · simpa [hn, a] using! hgood
    · rw [hn] at hgood'
      norm_num at hgood'
      linarith
  · have ha : 1/2 < a := by
      dsimp [a]
      apply (lt_div_iff₀ hMr).mpr
      have hz' : (M:ℝ) < 2*(z.val:ℝ) := by exact_mod_cast (show M < 2*z.val by omega)
      linarith
    rcases hn with hn | hn
    · rw [hn] at hgood'
      norm_num at hgood'
      linarith
    · simpa [hn, a, sub_sub, add_comm] using! hgood

end Qatlib.Concepts.SignalPrimitive.GridGradient
