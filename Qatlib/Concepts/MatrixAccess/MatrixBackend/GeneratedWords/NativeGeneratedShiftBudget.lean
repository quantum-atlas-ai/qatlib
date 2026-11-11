/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftCoefficientPrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannLogPrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
/-! Actual bit-length precision and cutoff of direct_precision_budget.
Both mathematical acceptance inequalities are derived from the generated
coefficient rate, then used in the same original-oracle logarithmic-tail
consumer. True separation and a condition cap remain inputs. The precision
bit-length bound does not certify all classical or primitive synthesis costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped Matrix.Norms.L2Operator

/-- Integer quantity actually used by direct_precision_budget. -/
def nativeShiftGapFactor (K : ℕ) : ℕ := 2*K^2+4*K^3

/-- Construction for native Shift Budget Precision in the native generated shift budget model. -/
def nativeShiftBudgetPrecision (K k : ℕ) : ℕ :=
  k+Nat.size (2*nativeShiftGapFactor K-1)

/-- Construction for native Shift Budget Cutoff in the native generated shift budget model. -/
def nativeShiftBudgetCutoff (K k : ℕ) : ℕ := K*K*(k+Nat.size (K-1)+2)

/-- The finite construction in `NativeGeneratedShiftBudget` satisfies `size_pred_eq_clog` under the displayed hypotheses. -/
private theorem size_pred_eq_clog (n : ℕ) (hn : 0<n) : Nat.size (n-1)=Nat.clog 2 n := by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    have hh := Nat.le_pow_clog (by decide : 1<2) n
    omega
  · apply Nat.clog_le_of_le_pow
    have hh := Nat.lt_size_self (n-1)
    omega

/-- The finite construction in `NativeGeneratedShiftBudget` satisfies `nativeShiftBudgetCutoff_eq` under the displayed hypotheses. -/
theorem nativeShiftBudgetCutoff_eq (K k : ℕ) (hK : 2 ≤ K) :
    nativeShiftBudgetCutoff K k=K*K*(k+Nat.clog 2 K+2) := by
  rw [nativeShiftBudgetCutoff,size_pred_eq_clog K (by omega)]

/-- The estimate `nativeShiftBudgetPrecision_eq` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeShiftBudgetPrecision_eq (K k : ℕ) (hK : 2 ≤ K) :
    nativeShiftBudgetPrecision K k=k+Nat.clog 2 (2*nativeShiftGapFactor K) := by
  rw [nativeShiftBudgetPrecision,size_pred_eq_clog _ (by unfold nativeShiftGapFactor; positivity)]

/-- The finite construction in `NativeGeneratedShiftBudget` satisfies `nativeShiftGapFactor_real` under the displayed hypotheses. -/
private theorem nativeShiftGapFactor_real (K : ℕ) :
    (nativeShiftGapFactor K : ℝ)=2*(K : ℝ)^2+4*(K : ℝ)^3 := by
  simp [nativeShiftGapFactor]

/-- The finite construction in `NativeGeneratedShiftBudget` satisfies `budget_power_lower` under the displayed hypotheses. -/
private theorem budget_power_lower (K k : ℕ) (hK : 2 ≤ K) :
    2*(2*(K : ℝ)^2+4*(K : ℝ)^3)*(2 : ℝ)^k ≤
      (2 : ℝ)^(nativeShiftBudgetPrecision K k) := by
  have hC : 0<2*nativeShiftGapFactor K := by unfold nativeShiftGapFactor; positivity
  have hsize := Nat.lt_size_self (2*nativeShiftGapFactor K-1)
  have hpow : 2*nativeShiftGapFactor K ≤ 2^Nat.size (2*nativeShiftGapFactor K-1) := by omega
  have hpowR : (2 : ℝ)*(nativeShiftGapFactor K : ℝ) ≤
      (2 : ℝ)^Nat.size (2*nativeShiftGapFactor K-1) := by exact_mod_cast hpow
  rw [nativeShiftGapFactor_real] at hpowR
  rw [nativeShiftBudgetPrecision,pow_add]
  calc
    _ ≤ (2 : ℝ)^Nat.size (2*nativeShiftGapFactor K-1)*(2 : ℝ)^k :=
      mul_le_mul_of_nonneg_right hpowR (by positivity)
    _ = _ := mul_comm _ _

/-- Both inequalities tested by the direct budget follow for any value
bounded by the same actual precision, not from a successful packet. -/
private theorem budget_of_precision (K k : ℕ) (hK : 2 ≤ K) (δ : ℝ)
    (hδ : δ ≤ 1/(2 : ℝ)^(nativeShiftBudgetPrecision K k)) :
    δ ≤ 1/(4*(K : ℝ)^2) ∧
      (2*(K : ℝ)^2+4*(K : ℝ)^3)*δ+((2 : ℝ)⁻¹)^(k+2) ≤ ((2 : ℝ)⁻¹)^k := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hC : (0 : ℝ)<2*(K : ℝ)^2+4*(K : ℝ)^3 := by positivity
  have hpow := budget_power_lower K k hK
  have hk : (1 : ℝ) ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hp : (0 : ℝ)<(2 : ℝ)^(nativeShiftBudgetPrecision K k) := by positivity
  have hscale : 4*(K : ℝ)^2 ≤ (2 : ℝ)^(nativeShiftBudgetPrecision K k) := by
    have hc : 4*(K : ℝ)^2 ≤ 2*(2*(K : ℝ)^2+4*(K : ℝ)^3) := by
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ K by positivity) 3]
    have hh := mul_le_mul_of_nonneg_left hk
      (show (0 : ℝ) ≤ 2*(2*(K : ℝ)^2+4*(K : ℝ)^3) by positivity)
    nlinarith
  constructor
  · exact hδ.trans (one_div_le_one_div_of_le (by positivity) hscale)
  · have hcδ : (2*(K : ℝ)^2+4*(K : ℝ)^3)*δ ≤ 1/(2*(2 : ℝ)^k) := by
      calc
        _ ≤ (2*(K : ℝ)^2+4*(K : ℝ)^3)*(1/(2 : ℝ)^(nativeShiftBudgetPrecision K k)) :=
          mul_le_mul_of_nonneg_left hδ hC.le
        _ = (2*(K : ℝ)^2+4*(K : ℝ)^3)/(2 : ℝ)^(nativeShiftBudgetPrecision K k) := by ring
        _ ≤ _ := (div_le_div_iff₀ hp (by positivity)).mpr (by nlinarith)
    have htail : ((2 : ℝ)⁻¹)^(k+2)=1/(4*(2 : ℝ)^k) := by
      rw [pow_add,inv_pow]
      norm_num
    have he : ((2 : ℝ)⁻¹)^k=1/(2 : ℝ)^k := by rw [inv_pow,one_div]
    rw [htail,he]
    calc
      _ ≤ 1/(2*(2 : ℝ)^k)+1/(4*(2 : ℝ)^k) := add_le_add hcδ le_rfl
      _ ≤ _ := by
        have ht : (0 : ℝ)<(2 : ℝ)^k := by positivity
        field_simp
        norm_num

/-- Same generated four-coordinate residual passes the two mathematical
checks of direct_precision_budget for every original-domain input. -/
theorem nativeShift_generated_coordinate_budget (K k : ℕ) (hK : 2 ≤ K)
    (α B x y : ℚ) (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    let δ := nativeShiftCoordinateResidual α B x y (nativeShiftBudgetPrecision K k)
    δ ≤ 1/(4*(K : ℝ)^2) ∧
      (2*(K : ℝ)^2+4*(K : ℝ)^3)*δ+((2 : ℝ)⁻¹)^(k+2) ≤ ((2 : ℝ)⁻¹)^k :=
  budget_of_precision K k hK _ (nativeShiftCoordinateResidual_le α B x y _ hα hB hz)

/-- The finite construction in `NativeGeneratedShiftBudget` satisfies `nativeShift_generated_coefficient_budget` under the displayed hypotheses. -/
private theorem nativeShift_generated_coefficient_budget (K k : ℕ) (hK : 2 ≤ K)
    (α B x y : ℚ) (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    let p := nativeShiftBudgetPrecision K k
    let δ := nativeCoefficientError (nativeShiftCircles α B x y p) (nativePhaseCircle x y p)
      (nativeShiftSlack α B x y) α B (gaussianRatComplex (x,y))
    δ ≤ 1/(4*(K : ℝ)^2) ∧
      (2*(K : ℝ)^2+4*(K : ℝ)^3)*δ+((2 : ℝ)⁻¹)^(k+2) ≤ ((2 : ℝ)⁻¹)^k :=
  budget_of_precision K k hK _ (nativeShiftCoefficient_error α B x y _ hα hB hz)


/-- Explicit precision growth in the integer input bit length; this is not
an end-to-end arithmetic bit-time or primitive-gate synthesis theorem. -/
theorem nativeShiftBudgetPrecision_growth (K k : ℕ) (hK : 2 ≤ K) :
    nativeShiftBudgetPrecision K k ≤ k+3*Nat.size K+4 := by
  have hbase : K ≤ 2^Nat.size K := (Nat.lt_size_self K).le
  have hcube : K^3 ≤ (2^Nat.size K)^3 := Nat.pow_le_pow_left hbase 3
  have hsq : K^2 ≤ K^3 := Nat.pow_le_pow_right (by omega : 1 ≤ K) (by decide : 2 ≤ 3)
  have hC : 2*nativeShiftGapFactor K ≤ 12*K^3 := by
    unfold nativeShiftGapFactor
    nlinarith
  have hlim : 2*nativeShiftGapFactor K < 16*(2^Nat.size K)^3 := by
    calc
      _ ≤ 12*K^3 := hC
      _ ≤ 12*(2^Nat.size K)^3 := Nat.mul_le_mul_left 12 hcube
      _ < _ := Nat.mul_lt_mul_of_pos_right (by decide : 12<16) (by positivity)
  have hpow : 16*(2^Nat.size K)^3=2^(3*Nat.size K+4) := by
    rw [show 3*Nat.size K+4=Nat.size K*3+4 by omega,pow_add,pow_mul]
    norm_num
    ring
  have hs : Nat.size (2*nativeShiftGapFactor K-1) ≤ 3*Nat.size K+4 :=
    Nat.size_le.mpr ((Nat.sub_le _ _).trans_lt (hlim.trans_eq hpow))
  unfold nativeShiftBudgetPrecision
  omega

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The actual source precision and cutoff generate one original-query
resolvent block encoding. Only the original rational input domain, exact
input encoding, true separation and a certified condition cap remain. -/
theorem native_generated_neumann_log_precision
    (K k : ℕ) (hK : 2 ≤ K) (α B x y : ℚ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2)
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (r : ℝ) (hbe : BlockEncoding A U F F (α : ℝ) 0) (hr : 0<r)
    (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖gaussianRatComplex (x,y)-w‖)
    (hcondition : jointResolventCondition (B : ℝ) r ≤ (K : ℝ)) :
    let p := nativeShiftBudgetPrecision K k
    let ps := nativeShiftCircles α B x y p
    let q := nativePhaseCircle x y p
    let slack := nativeShiftSlack α B x y
    let b := nativeShiftBudgetCutoff K k
    ∃ hb : 0<b,
      WellFormedAdjointCircuit (nativeOriginalNeumannWord b hb F ps q slack) ∧
      BlockEncoding (matrixResolvent A (gaussianRatComplex (x,y)))
        (evaluate (uniformNeumannOracle b (nativeDataQuery U))
          (nativeOriginalNeumannWord b hb F ps q slack))
        (uniformNeumannFrame b hb (nativeDataFrame F))
        (uniformNeumannFrame b hb (nativeDataFrame F))
        ((b : ℝ)/(B : ℝ)) (((2 : ℝ)⁻¹)^k/(B : ℝ)) ∧
      adjointQueryCount (nativeOriginalNeumannWord b hb F ps q slack)=2*b-1 ∧
      adjointGateCount (nativeOriginalNeumannWord b hb F ps q slack)=
        2*b+(2*b-1)*(436+(if slack then 1 else 0)) := by
  let p := nativeShiftBudgetPrecision K k
  let ps := nativeShiftCircles α B x y p
  let q := nativePhaseCircle x y p
  let slack := nativeShiftSlack α B x y
  have hB0 : (0 : ℝ)<B := by exact_mod_cast hα.trans_le hB
  have hd := nativeShift_generated_coefficient_budget K k hK α B x y hα hB hz
  have hw := native_original_neumann_log_precision K k hK ps q slack A U F (α : ℝ) (B : ℝ) r
    (gaussianRatComplex (x,y)) hbe hB0 (nativeShift_input_bound α B x y hB hz) hr hsep hcondition hd.1 hd.2
  dsimp only
  rw [nativeShiftBudgetCutoff_eq K k hK]
  exact hw

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
