module

public import Qatlib.Papers.RandCompiler19.ChannelBudget.TableIScaling
public import Qatlib.Papers.RandCompiler19.DiamondTools.ObservableTransfer
public import Qatlib.Papers.RandCompiler19.ControlledDrift.PrecisionRotation
public import Qatlib.Foundations.OperatorErrors.OperatorError
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# Consumer regression for the RandCompiler19 scaling increment

The concrete instance uses the two noncommuting Pauli contractions `X` and `Z` on a qubit.
This is a non-degenerate two-component Hamiltonian: both operators are Hermitian, both have
`L²` operator norm one, and the sampling law is uniform. The examples invoke the new Table I
scaling theorem, the diamond-to-observable transfer theorem on a normalized `EuclideanSpace`
state, and the controlled rotation-count theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.ReferenceModel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Papers.RandCompiler19.ChannelBudget
open Qatlib.Papers.RandCompiler19.DiamondTools
open Qatlib.Papers.RandCompiler19.ControlledDrift

namespace Tests.RandCompiler19ScalingRegression

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators

/-- The Pauli `X` matrix on a qubit. -/
private def xMat : Operator 2 := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix on a qubit. -/
private def zMat : Operator 2 := !![1, 0; 0, -1]

/-- The two-component Hamiltonian with noncommuting Pauli terms. -/
private def K2 : Fin 2 → Operator 2 := ![xMat, zMat]

/-- Pauli `X` is a Hermitian contraction. -/
private theorem xMat_contract : xMat.IsHermitian ∧ ‖xMat‖ ≤ 1 := by
  have hh : xMatᴴ = xMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [xMat, Matrix.conjTranspose_apply]
  refine ⟨hh, l2_norm_unitary_le_one ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli `Z` is a Hermitian contraction. -/
private theorem zMat_contract : zMat.IsHermitian ∧ ‖zMat‖ ≤ 1 := by
  have hh : zMatᴴ = zMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [zMat, Matrix.conjTranspose_apply]
  refine ⟨hh, l2_norm_unitary_le_one ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Both components are Hermitian contractions. -/
private theorem K2_contract : ∀ j, (K2 j).IsHermitian ∧ ‖K2 j‖ ≤ 1 := by
  intro j
  fin_cases j
  · simpa [K2] using xMat_contract
  · simpa [K2] using zMat_contract

/-- The basis ket `|0⟩` viewed as a normalized `EuclideanSpace` vector. -/
private noncomputable def psi0 : EuclideanSpace ℂ (Fin 2) :=
  toEuclidean_fromVec (Ket (0 : Fin 2))

/-- The concrete `EuclideanSpace` state is normalized. -/
private theorem psi0_norm : ‖psi0‖ = 1 := by
  rw [psi0]
  exact (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket 0)

/-- The linear-weight Table I bound is invoked at two components and unit scale. -/
example :
    ∃ C : ℝ, 0 < C ∧
      let lam := (1 : ℝ) * 2
      let N := qdriftSteps lam 1 (2 * (1 / 2 : ℝ))
      0 < N ∧ (N : ℝ) ≤ C * 1 ^ 2 * 2 ^ 2 * 1 ^ 2 / (1 / 2) + 1 ∧
        finiteDiamondDistance (exactQdriftMap qdriftTwoLaw K2 lam 1 N)
          (conjBranch (HamiltonianEvolution (qdriftHamiltonian qdriftTwoLaw K2 lam) 1)) ≤
          ENNReal.ofReal (1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := tableI_linear_component_scaling
  exact ⟨C, hC, h 2 2 (by norm_num) (by norm_num) qdriftTwoLaw K2 1 1 (1 / 2)
    (by norm_num) (by norm_num) K2_contract⟩

/-- The square-root Table I bound is invoked at the same nondegenerate instance. -/
example :
    ∃ C : ℝ, 0 < C ∧
      let lam := (1 : ℝ) * Real.sqrt (2 : ℝ)
      let N := qdriftSteps lam 1 (2 * (1 / 2 : ℝ))
      0 < N ∧ (N : ℝ) ≤ C * 1 ^ 2 * 2 * 1 ^ 2 / (1 / 2) + 1 ∧
        finiteDiamondDistance (exactQdriftMap qdriftTwoLaw K2 lam 1 N)
          (conjBranch (HamiltonianEvolution (qdriftHamiltonian qdriftTwoLaw K2 lam) 1)) ≤
          ENNReal.ofReal (1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := tableI_sqrt_component_scaling
  exact ⟨C, hC, h 2 2 (by norm_num) (by norm_num) qdriftTwoLaw K2 1 1 (1 / 2)
    (by norm_num) (by norm_num) K2_contract⟩

/-- The diamond-to-observable transfer is invoked on the actual qDRIFT channel pair, the
normalized `EuclideanSpace` state `|0⟩`, and the Pauli `X` observable. -/
example :
    let T := exactQdriftMap qdriftTwoLaw K2 1 1 (qdriftSteps 1 1 (2 * (1 / 2 : ℝ)))
    let S := conjBranch (HamiltonianEvolution (qdriftHamiltonian qdriftTwoLaw K2 1) 1)
    let ρ := outerProduct (toVec_fromEuclidean psi0)
    ∃ C : ℝ, 0 < C ∧ Matrix.traceNorm (T ρ - S ρ) ≤ C * (1 / 2) ∧
      ‖Matrix.trace (xMat * T ρ) - Matrix.trace (xMat * S ρ)‖ ≤
        C * ‖xMat‖ * (1 / 2 : ℝ) := by
  intro T S ρ
  obtain ⟨C, hC, h⟩ := finite_diamond_output_and_observable_transfer
  obtain ⟨Cp, _, hp⟩ := finite_diamond_pure_state_observable_transfer
  have hNpos : 0 < qdriftSteps (1 : ℝ) 1 (2 * (1 / 2 : ℝ)) := by
    unfold qdriftSteps
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hdiam := (exact_qdrift_actual_finite_diamond_budget 2 2 qdriftTwoLaw K2 1 1
    (qdriftSteps (1 : ℝ) 1 (2 * (1 / 2 : ℝ))) (by norm_num) hNpos K2_contract).2
      (1 / 2) (by norm_num)
  have hψ : Normalized (toVec_fromEuclidean psi0) := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
    simpa only [toEuclidean_fromVec_toVec_fromEuclidean] using psi0_norm
  have hρ : Matrix.traceNorm ρ ≤ 1 :=
    le_of_eq (traceNorm_outerProduct_of_normalized _ hψ)
  have htrace := (h 2 (by norm_num) T S (1 / 2) (by norm_num) hdiam.2.2 ρ xMat hρ).1
  have hobs := hp 2 (by norm_num) T S (1 / 2) (by norm_num) hdiam.2.2 psi0 psi0_norm xMat
  exact ⟨max C Cp, hC.trans_le (le_max_left _ _),
    htrace.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by norm_num)),
    hobs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg xMat)) (by norm_num))⟩

/-- The controlled rotation-count theorem is invoked at the same two-component instance. -/
example :
    ∃ N : ℕ,
      0 < N ∧
      N = qdriftSteps 1 1 (2 * (1 / 2 : ℝ)) ∧
      (N : ℝ) ≤ 2 * 1 ^ 2 * 1 ^ 2 / (1 / 2) + 1 ∧
      finiteDiamondDistance
        (exactQdriftMap qdriftTwoLaw (fun j => controlledCopyHamiltonian 2 (K2 j)) 1 1 N)
        (conjBranch (copyControlledEvolution (qdriftHamiltonian qdriftTwoLaw K2 1) 1)) ≤
          ENNReal.ofReal (1 / 2 : ℝ) ∧
      finiteDiamondDistance (exactQdriftMap qdriftTwoLaw K2 1 1 N)
        (conjBranch (HamiltonianEvolution (qdriftHamiltonian qdriftTwoLaw K2 1) 1)) ≤
          ENNReal.ofReal (1 / 2 : ℝ) ∧
      (∀ ω : Fin N → Fin 2,
        let s := (1 : ℝ) * 1 / N
        GateCount (mixturePathCircuit
          (fun j => HamiltonianEvolution (controlledCopyHamiltonian 2 (K2 j)) s) ω) = N ∧
        GateCount (mixturePathCircuit (fun j => HamiltonianEvolution (K2 j) s) ω) = N) := by
  obtain ⟨N, hNpos, hNeq, hNle, hctl, hunc, hgate⟩ :=
    controlled_qdrift_precision_rotation_budget 2 2 (by norm_num) (by norm_num)
      qdriftTwoLaw K2 1 1 (1 / 2) (by norm_num) (by norm_num) K2_contract
  exact ⟨N, hNpos, hNeq, hNle, hctl, hunc, fun ω => hgate ω _⟩

end Tests.RandCompiler19ScalingRegression
