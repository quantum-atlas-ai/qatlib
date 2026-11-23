module

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Papers.AnyCircuit08.MainResults.OracleSeparation
import Qatlib.Papers.AnyCircuit08.MainResults.RandomCircuitMoments

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AnyCircuit08.MainResults
open Qatlib.Papers.AnyCircuit08.MainResults

example : ‖phaseOracle (fun (_ : Unit) (x : Bool) => x) ()‖ = 1 :=
  norm_phaseOracle _ _

example :
    (Matrix.toEuclideanCLM (n := Bool) (𝕜 := ℂ) (phaseOracle (fun (_ : Unit) (x : Bool) => x) ())
      (uniformQueryState Bool)) true = -(1 / (Real.sqrt 2 : ℂ)) := by
  rw [phaseOracle_uniformQueryState]
  norm_num [oracleState, oracleSign]

private noncomputable def hadamardCircuit :
    EuclideanSpace ℂ Bool →ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × PUnit) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodPUnit Bool).symm).toLinearIsometry.comp
    ⟨Matrix.toEuclideanLin Hadamard,
      Qatlib.Foundations.PureStateMath.BornBridge.norm_toEuclideanCLM_of_mem_unitaryGroup
        hadamard_unitary⟩

/-- Relabeling the Hadamard output with a trivial workspace preserves its matrix entries. -/
private theorem hadamardCircuit_amplitude (a x : Bool) :
    circuitAmplitudes hadamardCircuit a PUnit.unit x = Hadamard a x := by
  change Matrix.mulVec Hadamard (WithLp.ofLp (EuclideanSpace.basisFun Bool ℂ x)) a = Hadamard a x
  rw [EuclideanSpace.basisFun_apply]
  exact congrFun (Matrix.mulVec_single_one Hadamard x) a

/-- Both Hadamard rows have the maximum first moment in dimension two. -/
private theorem hadamard_pseudoDispersing :
    IsPseudoDispersing (circuitAmplitudes hadamardCircuit) 1 1 := by
  refine ⟨Finset.univ, by simp, fun a _ => ⟨fun _ => 1, by simp [IsUnitVector], ?_⟩⟩
  have hentry (x : Bool) : ‖Hadamard a x‖ = (Real.sqrt 2)⁻¹ := by
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    cases a <;> cases x <;>
      simp [Hadamard, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwo : 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
    field_simp [hs.ne']
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [hadamardCircuit_amplitude, hentry, htwo]

example :
    ∃ (S : Finset Bool) (P : SingleLevelOracleProblem S Bool),
      1 < S.card ∧ ∀ a : S, (2 / Real.pi * 1) ^ 2 ≤
        outputProbability (oracleOutput hadamardCircuit P.f a) a.1 := by
  obtain ⟨S, P, hS, _, hquantum, _⟩ := exists_booleanOracle_separation hadamardCircuit
    (n := 1) (by decide) (by decide) (by norm_num) (by norm_num) hadamard_pseudoDispersing
  exact ⟨S, P, hS, hquantum⟩

example :
    (BitQueryTree.ask true
      (fun b => BitQueryTree.ask (!b) (fun c => BitQueryTree.guess (some c)))).run id =
      some false := rfl

private noncomputable def permutationCircuit (b : Bool) :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (if b then Equiv.swap false true else Equiv.refl Bool)

/-- The identity and bit flip each send every basis input to a basis output. -/
private theorem permutationCircuit_fourthMoment (b a : Bool) :
    rowFourthMoment (permutationCircuit b) a = 1 := by
  simp only [rowFourthMoment, circuitRow, permutationCircuit, norm_star,
    LinearIsometryEquiv.piLpCongrLeft_symm, EuclideanSpace.basisFun_apply,
    LinearIsometryEquiv.piLpCongrLeft_single]
  generalize (if b then Equiv.swap false true else Equiv.refl Bool).symm a = c
  cases c <;> simp

open scoped Classical in
example :
    1 - (2 * (1 / 4 : ℝ) ^ 2) / (1 - (2 : ℝ) ^ (-(1 : ℝ) * (1 - 1 / 2))) ≤
      (∑ b : Bool, if IsDispersing (circuitRow (permutationCircuit b)) (1 / 2) (1 / 4) then
        (1 : ℝ) else 0) / (Fintype.card Bool : ℝ) := by
  have hmean (a : Bool) :
      (∑ b, rowFourthMoment (permutationCircuit b) a) / (Fintype.card Bool : ℝ) ≤
        2 * (2 : ℝ) ^ (-(1 : ℝ)) := by
    norm_num [permutationCircuit_fourthMoment, Real.rpow_neg]
  simpa only [Nat.cast_one] using
    fraction_dispersing_of_mean_fourthMoment permutationCircuit (n := 1) (α := 1 / 2) (β := 1 / 4)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_one] using hmean)

#print axioms norm_phaseOracle
#print axioms exists_booleanOracle_separation
#print axioms fraction_dispersing_of_mean_fourthMoment
