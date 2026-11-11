/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.AccessLower.CoordinateFiber
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Tactic
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.BasisFrame
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.FrameTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TranslatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.TruncatedPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost
import Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport.MarkedColumns
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.InputHybrid
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.OutputReadout
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.Program
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.SourceWordTransport
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRange
import Qatlib.Foundations.OpCalculus.ContourCalc.NumericalRangeConvex

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Papers.CrouzeixLS26.AccessLower.Coordinate
open Qatlib.Concepts.BlockEncoding

/-! A concrete shared approximate oracle for two nonnormal target matrices.
The numerical-range and algorithmic indistinguishability claims are separate. -/
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointAmplify Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.JointTranscript Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol Qatlib.Concepts.QueryComplexity.AdversarySearch.MarkedSupport Qatlib.Foundations.OpCalculus.ContourCalc
namespace Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower
open Qatlib Matrix
open scoped Matrix.Norms.L2Operator

/-- Construction for jordan in the shared oracle core model. -/
def jordan : Matrix Bool Bool ℂ
  | false, true => 1
  | _, _ => 0

/-- Construction for oracle in the shared oracle core model. -/
def oracle (c l : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ
  | (false,false), (false,true) => c
  | (false,false), (true,false) => l
  | (false,true), (true,true) => 1
  | (true,false), (false,false) => 1
  | (true,true), (false,true) => l
  | (true,true), (true,false) => -c
  | _, _ => 0

/-- The restricted-access construction satisfies `oracle_unitary` under the complete displayed premises. -/
theorem oracle_unitary (c l : ℝ) (h : c^2+l^2=1) :
    oracle c l ∈ unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext ⟨a,b⟩ ⟨d,e⟩
  cases a <;> cases b <;> cases d <;> cases e <;>
    simp [oracle, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;>
      try ring_nf <;> try norm_num
  all_goals first | exact_mod_cast h | exact_mod_cast (show l^2+c^2=1 by nlinarith)

/-- The restricted-access construction satisfies `oracle_compress` under the complete displayed premises. -/
theorem oracle_compress (c l : ℝ) :
    compress (encodingFiber false) (oracle c l) (encodingFiber false) =
      (c : ℂ) • jordan := by
  ext a b
  rw [compress_encodingFiber_eq]
  cases a <;> cases b <;> simp [oracle, jordan]

/-- The restricted-access construction satisfies `jordan_norm` under the complete displayed premises. -/
theorem jordan_norm : ‖jordan‖ = 1 := by
  have hdiag : jordanᴴ * jordan = Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0) := by
    ext a b
    cases a <;> cases b <;> norm_num [jordan, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fintype.sum_bool]
  have hfun : ‖(fun b : Bool => if b then (1 : ℂ) else 0)‖ = 1 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro b
      cases b <;> norm_num
    · have h := norm_le_pi_norm (fun b : Bool => if b then (1 : ℂ) else 0) true
      simpa using h
  have h := Matrix.l2_opNorm_conjTranspose_mul_self jordan
  rw [hdiag, Matrix.l2_opNorm_diagonal, hfun] at h
  nlinarith [norm_nonneg jordan]

/-- The restricted-access construction satisfies `jordan_nonnormal` under the complete displayed premises. -/
theorem jordan_nonnormal : jordan * jordanᴴ ≠ jordanᴴ * jordan := by
  intro h
  have hh := congrArg (fun M : Matrix Bool Bool ℂ => M false false) h
  norm_num [jordan, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool] at hh

end Qatlib.Papers.CrouzeixLS26.AccessLower.SharedOracleInputLower
