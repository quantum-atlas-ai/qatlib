/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QueryLowerBound.ScalarSignalAccess
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

/-!
# Query bounds for fixed scalar signal words

This module bounds changes in the evaluation of a fixed well-formed oracle word by its query
count times the scalar signal distance. Compression and orthogonal projection estimates turn
this hybrid bound into response and leakage lower bounds related to [GilyenSuLowWiebe2019].

## Main statements

* `scalar_signal_fixed_word_hybrid_bound`: A query-count Lipschitz bound for a fixed word.
* `scalar_signal_actual_response_query_lower_bound`: Response separation forces a minimum number
  of queries.
* `scalar_signal_safe_leakage_query_lower_bound_corrected`: A lower bound combining response
  separation and a safe leakage difference.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.QsvtCore.QueryLowerBound
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Evaluation of a scalar-signal word is the product of its instruction matrices. -/
private theorem scalar_word_prod {W : Type} [Fintype W] [DecidableEq W]
    (x : ℝ) (word : List (AdjointStep (Bool×W))) :
    evaluate (scalarSignalLift W x) word=(word.map (instructionMatrix (scalarSignalLift W x))).prod := by
  induction word with
  | nil => rfl
  | cons c cs ih => simp [evaluate,ih]

/-- Tensor lifting to a finite workspace does not increase the scalar signal distance for
parameters in `[-1, 1]`. -/
private theorem scalar_lift_distance_le (W : Type) [Fintype W] [DecidableEq W]
    (x y : ℝ) (hx : x∈Set.Icc (-1) 1) (hy : y∈Set.Icc (-1) 1) :
    ‖scalarSignalLift W x-scalarSignalLift W y‖ ≤  scalarSignalDistance x y := by
  have he : scalarSignalLift W x-scalarSignalLift W y=TensorGate
      (scalarSignalReflection x-scalarSignalReflection y) (1 : Matrix W W ℂ) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    simp [scalarSignalLift,TensorGate,sub_mul]
  rw [he,TensorGate,l2_norm_kronecker,
    (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).1]
  simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left (l2_norm_one_le (I:=W)) (scalarSignalDistance_nonneg x y)

/-- Every instruction in a well-formed scalar-signal word has operator norm at most one when the
signal lies in `[-1, 1]`. -/
private theorem scalar_instruction_norm {W : Type} [Fintype W] [DecidableEq W]
    (x : ℝ) (hx : x∈Set.Icc (-1) 1) (word : List (AdjointStep (Bool×W)))
    (hw : WellFormedAdjointCircuit word) (c : AdjointStep (Bool×W)) (hc : c∈word) :
    ‖instructionMatrix (scalarSignalLift W x) c‖ ≤ 1 := by
  have hu := ((scalar_signal_actual_encoding x hx).2.2.2 W).unitary
  cases c with
  | gate V => exact l2_norm_unitary_le_one (hw V hc)
  | forward => exact l2_norm_unitary_le_one hu
  | backward => exact l2_norm_unitary_le_one (adjoint_unitary hu)

/-- For a fixed well-formed word and signals in `[-1, 1]`, the evaluation difference is at most
the query count times `scalarSignalDistance`. -/
theorem scalar_signal_fixed_word_hybrid_bound : ∀ (W : Type) [Fintype W] [DecidableEq W]
  (word : List (AdjointStep (Bool×W))) (x y : ℝ),
  WellFormedAdjointCircuit word → x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 →
  ‖evaluate (scalarSignalLift W x) word-evaluate (scalarSignalLift W y) word‖  ≤
    (adjointQueryCount word:ℝ)*scalarSignalDistance x y := by
  intro W _ _ word x y hw hx hy
  let pairs :=
      word.map (fun c=>(instructionMatrix (scalarSignalLift W x) c,instructionMatrix (scalarSignalLift W y) c))
  have hp := l2_norm_list_prod_sub_prod_le pairs (by
    intro p hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
    exact ⟨scalar_instruction_norm x hx word hw c hc,scalar_instruction_norm y hy word hw c hc⟩)
  have hxprod : (pairs.map Prod.fst).prod=evaluate (scalarSignalLift W x) word := by
    simp only [pairs,List.map_map,Function.comp_def,← scalar_word_prod]
  have hyprod : (pairs.map Prod.snd).prod=evaluate (scalarSignalLift W y) word := by
    simp only [pairs,List.map_map,Function.comp_def,← scalar_word_prod]
  rw [hxprod,hyprod] at hp
  have hlift := scalar_lift_distance_le W x y hx hy
  have hback : ‖(scalarSignalLift W x)ᴴ-(scalarSignalLift W y)ᴴ‖ ≤  scalarSignalDistance x y := by
    rw [← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose]
    exact hlift
  have hsum : ((word.map (fun c=>‖instructionMatrix (scalarSignalLift W x) c-
      instructionMatrix (scalarSignalLift W y) c‖)).sum) ≤ (adjointQueryCount word : ℝ)*scalarSignalDistance x y := by
    clear hw hp hxprod hyprod pairs
    induction word with
    | nil => simp [adjointQueryCount]
    | cons c cs ih =>
      cases c with
      | gate V => simpa only [List.map_cons,List.sum_cons,instructionMatrix,sub_self,norm_zero,zero_add,adjointQueryCount] using! ih
      | forward =>
        simp only [List.map_cons,List.sum_cons,instructionMatrix,adjointQueryCount,Nat.cast_add,Nat.cast_one] at ih ⊢
        nlinarith only [ih,hlift]
      | backward =>
        simp only [List.map_cons,List.sum_cons,instructionMatrix,adjointQueryCount,Nat.cast_add,Nat.cast_one] at ih ⊢
        nlinarith only [ih,hback]
  exact hp.trans (by simpa only [pairs,List.map_map,Function.comp_def] using! hsum)

/-- Compression between isometries does not increase the operator norm of a matrix difference. -/
private theorem scalar_compression_difference {W I : Type} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] (L R : Matrix (Bool×W) I ℂ)
    (hL : IsIsometry L) (hR : IsIsometry R) (V Z : Matrix (Bool×W) (Bool×W) ℂ) :
    ‖compress L V R-compress L Z R‖ ≤ ‖V-Z‖ := by
  have he : compress L V R-compress L Z R=Lᴴ*(V-Z)*R := by
    simp only [compress,Matrix.mul_sub,Matrix.sub_mul]
  rw [he]
  have hnorm := (Matrix.l2_opNorm_mul (Lᴴ*(V-Z)) R).trans
    (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Lᴴ (V-Z)) (norm_nonneg R))
  have hL1 : ‖Lᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact isometry_norm_le hL
  have hR1 := isometry_norm_le hR
  have hmid : ‖Lᴴ‖*‖V-Z‖ ≤ ‖V-Z‖ := by nlinarith only [hL1,norm_nonneg (V-Z)]
  have hh := mul_le_mul hmid hR1 (norm_nonneg R) (norm_nonneg (V-Z))
  exact hnorm.trans (by simpa only [mul_one] using! hh)

/-- Approximating scalar responses `a` and `b` at distinct signals within nonnegative error
`eps` requires at least `max 0 (|a - b| - 2 * eps) / scalarSignalDistance x y` queries. For
both signals in `[-1/2, 1/2]`, the denominator can be replaced by `2 * |x - y|`. -/
theorem scalar_signal_actual_response_query_lower_bound : ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I]
  [DecidableEq I] [Nonempty I] (L R : Matrix (Bool×W) I ℂ)
  (word : List (AdjointStep (Bool×W))) (x y a b eps : ℝ),
  IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
  x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x≠y → 0 ≤ eps →
  ‖(a:ℂ) • (1:Matrix I I ℂ)-compress L (evaluate (scalarSignalLift W x) word) R‖  ≤  eps →
  ‖(b:ℂ) • (1:Matrix I I ℂ)-compress L (evaluate (scalarSignalLift W y) word) R‖  ≤  eps →
  (adjointQueryCount word:ℝ) ≥ max 0 (|a-b|-2*eps)/scalarSignalDistance x y ∧
  (|x| ≤ 1/2 → |y| ≤ 1/2 →
    (adjointQueryCount word:ℝ) ≥ max 0 (|a-b|-2*eps)/(2*|x-y|)) := by
  intro W I _ _ _ _ _ L R word x y a b eps hL hR hw hx hy hxy heps ha hb
  have hdiff := (scalar_compression_difference L R hL hR
    (evaluate (scalarSignalLift W x) word) (evaluate (scalarSignalLift W y) word)).trans
    (scalar_signal_fixed_word_hybrid_bound W word x y hw hx hy)
  have htarget : ‖(a : ℂ) • (1 : Matrix I I ℂ)-(b : ℂ) • (1 : Matrix I I ℂ)‖=|a-b| := by
    rw [← sub_smul,← Complex.ofReal_sub,norm_smul,l2_norm_one_eq,Complex.norm_real,Real.norm_eq_abs,mul_one]
  let A : Matrix I I ℂ := (a : ℂ) • 1
  let B : Matrix I I ℂ := (b : ℂ) • 1
  let Cx : Matrix I I ℂ := compress L (evaluate (scalarSignalLift W x) word) R
  let Cy : Matrix I I ℂ := compress L (evaluate (scalarSignalLift W y) word) R
  have hYB : ‖Cy-B‖ ≤ eps := by rw [norm_sub_rev]; exact hb
  have htri : ‖A-B‖ ≤ eps+((adjointQueryCount word : ℝ)*scalarSignalDistance x y+eps) := calc
    _ ≤ ‖A-Cx‖+‖Cx-B‖ := norm_sub_le_norm_sub_add_norm_sub A Cx B
    _ ≤ ‖A-Cx‖+(‖Cx-Cy‖+‖Cy-B‖) := add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub Cx Cy B)
    _ ≤ _ := add_le_add ha (add_le_add hdiff hYB)
  have htri' : |a-b| ≤ eps+((adjointQueryCount word : ℝ)*scalarSignalDistance x y+eps) := by
    rw [← htarget]
    exact htri
  have hnum : max 0 (|a-b|-2*eps) ≤ (adjointQueryCount word : ℝ)*scalarSignalDistance x y := by
    apply max_le
    · exact mul_nonneg (Nat.cast_nonneg _) (scalarSignalDistance_nonneg x y)
    · linarith only [htri']
  have hd := scalar_signal_exact_distance_and_central_lipschitz x y hx hy
  refine ⟨(div_le_iff₀ (hd.2.2.2.1 hxy)).mpr hnum,?_⟩
  intro hxhalf hyhalf
  have hdx : 0<2*|x-y| := mul_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hxy))
  apply (div_le_iff₀ hdx).mpr
  exact hnum.trans (mul_le_mul_of_nonneg_left (hd.2.2.2.2 hxhalf hyhalf) (Nat.cast_nonneg _))

/-- An orthogonal projector and its complement split the squared Euclidean norm of a state
additively. -/
private theorem scalar_projector_norm_split {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (ψ : QState H) :
    ‖toEuclidean_fromVec ((1-P)*ᵥψ)‖^2+‖toEuclidean_fromVec (P*ᵥψ)‖^2=‖toEuclidean_fromVec ψ‖^2 := by
  simpa only [ProjectiveBranchMass,ProjectiveBranch,ApplyGate,↓reduceIte,MeasureProb,BornProb,
    ← norm_toEuclidean_fromVec_sq] using! projectiveBranchMass_add hP ψ

/-- The complement of an orthogonal projector is a contraction on state vectors. -/
private theorem scalar_failure_contract {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (ψ : QState H) :
    ‖toEuclidean_fromVec ((1-P)*ᵥψ)‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh := scalar_projector_norm_split P hP ψ
  nlinarith only [hh,sq_nonneg ‖toEuclidean_fromVec (P*ᵥψ)‖]

/-- For a unit state and an isometry `L`, the norm outside the range of `L` is the square root
of one minus the squared norm of `Lᴴ` applied to the state. -/
private theorem scalar_failure_norm {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (L : Matrix H I ℂ) (hL : IsIsometry L)
    (ψ : QState H) (hn : ‖toEuclidean_fromVec ψ‖=1) :
    ‖toEuclidean_fromVec ((1-rangeProjector L)*ᵥψ)‖=
      Real.sqrt (1-‖toEuclidean_fromVec (Lᴴ*ᵥψ)‖^2) := by
  have hP := rangeProjector_isOrthogonalProjector hL
  have hh := scalar_projector_norm_split (rangeProjector L) hP ψ
  have hs : ‖toEuclidean_fromVec ((rangeProjector L)*ᵥψ)‖=‖toEuclidean_fromVec (Lᴴ*ᵥψ)‖ := by
    rw [rangeProjector,← Matrix.mulVec_mulVec,isometry_mulVec_norm hL]
  rw [hn,hs] at hh
  have hrad : 0 ≤ 1-‖toEuclidean_fromVec (Lᴴ*ᵥψ)‖^2 := by
    nlinarith only [hh,sq_nonneg ‖toEuclidean_fromVec ((1-rangeProjector L)*ᵥψ)‖]
  nlinarith only [hh,Real.sq_sqrt hrad,norm_nonneg (toEuclidean_fromVec ((1-rangeProjector L)*ᵥψ)),Real.sqrt_nonneg (1-‖toEuclidean_fromVec (Lᴴ*ᵥψ)‖^2)]

/-- An operator-norm approximation to the scalar matrix `a` bounds the difference between `|a|`
and each compressed basis-output norm by `eps`. -/
private theorem scalar_corner_state_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (L R : Matrix H I ℂ) (V : Matrix H H ℂ)
    (a eps : ℝ) (j : I) (ha : ‖(a : ℂ) • (1 : Matrix I I ℂ)-compress L V R‖ ≤ eps) :
    abs (|a| - ‖toEuclidean_fromVec (Lᴴ*ᵥ(V*ᵥ(R*ᵥKet j)))‖) ≤ eps := by
  have hket : ‖toEuclidean_fromVec (Ket j)‖=1 :=
      (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j)
  have hc : Lᴴ*ᵥ(V*ᵥ(R*ᵥKet j))=compress L V R*ᵥKet j := by
    simp only [compress,Matrix.mulVec_mulVec,Matrix.mul_assoc]
  rw [hc]
  have he := l2_norm_mulVec_fromVec_le ((a : ℂ) • (1 : Matrix I I ℂ)-compress L V R) (Ket j)
  rw [hket,mul_one,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at he
  have hh := (abs_norm_sub_norm_le (toEuclidean_fromVec ((a : ℂ) • Ket j))
    (toEuclidean_fromVec (compress L V R*ᵥKet j))).trans (he.trans ha)
  have htarget : ‖toEuclidean_fromVec ((a : ℂ) • Ket j)‖=|a| := by
    change ‖(a : ℂ) • toEuclidean_fromVec (Ket j)‖=|a|
    rw [norm_smul,hket,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rwa [htarget] at hh

/-- Under the stated scalar response, isometry, and error assumptions, the query count is
bounded below by the maximum of zero, response separation, and the oriented leakage
difference, divided by scalar signal distance. This is the corrected leakage comparison in
the setting of [Gilyén et al., Theorem 73][GilyenSuLowWiebe2019]. -/
theorem scalar_signal_safe_leakage_query_lower_bound_corrected : ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I]
  [DecidableEq I] [Nonempty I] (L R : Matrix (Bool×W) I ℂ)
  (word : List (AdjointStep (Bool×W))) (x y a b eps : ℝ),
  IsIsometry L → IsIsometry R → WellFormedAdjointCircuit word →
  x ∈ Set.Icc (-1) 1 → y ∈ Set.Icc (-1) 1 → x≠y → 0 ≤ eps →
  eps ≤ a → a ≤ 1 → 0 ≤ b → b+eps ≤ 1 →
  ‖(a:ℂ) • (1:Matrix I I ℂ)-compress L (evaluate (scalarSignalLift W x) word) R‖  ≤  eps →
  ‖(b:ℂ) • (1:Matrix I I ℂ)-compress L (evaluate (scalarSignalLift W y) word) R‖  ≤  eps →
  (adjointQueryCount word:ℝ) ≥
    max (max 0 (|a-b|-2*eps))
      (Real.sqrt (1-(b+eps)^2)-Real.sqrt (1-(a-eps)^2))/scalarSignalDistance x y := by
  intro W I _ _ _ _ _ L R word x y a b eps hL hR hw hx hy hxy heps haeps ha1 hb0 hbeps ha hb
  let j : I := Classical.choice ‹Nonempty I›
  let Vx := evaluate (scalarSignalLift W x) word
  let Vy := evaluate (scalarSignalLift W y) word
  let ν := R*ᵥKet j
  let zx := Vx*ᵥν
  let zy := Vy*ᵥν
  let P := rangeProjector L
  have hP : IsOrthogonalProjector P := rangeProjector_isOrthogonalProjector hL
  have hket : ‖toEuclidean_fromVec (Ket j)‖=1 :=
      (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j)
  have hν : ‖toEuclidean_fromVec ν‖=1 := (isometry_mulVec_norm hR (Ket j)).trans hket
  have hVx := hw.evaluate_unitary ((scalar_signal_actual_encoding x hx).2.2.2 W).unitary
  have hVy := hw.evaluate_unitary ((scalar_signal_actual_encoding y hy).2.2.2 W).unitary
  have hIx : IsIsometry Vx := by simpa only [Matrix.star_eq_conjTranspose] using! hVx.1
  have hIy : IsIsometry Vy := by simpa only [Matrix.star_eq_conjTranspose] using! hVy.1
  have hzx : ‖toEuclidean_fromVec zx‖=1 := (isometry_mulVec_norm hIx ν).trans hν
  have hzy : ‖toEuclidean_fromVec zy‖=1 := (isometry_mulVec_norm hIy ν).trans hν
  have ha0 : 0 ≤ a := heps.trans haeps
  have hax := scalar_corner_state_error L R Vx a eps j ha
  have hby := scalar_corner_state_error L R Vy b eps j hb
  rw [abs_of_nonneg ha0] at hax
  rw [abs_of_nonneg hb0] at hby
  have hsx : a-eps ≤ ‖toEuclidean_fromVec (Lᴴ*ᵥzx)‖ := by
    have hh := (abs_le.mp hax).2
    exact sub_le_iff_le_add.mpr (by linarith only [hh])
  have hsy : ‖toEuclidean_fromVec (Lᴴ*ᵥzy)‖ ≤ b+eps := by
    have hh := (abs_le.mp hby).1
    linarith only [hh]
  have hxsq := pow_le_pow_left₀ (show 0 ≤ a-eps by linarith) hsx 2
  have hysq := pow_le_pow_left₀ (norm_nonneg _) hsy 2
  have hfx : ‖toEuclidean_fromVec ((1-P)*ᵥzx)‖ ≤ Real.sqrt (1-(a-eps)^2) := by
    rw [scalar_failure_norm L hL zx hzx]
    exact Real.sqrt_le_sqrt (by linarith only [hxsq])
  have hfy : Real.sqrt (1-(b+eps)^2) ≤ ‖toEuclidean_fromVec ((1-P)*ᵥzy)‖ := by
    rw [scalar_failure_norm L hL zy hzy]
    exact Real.sqrt_le_sqrt (by linarith only [hysq])
  have hdiff : ‖toEuclidean_fromVec (zy-zx)‖ ≤ (adjointQueryCount word : ℝ)*scalarSignalDistance x y := by
    have he := l2_norm_mulVec_fromVec_le (Vy-Vx) ν
    rw [hν,mul_one,Matrix.sub_mulVec,norm_sub_rev Vy Vx] at he
    exact he.trans (scalar_signal_fixed_word_hybrid_bound W word x y hw hx hy)
  have hgap :=
      abs_norm_sub_norm_le (toEuclidean_fromVec ((1-P)*ᵥzy)) (toEuclidean_fromVec ((1-P)*ᵥzx))
  have hproject : toEuclidean_fromVec ((1-P)*ᵥzy)-toEuclidean_fromVec ((1-P)*ᵥzx)=
      toEuclidean_fromVec ((1-P)*ᵥ(zy-zx)) := by rw [Matrix.mulVec_sub]; rfl
  rw [hproject] at hgap
  have hfgap := (le_abs_self (‖toEuclidean_fromVec ((1-P)*ᵥzy)‖-‖toEuclidean_fromVec ((1-P)*ᵥzx)‖)).trans
    (hgap.trans ((scalar_failure_contract P hP (zy-zx)).trans hdiff))
  have hLeak : Real.sqrt (1-(b+eps)^2)-Real.sqrt (1-(a-eps)^2) ≤
      (adjointQueryCount word : ℝ)*scalarSignalDistance x y := by linarith only [hfx,hfy,hfgap]
  have hδ := (scalar_signal_exact_distance_and_central_lipschitz x y hx hy).2.2.2.1 hxy
  have hresp :=
      (scalar_signal_actual_response_query_lower_bound W I L R word x y a b eps hL hR hw hx hy hxy heps ha hb).1
  apply (div_le_iff₀ hδ).mpr
  exact max_le ((div_le_iff₀ hδ).mp hresp) hLeak

end Qatlib.Concepts.QsvtCore.QueryLowerBound
