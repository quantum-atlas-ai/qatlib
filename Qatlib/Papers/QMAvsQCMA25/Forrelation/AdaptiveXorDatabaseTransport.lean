/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.XorCompressedDatabaseIntertwining

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.AdaptiveXorDatabaseTransport

open Matrix
open scoped BigOperators

inductive AdaptiveXorWord (I W O : Type) : Type where
  | nil : AdaptiveXorWord I W O
  | gate (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (σ : AdaptiveXorWord I W O) :
      AdaptiveXorWord I W O
  | query (σ : AdaptiveXorWord I W O) : AdaptiveXorWord I W O
  | branch (E : O → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      (σ : O → AdaptiveXorWord I W O) : AdaptiveXorWord I W O

inductive IsAdaptiveLeaf {I W O : Type} :
    AdaptiveXorWord I W O → List O → Prop where
  | nil : IsAdaptiveLeaf .nil []
  | gate (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (σ : AdaptiveXorWord I W O)
      {ω : List O} (h : IsAdaptiveLeaf σ ω) : IsAdaptiveLeaf (.gate V σ) ω
  | query (σ : AdaptiveXorWord I W O) {ω : List O} (h : IsAdaptiveLeaf σ ω) :
      IsAdaptiveLeaf (.query σ) ω
  | branch (E : O → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      (σ : O → AdaptiveXorWord I W O) (o : O) {ω : List O}
      (h : IsAdaptiveLeaf (σ o) ω) : IsAdaptiveLeaf (.branch E σ) (o :: ω)

noncomputable def adaptiveLeaves {O : Type} [Fintype O] [DecidableEq O] {I W : Type} :
    AdaptiveXorWord I W O → Finset (List O) :=
  AdaptiveXorWord.rec
    (motive := fun _ => Finset (List O))
    {[]}
    (fun _ _ ih => ih)
    (fun _ ih => ih)
    (fun _ _ ih => Finset.univ.biUnion fun o => (ih o).image fun l => o :: l)

/-- The empty adaptive word has exactly the empty outcome list as a leaf. -/
theorem adaptiveLeaves_nil {O : Type} [Fintype O] [DecidableEq O] {I W : Type} :
    adaptiveLeaves (I := I) (W := W)
      (AdaptiveXorWord.nil : AdaptiveXorWord I W O) = {[]} := rfl

/-- Prepending a gate leaves the set of adaptive leaves unchanged. -/
theorem adaptiveLeaves_gate {O : Type} [Fintype O] [DecidableEq O] {I W : Type}
    (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (σ : AdaptiveXorWord I W O) :
    adaptiveLeaves (I := I) (W := W) (.gate V σ) = adaptiveLeaves σ := rfl

/-- Prepending a query leaves the set of adaptive leaves unchanged. -/
theorem adaptiveLeaves_query {O : Type} [Fintype O] [DecidableEq O] {I W : Type}
    (σ : AdaptiveXorWord I W O) :
    adaptiveLeaves (I := I) (W := W) (.query σ) = adaptiveLeaves σ := rfl

/-- The leaves of a branch are obtained by prepending each outcome to the leaves of its
continuation. -/
theorem adaptiveLeaves_branch {O : Type} [Fintype O] [DecidableEq O] {I W : Type}
    (E : O → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (σ : O → AdaptiveXorWord I W O) :
    adaptiveLeaves (I := I) (W := W) (.branch E σ)
      = Finset.univ.biUnion fun o => (adaptiveLeaves (σ o)).image fun l => o :: l := rfl

/-- Every valid adaptive leaf belongs to the finite set `adaptiveLeaves`. -/
theorem mem_adaptiveLeaves {O : Type} [Fintype O] [DecidableEq O] {I W : Type}
    {σ : AdaptiveXorWord I W O} {ω : List O} (h : IsAdaptiveLeaf σ ω) :
    ω ∈ adaptiveLeaves σ := by
  induction h with
  | nil => rw [adaptiveLeaves_nil]; exact Finset.mem_singleton_self _
  | gate V σ _ ih => rw [adaptiveLeaves_gate]; exact ih
  | query σ _ ih => rw [adaptiveLeaves_query]; exact ih
  | branch E σ o _ ih =>
      rw [adaptiveLeaves_branch]
      refine Finset.mem_biUnion.mpr ⟨o, Finset.mem_univ o, ?_⟩
      exact Finset.mem_image_of_mem _ ih

inductive IsAdaptiveXorUnitary {I W O : Type} [Fintype I] [DecidableEq I] [Fintype W]
    [DecidableEq W] [Fintype O] :
    AdaptiveXorWord I W O → Prop where
  | nil : IsAdaptiveXorUnitary .nil
  | gate (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      (hV : V ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ) {σ : AdaptiveXorWord I W O}
      (hσ : IsAdaptiveXorUnitary σ) : IsAdaptiveXorUnitary (.gate V σ)
  | query {σ : AdaptiveXorWord I W O} (hσ : IsAdaptiveXorUnitary σ) :
      IsAdaptiveXorUnitary (.query σ)
  | branch (E : O → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
      (hE : ∑ o, (E o)ᴴ * (E o) = 1) {σ : O → AdaptiveXorWord I W O}
      (hσ : ∀ o, IsAdaptiveXorUnitary (σ o)) : IsAdaptiveXorUnitary (.branch E σ)

noncomputable section

open Matrix
open scoped BigOperators
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib.Papers.QMAvsQCMA25.Forrelation.XorCompressedDatabaseIntertwining

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def adaptiveWord {O : Type} :
    AdaptiveXorWord I W O → List O → Circuit (((I × Bool) × W) × (I → Bool)) :=
  AdaptiveXorWord.rec
    (motive := fun _ => List O → Circuit (((I × Bool) × W) × (I → Bool)))
    (fun _ => [])
    (fun V _ ih => fun ω =>
      Step.gate (TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ)) :: ih ω)
    (fun _ ih => fun ω => Step.query :: ih ω)
    (fun E _ ih => fun ω =>
      match ω with
      | [] => []
      | o :: ω' =>
        Step.gate (TensorGate (E o) (1 : Matrix (I → Bool) (I → Bool) ℂ)) :: ih o ω')

/-- The empty adaptive word yields an empty circuit for every outcome list. -/
theorem adaptiveWord_nil {O : Type} (ω : List O) :
    adaptiveWord
      (AdaptiveXorWord.nil : AdaptiveXorWord I W O) ω = [] := rfl

/-- Extracting the circuit of a gate node prepends that gate tensored with the database
identity. -/
theorem adaptiveWord_gate {O : Type}
    (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (σ : AdaptiveXorWord I W O)
    (ω : List O) :
    adaptiveWord (.gate V σ) ω
      = Step.gate (TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ))
          :: adaptiveWord σ ω := rfl

/-- Extracting the circuit of a query node prepends one query step. -/
theorem adaptiveWord_query {O : Type} (σ : AdaptiveXorWord I W O) (ω : List O) :
    adaptiveWord (.query σ) ω
      = Step.query :: adaptiveWord σ ω := rfl

/-- Extracting a branch circuit with no supplied outcomes yields the empty circuit. -/
theorem adaptiveWord_branch_nil {O : Type}
    (E : O → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (σ : O → AdaptiveXorWord I W O) :
    adaptiveWord (.branch E σ) [] = [] := rfl

/-- Extracting a branch circuit prepends the selected outcome operator and continues with the
remaining outcomes. -/
theorem adaptiveWord_branch_cons {O : Type}
    (E : O → Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ)
    (σ : O → AdaptiveXorWord I W O) (o : O) (ω : List O) :
    adaptiveWord (.branch E σ) (o :: ω)
      = Step.gate (TensorGate (E o) (1 : Matrix (I → Bool) (I → Bool) ℂ))
          :: adaptiveWord (σ o) ω := rfl

/-- The circuit extracted from a valid adaptive leaf is an algorithm circuit. -/
theorem adaptiveWord_isAlgorithmCircuit {O : Type} :
    ∀ {σ : AdaptiveXorWord I W O} {ω : List O}, IsAdaptiveLeaf σ ω →
      IsAlgorithmCircuit (adaptiveWord σ ω) := by
  intro σ ω hleaf
  induction hleaf with
  | nil =>
      rw [adaptiveWord_nil]
      exact isAlgorithmCircuit_nil
  | gate V σ _ ih =>
      rw [adaptiveWord_gate]
      intro U hU
      rcases List.mem_cons.mp hU with hU | hU
      · injection hU with hU
        exact ⟨V, hU⟩
      · exact ih U hU
  | query σ _ ih =>
      rw [adaptiveWord_query]
      intro U hU
      rcases List.mem_cons.mp hU with hU | hU
      · exact absurd hU (by simp)
      · exact ih U hU
  | branch E σ o _ ih =>
      rw [adaptiveWord_branch_cons]
      intro U hU
      rcases List.mem_cons.mp hU with hU | hU
      · injection hU with hU
        exact ⟨E o, hU⟩
      · exact ih U hU

/-- For `p` between zero and one, decoding intertwines database XOR execution and purified XOR
execution along every valid adaptive leaf. -/
theorem xorDecode_run_transport_adaptive_leaf (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} {σ : AdaptiveXorWord I W O} {ω : List O} (hleaf : IsAdaptiveLeaf σ ω)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (Run (databaseXorOracle p) (adaptiveWord σ ω) v)
      = Run xorPurifiedQuery (adaptiveWord σ ω) (ApplyGate (xorDecode p) v) :=
  xorDecode_run_transport_algorithm p hp0 hp1 (adaptiveWord σ ω)
    (adaptiveWord_isAlgorithmCircuit hleaf) v

section InstrumentMass

variable {Z : Type} [Fintype Z] [DecidableEq Z]

/-- The squared norm of a gate-applied state is the quadratic form of the gate's Gram matrix. -/
theorem inner_applyGate_eq_vecMul (F : Matrix Z Z ℂ) (v : QState Z) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate F v) (ApplyGate F v)
      = dotProduct (Matrix.vecMul (star v) (Fᴴ * F)) v := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

/-- A finite operator family whose Gram matrices sum to the identity preserves total Born mass
when summed over outcomes. -/
theorem instrument_family_mass {O : Type} [Fintype O]
    (F : O → Matrix Z Z ℂ) (hF : ∑ o, (F o)ᴴ * (F o) = 1) (v : QState Z) :
    ∑ o, ∑ z, BornProb (ApplyGate (F o) v) z = ∑ z, BornProb v z := by
  have key : (∑ o, Qatlib.Foundations.PureStateMath.Inner (ApplyGate (F o) v)
      (ApplyGate (F o) v) : ℂ) = Qatlib.Foundations.PureStateMath.Inner v v := by
    rw [Finset.sum_congr rfl fun o _ => inner_applyGate_eq_vecMul (F o) v,
      Finset.sum_congr rfl fun o _ =>
        (Matrix.dotProduct_mulVec (star v) ((F o)ᴴ * (F o)) v).symm,
      ← dotProduct_sum, ← Matrix.sum_mulVec, hF, Matrix.dotProduct_mulVec,
      Matrix.vecMul_one]
    rfl
  have hL : (∑ o, Qatlib.Foundations.PureStateMath.Inner (ApplyGate (F o) v)
      (ApplyGate (F o) v) : ℂ)
      = Complex.ofReal (∑ o, ∑ z, BornProb (ApplyGate (F o) v) z) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun o _ => by
      rw [Complex.ofReal_sum]
      exact Qatlib.Foundations.PureStateMath.inner_self (ApplyGate (F o) v)
  have hR : Qatlib.Foundations.PureStateMath.Inner v v
      = Complex.ofReal (∑ z, BornProb v z) := by
    rw [Complex.ofReal_sum]
    exact Qatlib.Foundations.PureStateMath.inner_self v
  rw [hL, hR] at key
  exact Complex.ofReal_inj.mp key

end InstrumentMass

section Lift

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- A finite sum of tensor gates with a fixed right factor equals the tensor gate of the sum of
the left factors. -/
theorem sum_tensorGate_left {O : Type} [Fintype O] (A : O → Matrix X X ℂ)
    (B : Matrix Y Y ℂ) :
    ∑ o, TensorGate (A o) B = TensorGate (∑ o, A o) B := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  simp only [Matrix.sum_apply, tensorGate_apply, Finset.sum_mul]

/-- A finite sum of tensor gates with a fixed left factor equals the tensor gate of the sum of
the right factors. -/
theorem sum_tensorGate_right {O : Type} [Fintype O] (A : Matrix X X ℂ)
    (B : O → Matrix Y Y ℂ) :
    ∑ o, TensorGate A (B o) = TensorGate A (∑ o, B o) := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  simp only [Matrix.sum_apply, tensorGate_apply, Finset.mul_sum]

/-- Tensoring each operator of a complete instrument with the identity preserves completeness. -/
theorem instrument_lift_complete {O : Type} [Fintype O]
    (E : O → Matrix X X ℂ) (hE : ∑ o, (E o)ᴴ * (E o) = 1) :
    ∑ o, (TensorGate (E o) (1 : Matrix Y Y ℂ))ᴴ * TensorGate (E o)
        (1 : Matrix Y Y ℂ) = 1 := by
  rw [Finset.sum_congr rfl fun o _ => by
      rw [tensorGate_conjTranspose, matrix_one_conjTranspose, tensorGate_mul,
        Matrix.one_mul],
    sum_tensorGate_left, hE, tensorGate_one]

end Lift

def flagDiag (b : Bool) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun c : Bool => if c = b then 1 else 0

/-- The flag matrix has entry one exactly when both indices equal the selected Boolean flag, and
zero otherwise. -/
theorem flagDiag_apply (b : Bool) (c c' : Bool) :
    flagDiag b c c' = if c = c' then (if c = b then (1 : ℂ) else 0) else 0 := by
  unfold flagDiag
  rw [Matrix.diagonal_apply]

/-- Each Boolean flag matrix is idempotent. -/
theorem flagDiag_mul_self (b : Bool) : flagDiag b * flagDiag b = flagDiag b := by
  unfold flagDiag
  rw [Matrix.diagonal_mul_diagonal]
  refine Matrix.ext fun c c' => ?_
  simp only [Matrix.diagonal_apply]
  by_cases h : c = c'
  · subst c'
    by_cases h2 : c = b <;> simp [h2]
  · simp [h]

/-- Each Boolean flag matrix is self-adjoint. -/
theorem flagDiag_conjTranspose (b : Bool) : (flagDiag b)ᴴ = flagDiag b := by
  unfold flagDiag
  rw [Matrix.diagonal_conjTranspose]
  refine Matrix.ext fun c c' => ?_
  simp only [Matrix.diagonal_apply]
  by_cases h : c = c'
  · subst c'
    by_cases h2 : c = b <;> simp [h2]
  · simp [h]

/-- The two Boolean flag matrices sum to the identity. -/
theorem flagDiag_sum : ∑ b : Bool, flagDiag b = 1 := by
  refine Matrix.ext fun c c' => ?_
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases h : c = c'
  · subst c'
    cases c <;> simp [flagDiag_apply]
  · simp [flagDiag_apply, h, Finset.sum_const_zero]

def flagProjector (I W : Type) [DecidableEq I] [DecidableEq W] (b : Bool) :
    Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  TensorGate (TensorGate (1 : Matrix I I ℂ) (flagDiag b)) (1 : Matrix W W ℂ)

/-- The Gram matrix of a flag projector equals the flag projector itself. -/
theorem flagProjector_idem (I W : Type) [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (b : Bool) :
    (flagProjector I W b)ᴴ * flagProjector I W b = flagProjector I W b := by
  unfold flagProjector
  rw [tensorGate_conjTranspose, tensorGate_conjTranspose,
    matrix_one_conjTranspose, matrix_one_conjTranspose, flagDiag_conjTranspose,
    tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.one_mul,
    flagDiag_mul_self]

/-- The Gram matrices of the two flag projectors sum to the identity. -/
theorem flagProjector_complete (I W : Type) [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] :
    ∑ b : Bool, (flagProjector (I := I) (W := W) b)ᴴ * flagProjector I W b = 1 := by
  rw [Finset.sum_congr rfl fun b _ => flagProjector_idem I W b]
  unfold flagProjector
  rw [sum_tensorGate_left, sum_tensorGate_right, flagDiag_sum, tensorGate_one,
    tensorGate_one]

/-- For `p` between zero and one, a unitary adaptive XOR word preserves total Born mass when
summed over all leaves. -/
theorem adaptive_leaf_mass (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} [Fintype O] [DecidableEq O] {σ : AdaptiveXorWord I W O} :
    IsAdaptiveXorUnitary σ → ∀ v : QState (((I × Bool) × W) × (I → Bool)),
      ∑ ω ∈ adaptiveLeaves σ,
        ∑ z, BornProb (Run (databaseXorOracle p) (adaptiveWord σ ω) v) z
        = ∑ z, BornProb v z := by
  induction σ with
  | nil =>
      intro _ v
      rw [adaptiveLeaves_nil, Finset.sum_singleton, adaptiveWord_nil, run_nil]
  | gate V σ ih =>
      intro hU
      cases hU with
      | gate _ hV hσ =>
        intro v
        have hlift : TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ) ∈
            Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ :=
          tensorGate_unitary hV (Submonoid.one_mem _)
        rw [adaptiveLeaves_gate,
          Finset.sum_congr rfl fun ω _ => by
            rw [adaptiveWord_gate, run_gate],
          ih hσ (ApplyGate (TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ)) v),
          applyGate_bornMass hlift v]
  | query σ ih =>
      intro hU
      cases hU with
      | query hσ =>
        intro v
        rw [adaptiveLeaves_query,
          Finset.sum_congr rfl fun ω _ => by
            rw [adaptiveWord_query, run_query],
          ih hσ (ApplyGate (databaseXorOracle p) v),
          databaseXorOracle_bornMass p hp0 hp1 v]
  | branch E σ ih =>
      intro hU
      cases hU with
      | branch _ hE hσ =>
        intro v
        have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset O)) fun o : O =>
            (adaptiveLeaves (σ o)).image fun l => o :: l := by
          intro o _ o' _ hne
          show Disjoint ((adaptiveLeaves (σ o)).image fun l => o :: l)
              ((adaptiveLeaves (σ o')).image fun l => o' :: l)
          rw [Finset.disjoint_left]
          intro x hx hxmem
          obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨t', -, heq⟩ := Finset.mem_image.mp hxmem
          rw [List.cons.injEq] at heq
          exact hne heq.1.symm
        rw [adaptiveLeaves_branch, Finset.sum_biUnion hdisj,
          Finset.sum_congr rfl fun o _ =>
            Finset.sum_image (fun a _ b _ h => by
              rw [List.cons.injEq] at h
              exact h.2),
          Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun t _ => by
            rw [adaptiveWord_branch_cons, run_gate],
          Finset.sum_congr rfl fun o _ => ih o (hσ o)
            (ApplyGate (TensorGate (E o) (1 : Matrix (I → Bool) (I → Bool) ℂ)) v)]
        exact instrument_family_mass (fun o : O =>
          TensorGate (E o) (1 : Matrix (I → Bool) (I → Bool) ℂ))
          (instrument_lift_complete E hE) v

/-- The leaf masses of a unitary adaptive XOR word sum to one for a normalized initial state and
`p` between zero and one. -/
theorem adaptive_leaf_mass_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} [Fintype O] [DecidableEq O] {σ : AdaptiveXorWord I W O}
    (hσ : IsAdaptiveXorUnitary σ) {v : QState (((I × Bool) × W) × (I → Bool))}
    (hv : Normalized v) :
    ∑ ω ∈ adaptiveLeaves σ,
      ∑ z, BornProb (Run (databaseXorOracle p) (adaptiveWord σ ω) v) z = 1 := by
  rw [adaptive_leaf_mass p hp0 hp1 hσ v]
  exact hv

def AmplitudeQueryBounded (k : ℕ) (d : I → Bool)
    (u : QState (((I × Bool) × W) × (I → Bool))) : Prop :=
  ∀ q : (I × Bool) × W, ∀ e : I → Bool, u (q, e) ≠ 0 →
    ∃ l : List I, XorReachable l d e ∧ l.length ≤ k

/-- A computational basis state with database `d` satisfies the zero-query amplitude bound
relative to `d`. -/
theorem amplitudeQueryBounded_ket (j : I) (b : Bool) (w : W) (d : I → Bool) :
    AmplitudeQueryBounded 0 d (Ket (((j, b), w), d)) := by
  rintro ⟨⟨j', b'⟩, w'⟩ e hne
  by_cases hq : (((j', b'), w'), e) = (((j, b), w), d)
  · simp only [Prod.mk.injEq] at hq
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hq
    exact ⟨[], XorReachable.nil _, by simp⟩
  · exact absurd (by simp [Ket, hq]) hne

/-- Applying a workspace gate tensored with the database identity preserves the amplitude query
bound. -/
theorem amplitudeQueryBounded_applyGate_tensorL
    (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) {k : ℕ} {d : I → Bool}
    {u : QState (((I × Bool) × W) × (I → Bool))} (h : AmplitudeQueryBounded k d u) :
    AmplitudeQueryBounded k d
      (ApplyGate (TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ)) u) := by
  rintro q e hne
  rw [tensor_one_left_slice' V u q e, applyGate_eq_sum] at hne
  obtain ⟨r, hr⟩ := exists_ne_zero_of_sum_ne_zero hne
  have hu : u (r, e) ≠ 0 := fun h0 => hr (by rw [h0, mul_zero])
  exact h r e hu

/-- For `p` between zero and one, applying the database XOR oracle increases the amplitude query
bound by at most one. -/
theorem amplitudeQueryBounded_apply_databaseXorOracle (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) {k : ℕ} {d : I → Bool}
    {u : QState (((I × Bool) × W) × (I → Bool))} (h : AmplitudeQueryBounded k d u) :
    AmplitudeQueryBounded (k + 1) d (ApplyGate (databaseXorOracle p) u) := by
  rintro ⟨⟨j, a⟩, w⟩ e hne
  rw [applyGate_eq_sum] at hne
  obtain ⟨z, hz⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨⟨⟨j₀, b₀⟩, w₀⟩, d₀⟩ := z
  have hentry : databaseXorOracle p (((j, a), w), e) (((j₀, b₀), w₀), d₀) ≠ 0 :=
    fun h0 => hz (by rw [h0, zero_mul])
  have hu : u (((j₀, b₀), w₀), d₀) ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
  have hjw : j₀ = j ∧ w₀ = w := by
    by_contra hcon
    rcases eq_or_ne j₀ j with hj | hj
    · rcases eq_or_ne w₀ w with hw | hw
      · exact hcon ⟨hj, hw⟩
      · exact hentry (databaseXorOracle_offblock p j j₀ a b₀ w w₀ e d₀ (Or.inr (Ne.symm hw)))
    · exact hentry (databaseXorOracle_offblock p j j₀ a b₀ w w₀ e d₀ (Or.inl (Ne.symm hj)))
  rw [← hjw.1, ← hjw.2] at hentry
  obtain ⟨l, hl, hlen⟩ := h ((j₀, b₀), w₀) d₀ hu
  have hloc := databaseXorOracle_locality p hp0 hp1 j₀ a b₀ w₀ e d₀ hentry
  have hwr : e = xorWriteAt j₀ (e j₀) d₀ :=
    xorWriteAt_eq_of_locality j₀ d₀ e (fun k hk => (hloc k hk).symm)
  refine ⟨l ++ [j₀], xorReachable_snoc j₀ hl (e j₀) hwr, ?_⟩
  rw [List.length_append, List.length_singleton]
  omega

/-- Executing a valid adaptive leaf increases the amplitude query bound by at most the query
count of its extracted circuit. -/
theorem amplitudeQueryBounded_run_adaptive_word (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} : ∀ {σ : AdaptiveXorWord I W O} {ω : List O}, IsAdaptiveLeaf σ ω →
      ∀ (k : ℕ) (d : I → Bool) (u : QState (((I × Bool) × W) × (I → Bool))),
        AmplitudeQueryBounded k d u →
        AmplitudeQueryBounded (k + QueryCount (adaptiveWord σ ω)) d
          (Run (databaseXorOracle p) (adaptiveWord σ ω) u) := by
  intro σ ω hleaf
  induction hleaf with
  | nil =>
      intro k d u hu
      rw [adaptiveWord_nil, run_nil]
      simpa using! hu
  | gate V σ _ ih =>
      intro k d u hu
      rw [adaptiveWord_gate, run_gate]
      exact ih k d _ (amplitudeQueryBounded_applyGate_tensorL V hu)
  | query σ _ ih =>
      intro k d u hu
      rw [adaptiveWord_query, run_query, queryCount_query]
      have key : ∀ q : ℕ, k + (q + 1) = k + 1 + q := fun q => by omega
      rw [key]
      exact ih (k + 1) d _
        (amplitudeQueryBounded_apply_databaseXorOracle p hp0 hp1 hu)
  | branch E σ o _ ih =>
      intro k d u hu
      rw [adaptiveWord_branch_cons, run_gate]
      exact ih k d _ (amplitudeQueryBounded_applyGate_tensorL (E o) hu)

/-- Execution from a basis state along a valid adaptive leaf satisfies the amplitude bound given
by its query count. -/
theorem adaptive_leaf_reachable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} {σ : AdaptiveXorWord I W O} {ω : List O} (hleaf : IsAdaptiveLeaf σ ω)
    (j : I) (b : Bool) (w : W) (d : I → Bool) :
    AmplitudeQueryBounded (QueryCount (adaptiveWord σ ω)) d
      (Run (databaseXorOracle p) (adaptiveWord σ ω) (Ket (((j, b), w), d))) := by
  have h := amplitudeQueryBounded_run_adaptive_word p hp0 hp1 hleaf 0 d
    (Ket (((j, b), w), d)) (amplitudeQueryBounded_ket j b w d)
  simpa using! h

/-- A nonzero amplitude reached from the empty database has support size at most the leaf's
query count, and each occupied index occurs in a witnessing XOR update list of that length
bound. -/
theorem adaptive_leaf_from_empty (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} {σ : AdaptiveXorWord I W O} {ω : List O} (hleaf : IsAdaptiveLeaf σ ω)
    (j : I) (b : Bool) (w : W) (q : (I × Bool) × W) (e : I → Bool)
    (hne : Run (databaseXorOracle p) (adaptiveWord σ ω)
        (Ket (((j, b), w), fun _ => false)) (q, e) ≠ 0) :
    databaseCard e ≤ QueryCount (adaptiveWord σ ω) ∧
      ∀ k : I, booleanValuedDatabase e k = some true → ∃ l : List I,
        XorReachable l (fun _ => false) e ∧ l.length ≤ QueryCount (adaptiveWord σ ω)
          ∧ k ∈ l := by
  obtain ⟨l, hreach, hlen⟩ :=
    adaptive_leaf_reachable p hp0 hp1 hleaf j b w (fun _ => false) q e hne
  exact ⟨(xorReachable_from_empty_card hreach).trans hlen,
    fun k hk => ⟨l, hreach, hlen, xorReachable_from_empty_label hreach (by
      by_cases hb : e k = true
      · exact hb
      · unfold booleanValuedDatabase at hk
        rw [ite_eq_right hb] at hk
        exact absurd hk (by simp))⟩⟩

def embedSchedule : List (I ≃ I) → AdaptiveXorWord I W Unit
  | [] => .nil
  | f :: fs => .gate (TensorGate (TensorGate (permGate f) (1 : Matrix Bool Bool ℂ))
      (1 : Matrix W W ℂ)) (.query (embedSchedule fs))

/-- Extracting the empty-outcome circuit of an embedded schedule gives `xorScheduleWord`. -/
theorem adaptiveWord_embedSchedule (fs : List (I ≃ I)) :
    adaptiveWord (embedSchedule (I := I) (W := W) fs) [] = xorScheduleWord fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show adaptiveWord (AdaptiveXorWord.gate _ (AdaptiveXorWord.query
        (embedSchedule fs))) [] = xorScheduleWord (f :: fs)
      rw [adaptiveWord_gate, adaptiveWord_query, ih, xorScheduleWord]
      rfl

/-- The empty outcome list is a valid leaf of every embedded schedule. -/
theorem isAdaptiveLeaf_embedSchedule (fs : List (I ≃ I)) :
    IsAdaptiveLeaf (embedSchedule (I := I) (W := W) fs) [] := by
  induction fs with
  | nil => exact IsAdaptiveLeaf.nil
  | cons f fs ih =>
      exact IsAdaptiveLeaf.gate _ _ (IsAdaptiveLeaf.query _ ih)

/-- Every embedded schedule is a unitary adaptive XOR word. -/
theorem embedSchedule_isAdaptiveXorUnitary (fs : List (I ≃ I)) :
    IsAdaptiveXorUnitary (embedSchedule (I := I) (W := W) fs) := by
  induction fs with
  | nil => exact IsAdaptiveXorUnitary.nil
  | cons f fs ih =>
      refine IsAdaptiveXorUnitary.gate _ ?_ (IsAdaptiveXorUnitary.query ih)
      exact tensorGate_unitary (tensorGate_unitary (permGate_unitary f)
        (Submonoid.one_mem _)) (Submonoid.one_mem _)

/-- The circuit extracted from an embedded schedule has one query per schedule entry. -/
theorem adaptiveWord_embedSchedule_queryCount (fs : List (I ≃ I)) :
    QueryCount (adaptiveWord (embedSchedule (I := I) (W := W) fs) []) = fs.length := by
  rw [adaptiveWord_embedSchedule, xorScheduleWord_queryCount]

/-- A database reached with nonzero amplitude by an embedded schedule has cardinality at most
the initial cardinality plus the schedule length. -/
theorem embedSchedule_leaf_card (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (j : I) (b : Bool) (w : W) (d : I → Bool)
    (q : (I × Bool) × W) (e : I → Bool)
    (h : Run (databaseXorOracle p)
        (adaptiveWord (embedSchedule (I := I) (W := W) fs) [])
        (Ket (((j, b), w), d)) (q, e) ≠ 0) :
    databaseCard e ≤ databaseCard d + fs.length := by
  obtain ⟨l, hl, hlen⟩ := adaptive_leaf_reachable p hp0 hp1
    (isAdaptiveLeaf_embedSchedule fs) j b w d q e h
  have hc := xorReachable_card hl
  rw [adaptiveWord_embedSchedule_queryCount] at hlen
  omega

/-- For a unitary adaptive XOR word, decoding transports each valid leaf, total leaf mass is
preserved, and nonzero amplitudes have XOR update witnesses bounded by the leaf query
count. -/
theorem frontier1 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} [Fintype O] [DecidableEq O] (σ : AdaptiveXorWord I W O)
    (hσ : IsAdaptiveXorUnitary σ) :
    (∀ ω : List O, IsAdaptiveLeaf σ ω →
        ∀ v : QState (((I × Bool) × W) × (I → Bool)),
          ApplyGate (xorDecode p) (Run (databaseXorOracle p) (adaptiveWord σ ω) v)
            = Run xorPurifiedQuery (adaptiveWord σ ω) (ApplyGate (xorDecode p) v)) ∧
    (∀ v : QState (((I × Bool) × W) × (I → Bool)),
        ∑ ω ∈ adaptiveLeaves σ,
          ∑ z, BornProb (Run (databaseXorOracle p) (adaptiveWord σ ω) v) z
          = ∑ z, BornProb v z) ∧
    (∀ ω : List O, IsAdaptiveLeaf σ ω →
        ∀ (j : I) (b : Bool) (w : W) (d : I → Bool) (q : (I × Bool) × W)
          (e : I → Bool),
        Run (databaseXorOracle p) (adaptiveWord σ ω) (Ket (((j, b), w), d)) (q, e) ≠ 0 →
        ∃ l : List I, XorReachable l d e
          ∧ l.length ≤ QueryCount (adaptiveWord σ ω)) :=
  ⟨fun _ω hleaf v => xorDecode_run_transport_adaptive_leaf p hp0 hp1 hleaf v,
    fun v => adaptive_leaf_mass p hp0 hp1 hσ v,
    fun _ω hleaf j b w d q e hne =>
      adaptive_leaf_reachable p hp0 hp1 hleaf j b w d q e hne⟩

/-- A valid leaf marked as a failure still satisfies decoding transport, and its Born mass is at
most the initial Born mass. -/
theorem frontier1_failure_leaves (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {O : Type} [Fintype O] [DecidableEq O] (σ : AdaptiveXorWord I W O)
    (hσ : IsAdaptiveXorUnitary σ) (fail : List O → Bool) {ω : List O}
    (hleaf : IsAdaptiveLeaf σ ω) (_hfail : fail ω = true)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (Run (databaseXorOracle p) (adaptiveWord σ ω) v)
      = Run xorPurifiedQuery (adaptiveWord σ ω) (ApplyGate (xorDecode p) v)
      ∧ ∑ z, BornProb (Run (databaseXorOracle p) (adaptiveWord σ ω) v) z
        ≤ ∑ z, BornProb v z := by
  refine ⟨(frontier1 p hp0 hp1 σ hσ).1 ω hleaf v, ?_⟩
  have hleafmem : ω ∈ adaptiveLeaves σ := mem_adaptiveLeaves hleaf
  rw [← adaptive_leaf_mass p hp0 hp1 hσ v, ← Finset.sum_erase_add _ _ hleafmem]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun ω' _ =>
      Finset.sum_nonneg fun z _ => bornProb_nonneg _ z)

end

end Qatlib.Papers.QMAvsQCMA25.Forrelation.AdaptiveXorDatabaseTransport
