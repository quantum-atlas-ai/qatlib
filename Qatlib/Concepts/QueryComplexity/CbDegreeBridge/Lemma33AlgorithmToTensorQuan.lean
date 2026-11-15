/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbFormsAux
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Lemma33AlgorithmToTensorStat

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Matrix

open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

section DiagPhase

variable {R : Type} [Fintype R] [DecidableEq R]

/-- A diagonal matrix acts coordinatewise by multiplication by its diagonal entries. -/
private theorem diagonal_mulVec_apply (d : R → ℂ) (φ : QState R) (i : R) :
    (Matrix.diagonal d *ᵥ φ) i = d i * φ i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl]
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Multiplication by a diagonal matrix with unit-norm entries preserves measurement probability
on every finite event. -/
private theorem measureProb_diagonal_unit (d : R → ℂ) (hd : ∀ i, ‖d i‖ = 1) (φ : QState R)
    (S : Finset R) :
    MeasureProb (Matrix.diagonal d *ᵥ φ) S = MeasureProb φ S := by
  refine Finset.sum_congr rfl fun i _ => ?_
  show ‖(Matrix.diagonal d *ᵥ φ) i‖ ^ 2 = ‖φ i‖ ^ 2
  rw [diagonal_mulVec_apply, norm_mul, hd, one_mul]

/-- Each completely bounded phase entry has norm one. -/
private theorem cbPhaseEntry_norm {n : ℕ} (x : Fin n → Bool) (o : Option (Fin n ⊕ Fin n)) :
    ‖cbPhaseEntry x o‖ = 1 := by
  cases o with
  | none => simp [cbPhaseEntry]
  | some k =>
    cases k with
    | inl i =>
      show ‖(if x i then (1 : ℂ) else -1)‖ = 1
      split <;> simp
    | inr i => simp [cbPhaseEntry]

/-- Repeated phase-oracle queries preserve measurement probability on every finite event. -/
private theorem measureProb_run_replicate_query {n : ℕ} (δ : R → Option (Fin n ⊕ Fin n))
    (x : Fin n → Bool) (k : ℕ) (φ : QState R) (S : Finset R) :
    MeasureProb (Run (cbPhaseOracle δ x) (List.replicate k Step.query) φ) S
      = MeasureProb φ S := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, run_query, ih (ApplyGate (cbPhaseOracle δ x) φ)]
    show MeasureProb ((Matrix.diagonal fun r => cbPhaseEntry x (δ r)) *ᵥ φ) S
      = MeasureProb φ S
    exact measureProb_diagonal_unit _ (fun i => cbPhaseEntry_norm x (δ i)) φ S

/-- Repeated phase-oracle queries preserve `signBias`. -/
private theorem signBias_run_replicate_query {n : ℕ} (δ : R → Option (Fin n ⊕ Fin n))
    (x : Fin n → Bool) (k : ℕ) (φ : QState R) (E : Finset R) :
    signBias (Run (cbPhaseOracle δ x) (List.replicate k Step.query) φ) E
      = signBias φ E := by
  show MeasureProb (Run (cbPhaseOracle δ x) (List.replicate k Step.query) φ) E
      - MeasureProb (Run (cbPhaseOracle δ x) (List.replicate k Step.query) φ) Eᶜ
    = MeasureProb φ E - MeasureProb φ Eᶜ
  rw [measureProb_run_replicate_query δ x k φ E, measureProb_run_replicate_query δ x k φ Eᶜ]

/-- A list of `k` query steps has query count `k`. -/
private theorem queryCount_replicate_query (k : ℕ) :
    QueryCount (List.replicate k (Step.query : Step R)) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, queryCount_query, ih]

/-- A circuit consisting entirely of query steps satisfies `IsUnitaryCircuit`. -/
private theorem isUnitaryCircuit_replicate_query (k : ℕ) :
    IsUnitaryCircuit (List.replicate k (Step.query : Step R)) := by
  intro U hU
  obtain ⟨_, h⟩ := List.mem_replicate.mp hU
  simp at h

/-- Complex conjugation fixes every completely bounded phase entry. -/
private theorem cbPhaseEntry_conj {n : ℕ} (x : Fin n → Bool) (o : Option (Fin n ⊕ Fin n)) :
    (starRingEnd ℂ) (cbPhaseEntry x o) = cbPhaseEntry x o := by
  cases o with
  | none => exact map_one _
  | some k =>
    cases k with
    | inl i =>
      show (starRingEnd ℂ) (if x i then (1 : ℂ) else -1) = if x i then (1 : ℂ) else -1
      split <;> simp
    | inr i => exact map_one _

/-- The completely bounded phase oracle is self-adjoint. -/
private theorem cbPhaseOracle_conjTranspose {n : ℕ} (δ : R → Option (Fin n ⊕ Fin n))
    (x : Fin n → Bool) :
    (cbPhaseOracle δ x)ᴴ = cbPhaseOracle δ x := by
  ext a b
  show (starRingEnd ℂ) ((Matrix.diagonal fun r => cbPhaseEntry x (δ r)) b a)
    = (Matrix.diagonal fun r => cbPhaseEntry x (δ r)) a b
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl]
    exact cbPhaseEntry_conj x _
  · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab, map_zero]

/-- Complex conjugation fixes every entry of `signVecC`. -/
private theorem signVecC_conj {n : ℕ} (x : Fin n → Bool) (k : Fin n ⊕ Fin n) :
    (starRingEnd ℂ) (signVecC x k) = signVecC x k := by
  cases k with
  | inl i =>
    show (starRingEnd ℂ) (if x i then (1 : ℂ) else -1) = if x i then (1 : ℂ) else -1
    split <;> simp
  | inr i => exact map_one _

/-- Evaluating `dzO` on a Boolean sign vector gives the corresponding phase entry. -/
private theorem dzO_signVecC {n : ℕ} (x : Fin n → Bool) (o : Option (Fin n ⊕ Fin n)) :
    dzO (signVecC x) o = cbPhaseEntry x o := by
  cases o with
  | none => rfl
  | some k =>
    cases k with
    | inl _ => rfl
    | inr _ => rfl

/-- Evaluating `cbDelta` on a Boolean sign vector gives the completely bounded phase oracle. -/
private theorem cbDelta_signVecC_eq_oracle {n : ℕ} (δ : R → Option (Fin n ⊕ Fin n))
    (x : Fin n → Bool) :
    cbDelta δ (signVecC x) = cbPhaseOracle δ x := by
  ext a b
  rw [cbDelta_apply]
  show (if a = b then dzval δ (signVecC x) a else 0)
    = (Matrix.diagonal fun r => cbPhaseEntry x (δ r)) a b
  rw [Matrix.diagonal_apply]
  by_cases hab : a = b
  · rw [ite_eq_left hab, ite_eq_left hab, dzval_eq_dzO, dzO_signVecC]
  · rw [ite_eq_right hab, ite_eq_right hab]

end DiagPhase

section TotalLabel

variable {n : ℕ}

private noncomputable def cbTotalLabel {R : Type} (δ : R → Option (Fin n ⊕ Fin n)) (i0 : Fin n) :
    R → Option (Fin n ⊕ Fin n) :=
  fun r => some (match δ r with | none => Sum.inr i0 | some k => k)

/-- The totalized label function always takes a value of the form `some k`. -/
private theorem cbTotalLabel_eq_some {R : Type} (δ : R → Option (Fin n ⊕ Fin n)) (i0 : Fin n)
    (r : R) :
    ∃ k, cbTotalLabel δ i0 r = some k :=
  ⟨match δ r with | none => Sum.inr i0 | some k => k, rfl⟩

/-- Totalizing the label function preserves its phase entries on Boolean inputs. -/
private theorem cbPhaseEntry_total {R : Type} (δ : R → Option (Fin n ⊕ Fin n)) (i0 : Fin n)
    (x : Fin n → Bool) (r : R) :
    cbPhaseEntry x (cbTotalLabel δ i0 r) = cbPhaseEntry x (δ r) := by
  cases h : δ r with
  | none => simp only [cbTotalLabel, h]; rfl
  | some k => simp only [cbTotalLabel, h]

/-- Totalizing the label function preserves the completely bounded phase oracle. -/
private theorem cbPhaseOracle_total {R : Type} [Fintype R] [DecidableEq R]
    (δ : R → Option (Fin n ⊕ Fin n)) (i0 : Fin n) (x : Fin n → Bool) :
    cbPhaseOracle (cbTotalLabel δ i0) x = cbPhaseOracle δ x := by
  show Matrix.diagonal (fun r => cbPhaseEntry x (cbTotalLabel δ i0 r))
    = Matrix.diagonal (fun r => cbPhaseEntry x (δ r))
  congr 1
  funext r
  exact cbPhaseEntry_total δ i0 x r

end TotalLabel

section GateBlocks

variable {R : Type} [Fintype R] [DecidableEq R]

private noncomputable def gateBlocks : Circuit R → List (Matrix R R ℂ)
  | [] => [1]
  | Step.query :: C => 1 :: gateBlocks C
  | Step.gate U :: C =>
      match gateBlocks C with
      | [] => [U]
      | M :: rest => (M * U) :: rest

/-- The gate blocks of the empty circuit form the singleton list containing the identity. -/
private theorem gateBlocks_nil : gateBlocks ([] : Circuit R) = [1] := rfl

/-- Prepending a query prepends an identity block to the gate-block list. -/
private theorem gateBlocks_query (C : Circuit R) :
    gateBlocks (Step.query :: C) = 1 :: gateBlocks C := rfl

/-- Prepending a gate multiplies it into the first gate block, or creates a singleton block if
the block list is empty. -/
private theorem gateBlocks_gate (U : Matrix R R ℂ) (C : Circuit R) :
    gateBlocks (Step.gate U :: C)
      = match gateBlocks C with | [] => [U] | M :: rest => (M * U) :: rest := rfl

/-- The gate-block list of every circuit is nonempty. -/
private theorem gateBlocks_ne_nil (C : Circuit R) : gateBlocks C ≠ [] := by
  induction C with
  | nil => simp [gateBlocks_nil]
  | cons s C _ =>
    cases s with
    | query => simp [gateBlocks_query]
    | gate U =>
      rw [gateBlocks_gate]
      cases gateBlocks C <;> simp

/-- The number of gate blocks equals the circuit query count plus one. -/
private theorem gateBlocks_length (C : Circuit R) :
    (gateBlocks C).length = QueryCount C + 1 := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | query =>
      rw [gateBlocks_query, List.length_cons, ih]
      rfl
    | gate U =>
      rw [gateBlocks_gate]
      cases h : gateBlocks C with
      | nil => exact absurd h (gateBlocks_ne_nil C)
      | cons M rest =>
        have hlen : (M :: rest).length = QueryCount C + 1 := h ▸ ih
        simp only [List.length_cons] at hlen ⊢
        show rest.length + 1 = QueryCount C + 1
        omega

/-- Every gate block of a unitary circuit is unitary. -/
private theorem gateBlocks_unitary {C : Circuit R} (hC : IsUnitaryCircuit C) :
    ∀ M ∈ gateBlocks C, M ∈ Matrix.unitaryGroup R ℂ := by
  induction C with
  | nil =>
    intro M hM
    rw [gateBlocks_nil, List.mem_singleton] at hM
    rw [hM]
    exact one_mem _
  | cons s C ih =>
    cases s with
    | query =>
      intro M hM
      rw [gateBlocks_query, List.mem_cons] at hM
      rcases hM with hM | hM
      · rw [hM]
        exact one_mem _
      · exact ih ((isUnitaryCircuit_query C).mp hC) M hM
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      intro M hM
      cases h : gateBlocks C with
      | nil => exact absurd h (gateBlocks_ne_nil C)
      | cons M₀ rest =>
        have hgg : gateBlocks (Step.gate U :: C) = (M₀ * U) :: rest := by
          rw [gateBlocks_gate, h]
        rw [hgg, List.mem_cons] at hM
        rcases hM with hM | hM
        · rw [hM]
          have h0 : M₀ ∈ gateBlocks C := by
            rw [h]
            exact List.mem_cons_self
          exact mul_mem (ih hC' M₀ h0) hU
        · have hmem : M ∈ gateBlocks C := by
            rw [h]
            exact List.mem_cons_of_mem M₀ hM
          exact ih hC' M hmem

private noncomputable def cbInterleave (O : Matrix R R ℂ) : List (Matrix R R ℂ) → Matrix R R ℂ
  | [] => 1
  | [G] => G
  | G :: B :: rest => cbInterleave O (B :: rest) * O * G

/-- Interleaving an oracle with an empty matrix list gives the identity. -/
private theorem cbInterleave_nil (O : Matrix R R ℂ) : cbInterleave O [] = 1 := rfl

/-- Interleaving an oracle with a singleton gate list gives that gate. -/
private theorem cbInterleave_single (O : Matrix R R ℂ) (G : Matrix R R ℂ) :
    cbInterleave O [G] = G := rfl

/-- Expands interleaving on a list with at least two gates into the remaining interleaving, the
oracle, and the first gate. -/
private theorem cbInterleave_cons_cons (O G B : Matrix R R ℂ) (rest : List (Matrix R R ℂ)) :
    cbInterleave O (G :: B :: rest) = cbInterleave O (B :: rest) * O * G := rfl

/-- For a nonempty tail, interleaving factors as the tail interleaving times the oracle times
the head gate. -/
private theorem cbInterleave_cons (O G : Matrix R R ℂ) (rest : List (Matrix R R ℂ))
    (hrest : rest ≠ []) :
    cbInterleave O (G :: rest) = cbInterleave O rest * O * G := by
  cases rest with
  | nil => exact absurd rfl hrest
  | cons B rest' => rfl

/-- Gate application equals matrix-vector multiplication. -/
private theorem applyGate_eq_mulVec (U : Matrix R R ℂ) (ψ : QState R) :
    ApplyGate U ψ = U *ᵥ ψ := rfl

/-- Running a circuit equals applying the matrix obtained by interleaving its gate blocks with
the oracle. -/
private theorem run_eq_interleave (oracle : Matrix R R ℂ) (C : Circuit R) (ψ : QState R) :
    Run oracle C ψ = cbInterleave oracle (gateBlocks C) *ᵥ ψ := by
  induction C generalizing ψ with
  | nil =>
    rw [gateBlocks_nil, cbInterleave_single, Matrix.one_mulVec]
    rfl
  | cons s C ih =>
    cases s with
    | query =>
      rw [run_query, ih (ApplyGate oracle ψ), applyGate_eq_mulVec,
        gateBlocks_query, cbInterleave_cons oracle 1 (gateBlocks C) (gateBlocks_ne_nil C),
        mul_one, ← Matrix.mulVec_mulVec]
    | gate U =>
      rw [run_gate, ih (ApplyGate U ψ), applyGate_eq_mulVec, gateBlocks_gate]
      cases h : gateBlocks C with
      | nil => exact absurd h (gateBlocks_ne_nil C)
      | cons M rest =>
        cases rest with
        | nil =>
          rw [cbInterleave_single, cbInterleave_single, Matrix.mulVec_mulVec]
        | cons B rest' =>
          rw [cbInterleave_cons_cons, cbInterleave_cons_cons,
            ← Matrix.mulVec_mulVec (U *ᵥ ψ)
              (cbInterleave oracle (B :: rest') * oracle) M,
            ← Matrix.mulVec_mulVec ψ
              (cbInterleave oracle (B :: rest') * oracle) (M * U),
            ← Matrix.mulVec_mulVec ψ M U]

end GateBlocks

section Sandwich

variable {R : Type} [Fintype R] [DecidableEq R]

private noncomputable def sandProd (D : Matrix R R ℂ) : List (Matrix R R ℂ) → Matrix R R ℂ
  | [] => 1
  | [W] => W
  | W :: X :: rest => W * D * sandProd D (X :: rest)

/-- The sandwich product of an empty list is the identity. -/
private theorem sandProd_nil (D : Matrix R R ℂ) : sandProd D [] = 1 := rfl

/-- The sandwich product of a singleton list is its sole matrix. -/
private theorem sandProd_single (D W : Matrix R R ℂ) : sandProd D [W] = W := rfl

/-- Expands the sandwich product of a list with at least two matrices at its first matrix. -/
private theorem sandProd_cons_cons (D W X : Matrix R R ℂ) (rest : List (Matrix R R ℂ)) :
    sandProd D (W :: X :: rest) = W * D * sandProd D (X :: rest) := rfl

/-- For a nonempty tail, the sandwich product factors as the head matrix, the fixed intervening
matrix, and the tail product. -/
private theorem sandProd_cons (D W : Matrix R R ℂ) (rest : List (Matrix R R ℂ))
    (hrest : rest ≠ []) :
    sandProd D (W :: rest) = W * D * sandProd D rest := by
  cases rest with
  | nil => exact absurd rfl hrest
  | cons X rest' => rfl

/-- Appending a matrix to a nonempty sandwich-product list multiplies the previous product by
the intervening matrix and the appended matrix. -/
private theorem sandProd_snoc (D W : Matrix R R ℂ) (Ws : List (Matrix R R ℂ)) (hWs : Ws ≠ []) :
    sandProd D (Ws ++ [W]) = sandProd D Ws * D * W := by
  induction Ws with
  | nil => exact absurd rfl hWs
  | cons G tail ih =>
    cases tail with
    | nil =>
      show sandProd D ([G] ++ [W]) = sandProd D [G] * D * W
      rw [List.singleton_append]
      rfl
    | cons X rest' =>
      have hne : (X :: rest') ≠ [] := List.cons_ne_nil _ _
      have happ : (G :: X :: rest') ++ [W] = G :: ((X :: rest') ++ [W]) := rfl
      rw [happ, sandProd_cons D G _ (by
          rw [List.cons_append]
          exact List.cons_ne_nil _ _), sandProd_cons_cons, ih hne]
      noncomm_ring

/-- The sandwich product of a nonempty list followed by the intervening matrix equals the list
product of the corresponding right-multiplied matrices. -/
private theorem sandProd_mul_eq (D : Matrix R R ℂ) (l : List (Matrix R R ℂ)) (hl : l ≠ []) :
    sandProd D l * D = (l.map fun W => W * D).prod := by
  induction l with
  | nil => exact absurd rfl hl
  | cons W tail ih =>
    cases tail with
    | nil =>
      rw [sandProd_single, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
    | cons X rest' =>
      rw [sandProd_cons_cons, mul_assoc, ih (List.cons_ne_nil _ _),
        List.map_cons (f := fun W' => W' * D) (a := W) (l := X :: rest'), List.prod_cons]

private noncomputable def palW : List (Matrix R R ℂ) → Matrix R R ℂ → List (Matrix R R ℂ)
  | [], QE => [QE]
  | [G], QE => [Gᴴ * QE * G]
  | G :: B :: rest, QE => Gᴴ :: (palW (B :: rest) QE ++ [G])

/-- The palindromic matrix list of an empty gate list consists of the central matrix. -/
private theorem palW_nil (QE : Matrix R R ℂ) : palW [] QE = [QE] := rfl

/-- For a singleton gate list, the palindromic list consists of the central matrix conjugated by
that gate. -/
private theorem palW_single (G QE : Matrix R R ℂ) : palW [G] QE = [Gᴴ * QE * G] := rfl

/-- Expands the palindromic matrix list by placing the first gate's adjoint at the front and the
gate itself at the end. -/
private theorem palW_cons_cons (G B QE : Matrix R R ℂ) (rest : List (Matrix R R ℂ)) :
    palW (G :: B :: rest) QE = Gᴴ :: (palW (B :: rest) QE ++ [G]) := rfl

/-- Every palindromic matrix list is nonempty. -/
private theorem palW_ne_nil (Gs : List (Matrix R R ℂ)) (QE : Matrix R R ℂ) : palW Gs QE ≠ [] := by
  match Gs with
  | [] => simp [palW_nil]
  | [G] => simp [palW_single]
  | G :: B :: rest => rw [palW_cons_cons]; simp

/-- For a nonempty gate list, the palindromic list has twice its length minus one entries. -/
private theorem palW_length (Gs : List (Matrix R R ℂ)) (QE : Matrix R R ℂ) :
    Gs ≠ [] → (palW Gs QE).length = 2 * Gs.length - 1 := by
  induction Gs with
  | nil => intro h; exact absurd rfl h
  | cons G tail ih =>
    intro _
    cases tail with
    | nil => rfl
    | cons B rest =>
      rw [palW_cons_cons, List.length_cons, List.length_append, List.length_singleton]
      have h := ih (List.cons_ne_nil _ _)
      simp only [List.length_cons] at h ⊢
      omega

/-- For a self-adjoint intervening matrix, the palindromic sandwich product equals conjugation
of the central matrix by the interleaved gate product. -/
private theorem pal_eq (Gs : List (Matrix R R ℂ)) (D QE : Matrix R R ℂ) (hD : Dᴴ = D) :
    sandProd D (palW Gs QE) = (cbInterleave D Gs)ᴴ * QE * cbInterleave D Gs := by
  induction Gs with
  | nil =>
    rw [palW_nil, sandProd_single, cbInterleave_nil, Matrix.conjTranspose_one, one_mul,
      mul_one]
  | cons G tail ih =>
    cases tail with
    | nil =>
      rw [palW_single, sandProd_single, cbInterleave_single]
    | cons B rest =>
      rw [cbInterleave_cons_cons, palW_cons_cons,
        sandProd_cons D Gᴴ _ (by simp), sandProd_snoc D G _ (palW_ne_nil _ _), ih,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD]
      noncomm_ring

end Sandwich

section Norms

variable {R : Type} [Fintype R] [DecidableEq R]

/-- A unitary matrix has operator norm at most one. -/
private theorem unitary_norm_le {U : Matrix R R ℂ} (hU : U ∈ Matrix.unitaryGroup R ℂ) :
    ‖U‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le zero_le_one U fun v => ?_
  have hsq : ‖toEuclidean_fromVec (U *ᵥ v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    have h := sum_normSq_mulVec_of_mem_unitaryGroup hU v
    simp_rw [Complex.normSq_eq_norm_sq] at h
    exact h
  have heq : ‖toEuclidean_fromVec (U *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ := by
    calc ‖toEuclidean_fromVec (U *ᵥ v)‖
        = Real.sqrt (‖toEuclidean_fromVec (U *ᵥ v)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖toEuclidean_fromVec v‖ ^ 2) := by rw [hsq]
      _ = ‖toEuclidean_fromVec v‖ := Real.sqrt_sq (norm_nonneg _)
  rw [heq, one_mul]

private noncomputable def signDiag (E : Finset R) : Matrix R R ℂ :=
  Matrix.diagonal fun r => if r ∈ E then 1 else -1

/-- The sign diagonal acts by multiplication by one on the event and minus one off the event. -/
private theorem signDiag_mulVec (E : Finset R) (φ : QState R) (i : R) :
    (signDiag E *ᵥ φ) i = (if i ∈ E then (1 : ℂ) else -1) * φ i :=
  diagonal_mulVec_apply _ _ _

/-- The operator norm of the sign diagonal is at most one. -/
private theorem signDiag_norm_le (E : Finset R) : ‖signDiag E‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le zero_le_one _ fun v => ?_
  have hsq : ‖toEuclidean_fromVec (signDiag E *ᵥ v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [signDiag_mulVec]
    split <;> simp
  have heq : ‖toEuclidean_fromVec (signDiag E *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ := by
    calc ‖toEuclidean_fromVec (signDiag E *ᵥ v)‖
        = Real.sqrt (‖toEuclidean_fromVec (signDiag E *ᵥ v)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖toEuclidean_fromVec v‖ ^ 2) := by rw [hsq]
      _ = ‖toEuclidean_fromVec v‖ := Real.sqrt_sq (norm_nonneg _)
  rw [heq, one_mul]

private noncomputable def conjMat (A : Matrix R R ℂ) : Matrix R R ℂ :=
  Matrix.of fun a b => (starRingEnd ℂ) (A a b)

/-- The entries of `conjMat` are the complex conjugates of the original matrix entries. -/
private theorem conjMat_apply (A : Matrix R R ℂ) (a b : R) :
    conjMat A a b = (starRingEnd ℂ) (A a b) := rfl

/-- Applying the entrywise conjugate matrix equals conjugating the result of applying the
original matrix to the conjugate vector. -/
private theorem conjMat_mulVec (A : Matrix R R ℂ) (v : QState R) :
    conjMat A *ᵥ v
      = fun i => (starRingEnd ℂ) ((A *ᵥ fun j => (starRingEnd ℂ) (v j)) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, conjMat_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, starRingEnd_self_apply]

/-- Entrywise complex conjugation preserves a state's Euclidean norm. -/
private theorem norm_toEuclidean_conj (w : QState R) :
    ‖toEuclidean_fromVec (fun i => (starRingEnd ℂ) (w i))‖ = ‖toEuclidean_fromVec w‖ := by
  have hsq : ‖toEuclidean_fromVec (fun i => (starRingEnd ℂ) (w i))‖ ^ 2
      = ‖toEuclidean_fromVec w‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.norm_conj]
  calc ‖toEuclidean_fromVec (fun i => (starRingEnd ℂ) (w i))‖
      = Real.sqrt (‖toEuclidean_fromVec (fun i => (starRingEnd ℂ) (w i))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖toEuclidean_fromVec w‖ ^ 2) := by rw [hsq]
    _ = ‖toEuclidean_fromVec w‖ := Real.sqrt_sq (norm_nonneg _)

/-- Entrywise complex conjugation does not increase matrix operator norm. -/
private theorem conjMat_norm_le (A : Matrix R R ℂ) : ‖conjMat A‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_mulVec_le (norm_nonneg _) _ fun v => ?_
  rw [conjMat_mulVec, norm_toEuclidean_conj]
  calc ‖toEuclidean_fromVec (A *ᵥ fun j => (starRingEnd ℂ) (v j))‖
      ≤ ‖A‖ * ‖toEuclidean_fromVec (fun j => (starRingEnd ℂ) (v j))‖ :=
        l2_norm_mulVec_fromVec_le _ _
    _ = ‖A‖ * ‖toEuclidean_fromVec v‖ := by rw [norm_toEuclidean_conj]

/-- If the gates and central matrix have norm at most one, every matrix in the palindromic list
has norm at most one. -/
private theorem palW_norm_le (Gs : List (Matrix R R ℂ)) (QE : Matrix R R ℂ)
    (hG : ∀ G ∈ Gs, ‖G‖ ≤ 1) (hQE : ‖QE‖ ≤ 1) :
    ∀ X ∈ palW Gs QE, ‖X‖ ≤ 1 := by
  induction Gs with
  | nil =>
    intro X hX
    rw [palW_nil, List.mem_singleton] at hX
    rwa [hX]
  | cons G tail ih =>
    cases tail with
    | nil =>
      intro X hX
      rw [palW_single, List.mem_singleton] at hX
      rw [hX]
      have hGG := hG G List.mem_cons_self
      have hGs : ‖Gᴴ‖ ≤ 1 := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact hGG
      calc ‖Gᴴ * QE * G‖ ≤ ‖Gᴴ * QE‖ * ‖G‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (‖Gᴴ‖ * ‖QE‖) * ‖G‖ :=
            mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
        _ ≤ (1 * 1) * 1 :=
            mul_le_mul (mul_le_mul hGs hQE (norm_nonneg _) zero_le_one) hGG
              (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    | cons B rest =>
      intro X hX
      rw [palW_cons_cons, List.mem_cons] at hX
      rcases hX with hX | hX
      · rw [hX, Matrix.l2_opNorm_conjTranspose]
        exact hG G List.mem_cons_self
      · rw [List.mem_append, List.mem_singleton] at hX
        rcases hX with hX | hX
        · exact ih (fun G' hG' => hG G' (List.mem_cons_of_mem G hG')) X hX
        · rw [hX]
          exact hG G List.mem_cons_self

private noncomputable def listW {s : ℕ} (l : List (Matrix R R ℂ)) (hl : l.length = s + 1) :
    Fin (s + 1) → Matrix R R ℂ :=
  fun m => l[(m : ℕ)]'(by rw [hl]; exact m.isLt)

/-- Enumerating `listW` over its finite index range recovers the original matrix list. -/
private theorem finRange_map_listW {s : ℕ} (l : List (Matrix R R ℂ)) (hl : l.length = s + 1) :
    ((List.finRange (s + 1)).map (listW l hl)) = l := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, hl]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_finRange]
    rfl

/-- When all diagonal factors agree with a fixed matrix, `cbSandwichMatrix` equals the
corresponding sandwich product. -/
private theorem cbSandwichMatrix_eq_sandProd {κ : Type} [Fintype κ] {s : ℕ}
    (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ) (D : Matrix R R ℂ)
    (z : Fin s → κ → ℂ) (hz : ∀ j, cbDelta δ (z j) = D) :
    cbSandwichMatrix W δ z = sandProd D ((List.finRange (s + 1)).map W) := by
  have hF : (fun j : Fin s => W j.castSucc * cbDelta δ (z j))
      = fun j : Fin s => W j.castSucc * D := funext fun j => by rw [hz j]
  show matProdFin s (fun j => W j.castSucc * cbDelta δ (z j)) * W (Fin.last s) = _
  rw [hF]
  cases s with
  | zero =>
    rw [List.finRange_succ, List.finRange_zero, List.map_nil, List.map_cons,
      List.map_nil, sandProd_single]
    show ((List.finRange 0).map (fun j : Fin 0 => W j.castSucc * D)).prod * W (Fin.last 0)
      = W 0
    rw [List.finRange_zero, List.map_nil, List.prod_nil, one_mul]
    rfl
  | succ s =>
    show ((List.finRange (s + 1)).map (fun j => W j.castSucc * D)).prod
        * W (Fin.last (s + 1)) = _
    have hsplit : List.finRange (s + 1 + 1)
        = (List.finRange (s + 1)).map Fin.castSucc ++ [Fin.last (s + 1)] :=
      List.finRange_succ_last
    rw [hsplit, List.map_append, List.map_map, List.map_singleton]
    have hne : (List.finRange (s + 1)).map (W ∘ Fin.castSucc) ≠ [] := by
      intro h
      have h2 := congrArg List.length h
      simp [List.length_map] at h2
    rw [sandProd_snoc D (W (Fin.last (s + 1))) _ hne, sandProd_mul_eq _ _ hne,
      List.map_map]
    rfl

end Norms

section InnerLemmas

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Moves a matrix across `Inner` by applying its conjugate transpose to the first argument. -/
private theorem inner_mulVec_conjTranspose (A : Matrix R R ℂ) (u v : QState R) :
    Qatlib.Foundations.PureStateMath.Inner u (A *ᵥ v) = Qatlib.Foundations.PureStateMath.Inner (Aᴴ *ᵥ u) v := by
  unfold Qatlib.Foundations.PureStateMath.Inner
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- Scaling the first argument of `Inner` multiplies the inner product by the conjugate scalar. -/
private theorem inner_smul_left (ξ : QState R) (c : ℂ) (w : QState R) :
    Qatlib.Foundations.PureStateMath.Inner (c • ξ) w = (starRingEnd ℂ) c * Qatlib.Foundations.PureStateMath.Inner ξ w := by
  rw [inner_apply, inner_apply]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.sum_congr rfl (fun i _ => mul_assoc _ _ _), ← Finset.mul_sum]

/-- A finite sum weighted by event signs equals the sum over the event minus the sum over its
complement. -/
private theorem sum_ite_sign (E : Finset R) (f : R → ℝ) :
    ∑ i, (if i ∈ E then (1 : ℝ) else -1) * f i
      = ∑ i ∈ E, f i - ∑ i ∈ Eᶜ, f i := by
  have h1 : (∑ i ∈ E, (if i ∈ E then (1 : ℝ) else -1) * f i) = ∑ i ∈ E, f i :=
    Finset.sum_congr rfl fun i hi => by rw [ite_eq_left hi, one_mul]
  have h2 : (∑ i ∈ Eᶜ, (if i ∈ E then (1 : ℝ) else -1) * f i) = -∑ i ∈ Eᶜ, f i := by
    have h2a : (∑ i ∈ Eᶜ, (if i ∈ E then (1 : ℝ) else -1) * f i) = ∑ i ∈ Eᶜ, -f i :=
      Finset.sum_congr rfl fun i hi => by rw [ite_eq_right (Finset.mem_compl.mp hi), neg_one_mul]
    rw [h2a, Finset.sum_neg_distrib]
  rw [← Finset.sum_add_sum_compl E (fun i => (if i ∈ E then (1 : ℝ) else -1) * f i),
    h1, h2, sub_eq_add_neg]

/-- The inner product with the sign diagonal equals the complex coercion of `signBias`. -/
private theorem signBias_eq_inner (φ : QState R) (E : Finset R) :
    Qatlib.Foundations.PureStateMath.Inner φ (signDiag E *ᵥ φ) = (signBias φ E : ℂ) := by
  have hstep : ∀ i : R, (starRingEnd ℂ) (φ i) * (signDiag E *ᵥ φ) i
      = ((if i ∈ E then (1 : ℝ) else -1) * ‖φ i‖ ^ 2 : ℝ) := by
    intro i
    rw [signDiag_mulVec]
    by_cases hi : i ∈ E
    · rw [ite_eq_left hi, ite_eq_left hi, one_mul, one_mul, ← Complex.normSq_eq_norm_sq]
      exact Complex.normSq_eq_conj_mul_self.symm
    · rw [ite_eq_right hi, ite_eq_right hi, neg_one_mul, neg_one_mul, Complex.ofReal_neg, mul_neg,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [inner_apply, Finset.sum_congr rfl (fun i _ => hstep i), ← Complex.ofReal_sum,
    sum_ite_sign]
  rfl

end InnerLemmas

section BDiag

variable {R : Type} [Fintype R] [DecidableEq R]

private noncomputable def bdiag (A B : Matrix R R ℂ) : Matrix (R ⊕ R) (R ⊕ R) ℂ :=
  Matrix.of fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => A a b
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr a, Sum.inr b => B a b

/-- The upper-left block of `bdiag A B` is `A`. -/
private theorem bdiag_inl_inl (A B : Matrix R R ℂ) (a b : R) :
    bdiag A B (Sum.inl a) (Sum.inl b) = A a b := rfl

/-- The upper-right block of `bdiag A B` is zero. -/
private theorem bdiag_inl_inr (A B : Matrix R R ℂ) (a b : R) :
    bdiag A B (Sum.inl a) (Sum.inr b) = 0 := rfl

/-- The lower-left block of `bdiag A B` is zero. -/
private theorem bdiag_inr_inl (A B : Matrix R R ℂ) (a b : R) :
    bdiag A B (Sum.inr a) (Sum.inl b) = 0 := rfl

/-- The lower-right block of `bdiag A B` is `B`. -/
private theorem bdiag_inr_inr (A B : Matrix R R ℂ) (a b : R) :
    bdiag A B (Sum.inr a) (Sum.inr b) = B a b := rfl

/-- The block diagonal of two identity matrices is the identity. -/
private theorem bdiag_one : bdiag (1 : Matrix R R ℂ) 1 = 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [bdiag_inl_inl, bdiag_inl_inr, bdiag_inr_inl, bdiag_inr_inr, Matrix.one_apply]

/-- Multiplication of block diagonal matrices multiplies their corresponding diagonal blocks. -/
private theorem bdiag_mul (A B C D : Matrix R R ℂ) :
    bdiag A B * bdiag C D = bdiag (A * C) (B * D) := by
  ext x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      rw [bdiag_inl_inl, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
      have hzero : (∑ a₂ : R,
          bdiag A B (Sum.inl a) (Sum.inr a₂) * bdiag C D (Sum.inr a₂) (Sum.inl b)) = 0 := by
        refine Finset.sum_eq_zero fun a₂ _ => ?_
        rw [bdiag_inl_inr, zero_mul]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [bdiag_inl_inl, bdiag_inl_inl]
    | inr b =>
      rw [bdiag_inl_inr, Matrix.mul_apply, Fintype.sum_sum_type]
      have hz1 : (∑ a' : R,
          bdiag A B (Sum.inl a) (Sum.inl a') * bdiag C D (Sum.inl a') (Sum.inr b)) = 0 := by
        refine Finset.sum_eq_zero fun a' _ => ?_
        rw [bdiag_inl_inl, bdiag_inl_inr, mul_zero]
      have hz2 : (∑ b' : R,
          bdiag A B (Sum.inl a) (Sum.inr b') * bdiag C D (Sum.inr b') (Sum.inr b)) = 0 := by
        refine Finset.sum_eq_zero fun b' _ => ?_
        rw [bdiag_inl_inr, zero_mul]
      rw [hz1, hz2, add_zero]
  | inr a =>
    cases y with
    | inl b =>
      rw [bdiag_inr_inl, Matrix.mul_apply, Fintype.sum_sum_type]
      have hz1 : (∑ a' : R,
          bdiag A B (Sum.inr a) (Sum.inl a') * bdiag C D (Sum.inl a') (Sum.inl b)) = 0 := by
        refine Finset.sum_eq_zero fun a' _ => ?_
        rw [bdiag_inr_inl, zero_mul]
      have hz2 : (∑ b' : R,
          bdiag A B (Sum.inr a) (Sum.inr b') * bdiag C D (Sum.inr b') (Sum.inl b)) = 0 := by
        refine Finset.sum_eq_zero fun b' _ => ?_
        rw [bdiag_inr_inr, bdiag_inr_inl, mul_zero]
      rw [hz1, hz2, add_zero]
    | inr b =>
      rw [bdiag_inr_inr, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
      have hzero : (∑ a' : R,
          bdiag A B (Sum.inr a) (Sum.inl a') * bdiag C D (Sum.inl a') (Sum.inr b)) = 0 := by
        refine Finset.sum_eq_zero fun a' _ => ?_
        rw [bdiag_inr_inl, zero_mul]
      rw [hzero, zero_add]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [bdiag_inr_inr, bdiag_inr_inr]

/-- A list product of block diagonal matrices equals the block diagonal of the two component
list products. -/
private theorem list_prod_bdiag : ∀ (l : List (Matrix R R ℂ × Matrix R R ℂ)),
    (l.map fun p => bdiag p.1 p.2).prod
      = bdiag (l.map Prod.fst).prod (l.map Prod.snd).prod := by
  intro l
  induction l with
  | nil => simp [List.map_nil, List.prod_nil, bdiag_one]
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.map_cons, List.prod_cons,
      List.prod_cons, ih, bdiag_mul]

/-- A finite indexed product of block diagonal matrices equals the block diagonal of the
component products. -/
private theorem matProdFin_bdiag (k : ℕ) (A B : Fin k → Matrix R R ℂ) :
    matProdFin k (fun j => bdiag (A j) (B j))
      = bdiag (matProdFin k A) (matProdFin k B) := by
  have h := list_prod_bdiag ((List.finRange k).map fun j => (A j, B j))
  rw [List.map_map, List.map_map, List.map_map] at h
  show ((List.finRange k).map (fun j => bdiag (A j) (B j))).prod
    = bdiag ((List.finRange k).map A).prod ((List.finRange k).map B).prod
  exact h

/-- On the left summand, a block diagonal matrix acts by its first block on the left component
of the vector. -/
private theorem bdiag_mulVec_inl (A B : Matrix R R ℂ) (z : QState (R ⊕ R)) (a : R) :
    (bdiag A B *ᵥ z) (Sum.inl a) = (A *ᵥ fun b => z (Sum.inl b)) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  have hzero : (∑ a₂ : R, bdiag A B (Sum.inl a) (Sum.inr a₂) * z (Sum.inr a₂)) = 0 := by
    refine Finset.sum_eq_zero fun a₂ _ => ?_
    rw [bdiag_inl_inr, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [bdiag_inl_inl]

/-- On the right summand, a block diagonal matrix acts by its second block on the right
component of the vector. -/
private theorem bdiag_mulVec_inr (A B : Matrix R R ℂ) (z : QState (R ⊕ R)) (a : R) :
    (bdiag A B *ᵥ z) (Sum.inr a) = (B *ᵥ fun b => z (Sum.inr b)) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type]
  have hzero : (∑ a' : R, bdiag A B (Sum.inr a) (Sum.inl a') * z (Sum.inl a')) = 0 := by
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [bdiag_inr_inl, zero_mul]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [bdiag_inr_inr]

/-- An inner product involving a block diagonal matrix splits into the sum of the two blockwise
inner products. -/
private theorem inner_bdiag_mulVec (A B : Matrix R R ℂ) (u v : QState (R ⊕ R)) :
    Qatlib.Foundations.PureStateMath.Inner u (bdiag A B *ᵥ v)
      = Qatlib.Foundations.PureStateMath.Inner (fun a => u (Sum.inl a)) (A *ᵥ (fun a => v (Sum.inl a)))
        + Qatlib.Foundations.PureStateMath.Inner (fun b => u (Sum.inr b)) (B *ᵥ (fun b => v (Sum.inr b))) := by
  rw [inner_apply, Fintype.sum_sum_type, inner_apply, inner_apply]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [bdiag_mulVec_inl]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [bdiag_mulVec_inr]

/-- The operator norm of a block diagonal matrix is at most the maximum of the two block norms. -/
private theorem bdiag_norm_le (A B : Matrix R R ℂ) : ‖bdiag A B‖ ≤ max ‖A‖ ‖B‖ := by
  have hnonneg : 0 ≤ max ‖A‖ ‖B‖ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hA : ∀ w : QState R, ∑ a, ‖(A *ᵥ w) a‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
    intro w
    have h := l2_norm_mulVec_fromVec_le A w
    have hsq := sq_le_sq_nn (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h
    rwa [mul_pow, norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq] at hsq
  have hB : ∀ w : QState R, ∑ b, ‖(B *ᵥ w) b‖ ^ 2 ≤ ‖B‖ ^ 2 * ∑ b, ‖w b‖ ^ 2 := by
    intro w
    have h := l2_norm_mulVec_fromVec_le B w
    have hsq := sq_le_sq_nn (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h
    rwa [mul_pow, norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq] at hsq
  refine l2_opNorm_le_of_mulVec_le hnonneg _ fun z => ?_
  have hs1 : (∑ a, ‖(bdiag A B *ᵥ z) (Sum.inl a)‖ ^ 2)
      = ∑ a, ‖(A *ᵥ fun b => z (Sum.inl b)) a‖ ^ 2 :=
    Finset.sum_congr rfl fun a _ => by rw [bdiag_mulVec_inl]
  have hs2 : (∑ b, ‖(bdiag A B *ᵥ z) (Sum.inr b)‖ ^ 2)
      = ∑ b, ‖(B *ᵥ fun b => z (Sum.inr b)) b‖ ^ 2 :=
    Finset.sum_congr rfl fun b _ => by rw [bdiag_mulVec_inr]
  have hmain : ‖toEuclidean_fromVec (bdiag A B *ᵥ z)‖ ^ 2
      ≤ (max ‖A‖ ‖B‖ * ‖toEuclidean_fromVec z‖) ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type, hs1, hs2, mul_pow]
    calc ∑ a, ‖(A *ᵥ fun b => z (Sum.inl b)) a‖ ^ 2
          + ∑ b, ‖(B *ᵥ fun b => z (Sum.inr b)) b‖ ^ 2
        ≤ ‖A‖ ^ 2 * ∑ a, ‖z (Sum.inl a)‖ ^ 2 + ‖B‖ ^ 2 * ∑ b, ‖z (Sum.inr b)‖ ^ 2 :=
          add_le_add (hA _) (hB _)
      _ ≤ max ‖A‖ ‖B‖ ^ 2 * (∑ a, ‖z (Sum.inl a)‖ ^ 2 + ∑ b, ‖z (Sum.inr b)‖ ^ 2) := by
          rw [mul_add]
          refine add_le_add
            (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun a _ => sq_nonneg _))
            (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun b _ => sq_nonneg _))
          · exact sq_le_sq_nn (norm_nonneg _) hnonneg (le_max_left _ _)
          · exact sq_le_sq_nn (norm_nonneg _) hnonneg (le_max_right _ _)
      _ = max ‖A‖ ‖B‖ ^ 2 * ‖toEuclidean_fromVec z‖ ^ 2 := by
          rw [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type]
  calc ‖toEuclidean_fromVec (bdiag A B *ᵥ z)‖
      = Real.sqrt (‖toEuclidean_fromVec (bdiag A B *ᵥ z)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((max ‖A‖ ‖B‖ * ‖toEuclidean_fromVec z‖) ^ 2) := Real.sqrt_le_sqrt hmain
    _ = max ‖A‖ ‖B‖ * ‖toEuclidean_fromVec z‖ :=
        Real.sqrt_sq (mul_nonneg hnonneg (norm_nonneg _))

/-- Duplicating the label function across a sum type makes `cbDelta` block diagonal with two
identical blocks. -/
private theorem cbDelta_bdiag {κ : Type} [Fintype κ] (δ : R → Option κ) (w : κ → ℂ) :
    cbDelta (Sum.elim δ δ) w = bdiag (cbDelta δ w) (cbDelta δ w) := by
  ext x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      rw [cbDelta_apply, bdiag_inl_inl, cbDelta_apply]
      simp only [Sum.inl.injEq]
      rfl
    | inr b =>
      rw [cbDelta_apply, bdiag_inl_inr, ite_eq_right (by simp)]
  | inr a =>
    cases y with
    | inl b =>
      rw [cbDelta_apply, bdiag_inr_inl, ite_eq_right (by simp)]
    | inr b =>
      rw [cbDelta_apply, bdiag_inr_inr, cbDelta_apply]
      simp only [Sum.inr.injEq]
      rfl

end BDiag

section ConjSandwich

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Conjugating `cbPathVal` is equivalent to conjugating its matrices and endpoint states. -/
private theorem cbPathVal_conj {s : ℕ} (W : Fin (s + 1) → Matrix R R ℂ) (u v : QState R)
    (r : Fin (s + 2) → R) :
    (starRingEnd ℂ) (cbPathVal W u v r)
      = cbPathVal (fun m => conjMat (W m)) (fun a => (starRingEnd ℂ) (u a))
          (fun a => (starRingEnd ℂ) (v a)) r := by
  unfold cbPathVal
  rw [map_mul, map_mul, map_mul, map_prod]
  simp only [conjMat_apply, starRingEnd_self_apply]

/-- Conjugating `dzval` evaluated on conjugated coefficients recovers its original value. -/
private theorem dzval_conj {κ : Type} [Fintype κ] (δ : R → Option κ) (w : κ → ℂ) (r : R) :
    (starRingEnd ℂ) (dzval δ (fun k => (starRingEnd ℂ) (w k)) r) = dzval δ w r := by
  rw [dzval_eq_dzO, dzval_eq_dzO]
  cases h : δ r with
  | none => simp [dzO]
  | some k => simp [dzO]

/-- Conjugating the matrices and endpoint states in `cbSandwich` corresponds to conjugating its
value with conjugated input coefficients. -/
private theorem cbSandwich_conj {κ : Type} [Fintype κ] {s : ℕ}
    (W : Fin (s + 1) → Matrix R R ℂ) (δ : R → Option κ) (u v : QState R)
    (z : Fin s → κ → ℂ) :
    cbSandwich (fun m => conjMat (W m)) δ (fun a => (starRingEnd ℂ) (u a))
        (fun a => (starRingEnd ℂ) (v a)) z
      = (starRingEnd ℂ) (cbSandwich W δ u v fun j k => (starRingEnd ℂ) (z j k)) := by
  rw [cbSandwich_eq_sum, cbSandwich_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, map_prod, cbPathVal_conj]
  refine congrArg _ (Finset.prod_congr rfl fun j _ => ?_)
  exact (dzval_conj δ (z j) (r j.castSucc.succ)).symm

/-- For a total label function, a fiber sum with a `none` coordinate vanishes. -/
private theorem cbFiberSum_eq_zero_of_total {κ : Type} [Fintype κ] {s : ℕ} (δ : R → Option κ)
    (hδ : ∀ r, ∃ k, δ r = some k) (W : Fin (s + 1) → Matrix R R ℂ) (u v : QState R)
    (p : Fin s → Option κ) (j₀ : Fin s) (hj₀ : p j₀ = none) :
    cbFiberSum W δ u v p = 0 := by
  unfold cbFiberSum
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [ite_eq_right, zero_mul]
  intro hpat
  have h1 : δ (r j₀.castSucc.succ) = p j₀ := congrFun hpat j₀
  rw [hj₀] at h1
  obtain ⟨k, hk⟩ := hδ (r j₀.castSucc.succ)
  rw [hk] at h1
  exact Option.some_ne_none k h1

/-- For a total label function, expands `cbSandwich` as a sum over label tuples weighted by
their fiber sums and input monomials. -/
private theorem cbSandwich_total_eq {κ : Type} [Fintype κ] {s : ℕ} (δ : R → Option κ)
    (hδ : ∀ r, ∃ k, δ r = some k) (W : Fin (s + 1) → Matrix R R ℂ) (u v : QState R)
    (z : Fin s → κ → ℂ) :
    cbSandwich W δ u v z
      = ∑ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) * ∏ j, z j (i j) := by
  have key : ∀ p : Fin s → Option κ, cbFiberSum W δ u v p
      = ∑ i : Fin s → κ, (if (fun j => some (i j)) = p then (1 : ℂ) else 0) *
          cbFiberSum W δ u v (fun j => some (i j)) := by
    intro p
    by_cases hp : ∃ i₀ : Fin s → κ, p = fun j => some (i₀ j)
    · obtain ⟨i₀, rfl⟩ := hp
      rw [Finset.sum_eq_single i₀]
      · rw [ite_eq_left rfl, one_mul]
      · intro b _ hb
        rw [ite_eq_right, zero_mul]
        intro hfb
        exact hb (funext fun j => Option.some.inj (congrFun hfb j))
      · intro hmem
        exact absurd (Finset.mem_univ i₀) hmem
    · obtain ⟨j₀, hj₀⟩ : ∃ j₀, p j₀ = none := by
        by_contra hcon
        have hcon' : ∀ j₀, p j₀ ≠ none := fun j₀ hj => hcon ⟨j₀, hj⟩
        exact hp ⟨fun j => (Option.ne_none_iff_exists.mp (hcon' j)).choose,
          funext fun j => ((Option.ne_none_iff_exists.mp (hcon' j)).choose_spec).symm⟩
      rw [cbFiberSum_eq_zero_of_total δ hδ W u v p j₀ hj₀]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right (by
        intro hfi
        have h2 : (fun j => some (i j)) j₀ = p j₀ := congrFun hfi j₀
        rw [hj₀] at h2
        exact Option.some_ne_none _ h2), zero_mul]
  rw [cbSandwich_eq_fiber]
  calc ∑ p, cbFiberSum W δ u v p * ∏ j, dzO (z j) (p j)
      = ∑ p, (∑ i : Fin s → κ,
            (if (fun j => some (i j)) = p then (1 : ℂ) else 0) *
              cbFiberSum W δ u v (fun j => some (i j))) * ∏ j, dzO (z j) (p j) :=
        Finset.sum_congr rfl fun p _ => congrArg (· * _) (key p)
    _ = ∑ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) *
          (fun p => ∏ j, dzO (z j) (p j)) (fun j => some (i j)) :=
        (sum_pattern_distrib (fun i : Fin s → κ => fun j => some (i j))
          (fun i => cbFiberSum W δ u v (fun j => some (i j)))
          (fun p => ∏ j, dzO (z j) (p j))).symm
    _ = ∑ i : Fin s → κ, cbFiberSum W δ u v (fun j => some (i j)) * ∏ j, z j (i j) := by
        refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
        show (∏ j, dzO (z j) (some (i j))) = ∏ j, z j (i j)
        exact Finset.prod_congr rfl fun j _ => rfl

/-- Half a complex number plus half its conjugate is the complex coercion of its real part. -/
private theorem half_add_conj (w : ℂ) :
    (2 : ℂ)⁻¹ * w + (2 : ℂ)⁻¹ * (starRingEnd ℂ) w = ((w.re : ℝ) : ℂ) := by
  rw [← mul_add, Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat,
    ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]

end ConjSandwich

section Main

/-- For positive input size, a sign algorithm with `t` queries yields a real tensor of order
twice `t` with a completely bounded factorization and the same Boolean bias evaluations. -/
theorem lemma3_3AlgorithmToTensor : Lemma3_3AlgorithmToTensor := by
  intro n hn t β h
  obtain ⟨R, instF, instD, δ, C, ψ, E, hC, hψ, hCt, hβ⟩ := h
  let := instF
  let := instD
  classical

  set δt := cbTotalLabel δ ⟨0, hn⟩ with hδt_def
  have hδt : ∀ r, ∃ k, δt r = some k := fun r => cbTotalLabel_eq_some δ ⟨0, hn⟩ r
  have horacle : ∀ x : Fin n → Bool, cbPhaseOracle δt x = cbPhaseOracle δ x :=
    fun x => cbPhaseOracle_total δ ⟨0, hn⟩ x

  set padC : Circuit R := C ++ List.replicate (t - QueryCount C) Step.query with hpadC_def
  have hpadU : IsUnitaryCircuit padC :=
    (isUnitaryCircuit_append _ _).mpr ⟨hC, isUnitaryCircuit_replicate_query _⟩
  have hpadQ : QueryCount padC = t := by
    rw [hpadC_def, queryCount_append, queryCount_replicate_query]
    omega
  have hpadBias : ∀ x : Fin n → Bool,
      signBias (Run (cbPhaseOracle δ x) padC ψ) E = β x := by
    intro x
    rw [hpadC_def, run_append, signBias_run_replicate_query]
    exact hβ x

  set Gs := gateBlocks padC with hGs_def
  have hGs_len : Gs.length = t + 1 := by
    rw [hGs_def, gateBlocks_length, hpadQ]
  have hGs_ne : Gs ≠ [] := hGs_def ▸ gateBlocks_ne_nil padC
  have hGs_unit : ∀ G ∈ Gs, G ∈ Matrix.unitaryGroup R ℂ :=
    hGs_def ▸ gateBlocks_unitary hpadU
  set Wl := palW Gs (signDiag E) with hWl_def
  have hWl_len : Wl.length = 2 * t + 1 := by
    rw [hWl_def, palW_length Gs (signDiag E) hGs_ne, hGs_len]
    omega
  set W : Fin (2 * t + 1) → Matrix R R ℂ := listW Wl hWl_len with hW_def
  have hWl_map : (List.finRange (2 * t + 1)).map W = Wl := finRange_map_listW Wl hWl_len
  have hW_norm : ∀ m, ‖W m‖ ≤ 1 := by
    intro m
    have hmem : W m ∈ Wl := List.getElem_mem _
    exact palW_norm_le Gs (signDiag E)
      (fun G hG => unitary_norm_le (hGs_unit G hG)) (signDiag_norm_le E) (W m) hmem

  set C0 : (Fin (2 * t) → (Fin n ⊕ Fin n)) → ℂ :=
    fun i => cbFiberSum W δt ψ ψ (fun j => some (i j)) with hC0_def
  set T : RealTensor (Fin n ⊕ Fin n) (2 * t) := fun i => (C0 i).re with hT_def

  have hbool : ∀ x : Fin n → Bool,
      cbSandwich W δt ψ ψ (fun _ => signVecC x) = (β x : ℂ) := by
    intro x
    have hchain : cbSandwichMatrix W δt (fun _ => signVecC x)
        = (cbInterleave (cbPhaseOracle δt x) Gs)ᴴ * signDiag E *
            cbInterleave (cbPhaseOracle δt x) Gs := by
      rw [cbSandwichMatrix_eq_sandProd W δt (cbDelta δt (signVecC x)) (fun _ => signVecC x)
        (fun _ => rfl), hWl_map, cbDelta_signVecC_eq_oracle]
      exact pal_eq Gs (cbPhaseOracle δt x) (signDiag E) (cbPhaseOracle_conjTranspose δt x)
    show Qatlib.Foundations.PureStateMath.Inner ψ
        (cbSandwichMatrix W δt (fun _ => signVecC x) *ᵥ ψ) = (β x : ℂ)
    rw [hchain, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      inner_mulVec_conjTranspose, Matrix.conjTranspose_conjTranspose, signBias_eq_inner,
      hGs_def, ← run_eq_interleave, horacle x, hpadBias x]

  have hconj_eval : ∀ z : Fin (2 * t) → (Fin n ⊕ Fin n) → ℂ,
      cbSandwich (fun m => conjMat (W m)) δt (fun a => (starRingEnd ℂ) (ψ a))
          (fun a => (starRingEnd ℂ) (ψ a)) z
        = ∑ i : Fin (2 * t) → (Fin n ⊕ Fin n),
            (starRingEnd ℂ) (C0 i) * ∏ j, z j (i j) := by
    intro z
    rw [cbSandwich_conj, cbSandwich_total_eq δt hδt W ψ ψ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_prod]
    refine congrArg₂ (· * ·) ?_ ?_
    · rfl
    · refine Finset.prod_congr rfl fun j _ => ?_
      show (starRingEnd ℂ) ((starRingEnd ℂ) (z j (i j))) = z j (i j)
      exact starRingEnd_self_apply _

  have hid : ∀ z : Fin (2 * t) → (Fin n ⊕ Fin n) → ℂ,
      tensorEval T z = (2 : ℂ)⁻¹ * cbSandwich W δt ψ ψ z +
        (2 : ℂ)⁻¹ * cbSandwich (fun m => conjMat (W m)) δt
          (fun a => (starRingEnd ℂ) (ψ a)) (fun a => (starRingEnd ℂ) (ψ a)) z := by
    intro z
    have hS : cbSandwich W δt ψ ψ z
        = ∑ i : Fin (2 * t) → (Fin n ⊕ Fin n), C0 i * ∏ j, z j (i j) :=
      cbSandwich_total_eq δt hδt W ψ ψ z
    calc tensorEval T z
        = ∑ i : Fin (2 * t) → (Fin n ⊕ Fin n), ((C0 i).re : ℂ) * ∏ j, z j (i j) := rfl
      _ = ∑ i : Fin (2 * t) → (Fin n ⊕ Fin n),
            ((2 : ℂ)⁻¹ * C0 i + (2 : ℂ)⁻¹ * (starRingEnd ℂ) (C0 i)) * ∏ j, z j (i j) :=
          Finset.sum_congr rfl fun i _ => by rw [half_add_conj (C0 i)]
      _ = (2 : ℂ)⁻¹ * (∑ i : Fin (2 * t) → (Fin n ⊕ Fin n), C0 i * ∏ j, z j (i j)) +
            (2 : ℂ)⁻¹ * (∑ i : Fin (2 * t) → (Fin n ⊕ Fin n),
              (starRingEnd ℂ) (C0 i) * ∏ j, z j (i j)) := by
          have hterm : ∀ i : Fin (2 * t) → (Fin n ⊕ Fin n),
              ((2 : ℂ)⁻¹ * C0 i + (2 : ℂ)⁻¹ * (starRingEnd ℂ) (C0 i)) * ∏ j, z j (i j)
                = (2 : ℂ)⁻¹ * (C0 i * ∏ j, z j (i j)) +
                  (2 : ℂ)⁻¹ * ((starRingEnd ℂ) (C0 i) * ∏ j, z j (i j)) := fun i => by ring
          rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (2 : ℂ)⁻¹ * cbSandwich W δt ψ ψ z +
            (2 : ℂ)⁻¹ * cbSandwich (fun m => conjMat (W m)) δt
              (fun a => (starRingEnd ℂ) (ψ a)) (fun a => (starRingEnd ℂ) (ψ a)) z := by
          rw [← hS, hconj_eval z]

  set c : ℂ := ((Real.sqrt 2 : ℂ))⁻¹ with hc_def
  have hcc : c * c = (2 : ℂ)⁻¹ := by
    rw [hc_def]
    exact inv_sqrt2_mul_self
  have hcstar : (starRingEnd ℂ) c = c := by
    rw [hc_def, map_inv₀, Complex.conj_ofReal]
  have hc2 : ‖c‖ ^ 2 = (2 : ℝ)⁻¹ := by
    have hcval : ‖c‖ = (Real.sqrt 2)⁻¹ := by
      rw [hc_def, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hcval, inv_pow, Real.sq_sqrt (by norm_num)]
  set δ2 : R ⊕ R → Option (Fin n ⊕ Fin n) := Sum.elim δt δt with hδ2_def
  set u2 : QState (R ⊕ R) :=
    Sum.elim (c • ψ) (c • fun a => (starRingEnd ℂ) (ψ a)) with hu2_def
  set W2 : Fin (2 * t + 1) → Matrix (R ⊕ R) (R ⊕ R) ℂ :=
    fun m => bdiag (W m) (conjMat (W m)) with hW2_def
  have hu2_norm : Normalized u2 := by
    have h1 : ∀ a : R, ‖u2 (Sum.inl a)‖ ^ 2 = ‖c‖ ^ 2 * ‖ψ a‖ ^ 2 := by
      intro a
      have hu2a : u2 (Sum.inl a) = c * ψ a := rfl
      rw [hu2a, norm_mul, mul_pow]
    have h2 : ∀ b : R, ‖u2 (Sum.inr b)‖ ^ 2 = ‖c‖ ^ 2 * ‖ψ b‖ ^ 2 := by
      intro b
      have hu2b : u2 (Sum.inr b) = c * (starRingEnd ℂ) (ψ b) := rfl
      rw [hu2b, norm_mul, mul_pow, Complex.norm_conj]
    show ∑ x : R ⊕ R, ‖u2 x‖ ^ 2 = 1
    rw [Fintype.sum_sum_type, Finset.sum_congr rfl (fun a _ => h1 a),
      Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.mul_sum]
    have hψ' : ∑ i : R, ‖ψ i‖ ^ 2 = 1 := hψ
    rw [hψ', hc2]
    norm_num
  have hW2_norm : ∀ m, ‖W2 m‖ ≤ 1 := by
    intro m
    have hW2m : W2 m = bdiag (W m) (conjMat (W m)) := rfl
    rw [hW2m]
    exact le_trans (bdiag_norm_le _ _)
      (max_le (hW_norm m) (le_trans (conjMat_norm_le _) (hW_norm m)))
  have hsplit : ∀ z : Fin (2 * t) → (Fin n ⊕ Fin n) → ℂ,
      cbSandwich W2 δ2 u2 u2 z = c * (c * cbSandwich W δt ψ ψ z) +
        c * (c * cbSandwich (fun m => conjMat (W m)) δt (fun a => (starRingEnd ℂ) (ψ a))
          (fun a => (starRingEnd ℂ) (ψ a)) z) := by
    intro z
    have hmatrix : cbSandwichMatrix W2 δ2 z
        = bdiag (cbSandwichMatrix W δt z)
            (cbSandwichMatrix (fun m => conjMat (W m)) δt z) := by
      have hfactor : ∀ j : Fin (2 * t),
          W2 j.castSucc * cbDelta δ2 (z j)
            = bdiag (W j.castSucc * cbDelta δt (z j))
                (conjMat (W j.castSucc) * cbDelta δt (z j)) := by
        intro j
        have h1 : W2 j.castSucc = bdiag (W j.castSucc) (conjMat (W j.castSucc)) := rfl
        have h2 : cbDelta δ2 (z j) = bdiag (cbDelta δt (z j)) (cbDelta δt (z j)) := by
          have hδ2v : δ2 = Sum.elim δt δt := rfl
          rw [hδ2v]
          exact cbDelta_bdiag δt (z j)
        rw [h1, h2, bdiag_mul]
      show matProdFin (2 * t) (fun j => W2 j.castSucc * cbDelta δ2 (z j)) * W2 (Fin.last (2 * t))
        = bdiag (matProdFin (2 * t) (fun j => W j.castSucc * cbDelta δt (z j))
            * W (Fin.last (2 * t)))
          (matProdFin (2 * t) (fun j => conjMat (W j.castSucc) * cbDelta δt (z j))
            * conjMat (W (Fin.last (2 * t))))
      rw [show (fun j : Fin (2 * t) => W2 j.castSucc * cbDelta δ2 (z j))
          = fun j => bdiag (W j.castSucc * cbDelta δt (z j))
              (conjMat (W j.castSucc) * cbDelta δt (z j)) from funext hfactor]
      rw [matProdFin_bdiag]
      have h3 : W2 (Fin.last (2 * t))
          = bdiag (W (Fin.last (2 * t))) (conjMat (W (Fin.last (2 * t)))) := rfl
      rw [h3, bdiag_mul]
    show Qatlib.Foundations.PureStateMath.Inner u2 (cbSandwichMatrix W2 δ2 z *ᵥ u2) = _
    rw [hmatrix, inner_bdiag_mulVec,
      show (fun a => u2 (Sum.inl a)) = c • ψ from funext fun a => rfl,
      show (fun a => u2 (Sum.inr a)) = c • (fun a => (starRingEnd ℂ) (ψ a)) from
        funext fun a => rfl,
      inner_smul_left, inner_smul_left, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Qatlib.Concepts.QueryComplexity.CbDegreeBridge.inner_smul_right, Qatlib.Concepts.QueryComplexity.CbDegreeBridge.inner_smul_right, hcstar]
    rfl
  refine ⟨T, ⟨R ⊕ R, inferInstance, inferInstance, δ2, u2, u2, W2, hu2_norm, hu2_norm,
    hW2_norm, ?_⟩, ?_⟩
  · intro z
    rw [hid z, hsplit z, ← hcc, mul_assoc, mul_assoc]
  · intro x
    rw [hid]
    have hzB : (fun j k => (starRingEnd ℂ) ((fun _ : Fin (2 * t) => signVecC x) j k))
        = fun _ => signVecC x := by
      funext j k
      show (starRingEnd ℂ) (signVecC x k) = signVecC x k
      exact signVecC_conj x k
    rw [hbool x, cbSandwich_conj, hzB, hbool x, Complex.conj_ofReal, ← two_mul,
      ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]

end Main

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
