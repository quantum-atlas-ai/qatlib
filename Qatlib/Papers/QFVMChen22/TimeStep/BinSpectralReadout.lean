/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.BinSpectralReference
public import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwSpectralMixture
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Spectral readout of the staged stencil reference

The phased procedure in [ChenXueChenEtAl2022], Appendix C.3, tests the
cosine of a walk phase. The Hermitian part of the walk restricts to
the normalized stencil on the embedded signal. Consequently the
spectral mask of a decision bin can be applied before embedding into
the walk workspace.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (lift)
open Qatlib.Foundations.InstrumentCore.Measurement (Collapse collapse_apply)
open Qatlib.Foundations.MatrixGeometry.StochasticFrame (rangeReflection rangeReflection_adjoint)
open Qatlib.Foundations.PureStateMath
  (ApplyGate BornProb Inner Ket MeasureProb QState TensorState inner_mulVec_left_rect inner_self ket_apply)
open Qatlib.Foundations.PureStateMath.BornBridge (norm_toEuclidean_fromVec_sq toEuclidean_fromVec toVec_fromEuclidean)
open Qatlib.Concepts.BlockEncoding.Postselection (stateVector_mulVec_norm_le)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (reflection_frame signal walk walk_unitary)
open Qatlib.Concepts.QueryComplexity.DegreeMethod (sum_norm_sq_diagonal_gram)
open Qatlib.Concepts.QsvtCore.LinearSystems (nearOptimalReciprocalPolynomial)
open Qatlib.Concepts.WalkSearch.Spectral
  (aeval_eq_spectralDiagonal_of_action eq_spectralDiagonal_of_action matrix_aeval_apply_of_action
    spectralDiagonal spectralDiagonal_const)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open scoped BigOperators Classical Matrix.Norms.L2Operator

variable {M N J L : Type} [Fintype M] [Fintype N] [Fintype J] [Fintype L]
  [DecidableEq M] [DecidableEq N] [DecidableEq J] [DecidableEq L]

/-- The Hermitian part of the qubitized walk restricts to the stencil signal in its frame. -/
theorem walk_hermitian_part_frame (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) :
    ((1 / 2 : ℂ) • (walk C U + (walk C U)ᴴ)) * C = C * signal C U := by
  have hAssoc : (C * Cᴴ) * U * C = C * (Cᴴ * U * C) := by
    simp only [Matrix.mul_assoc]
  have hSum : (walk C U + (walk C U)ᴴ) * C = (2 : ℂ) • (C * signal C U) := by
    simp only [Matrix.add_mul, walk, Matrix.conjTranspose_mul, hU, rangeReflection_adjoint]
    rw [Matrix.mul_assoc U (rangeReflection C) C, reflection_frame C hC]
    simp only [rangeReflection, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hAssoc, signal, sub_add_cancel]
  rw [Matrix.smul_mul, hSum, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]

/-- Polynomial evaluation preserves a rectangular intertwining relation. -/
private theorem polynomial_intertwines (A : Matrix M M ℂ) (B : Matrix N N ℂ)
    (C : Matrix M N ℂ) (h : A * C = C * B) (p : Polynomial ℂ) :
    Polynomial.aeval A p * C = C * Polynomial.aeval B p := by
  have hPow (k : ℕ) : A ^ k * C = C * B ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, hPow]

/-- A unit-modulus walk eigenvalue gives its real part as the eigenvalue of the Hermitian part. -/
private theorem hermitian_part_action (W : Matrix M M ℂ) (hW : Wᴴ * W = 1)
    (z : ℂ) (hz : ‖z‖ = 1) (v : QState M) (hv : W *ᵥ v = z • v) :
    ((1 / 2 : ℂ) • (W + Wᴴ)) *ᵥ v = (z.re : ℂ) • v := by
  have hFix : z • (Wᴴ *ᵥ v) = v := by
    rw [← Matrix.mulVec_smul, ← hv, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
  have hScalar : star z * z = 1 := by
    rw [mul_comm]
    simpa only [Complex.star_def, hz, one_pow, Complex.ofReal_one] using Complex.mul_conj' z
  have hAdj : Wᴴ *ᵥ v = star z • v := by
    calc
      _ = (star z * z) • (Wᴴ *ᵥ v) := by rw [hScalar, one_smul]
      _ = _ := by rw [← smul_smul, hFix]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, hv, hAdj, ← add_smul, smul_smul]
  congr 1
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp

omit [DecidableEq J] in
set_option maxHeartbeats 800000 in
/-- Weighting a walk packet by a function of phase cosine equals weighting the unembedded
signal by that function of the stencil eigenvalue. The function is arbitrary on the two
finite spectra, including discontinuous threshold masks. -/
theorem walk_cosine_weighting_in_frame (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ N)) (eigenvalue : L → ℝ)
    (hSignal : ∀ i, (signal C U).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (v : J → QState M) (c : J → ℂ) (phase μ : J → ℝ) (b : QState N)
    (hInput : (∑ j, c j • v j) = C *ᵥ b)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hWalk : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (f : ℝ → ℂ) :
    (∑ j, (f (μ j) * c j) • v j) =
      C *ᵥ (spectralDiagonal basis (fun i => f (eigenvalue i)) *ᵥ b) := by
  let W := walk C U
  let A := (1 / 2 : ℂ) • (W + Wᴴ)
  let B := signal C U
  let nodes := (Finset.univ.image μ) ∪ (Finset.univ.image eigenvalue)
  let p := Lagrange.interpolate nodes Complex.ofReal f
  have hEval (x : ℝ) (hx : x ∈ nodes) : p.eval (x : ℂ) = f x :=
    Lagrange.eval_interpolate_at_node f Complex.ofReal_injective.injOn hx
  have hNodeWalk (j : J) : μ j ∈ nodes :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  have hNodeSignal (i : L) : eigenvalue i ∈ nodes :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hA (j : J) : A *ᵥ v j = (μ j : ℂ) • v j := by
    let angle : ℝ := 2 * Real.pi * phase j
    let z := Complex.exp ((angle : ℂ) * Complex.I)
    have hArgument : (angle : ℂ) * Complex.I = 2 * Real.pi * Complex.I * (phase j : ℂ) := by
      simp only [angle]
      push_cast
      ring
    have hEig : W *ᵥ v j = z • v j := by
      simpa only [z, hArgument] using hWalk j
    have hRe : z.re = μ j := by rw [show z.re = Real.cos angle from Complex.exp_ofReal_mul_I_re angle, hCos]
    simpa only [hRe] using
      hermitian_part_action W (walk_unitary C U hC hU hSq) z (Complex.norm_exp_ofReal_mul_I angle) (v j) hEig
  have hAeval (j : J) : Polynomial.aeval A p *ᵥ v j = f (μ j) • v j := by
    have hAE : A.toEuclideanLin (toEuclidean_fromVec (v j)) = (μ j : ℂ) • toEuclidean_fromVec (v j) :=
      congrArg toEuclidean_fromVec (hA j)
    have he := matrix_aeval_apply_of_action A p (toEuclidean_fromVec (v j)) (μ j : ℂ)
      hAE
    rw [hEval _ (hNodeWalk j)] at he
    exact congrArg toVec_fromEuclidean he
  have hBeval : Polynomial.aeval B p = spectralDiagonal basis (fun i => f (eigenvalue i)) := by
    rw [aeval_eq_spectralDiagonal_of_action basis B (fun i => (eigenvalue i : ℂ)) hSignal]
    congr 1
    exact funext fun i => hEval _ (hNodeSignal i)
  calc
    _ = ∑ j, c j • (Polynomial.aeval A p *ᵥ v j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hAeval, smul_smul, mul_comm]
    _ = Polynomial.aeval A p *ᵥ (∑ j, c j • v j) := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    _ = _ := by
      rw [hInput, Matrix.mulVec_mulVec,
        polynomial_intertwines A B C (walk_hermitian_part_frame C U hC hU) p, ← Matrix.mulVec_mulVec, hBeval]

variable {n : ℕ}

/-- The diagonal mask that keeps precisely the components first accepted at this bin. -/
def binSpectralMask (threshold : Fin n → ℝ) (t : Fin n) (x : ℝ) : ℂ :=
  if threshold t ≤ |x| ∧ ∀ s : Fin n, s.val < t.val → |x| < threshold s then 1 else 0

/-- The mask at a covered spectral value is the indicator of its first accepting bin. -/
theorem bin_spectral_mask_eq (threshold : Fin n → ℝ) (t : Fin n) (x : ℝ)
    (hCovered : ∃ s, threshold s ≤ |x|) :
    binSpectralMask threshold t x = if firstThresholdBin threshold x hCovered = t then 1 else 0 := by
  let s := firstThresholdBin threshold x hCovered
  have hs := first_threshold_bin_spec threshold x hCovered
  have hMask : (threshold t ≤ |x| ∧ ∀ u : Fin n, u.val < t.val → |x| < threshold u) ↔ s = t := by
    constructor
    · rintro ⟨ht, hEarlier⟩
      apply le_antisymm
      · exact le_of_not_gt (fun h => (not_le.mpr (hs.2 t h)) ht)
      · exact le_of_not_gt (fun h => (not_le.mpr (hEarlier s h)) hs.1)
    · intro h
      subst t
      exact hs
  change (if _ then (1 : ℂ) else 0) = if s = t then 1 else 0
  simp only [hMask]

omit [Fintype J] [DecidableEq J] in
/-- Applying the mask to a spectral weight reproduces the emitted coefficient. -/
private theorem masked_weight (threshold : Fin n → ℝ) (t : Fin n) (μ : J → ℝ) (c : J → ℂ) (j : J) :
    binSpectralMask threshold t (μ j) * c j = acceptingBinWeight threshold μ c t j := by
  unfold binSpectralMask acceptingBinWeight runningBinWeight
  by_cases h : threshold t ≤ |μ j|
  · by_cases hk : ∀ s : Fin n, s.val < t.val → |μ j| < threshold s
    · simp only [ite_eq_left (And.intro h hk), ite_eq_left h, ite_eq_left hk, one_mul]
    · have hn : ¬(threshold t ≤ |μ j| ∧ ∀ s : Fin n, s.val < t.val → |μ j| < threshold s) :=
        fun he => hk he.2
      simp only [ite_eq_right hn, ite_eq_left h, ite_eq_right hk, zero_mul]
  · simp only [h, false_and, ite_false, zero_mul]

omit [DecidableEq J] in
/-- An accepted ideal packet is the stencil-frame embedding of the masked residual. -/
theorem ideal_bin_packet_in_frame (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hSq : U * U = 1)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ N)) (eigenvalue : L → ℝ)
    (hSignal : ∀ i, (signal C U).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (v : J → QState M) (c : J → ℂ) (phase μ : J → ℝ) (b : QState N)
    (hInput : (∑ j, c j • v j) = C *ᵥ b)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hWalk : ∀ j, walk C U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (threshold : Fin n → ℝ) (t : Fin n) :
    (∑ j, acceptingBinWeight threshold μ c t j • v j) =
      C *ᵥ (spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i)) *ᵥ b) := by
  simpa only [masked_weight] using
    walk_cosine_weighting_in_frame C U hC hU hSq basis eigenvalue hSignal v c phase μ b hInput hCos hWalk
      (binSpectralMask threshold t)

omit [DecidableEq N] in
set_option maxHeartbeats 500000 in
/-- Reading the clean coefficient slice of an accepted packet and decoding its signal gives
the corresponding compressed reciprocal applied to the unembedded input. -/
private theorem seeded_bin_compressed_readout (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t)
    (condition : Fin n → ℝ) (precision : ℝ) (t : Fin n)
    (C : Matrix M N ℂ) (U : Matrix M M ℂ) (x : QState N) :
    let tape := binDecisionTape width hWidth t true
    let clean := cleanReciprocalTape condition precision
    Cᴴ *ᵥ (fun m => ApplyGate (conditionalBinReciprocal width condition precision
      (commonBinMass condition precision) t C U)
      (seededBinState width condition precision tape (C *ᵥ x)) (tape, (clean, m))) =
        compressedBinReciprocal (condition t) precision (commonBinMass condition precision) C U *ᵥ x := by
  intro tape clean
  let packet (history : PhaseTape width) : QState N := Ket tape history • x
  have hInput : seededBinState width condition precision tape (C *ᵥ x) =
      fun p => Ket clean p.2.1 * (C *ᵥ packet p.1) p.2.2 := by
    funext p
    simp only [seededBinState, TensorState, packet, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hAccept : firstBinAcceptance (width := width) t tape := by
    refine ⟨(bin_decision_tape_true width hWidth t t).2 rfl, ?_⟩
    rintro ⟨s, hs, ha⟩
    exact (ne_of_lt hs) ((bin_decision_tape_true width hWidth t s).1 ha)
  have hPacket : packet tape = x := by simp [packet, ket_apply]
  rw [hInput, conditional_bin_reciprocal_compressed width condition precision
    (commonBinMass condition precision) t C U tape hAccept packet, hPacket]

/-- Decoding the stencil frame reads the coordinate at the assigned physical label. -/
theorem stencil_walk_frame_adjoint_apply {depth rows columns : ℕ}
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (ψ : QState (StencilWorkspace depth rows columns)) (i : Address depth ⊕ Address depth) :
    ((stencilWalkFrame depth rowScratch columnScratch)ᴴ *ᵥ ψ) i =
      ψ (stencilFrameLabel rowScratch columnScratch i) := by
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, stencil_walk_frame_apply, apply_ite, ite_mul]

omit [DecidableEq J] in
set_option maxHeartbeats 1200000 in
/-- The ideal terminal success component is a sum of the masked inverse outputs embedded
in the physical right register with their individual acceptance tapes. Its Born mass is
the sum of the squared amplitudes of these distinct history slices. -/
theorem stencil_bin_reference_readout {depth rows columns : ℕ}
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : (stencilWalkFrame depth rowScratch columnScratch)ᴴ * stencilWalkFrame depth rowScratch columnScratch = 1)
    (hU : Uᴴ = U) (hSq : U * U = 1)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (Address depth ⊕ Address depth))) (eigenvalue : L → ℝ)
    (hSignal : ∀ i, (signal (stencilWalkFrame depth rowScratch columnScratch) U).toEuclideanLin (basis i) =
      (eigenvalue i : ℂ) • basis i)
    (v : J → QState (StencilWorkspace depth rows columns)) (c : J → ℂ) (phase μ : J → ℝ)
    (b : QState (Address depth ⊕ Address depth))
    (hInput : (∑ j, c j • v j) = stencilWalkFrame depth rowScratch columnScratch *ᵥ b)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hWalk : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch) U *ᵥ v j =
      Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hCovered : ∀ j, ∃ t, threshold t ≤ |μ j|) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let reference := idealBinReference width hWidth condition threshold precision C U v c μ (Fin.last n)
    let binInput t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i)) *ᵥ b
    let binOutput t := compressedBinReciprocal (condition t) precision
      (commonBinMass condition precision) C U *ᵥ binInput t
    let right : Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
      diagonal (Sum.elim 0 1)
    let success := stencilBinSuccess rowScratch columnScratch width condition precision
    (MeasureProb reference success = ∑ t, ∑ col : Address depth, ‖binOutput t (Sum.inr col)‖ ^ 2) ∧
      Collapse reference success = ∑ t, seededBinState width condition precision
        (binDecisionTape width hWidth t true) (C *ᵥ (right *ᵥ binOutput t)) := by
  intro C reference binInput binOutput right success
  let emitted := idealBinAccepted width hWidth condition threshold precision C U v c μ
  let tape t := binDecisionTape width hWidth t true
  let clean := cleanReciprocalTape condition precision
  let label (col : Address depth) := stencilFrameLabel (depth := depth) rowScratch columnScratch (Sum.inr col)
  let histories := Finset.univ.filter fun (history : PhaseTape width) => ∃ t, (history t).1 = true
  have hInjective : Function.Injective tape := by
    intro s t he
    have hs := (bin_decision_tape_true width hWidth s s).2 rfl
    change (tape s s).1 = true at hs
    rw [he] at hs
    exact (bin_decision_tape_true width hWidth t s).1 hs
  have hSub : Finset.univ.image tape ⊆ histories := by
    intro history hh
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, (bin_decision_tape_true width hWidth t t).2 rfl⟩
  have hReference : reference = ∑ t, emitted t :=
    ideal_bin_reference_terminal width hWidth condition threshold precision C U v c μ hCovered
  have hTapeValue (t : Fin n) (col : Address depth) :
      reference (tape t, (clean, label col)) = emitted t (tape t, (clean, label col)) := by
    rw [hReference, Finset.sum_apply]
    refine Finset.sum_eq_single t (fun s _ hst => ?_) (fun ht => (ht (Finset.mem_univ t)).elim)
    exact ideal_bin_accepted_supported width hWidth condition threshold precision C U v c μ s _
      (fun he => hst (hInjective he).symm)
  have hOutside (history : PhaseTape width) (hh : history ∉ Finset.univ.image tape) (col : Address depth) :
      reference (history, (clean, label col)) = 0 := by
    rw [hReference, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro s _
    exact ideal_bin_accepted_supported width hWidth condition threshold precision C U v c μ s _
      (fun he => hh (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, he.symm⟩))
  have hClean (t : Fin n) (col : Address depth) :
      emitted t (tape t, (clean, label col)) = binOutput t (Sum.inr col) := by
    have hInputBin := ideal_bin_packet_in_frame C U hC hU hSq basis eigenvalue hSignal
      v c phase μ b hInput hCos hWalk threshold t
    have he := seeded_bin_compressed_readout width hWidth condition precision t C U (binInput t)
    have hp := congrFun he (Sum.inr col)
    change ((stencilWalkFrame depth rowScratch columnScratch)ᴴ *ᵥ _) (Sum.inr col) = _ at hp
    rw [stencil_walk_frame_adjoint_apply] at hp
    change ApplyGate (conditionalBinReciprocal width condition precision (commonBinMass condition precision) t C U)
      (seededBinState width condition precision (tape t) (∑ j, acceptingBinWeight threshold μ c t j • v j))
      (tape t, (clean, label col)) = _
    rw [hInputBin]
    exact hp
  constructor
  · rw [stencil_bin_success_mass]
    change (∑ history ∈ histories, ∑ col : Address depth, BornProb reference (history, (clean, label col))) = _
    rw [← Finset.sum_subset hSub (fun history _ hh => by
        simp only [BornProb, hOutside history hh, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]),
      Finset.sum_image (fun _ _ _ _ h => hInjective h)]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro col _
    simp only [BornProb, hTapeValue, hClean]
  · have hAt (t : Fin n) (col : Address depth) : (C *ᵥ (right *ᵥ binOutput t)) (label col) =
          binOutput t (Sum.inr col) := by
      have hNorm : Cᴴ *ᵥ (C *ᵥ (right *ᵥ binOutput t)) = right *ᵥ binOutput t := by
        rw [Matrix.mulVec_mulVec, hC, Matrix.one_mulVec]
      have hEntry := congrFun hNorm (Sum.inr col)
      rw [stencil_walk_frame_adjoint_apply] at hEntry
      simpa only [right, Matrix.mulVec_diagonal, Sum.elim_inr, Pi.one_apply, one_mul, label] using hEntry
    have hZero (t : Fin n) (p : StencilWorkspace depth rows columns)
        (hp : ∀ col, p ≠ label col) : (C *ᵥ (right *ᵥ binOutput t)) p = 0 := by
      change (∑ i, stencilWalkFrame depth rowScratch columnScratch p i * (right *ᵥ binOutput t) i) = 0
      apply Finset.sum_eq_zero
      intro i _
      cases i with
      | inl row => simp [right, Matrix.mulVec_diagonal]
      | inr col => rw [stencil_walk_frame_apply, ite_eq_right (hp col), zero_mul]
    funext p
    rw [collapse_apply, Finset.sum_apply]
    by_cases hp : p ∈ success
    · obtain ⟨_, hCoeff, col, hLabel⟩ := (Finset.mem_filter.mp hp).2
      rcases p with ⟨history, coeff, signal⟩
      change coeff = clean at hCoeff
      change signal = label col at hLabel
      subst coeff
      subst signal
      rw [ite_eq_left hp, hReference, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro t _
      by_cases hh : history = tape t
      · subst history
        rw [hClean]
        simp [seededBinState, TensorState, hAt, tape, clean]
      · have he : emitted t (history, (clean, label col)) = 0 :=
          ideal_bin_accepted_supported width hWidth condition threshold precision C U v c μ t
            (history, (clean, label col)) hh
        rw [he]
        simp [seededBinState, TensorState, ket_apply, hh, tape]
    · rw [ite_eq_right hp]
      symm
      apply Finset.sum_eq_zero
      intro t _
      by_cases hh : p.1 = tape t
      · by_cases hc : p.2.1 = clean
        · have hNo (col : Address depth) : p.2.2 ≠ label col := by
            intro he
            apply hp
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t, ?_⟩, hc, col, he⟩
            rw [hh]
            exact (bin_decision_tape_true width hWidth t t).2 rfl
          change Ket (tape t) p.1 * (Ket clean p.2.1 * (C *ᵥ (right *ᵥ binOutput t)) p.2.2) = 0
          rw [hZero t p.2.2 hNo, mul_zero, mul_zero]
        · simp [seededBinState, TensorState, ket_apply, hc, clean]
      · simp [seededBinState, TensorState, ket_apply, hh, tape]

omit [DecidableEq J] in
/-- The reference success probability is the sum of the physical right-register
probabilities of the compressed bin reciprocals. -/
theorem stencil_bin_reference_success_mass {depth rows columns : ℕ}
    (rowScratch : Fin rows) (columnScratch : Fin columns)
    (U : Matrix (StencilWorkspace depth rows columns) (StencilWorkspace depth rows columns) ℂ)
    (hC : (stencilWalkFrame depth rowScratch columnScratch)ᴴ * stencilWalkFrame depth rowScratch columnScratch = 1)
    (hU : Uᴴ = U) (hSq : U * U = 1)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (Address depth ⊕ Address depth))) (eigenvalue : L → ℝ)
    (hSignal : ∀ i, (signal (stencilWalkFrame depth rowScratch columnScratch) U).toEuclideanLin (basis i) =
      (eigenvalue i : ℂ) • basis i)
    (v : J → QState (StencilWorkspace depth rows columns)) (c : J → ℂ) (phase μ : J → ℝ)
    (b : QState (Address depth ⊕ Address depth))
    (hInput : (∑ j, c j • v j) = stencilWalkFrame depth rowScratch columnScratch *ᵥ b)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = μ j)
    (hWalk : ∀ j, walk (stencilWalkFrame depth rowScratch columnScratch) U *ᵥ v j =
      Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j)
    (width : Fin n → ℕ) (hWidth : ∀ t, 0 < width t) (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hCovered : ∀ j, ∃ t, threshold t ≤ |μ j|) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let reference := idealBinReference width hWidth condition threshold precision C U v c μ (Fin.last n)
    let binInput t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i)) *ᵥ b
    MeasureProb reference (stencilBinSuccess rowScratch columnScratch width condition precision) =
      ∑ t, ∑ col : Address depth, ‖(compressedBinReciprocal (condition t) precision
        (commonBinMass condition precision) C U *ᵥ binInput t) (Sum.inr col)‖ ^ 2 := by
  intro C reference binInput
  exact (stencil_bin_reference_readout rowScratch columnScratch U hC hU hSq basis eigenvalue
    hSignal v c phase μ b hInput hCos hWalk width hWidth condition threshold precision hCovered).1

set_option maxHeartbeats 750000 in
/-- Summing the decoded bin outputs and restoring the common coefficient normalization
approximates the inverse applied to the residual. The error is uniform over the number of
bins and scales with the residual norm. -/
theorem stencil_bin_decoded_sum_error (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (hCondition : ∀ t, 1 < condition t)
    (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ N)) (eigenvalue : L → ℝ)
    (hSignal : ∀ i, (signal C U).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (hCovered : ∀ i, ∃ t, threshold t ≤ |eigenvalue i|) (hBound : ∀ i, |eigenvalue i| ≤ 1)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t) (b : QState N) :
    let mass := commonBinMass condition precision
    let P t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let solution := spectralDiagonal basis (fun i => (eigenvalue i : ℂ)⁻¹) *ᵥ b
    ‖toEuclidean_fromVec ((mass : ℂ) •
      (∑ t, compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b)) - solution)‖ ≤
      (2 * precision) * ‖toEuclidean_fromVec b‖ := by
  intro mass P solution
  let R t := compressedBinReciprocal (condition t) precision mass C U
  let X := spectralDiagonal basis (fun i => (eigenvalue i : ℂ)⁻¹)
  let total := ∑ t, ((mass : ℂ) • R t) * P t
  have hP (t : Fin n) : P t = spectralDiagonal basis
      (fun i => if firstThresholdBin threshold (eigenvalue i) (hCovered i) = t then 1 else 0) := by
    unfold P
    congr 1
    exact funext fun i => bin_spectral_mask_eq threshold t (eigenvalue i) (hCovered i)
  obtain ⟨hPos, hMass⟩ := common_bin_mass_bounds condition precision
  have hOperator : ‖total - X‖ ≤ 2 * precision := by
    unfold total
    simp_rw [hP]
    exact bin_reciprocal_partition_error condition threshold precision mass C U hC hSq hPos hMass hCondition
      hPrecision hHalf basis eigenvalue hSignal hCovered hBound hCutoff
  have hTotal : total *ᵥ b = (mass : ℂ) • (∑ t, R t *ᵥ (P t *ᵥ b)) := by
    unfold total
    rw [Matrix.sum_mulVec, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  have hDifference : (total - X) *ᵥ b = (mass : ℂ) • (∑ t, R t *ᵥ (P t *ᵥ b)) - solution := by
    rw [Matrix.sub_mulVec, hTotal]
  change ‖toEuclidean_fromVec ((mass : ℂ) • (∑ t, R t *ᵥ (P t *ᵥ b)) - solution)‖ ≤ _
  rw [← hDifference]
  exact (stateVector_mulVec_norm_le (total - X) b).trans (mul_le_mul_of_nonneg_right hOperator (norm_nonneg _))

set_option maxHeartbeats 650000 in
/-- An even spectral weight commutes with any map interchanging the positive and negative
eigenspaces of the signed operator. -/
private theorem even_spectral_diagonal_commutes (A D : Matrix N N ℂ) (hAnti : A * D = D * (-A))
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ N)) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, A.toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (f : ℝ → ℂ) (hEven : ∀ x, f (-x) = f x) :
    spectralDiagonal basis (fun i => f (eigenvalue i)) * D =
      D * spectralDiagonal basis (fun i => f (eigenvalue i)) := by
  let nodes := (Finset.univ.image eigenvalue) ∪ (Finset.univ.image (fun i => -eigenvalue i))
  let p := Lagrange.interpolate nodes Complex.ofReal f
  have hEval (x : ℝ) (hx : x ∈ nodes) : p.eval (x : ℂ) = f x :=
    Lagrange.eval_interpolate_at_node f Complex.ofReal_injective.injOn hx
  have hPos (i : L) : eigenvalue i ∈ nodes :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hNeg (i : L) : -eigenvalue i ∈ nodes :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hNegEigen (i : L) : (-A).toEuclideanLin (basis i) = ((-eigenvalue i : ℝ) : ℂ) • basis i := by
    simp only [map_neg, LinearMap.neg_apply, hEigen, Complex.ofReal_neg, neg_smul]
  have hAeval : Polynomial.aeval A p = spectralDiagonal basis (fun i => f (eigenvalue i)) := by
    rw [aeval_eq_spectralDiagonal_of_action basis A (fun i => (eigenvalue i : ℂ)) hEigen]
    congr 1
    exact funext fun i => hEval _ (hPos i)
  have hNegAeval : Polynomial.aeval (-A) p = spectralDiagonal basis (fun i => f (eigenvalue i)) := by
    rw [aeval_eq_spectralDiagonal_of_action basis (-A) (fun i => ((-eigenvalue i : ℝ) : ℂ)) hNegEigen]
    congr 1
    exact funext fun i => (hEval _ (hNeg i)).trans (hEven _)
  rw [← hAeval, polynomial_intertwines A (-A) D hAnti p, hNegAeval, hAeval]

set_option maxHeartbeats 650000 in
/-- The first-acceptance mask commutes with restriction to the right signal register.
This uses the off-diagonal Hermitian lift and the fact that the phase tests use absolute
eigenvalues. -/
theorem bin_spectral_mask_commutes_right {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I K ℂ) (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (I ⊕ K))) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, (lift A).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (threshold : Fin n → ℝ) (t : Fin n) :
    let P := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let right : Matrix (I ⊕ K) (I ⊕ K) ℂ := diagonal (Sum.elim 0 1)
    P * right = right * P := by
  intro P right
  let sign : Matrix (I ⊕ K) (I ⊕ K) ℂ := diagonal (Sum.elim 1 (-1))
  have hAnti : lift A * sign = sign * (-lift A) := by
    ext i j
    cases i <;> cases j <;>
      simp [sign, lift, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  have hSign : P * sign = sign * P :=
    even_spectral_diagonal_commutes (lift A) sign hAnti basis eigenvalue hEigen
      (binSpectralMask threshold t) (fun x => by simp [binSpectralMask])
  have hRight : right = (1 / 2 : ℂ) • (1 - sign) := by
    ext i j
    by_cases h : i = j
    · subst j
      cases i <;> norm_num [right, sign, Matrix.one_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, Matrix.sub_apply]
    · simp [right, sign, Matrix.smul_apply, Matrix.sub_apply, h]
  rw [hRight, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul, hSign]

set_option maxHeartbeats 1200000 in
/-- Right-register readout preserves the first-acceptance spectral masks. The resulting
packets are mutually orthogonal, so their squared norms sum to that of the total readout. -/
theorem decoded_bin_right_projection {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I K ℂ) (C : Matrix M (I ⊕ K) ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hLift : signal C U = lift A)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (I ⊕ K))) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, (lift A).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hCovered : ∀ i, ∃ t, threshold t ≤ |eigenvalue i|) (b : QState (I ⊕ K)) :
    let mass := commonBinMass condition precision
    let P t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let z t := compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b)
    let right : Matrix (I ⊕ K) (I ⊕ K) ℂ := diagonal (Sum.elim 0 1)
    (‖toEuclidean_fromVec (right *ᵥ ((mass : ℂ) • (∑ t, z t)))‖ ^ 2 =
      mass ^ 2 * ∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2) ∧
    ∀ s t, P s *ᵥ (right *ᵥ z t) = if s = t then right *ᵥ z t else 0 := by
  intro mass P z right
  let R t := ((mass : ℂ) • compressedBinReciprocal (condition t) precision mass C U) * P t
  let r (t : Fin n) (i : L) : ℂ :=
    (↑((nearOptimalReciprocalPolynomial (condition t) precision).eval (eigenvalue i)) : ℂ) *
      binSpectralMask threshold t (eigenvalue i)
  let y t := right *ᵥ (R t *ᵥ b)
  obtain ⟨hPos, hMass⟩ := common_bin_mass_bounds condition precision
  have hSignal (i : L) : (signal C U).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i := by
    rw [hLift]
    exact hEigen i
  have hR (t : Fin n) : R t = spectralDiagonal basis (r t) := by
    unfold R
    rw [bin_reciprocal_spectral (condition t) precision mass C U hC hSq hPos (hMass t) basis eigenvalue hSignal,
      spectral_diagonal_mul]
  have hSelf (t : Fin n) : (P t)ᴴ = P t := by
    have hStar : star (fun i => binSpectralMask threshold t (eigenvalue i)) =
        (fun i => binSpectralMask threshold t (eigenvalue i)) := by
      funext i
      simp only [Pi.star_apply, binSpectralMask]
      split_ifs <;> simp
    simp only [P, spectralDiagonal, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc, hStar]
  have hPR (s t : Fin n) : P s * R t = if s = t then R t else 0 := by
    rw [hR, show P s = spectralDiagonal basis (fun i => binSpectralMask threshold s (eigenvalue i)) from rfl,
      spectral_diagonal_mul]
    by_cases hst : s = t
    · subst s
      simp only [ite_true]
      congr 1
      funext i
      simp only [r, bin_spectral_mask_eq threshold t (eigenvalue i) (hCovered i)]
      split_ifs <;> simp
    · rw [ite_eq_right hst]
      have hZero (i : L) : binSpectralMask threshold s (eigenvalue i) * r t i = 0 := by
        simp only [r, bin_spectral_mask_eq threshold s (eigenvalue i) (hCovered i),
          bin_spectral_mask_eq threshold t (eigenvalue i) (hCovered i)]
        split_ifs with hs ht
        · exact (hst (hs.symm.trans ht)).elim
        all_goals simp
      simp [hZero, spectralDiagonal]
  have hProj (s t : Fin n) : P s *ᵥ y t = if s = t then y t else 0 := by
    change P s *ᵥ (right *ᵥ (R t *ᵥ b)) = _
    rw [Matrix.mulVec_mulVec, bin_spectral_mask_commutes_right A basis eigenvalue hEigen threshold s,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := P s), hPR]
    split_ifs <;> simp [y, right]
  have hOrth (s t : Fin n) (hst : s ≠ t) : Inner (y s) (y t) = 0 := by
    calc
      _ = Inner (P s *ᵥ y s) (y t) := by rw [hProj, ite_eq_left rfl]
      _ = Inner (y s) ((P s)ᴴ *ᵥ y t) := inner_mulVec_left_rect _ _ _
      _ = _ := by rw [hSelf, hProj, ite_eq_right hst]; simp [Qatlib.Foundations.PureStateMath.Inner]
  have hNorm : ‖toEuclidean_fromVec (∑ t, y t)‖ ^ 2 =
      ∑ t, ‖toEuclidean_fromVec (y t)‖ ^ 2 := by
    have hg (s t : Fin n) : Inner (y s) (y t) =
        if s = t then ((‖toEuclidean_fromVec (y s)‖ ^ 2 : ℝ) : ℂ) else 0 := by
      by_cases h : s = t
      · subst t
        simp only [ite_true, inner_self, norm_toEuclidean_fromVec_sq, Complex.ofReal_sum]
      · simp only [ite_eq_right h, hOrth s t h]
    have hp := sum_norm_sq_diagonal_gram y (fun _ => 1) (fun t => ‖toEuclidean_fromVec (y t)‖ ^ 2) (by
      intro s t
      by_cases h : s = t
      · simpa only [ite_eq_left h] using hg s t
      · simpa only [ite_eq_right h] using hg s t)
    simpa only [MeasureProb, BornProb, norm_toEuclidean_fromVec_sq, one_smul, norm_one, one_pow, one_mul] using hp
  have hY (t : Fin n) : y t = (mass : ℂ) • (right *ᵥ z t) := by
    unfold y R z
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hTotal : right *ᵥ ((mass : ℂ) • ∑ t, z t) = ∑ t, y t := by
    rw [Finset.smul_sum, Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Matrix.mulVec_smul, hY]
  have hRightNorm (t : Fin n) : ‖toEuclidean_fromVec (right *ᵥ z t)‖ ^ 2 = ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type]
    simp [right, Matrix.mulVec_diagonal]
  constructor
  · rw [hTotal, hNorm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [hY, show toEuclidean_fromVec ((mass : ℂ) • (right *ᵥ z t)) =
        (mass : ℂ) • toEuclidean_fromVec (right *ᵥ z t) from rfl,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPos, mul_pow, hRightNorm]
  · intro s t
    have hMassNe : (mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hPos.ne'
    have he := hProj s t
    rw [hY, Matrix.mulVec_smul] at he
    have hc := congrArg (fun x : QState (I ⊕ K) => ((mass : ℂ)⁻¹) • x) he
    by_cases hst : s = t
    · simpa only [ite_eq_left hst, smul_smul, inv_mul_cancel₀ hMassNe, one_smul] using hc
    · simpa only [ite_eq_right hst, smul_smul, inv_mul_cancel₀ hMassNe, one_smul, smul_zero] using hc

/-- The squared norm of the combined right-register output equals the sum of the
individual probabilities, including the common coefficient scale. -/
theorem decoded_bin_right_norm_sq {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I K ℂ) (C : Matrix M (I ⊕ K) ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hLift : signal C U = lift A)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (I ⊕ K))) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, (lift A).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (condition threshold : Fin n → ℝ) (precision : ℝ)
    (hCovered : ∀ i, ∃ t, threshold t ≤ |eigenvalue i|) (b : QState (I ⊕ K)) :
    let mass := commonBinMass condition precision
    let P t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let z t := compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b)
    let right : Matrix (I ⊕ K) (I ⊕ K) ℂ := diagonal (Sum.elim 0 1)
    ‖toEuclidean_fromVec (right *ᵥ ((mass : ℂ) • (∑ t, z t)))‖ ^ 2 =
      mass ^ 2 * ∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2 := by
  intro mass P z right
  exact (decoded_bin_right_projection A C U hC hSq hLift basis eigenvalue hEigen condition threshold
    precision hCovered b).1

/-- The inverse of an off-diagonal lift sends a left-supported residual to the right register. -/
private theorem lift_inverse_right_support {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I K ℂ) (X : Matrix (I ⊕ K) (I ⊕ K) ℂ)
    (hLeft : X * lift A = 1) (hRight : lift A * X = 1) (b : QState (I ⊕ K))
    (hb : ∀ k : K, b (Sum.inr k) = 0) :
    ∀ i : I, (X *ᵥ b) (Sum.inl i) = 0 := by
  let y := X *ᵥ b
  let left : QState (I ⊕ K) := Sum.elim (y ∘ Sum.inl) 0
  have hy : lift A *ᵥ y = b := by
    change lift A *ᵥ (X *ᵥ b) = b
    rw [Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]
  have hBlock : Aᴴ *ᵥ (y ∘ Sum.inl) = 0 := by
    rw [lift, Matrix.fromBlocks_mulVec] at hy
    funext k
    have hk := congrFun hy (Sum.inr k)
    simpa [hb, Function.comp_apply] using hk
  have hZero : lift A *ᵥ left = 0 := by
    rw [lift, Matrix.fromBlocks_mulVec]
    funext p
    cases p <;> simp [left, hBlock]
  have hLeftZero : left = 0 := by
    calc
      left = X *ᵥ (lift A *ᵥ left) := by rw [Matrix.mulVec_mulVec, hLeft, Matrix.one_mulVec]
      _ = 0 := by rw [hZero, Matrix.mulVec_zero]
  intro i
  exact congrFun hLeftZero (Sum.inl i)

set_option maxHeartbeats 1100000 in
/-- The combined physical output approximates the scaled inverse solution in Euclidean
norm. Its right-register probability also gives a success amplitude lower bound that
is independent of the number of bins. -/
theorem decoded_bin_right_solution_bounds {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I K ℂ) (C : Matrix M (I ⊕ K) ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hLift : signal C U = lift A)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (I ⊕ K))) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, (lift A).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (hCondition : ∀ t, 1 < condition t)
    (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hCovered : ∀ i, ∃ t, threshold t ≤ |eigenvalue i|) (hBound : ∀ i, |eigenvalue i| ≤ 1)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t) (b : QState (I ⊕ K))
    (hb : ∀ k : K, b (Sum.inr k) = 0) :
    let mass := commonBinMass condition precision
    let P t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let z t := compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b)
    let solution := spectralDiagonal basis (fun i => (eigenvalue i : ℂ)⁻¹) *ᵥ b
    let right : Matrix (I ⊕ K) (I ⊕ K) ℂ := diagonal (Sum.elim 0 1)
    (‖toEuclidean_fromVec ((∑ t, right *ᵥ z t) - (mass : ℂ)⁻¹ • solution)‖ ≤
      (2 * precision) * ‖toEuclidean_fromVec b‖ / mass) ∧
    (‖toEuclidean_fromVec solution‖ - (2 * precision) * ‖toEuclidean_fromVec b‖ ≤
      mass * Real.sqrt (∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2)) := by
  intro mass P z solution right
  let X := spectralDiagonal basis (fun i => (eigenvalue i : ℂ)⁻¹)
  let combined := (mass : ℂ) • ∑ t, z t
  have hNonzero (i : L) : (eigenvalue i : ℂ) ≠ 0 := by
    obtain ⟨t, ht⟩ := hCovered i
    exact Complex.ofReal_ne_zero.mpr (abs_pos.mp ((inv_pos.mpr (zero_lt_one.trans (hCondition t))).trans_le
      ((hCutoff t).trans ht)))
  have hDiagonal : lift A = spectralDiagonal basis (fun i => (eigenvalue i : ℂ)) :=
    eq_spectralDiagonal_of_action basis (lift A) _ hEigen
  have hLeftCoeff : (fun i => ((eigenvalue i : ℂ)⁻¹) * (eigenvalue i : ℂ)) = fun _ => 1 :=
    funext fun i => inv_mul_cancel₀ (hNonzero i)
  have hRightCoeff : (fun i => (eigenvalue i : ℂ) * ((eigenvalue i : ℂ)⁻¹)) = fun _ => 1 :=
    funext fun i => mul_inv_cancel₀ (hNonzero i)
  have hLeft : X * lift A = 1 := by
    dsimp only [X]
    rw [hDiagonal, spectral_diagonal_mul, hLeftCoeff, spectralDiagonal_const, one_smul]
  have hRight : lift A * X = 1 := by
    dsimp only [X]
    rw [hDiagonal, spectral_diagonal_mul, hRightCoeff, spectralDiagonal_const, one_smul]
  have hRestore : right *ᵥ solution = solution := by
    have hl := lift_inverse_right_support A X hLeft hRight b hb
    funext p
    cases p <;> simp [right, Matrix.mulVec_diagonal, show ∀ i : I, solution (Sum.inl i) = 0 from hl]
  have hContract : ‖right‖ ≤ 1 := by
    unfold right
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by cases i <;> simp)
  have hSignal (i : L) : (signal C U).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i := by
    rw [hLift]
    exact hEigen i
  have hClose : ‖toEuclidean_fromVec (combined - solution)‖ ≤ (2 * precision) * ‖toEuclidean_fromVec b‖ :=
    stencil_bin_decoded_sum_error C U hC hSq condition threshold precision hCondition hPrecision hHalf
      basis eigenvalue hSignal hCovered hBound hCutoff b
  have hCloseRight : ‖toEuclidean_fromVec (right *ᵥ combined - solution)‖ ≤
      (2 * precision) * ‖toEuclidean_fromVec b‖ := by
    rw [show right *ᵥ combined - solution = right *ᵥ (combined - solution) by
      rw [Matrix.mulVec_sub, hRestore]]
    exact (stateVector_mulVec_norm_le right (combined - solution)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hContract).trans hClose)
  have hMassPos : 0 < mass := (common_bin_mass_bounds condition precision).1
  constructor
  · have hMassNe : (mass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMassPos.ne'
    have hScaled : (mass : ℂ) • ((∑ t, right *ᵥ z t) - (mass : ℂ)⁻¹ • solution) =
        right *ᵥ combined - solution := by
      unfold combined
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hMassNe, one_smul, Matrix.mulVec_smul, Matrix.mulVec_sum]
    have hScaledBound := hCloseRight
    rw [← hScaled] at hScaledBound
    change ‖(mass : ℂ) • toEuclidean_fromVec ((∑ t, right *ᵥ z t) - (mass : ℂ)⁻¹ • solution)‖ ≤ _ at hScaledBound
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMassPos] at hScaledBound
    exact (le_div_iff₀ hMassPos).2 (by simpa only [mul_comm mass] using hScaledBound)
  · have hNormSq : ‖toEuclidean_fromVec (right *ᵥ combined)‖ ^ 2 =
        mass ^ 2 * ∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2 :=
      decoded_bin_right_norm_sq A C U hC hSq hLift basis eigenvalue hEigen condition threshold precision hCovered b
    have hNonneg : 0 ≤ (∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2) := by positivity
    have hNorm : ‖toEuclidean_fromVec (right *ᵥ combined)‖ =
        mass * Real.sqrt (∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2) := by
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hMassPos.le (Real.sqrt_nonneg _))).mp
      rw [hNormSq, mul_pow, Real.sq_sqrt hNonneg]
    have hDiff := norm_sub_norm_le (toEuclidean_fromVec solution) (toEuclidean_fromVec (right *ᵥ combined))
    rw [norm_sub_rev] at hDiff
    have h := hDiff.trans hCloseRight
    rw [hNorm] at h
    linarith

/-- The right-register success amplitude is bounded below by the inverse response
minus the reciprocal approximation error, divided by the coefficient normalization. -/
theorem decoded_bin_right_amplitude_lower {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I K ℂ) (C : Matrix M (I ⊕ K) ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hLift : signal C U = lift A)
    (basis : OrthonormalBasis L ℂ (EuclideanSpace ℂ (I ⊕ K))) (eigenvalue : L → ℝ)
    (hEigen : ∀ i, (lift A).toEuclideanLin (basis i) = (eigenvalue i : ℂ) • basis i)
    (condition threshold : Fin n → ℝ) (precision : ℝ) (hCondition : ∀ t, 1 < condition t)
    (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (hCovered : ∀ i, ∃ t, threshold t ≤ |eigenvalue i|) (hBound : ∀ i, |eigenvalue i| ≤ 1)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t) (b : QState (I ⊕ K))
    (hb : ∀ k : K, b (Sum.inr k) = 0) :
    let mass := commonBinMass condition precision
    let P t := spectralDiagonal basis (fun i => binSpectralMask threshold t (eigenvalue i))
    let z t := compressedBinReciprocal (condition t) precision mass C U *ᵥ (P t *ᵥ b)
    let solution := spectralDiagonal basis (fun i => (eigenvalue i : ℂ)⁻¹) *ᵥ b
    ‖toEuclidean_fromVec solution‖ - (2 * precision) * ‖toEuclidean_fromVec b‖ ≤
      mass * Real.sqrt (∑ t, ∑ k : K, ‖z t (Sum.inr k)‖ ^ 2) := by
  intro mass P z solution
  exact (decoded_bin_right_solution_bounds A C U hC hSq hLift basis eigenvalue hEigen condition threshold
    precision hCondition hPrecision hHalf hCovered hBound hCutoff b hb).2

end Qatlib.Papers.QFVMChen22.TimeStep
