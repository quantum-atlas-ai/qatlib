/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.DistinctLB26.MainResults.Execution.LinearRun
public import Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelianState

@[expose] public section

/-!
# Actual computational-input readout of the Fourier state

The input-register change of basis is the normalized finite-group Fourier
transform. It preserves the Hilbert norm. Its canonical character indexing
identifies the transformed zero-input state with the physical algorithm's
uniform family of input executions.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Papers.DistinctLB26.MainResults.Execution

variable {n q : ℕ} [NeZero q] {W : Type*} [Fintype W]

/-- Negative canonical characters label the computational readout basis. -/
def readoutEquiv : Label n q ≃ AddChar (Label n q) ℂ :=
  inputCharEquiv.trans (Equiv.neg _)

/-- The finite-group Fourier transform with its actual Hilbert-space norm. -/
theorem fourier_norm (v : EuclideanSpace ℂ (Label n q)) :
    ‖WithLp.toLp 2 (fourier (fun σ => v σ))‖ = ‖v‖ := by
  have hi := Qatlib.Concepts.WalkFind.UniformThree.inner_fourier
    (fun σ : Label n q => v σ) (fun σ : Label n q => v σ)
  have he : inner ℂ (WithLp.toLp 2 (fourier (fun σ => v σ)))
      (WithLp.toLp 2 (fourier (fun σ => v σ))) = inner ℂ v v := by
    simpa only [EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_eq_star_dotProduct,
      Qatlib.Foundations.PureStateMath.Inner, dotProduct_comm] using hi
  have hs : ‖WithLp.toLp 2 (fourier (fun σ => v σ))‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, he]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fourier (fun σ => v σ))), norm_nonneg v]

/-- The readout of a hidden-input column using the complete canonical Fourier basis. -/
def decode (v : EuclideanSpace ℂ (Label n q)) : EuclideanSpace ℂ (Label n q) :=
  WithLp.toLp 2 (fun x => fourier (fun σ => v σ) (readoutEquiv x))

/-- Reindexing the complete character basis preserves the physical input norm. -/
theorem decode_norm (v : EuclideanSpace ℂ (Label n q)) : ‖decode v‖ = ‖v‖ := by
  have hs : ‖decode v‖ ^ 2 =
      ‖WithLp.toLp 2 (fourier (fun σ => v σ))‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv readoutEquiv _ _ (fun _ => rfl)
  rw [fourier_norm] at hs
  nlinarith [norm_nonneg (decode v), norm_nonneg v]

/-- The actual input amplitudes are the canonical character-weighted Fourier sum. -/
theorem decode_apply (v : EuclideanSpace ℂ (Label n q)) (x : Label n q) :
    decode v x = ((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) *
      ∑ σ : Label n q, inputChar x σ * v σ := by
  change fourier (fun σ => v σ) (-inputChar x) = _
  rw [fourier_apply]
  simp only [fourierScale, AddChar.neg_apply, AddChar.map_neg_eq_conj,
    Complex.conj_conj]

/-- Orthogonality of two different physical input plane waves. -/
theorem input_pair (x y : Label n q) :
    (∑ σ : Label n q, inputChar x σ * inputChar y (-σ)) =
      if x = y then (Fintype.card (Label n q) : ℂ) else 0 := by
  classical
  simpa only [AddChar.sub_apply, sub_eq_zero, inputChar_injective.eq_iff] using
    (AddChar.sum_eq_ite (inputChar x - inputChar y))

/-- A Fourier-label column at one physical work coordinate. -/
def inputColumn (ψ : Joint n q W) (a : Work n q W) : EuclideanSpace ℂ (Label n q) :=
  WithLp.toLp 2 (fun σ => ψ (σ, a))

/-- Change only the hidden input register into the computational basis. -/
def readout (ψ : Joint n q W) : Joint n q W :=
  WithLp.toLp 2 (fun z => decode (inputColumn ψ z.2) z.1)

/-- The hidden-register Fourier transform preserves the entire joint norm. -/
theorem readout_norm (ψ : Joint n q W) : ‖readout ψ‖ = ‖ψ‖ := by
  have hs (a : Work n q W) :
      (∑ x : Label n q, ‖decode (inputColumn ψ a) x‖ ^ 2) =
        ∑ σ : Label n q, ‖ψ (σ, a)‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, decode_norm, EuclideanSpace.norm_sq_eq]
    rfl
  have hsq : ‖readout ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun σ a => ‖ψ (σ, a)‖ ^ 2)]
    exact Finset.sum_congr rfl fun a _ => hs a
  nlinarith [norm_nonneg (readout ψ), norm_nonneg ψ]

omit [Fintype W] in
/-- A plane wave decodes to exactly its own computational input. -/
theorem readout_plane (y : Label n q) (φ : Local n q W)
    (x : Label n q) (a : Work n q W) :
    readout (plane y φ) (x, a) = if x = y then φ a else 0 := by
  classical
  change decode (inputColumn (plane y φ) a) x = _
  rw [decode_apply]
  let c : ℂ := (Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹
  change c * (∑ σ : Label n q,
    inputChar x σ * ((inputChar y (-σ) * c) * φ a)) = _
  calc
    c * (∑ σ : Label n q, inputChar x σ * ((inputChar y (-σ) * c) * φ a)) =
        (c * c) * (∑ σ : Label n q, inputChar x σ * inputChar y (-σ)) * φ a := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      congr 1
      funext σ
      ring
    _ = if x = y then φ a else 0 := by
      rw [input_pair]
      by_cases h : x = y
      · simp only [h, ite_true]
        change ((fourierScale (Label n q) * fourierScale (Label n q)) * _) * _ = _
        rw [fourierScale_sq_mul_card, one_mul]
      · simp only [h, ite_false, mul_zero, zero_mul]

/-- The hidden-register Fourier readout is an actual complex linear map. -/
def readoutLinear : Joint n q W →ₗ[ℂ] Joint n q W where
  toFun := readout
  map_add' ψ φ := by
    ext z
    change decode (inputColumn (ψ + φ) z.2) z.1 =
      decode (inputColumn ψ z.2) z.1 + decode (inputColumn φ z.2) z.1
    simp only [decode_apply, inputColumn, PiLp.add_apply,
      mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext z
    change decode (inputColumn (c • ψ) z.2) z.1 = c * decode (inputColumn ψ z.2) z.1
    simp only [decode_apply, inputColumn, PiLp.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring

/-- Computational readout is the uniformly weighted family of the actual physical input runs. -/
theorem readout_execute (prog : List (Instr n q W)) (φ : Local n q W)
    (x : Label n q) (a : Work n q W) :
    readout (execute prog (zeroInput φ)) (x, a) =
      ((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) * inputRun x prog φ a := by
  classical
  have hv : readout (execute prog (zeroInput φ)) =
      ((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) •
        ∑ y : Label n q, readout (plane y (inputRun y prog φ)) := by
    change readoutLinear (execute prog (zeroInput φ)) = _
    rw [execute_uniform, map_smul, map_sum]
    rfl
  rw [hv]
  change (jointCoord (x, a)) (((Real.sqrt (Fintype.card (Label n q)) : ℂ)⁻¹) •
    ∑ y : Label n q,
    readout (plane y (inputRun y prog φ))) = _
  rw [map_smul, map_sum]
  change _ * (∑ y : Label n q, readout (plane y (inputRun y prog φ)) (x, a)) = _
  simp only [readout_plane]
  simp

end Qatlib.Papers.DistinctLB26.MainResults.Execution
