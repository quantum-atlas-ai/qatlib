/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Concepts.BlockEncoding.Postselection


open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Concepts.LchsSimulation.LchsRep

open Matrix Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

noncomputable def imaginaryWord {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) : List (Matrix I I ℂ) :=
  (List.replicate r [NormedSpace.exp (-(t / (r : ℝ)) • A),
    NormedSpace.exp (-(t / (r : ℝ)) • B)]).flatten

noncomputable def imaginaryRun {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) : Matrix I I ℂ :=
  (imaginaryWord A B t r).prod

theorem imaginary_exp_psd_contraction {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp (-s • A)‖ ≤ 1 := by
  let V := fun u : ℝ => NormedSpace.exp (-u • A)
  have hd (u : ℝ) : HasDerivAt V (-(A * V u)) u := by
    simpa only [V, smul_neg, neg_smul, neg_mul] using!
      hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) u
  have he := (ordered_evolution_dyson_semantics I (fun _ => A) continuous_const).2.2.2.2
    0 V (by simp [V]) hd
  have hc := ordered_evolution_psd_contraction I (fun _ => A) continuous_const
    (fun _ => by rw [hA.isHermitian.eq]; exact hA.add hA) 0 s hs
  rw [← he] at hc
  exact hc

private noncomputable def ipExp {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ := NormedSpace.exp (s • X)

private theorem ipExp_deriv {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (s : ℝ) : HasDerivAt (ipExp X) (X * ipExp X s) s :=
  hasDerivAt_exp_smul_const' X s

private theorem ipExp_scaled_deriv {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (s u : ℝ) :
    HasDerivAt (fun v => ipExp X (v * s)) (s • (X * ipExp X (u * s))) u := by
  convert! (ipExp_deriv X (u * s)).scomp u ((hasDerivAt_id u).mul_const s) using 1
  simp

private theorem ipExp_backward_scaled_deriv {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (s u : ℝ) :
    HasDerivAt (fun v => ipExp X ((1 - v) * s))
      ((-s) • (ipExp X ((1 - u) * s) * X)) u := by
  have hi : HasDerivAt (fun v : ℝ => (1 - v) * s) (-s) u := by
    simpa using! ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).mul_const s
  convert! (hasDerivAt_exp_smul_const (𝕂 := ℝ) X ((1 - u) * s)).scomp u hi using 1

private theorem imaginary_exp_commutator_bound {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (hX : ∀ s : ℝ, 0 ≤ s → ‖ipExp X s‖ ≤ 1)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖ipExp X s * Y - Y * ipExp X s‖ ≤ s * ‖X * Y - Y * X‖ := by
  let f : ℝ → Matrix I I ℂ := fun u => ipExp X ((1 - u) * s) * Y * ipExp X (u * s)
  have hd (u : ℝ) : HasDerivAt f
      (s • (ipExp X ((1 - u) * s) * (Y * X - X * Y) * ipExp X (u * s))) u := by
    convert! ((ipExp_backward_scaled_deriv X s u).mul_const Y).mul
      (ipExp_scaled_deriv X s u) using 1
    (try dsimp [f])
    simp only [neg_smul, neg_mul, smul_mul_assoc, mul_smul_comm, smul_sub, mul_sub, sub_mul,
        mul_assoc]
    module
  have hb (u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
      ‖s • (ipExp X ((1 - u) * s) * (Y * X - X * Y) * ipExp X (u * s))‖ ≤
        s * ‖X * Y - Y * X‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs]
    apply mul_le_mul_of_nonneg_left _ hs
    have hn := l2_norm_sandwich_le (ipExp X ((1 - u) * s)) (Y * X - X * Y)
      (ipExp X (u * s)) (hX _ (mul_nonneg (by linarith [hu.2]) hs))
      (hX _ (mul_nonneg hu.1 hs))
    exact hn.trans_eq (norm_sub_rev _ _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u (_ : u ∈ Icc (0 : ℝ) 1) => (hd u).hasDerivWithinAt) hb 1 ⟨zero_le_one, le_rfl⟩
  simpa only [f, ipExp, sub_self, zero_mul, zero_smul, NormedSpace.exp_zero,
    mul_one, one_mul, sub_zero, one_smul, norm_sub_rev] using! h

private theorem imaginary_lie_contraction_generators {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ)
    (hX : ∀ s : ℝ, 0 ≤ s → ‖ipExp X s‖ ≤ 1)
    (hY : ∀ s : ℝ, 0 ≤ s → ‖ipExp Y s‖ ≤ 1)
    (hZ : ∀ s : ℝ, 0 ≤ s → ‖ipExp (X + Y) s‖ ≤ 1) :
    ‖ipExp X 1 * ipExp Y 1 - ipExp (X + Y) 1‖ ≤ ‖X * Y - Y * X‖ / 2 := by
  let f : ℝ → Matrix I I ℂ := fun s => ipExp (X + Y) (1 - s) * ipExp X s * ipExp Y s
  let d : ℝ → Matrix I I ℂ := fun s =>
    ipExp (X + Y) (1 - s) * (ipExp X s * Y - Y * ipExp X s) * ipExp Y s
  have hd (s : ℝ) : HasDerivAt f (d s) s := by
    convert! ((ipExp_backward_scaled_deriv (X + Y) 1 s).mul (ipExp_deriv X s)).mul
      (ipExp_deriv Y s) using 1
    · dsimp [f, ipExp]
      simp only [mul_one]
      rfl
    · dsimp [d, ipExp]
      simp only [mul_one, neg_one_smul]
      noncomm_ring
  have hdn (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) : ‖d s‖ ≤ s * ‖X * Y - Y * X‖ := by
    apply (l2_norm_sandwich_le _ _ _ (hZ _ (by linarith [hs.2])) (hY _ hs.1)).trans
    exact imaginary_exp_commutator_bound X Y hX s hs.1
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s - f 0‖ ≤ s ^ 2 * ‖X * Y - Y * X‖ / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => f s - f 0) (f' := d)
      (B := fun s => s ^ 2 * ‖X * Y - Y * X‖ / 2) (B' := fun s => s * ‖X * Y - Y * X‖)
      (fun s _ => ((hd s).sub_const _).continuousAt.continuousWithinAt)
      (fun s _ => ((hd s).sub_const _).hasDerivWithinAt) (by simp) ?_ hdn
    intro s
    convert! ((hasDerivAt_id s).pow 2).mul_const (‖X * Y - Y * X‖ / 2) using 1
    · ext u; dsimp; ring
    · dsimp; ring
  simpa [f, ipExp] using! hbound 1 ⟨zero_le_one, le_rfl⟩

theorem imaginary_psd_lie_segment_error {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp (-s • A) * NormedSpace.exp (-s • B) -
      NormedSpace.exp (-s • (A + B))‖ ≤ s ^ 2 * ‖A * B - B * A‖ / 2 := by
  let X := -s • A
  let Y := -s • B
  have hn (H : Matrix I I ℂ) (hH : H.PosSemidef) (u : ℝ) (hu : 0 ≤ u) :
      ‖ipExp (-s • H) u‖ ≤ 1 := by
    simpa only [ipExp, smul_smul, mul_neg] using!
      imaginary_exp_psd_contraction H hH (u * s) (mul_nonneg hu hs)
  have hz : X + Y = -s • (A + B) := (smul_add _ _ _).symm
  have h := imaginary_lie_contraction_generators X Y (hn A hA) (hn B hB)
    (by rw [hz]; exact hn (A + B) (hA.add hB))
  have hc : X * Y - Y * X = s ^ 2 • (A * B - B * A) := by
    dsimp [X, Y]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_sub]
    congr 1
    ring
  rw [hz, hc, norm_smul, Real.norm_of_nonneg (sq_nonneg s)] at h
  simpa only [ipExp, one_smul] using! h

theorem imaginaryRun_power {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) :
    imaginaryRun A B t r =
      (NormedSpace.exp (-(t / (r : ℝ)) • A) * NormedSpace.exp (-(t / (r : ℝ)) • B)) ^ r := by
  simp [imaginaryRun, imaginaryWord, List.prod_flatten, List.map_replicate]

theorem imaginaryWord_length {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (t : ℝ) (r : ℕ) : (imaginaryWord A B t r).length = 2 * r := by
  simp [imaginaryWord, List.length_flatten, List.map_replicate, Nat.mul_comm]

theorem imaginary_contraction_pow_norm {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : ‖U‖ ≤ 1) (r : ℕ) : ‖U ^ r‖ ≤ 1 := by
  exact l2_norm_pow_le_one U hU r

theorem imaginary_contraction_power_error {I : Type} [Fintype I] [DecidableEq I]
    (U V : Matrix I I ℂ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (r : ℕ) :
    ‖U ^ r - V ^ r‖ ≤ (r : ℝ) * ‖U - V‖ := by
  exact l2_norm_pow_sub_pow_le U V hU hV r

theorem imaginary_exp_power {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (s : ℝ) (r : ℕ) :
    (NormedSpace.exp (-s • A)) ^ r = NormedSpace.exp (-((r : ℝ) * s) • A) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hc : Commute (-((r : ℝ) * s) • A) (-s • A) :=
      ((Commute.refl A).smul_left _).smul_right _
    rw [pow_succ, ih, ← Matrix.exp_add_of_commute _ _ hc]
    congr 1
    rw [← add_smul]
    push_cast
    congr 1
    ring

theorem imaginary_product_contraction_and_commutator_error :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
      (t : ℝ) (r : ℕ), A.PosSemidef → B.PosSemidef → 0 ≤ t → 0 < r →
      ‖imaginaryRun A B t r‖ ≤ 1 ∧ (imaginaryWord A B t r).length = 2 * r ∧
      ‖imaginaryRun A B t r - NormedSpace.exp (-t • (A + B))‖ ≤
        t ^ 2 * ‖A * B - B * A‖ / (2 * r) := by
  intro I _ _ A B t r hA hB ht hr
  let s := t / (r : ℝ)
  let U := NormedSpace.exp (-s • A) * NormedSpace.exp (-s • B)
  let V := NormedSpace.exp (-s • (A + B))
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hs : 0 ≤ s := div_nonneg ht hrR.le
  have hU : ‖U‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul (imaginary_exp_psd_contraction A hA s hs)
      (imaginary_exp_psd_contraction B hB s hs) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hV : ‖V‖ ≤ 1 := imaginary_exp_psd_contraction (A + B) (hA.add hB) s hs
  have hVpow : V ^ r = NormedSpace.exp (-t • (A + B)) := by
    rw [imaginary_exp_power]
    congr 1
    dsimp [s]
    rw [mul_div_cancel₀ _ hrR.ne']
  refine ⟨?_, imaginaryWord_length A B t r, ?_⟩
  · rw [imaginaryRun_power]
    exact imaginary_contraction_pow_norm U hU r
  · rw [imaginaryRun_power, ← hVpow]
    apply (imaginary_contraction_power_error U V hU hV r).trans
    have he := mul_le_mul_of_nonneg_left (imaginary_psd_lie_segment_error A B hA hB s hs)
      (Nat.cast_nonneg r)
    apply he.trans_eq
    dsimp [s]
    field_simp

theorem imaginary_product_actual_postselection_consumer :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
      (t : ℝ) (r : ℕ) (ψ : I → ℂ), A.PosSemidef → B.PosSemidef → 0 ≤ t →
      0 < r → ‖toEuclidean_fromVec ψ‖ = 1 →
      let v := toEuclidean_fromVec ((NormedSpace.exp (-t • (A + B))).mulVec ψ)
      let y := toEuclidean_fromVec ((imaginaryRun A B t r).mulVec ψ)
      let η := t ^ 2 * ‖A * B - B * A‖ / (2 * r)
      η < ‖v‖ → (‖v‖ - η) ^ 2 ≤ ‖y‖ ^ 2 ∧
        ‖NormedSpace.normalize y - NormedSpace.normalize v‖ ≤ 2 * η / ‖v‖ ∧ ‖y‖ ≤ 1 := by
  intro I _ _ A B t r ψ hA hB ht hr hψ v y η hgap
  have h := imaginary_product_contraction_and_commutator_error I A B t r hA hB ht hr
  exact contractive_mulVec_output_of_gap (imaginaryRun A B t r)
    (NormedSpace.exp (-t • (A + B))) ψ η h.1 h.2.2 hψ hgap

end Qatlib.Concepts.LchsSimulation.LchsRep
