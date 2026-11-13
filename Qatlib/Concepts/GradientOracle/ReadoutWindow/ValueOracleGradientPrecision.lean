/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.C2GradientAlg.ValueOracleGradientConsumers
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Rounded value oracles and gradient precision

This module rounds real phase tables to modular value labels and prepares their character
register with an inverse Fourier transform. It transfers rounding and phase-error bounds to
gradient readout, including a cosine-squared guarantee for affine targets, in the construction
of [Jordan2005Gradient].

## Main statements

* `gradient_value_rounded_table_precision`: modular phase error is at most `1/(2*Q)`.
* `gradient_value_c2_rounded_consumer`: a rounded oracle gives an explicit joint coordinate
  success bound for a function with bounded second derivative.
* `gradient_affine_precision_cos2_window`: bounded phase error gives probability at least `cos θ
  ^ 2` at the affine output.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.GradientOracle.C2GradientAlg
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Qatlib.Concepts.GradientOracle.ReadoutWindow
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The modular value table obtained by rounding `Q*w z` to the nearest integer and reducing
modulo `Q`. -/
noncomputable def gradientValueRoundedTable (d M Q : ℕ) [NeZero Q]
    (w : GradientGrid d M → ℝ) : GradientGrid d M → ZMod Q :=
  fun z => ((round ((Q : ℝ) * w z) : ℤ) : ZMod Q)

/-- The single fixed-gate circuit applying the inverse modular Fourier transform to the target
register and identity to the data register. -/
noncomputable def gradientCharPrep (d M Q : ℕ) [NeZero Q] :
    Circuit (GradientGrid d M × ZMod Q) :=
  [Step.gate (TensorGate (1 : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
    ((zmodQFTGate (N := Q))ᴴ))]

/-- The circuit word formed by `gradientCharPrep d M Q ++ gradientValueWord d M Q`. -/
noncomputable def gradientValueProgram (d M Q : ℕ) [NeZero Q] :
    Circuit (GradientGrid d M × ZMod Q) :=
  gradientCharPrep d M Q ++ gradientValueWord d M Q

/-- The phase decoded from the rounded value table differs from the target real phase by at most
`1/(2*Q)` modulo an integer. See [Jordan2005Gradient]. -/
theorem gradient_value_rounded_table_precision :
    ∀ (d M Q : ℕ) [NeZero Q] (w : GradientGrid d M → ℝ) (z : GradientGrid d M),
      ∃ k : ℤ, |gradientValuePhase Q (gradientValueRoundedTable d M Q w) z-w z-k| ≤ 1/(2*Q) := by
  intro d M Q _ w z
  let r : ℤ := round ((Q : ℝ)*w z)
  let s : ℕ := (r : ZMod Q).val
  let j : ℤ := r/(Q : ℤ)
  have hQ : 0 < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
  have hm : (s : ℤ)+(Q : ℤ)*j=r := by
    rw [show (s : ℤ)=r%(Q : ℤ) from ZMod.val_intCast r]
    exact Int.emod_add_mul_ediv r Q
  have hmr : (s : ℝ)+(Q : ℝ)*(j : ℝ)=(r : ℝ) := by exact_mod_cast hm
  refine ⟨-j,?_⟩
  have he : gradientValuePhase Q (gradientValueRoundedTable d M Q w) z-w z-(-j : ℤ) =
      ((r : ℝ)-(Q : ℝ)*w z)/(Q : ℝ) := by
    change (s : ℝ)/(Q : ℝ)-w z-((-j : ℤ) : ℝ) = _
    push_cast
    field_simp
    linarith only [hmr]
  have hb : |(r : ℝ)-(Q : ℝ)*w z| ≤ 1/2 := by
    simpa only [abs_sub_comm] using! (abs_sub_round ((Q : ℝ)*w z))
  rw [he,abs_div,abs_of_pos hQ]
  calc
    _ ≤ (1/2)/(Q : ℝ) := div_le_div_of_nonneg_right hb hQ.le
    _ = _ := by ring

/-- Under the stated smoothness, Hessian, derivative-range, and grid assumptions, rounded value
readout estimates all signed derivative coordinates within `w` with probability at least
`1-16*d/(M*w)-π*M*H*h*d/2-2*π/Q`. See [Jordan2005Gradient]. -/
theorem gradient_value_c2_rounded_consumer :
    ∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q]
      (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (H h w : ℝ),
      ContDiff ℝ 2 f → 0 ≤ H → (∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) →
      2 ≤ M → 0 < h → 0 < w → w ≤ 1/8 →
      let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
      (∀ j, |g j| ≤ 1/4) →
      let φ := fun z : GradientGrid d M => (M : ℝ)/h*f (x+
        WithLp.toLp 2 (fun j : Fin d => h*((z j).val/(M : ℝ)-1/2)))
      MeasureProb (gradientReadout d M hM (gradientValuePhase Q (gradientValueRoundedTable d M Q φ)))
        (Finset.univ.filter (fun z => ∀ j : Fin d, |signedGridValue M (z j)-g j| ≤ w)) ≥
        1-16*d/((M : ℝ)*w)-Real.pi*M*H*h*d/2-2*Real.pi/(Q : ℝ) := by
  intro d M Q hM _ f x H h w hf hH hessian hM2 hh hw0 hw
  (try dsimp only)
  intro hg
  let φ := fun z : GradientGrid d M => (M : ℝ)/h*f (x+
    WithLp.toLp 2 (fun j : Fin d => h*((z j).val/(M : ℝ)-1/2)))
  have he := gradient_value_c2_same_record_consumer d M Q hM (gradientValueRoundedTable d M Q φ)
    f x H h w (1/(2*(Q : ℝ))) hf hH hessian hM2 hh hw0 hw (by positivity) hg
    (gradient_value_rounded_table_precision d M Q φ)
  have hδ : 4*Real.pi*(1/(2*(Q : ℝ)))=2*Real.pi/(Q : ℝ) := by ring
  rw [hδ] at he
  exact he

/-- The inverse target Fourier gate maps the target basis state at one to `gradientKickState`,
leaving the zero data state unchanged; the preparation circuit has zero queries and one
gate. See [Jordan2005Gradient]. -/
theorem gradient_char_prep_inverse_qft :
    ∀ (d M : ℕ) (hM : 0 < M) (Q : ℕ) [NeZero Q],
      ApplyGate (TensorGate (1 : Matrix (GradientGrid d M) (GradientGrid d M) ℂ)
          ((zmodQFTGate (N := Q))ᴴ))
        (TensorState (Ket (gradientZero d M hM)) (Ket 1)) =
        TensorState (Ket (gradientZero d M hM)) (gradientKickState Q) ∧
      QueryCount (gradientCharPrep d M Q)=0 ∧ GateCount (gradientCharPrep d M Q)=1 := by
  intro d M hM Q _
  have hchar : ApplyGate ((zmodQFTGate (N := Q))ᴴ) (Ket 1)=gradientKickState Q := by
    ext y
    simp only [ApplyGate,Matrix.mulVec,dotProduct,Ket,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,Matrix.conjTranspose_apply,zmodQFTGate_apply,
      one_mul,gradientKickState,star_mul,Complex.star_def]
    simp [mul_comm]
  constructor
  · rw [applyGate_tensorGate,applyGate_one,hchar]
  · simp [gradientCharPrep,QueryCount,GateCount]

/-- Executing the same list of unitary fixed gates on two states preserves their inner product,
independently of the supplied oracles. -/
private theorem gradient_precision_gate_list_inner {I : Type} [Fintype I] [DecidableEq I]
    (O P : Matrix I I ℂ) (gs : List (Matrix I I ℂ))
    (hgs : ∀ U ∈ gs, U ∈ Matrix.unitaryGroup I ℂ) (ψ χ : QState I) :
    Inner (Run O (gs.map Step.gate) ψ) (Run P (gs.map Step.gate) χ)=Inner ψ χ := by
  induction gs generalizing ψ χ with
  | nil => rfl
  | cons U gs ih =>
    simp only [List.map_cons,run_gate]
    rw [ih (fun V hV => hgs V (List.mem_cons_of_mem _ hV))]
    exact inner_applyGate (hgs U List.mem_cons_self) ψ χ

/-- The real overlap of two scalar phase rotations of `u` equals `‖u‖^2 * cos (2*π*(b-a))`. -/
private theorem gradient_precision_phase_inner_re (a b : ℝ) (u : ℂ) :
    ((starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(a : ℂ))*u)*
      (Complex.exp (2*Real.pi*Complex.I*(b : ℂ))*u)).re =
      ‖u‖^2*Real.cos (2*Real.pi*(b-a)) := by
  have he : (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(a : ℂ)))*
      Complex.exp (2*Real.pi*Complex.I*(b : ℂ)) =
        Complex.exp (((2*Real.pi*(b-a) : ℝ) : ℂ)*Complex.I) := by
    rw [← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  calc
    _ = (((starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(a : ℂ)))*
        Complex.exp (2*Real.pi*Complex.I*(b : ℂ)))*((starRingEnd ℂ) u*u)).re := by
      rw [map_mul]
      congr 1
      ring
    _ = _ := by
      rw [he,Complex.conj_mul']
      rw [show (‖u‖ : ℂ)^2=((‖u‖^2 : ℝ) : ℂ) by norm_cast]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
        Complex.exp_ofReal_mul_I_re]
      ring

/-- If `b-a` is within `θ/(2*π)` of an integer and `θ ≤ π`, then `cos (2*π*(b-a))` is at least
`cos θ`. -/
private theorem gradient_precision_cos_lower (a b θ : ℝ) (hθ : θ ≤ Real.pi)
    (h : ∃ k : ℤ, |b-a-k| ≤ θ/(2*Real.pi)) : Real.cos θ ≤ Real.cos (2*Real.pi*(b-a)) := by
  obtain ⟨k,hk⟩ := h
  have hp : 0 < 2*Real.pi := by positivity
  have hδ : |2*Real.pi*(b-a-(k : ℝ))| ≤ θ := by
    rw [abs_mul,abs_of_pos hp]
    have he := (le_div_iff₀ hp).1 hk
    nlinarith only [he]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2*Real.pi*(b-a-(k : ℝ)))) hθ hδ
  rw [Real.cos_abs] at hc
  have he : 2*Real.pi*(b-a-(k : ℝ))=2*Real.pi*(b-a)-(k : ℝ)*(2*Real.pi) := by ring
  rw [he,Real.cos_sub_int_mul_two_pi] at hc
  exact hc

/-- For `0 ≤ θ ≤ π`, pointwise modular phase discrepancy at most `θ/(2*π)` gives
gradient-readout overlap norm at least `cos θ`. See [Jordan2005Gradient]. -/
theorem gradient_readout_inner_phase_error :
    ∀ (d M : ℕ) (hM : 0 < M) (φ phiHat : GradientGrid d M → ℝ) (θ : ℝ),
      0 ≤ θ → θ ≤ Real.pi →
      (∀ z, ∃ k : ℤ, |phiHat z-φ z-k| ≤ θ/(2*Real.pi)) →
      Real.cos θ ≤ ‖Inner (gradientReadout d M hM φ) (gradientReadout d M hM phiHat)‖ := by
  intro d M hM φ phiHat θ _hθ0 hθ herror
  let gs := List.ofFn (coordinateQFT d M)
  let O := gradientPhase d M φ
  let P := gradientPhase d M phiHat
  let u := Run O (gs.map Step.gate) (Ket (gradientZero d M hM))
  have hgs : ∀ U ∈ gs, U ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ := by
    intro U hU
    obtain ⟨j,rfl⟩ := List.mem_ofFn.1 hU
    exact coordinateQFT_unitary d M j hM
  have hf : gradientQFTWord d M=gs.map Step.gate := by
    simp [gradientQFTWord,gs,List.map_ofFn,Function.comp_def]
  have hforward : Run P (gs.map Step.gate) (Ket (gradientZero d M hM))=u := by
    apply run_eq_of_queryCount_eq_zero
    induction gs with
    | nil => rfl
    | cons U gs ih => simp [ih]
  have hu : Normalized u := by
    apply normalized_run O (gradientPhase_unitary d M φ) (gs.map Step.gate) ?_ (normalized_ket _)
    intro U hU
    obtain ⟨V,hV,he⟩ := List.mem_map.1 hU
    cases he
    exact hgs U hV
  have hback : ∀ U ∈ gs.reverse.map (fun U => Uᴴ), U ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ := by
    intro U hU
    obtain ⟨V,hV,rfl⟩ := List.mem_map.1 hU
    have hV := hgs V (List.mem_reverse.1 hV)
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose] at hV
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    exact hV
  have hword : gradientWord d M=(gs.map Step.gate)++[Step.query]++gs.reverse.map (fun U => Step.gate Uᴴ) := by
    simp [gradientWord,hf,← List.map_reverse,List.map_map,Function.comp_def]
  have hinner : Inner (gradientReadout d M hM φ) (gradientReadout d M hM phiHat)=
      Inner (ApplyGate O u) (ApplyGate P u) := by
    simp only [gradientReadout,hword,run_append,run_query,run_nil]
    change Inner (Run O (gs.reverse.map (fun U => Step.gate Uᴴ)) (ApplyGate O u))
      (Run P (gs.reverse.map (fun U => Step.gate Uᴴ))
        (ApplyGate P (Run P (gs.map Step.gate) (Ket (gradientZero d M hM))))) = _
    rw [hforward]
    have he :
        gs.reverse.map (fun U => Step.gate Uᴴ)=(gs.reverse.map (fun U => Uᴴ)).map Step.gate := by
          simp [List.map_map]
    rw [he]
    exact gradient_precision_gate_list_inner O P _ hback _ _
  rw [hinner]
  apply le_trans ?_ (Complex.re_le_norm _)
  rw [inner_apply]
  simp only [O,P,gradientPhase,ApplyGate,Matrix.mulVec_diagonal,Complex.re_sum,
    gradient_precision_phase_inner_re]
  have he := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (gradient_precision_cos_lower (φ z) (phiHat z) θ hθ (herror z)) (sq_nonneg ‖u z‖))
  rw [← Finset.sum_mul] at he
  change (∑ z, ‖u z‖^2)=1 at hu
  rw [hu,one_mul] at he
  exact he

/-- If a phase is within `θ/(2*π)` modulo integers of the affine phase for grid output `q`, with
`0 ≤ θ ≤ π/2`, its readout probability at `q` is at least `cos θ ^ 2`. See
[Jordan2005Gradient]. -/
theorem gradient_affine_precision_cos2_window :
    ∀ (d M : ℕ) (hM : 0 < M) (q : GradientGrid d M) (c θ : ℝ) (phiHat : GradientGrid d M → ℝ),
      0 ≤ θ → θ ≤ Real.pi/2 →
      (∀ z, ∃ k : ℤ,
        |phiHat z-(c+∑ j : Fin d, (q j).val*(z j).val/(M : ℝ))-k| ≤ θ/(2*Real.pi)) →
      Real.cos θ^2 ≤ MeasureProb (gradientReadout d M hM phiHat) {q} := by
  intro d M hM q c θ phiHat hθ0 hθ herror
  have h := gradient_readout_inner_phase_error d M hM
    (fun z => c+∑ j : Fin d, (q j).val*(z j).val/(M : ℝ)) phiHat θ hθ0
    (by linarith [Real.pi_pos]) herror
  rw [gradient_affine_actual_exact_readout] at h
  have hn : ‖Inner (Complex.exp (2*Real.pi*Complex.I*(c : ℂ)) • Ket q)
        (gradientReadout d M hM phiHat)‖ = ‖gradientReadout d M hM phiHat q‖ := by
    rw [inner_apply,Finset.sum_eq_single q]
    · simp only [Pi.smul_apply,smul_eq_mul,Ket,ite_true,mul_one,norm_mul]
      rw [show ‖(starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(c : ℂ)))‖=1 by
        simpa only [Complex.norm_conj] using! norm_exp_two_pi_I c]
      rw [one_mul]
    · intro z _ hz
      simp [Pi.smul_apply,Ket,hz]
    · simp
  rw [hn] at h
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hθ⟩
  have hs := mul_self_le_mul_self hcos0 h
  simpa only [MeasureProb,Finset.sum_singleton,BornProb,pow_two] using! hs

end Qatlib.Concepts.GradientOracle.ReadoutWindow
