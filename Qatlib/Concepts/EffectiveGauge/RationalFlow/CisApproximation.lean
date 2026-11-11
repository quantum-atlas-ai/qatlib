/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisProgram
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceAngle

set_option backward.isDefEq.respectTransparency false

/-! # The same rational cis execution approximates a native quaternion phase -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of rational Circle Quaternion in the Rational Flow construction. -/
def rationalCircleQuaternion (p : RationalCircleSample) : Quaternion ℚ := ⟨p.1,p.2,0,0⟩

noncomputable section
open scoped Quaternion

/-- Original `cisPairSquare_cast` guarantee for the `CisApproximation` construction; the complete source hypotheses are retained. -/
theorem cisPairSquare_cast (a : RationalCircleSample) :
    rationalCircleCast (cisPairSquare a)=rationalCircleCast a*rationalCircleCast a := by
  have he : cisPairSquare a=cisPairMul a a := by apply Prod.ext <;> dsimp [cisPairSquare,cisPairMul] <;> ring
  rw [he,cisPairMul_cast]

/-- Original `complex_square_error` guarantee for the `CisApproximation` construction; the complete source hypotheses are retained. -/
private theorem complex_square_error (z w : ℂ) (E : ℝ) (hw : ‖w‖=1) (he : ‖z-w‖ ≤ E) :
    ‖z*z-w*w‖ ≤ E*(2+E) := by
  have hE : 0 ≤ E := (norm_nonneg _).trans he
  have hn : ‖z‖ ≤ 1+E := by
    have h := (norm_le_norm_sub_add z w).trans (add_le_add he hw.le)
    linarith
  have hid : z*z-w*w=(z-w)*z+w*(z-w) := by ring
  calc
    _ ≤ ‖(z-w)*z‖+‖w*(z-w)‖ := by rw [hid]; exact norm_add_le _ _
    _ = ‖z-w‖*‖z‖+‖z-w‖ := by rw [norm_mul,norm_mul,hw,one_mul]
    _ ≤ E*(1+E)+E := add_le_add (mul_le_mul he hn (norm_nonneg _) hE) he
    _ = _ := by ring

/-- Original `cisSquares_error` guarantee for the `CisApproximation` construction; the complete source hypotheses are retained. -/
theorem cisSquares_error (h : ℕ) (r : RationalCisResult) (x : ℝ)
    (he : ‖rationalCircleCast r.value-complexPhase x‖ ≤ (r.error : ℝ)) :
    ‖rationalCircleCast (cisSquares h r).value-complexPhase ((2^h : ℝ)*x)‖ ≤ ((cisSquares h r).error : ℝ) := by
  induction h with
  | zero => simpa only [cisSquares,pow_zero,one_mul] using he
  | succ h ih =>
    have hp : (2^(h+1) : ℝ)*x=(2^h : ℝ)*x+(2^h : ℝ)*x := by rw [pow_succ]; ring
    change ‖rationalCircleCast (cisPairSquare (cisSquares h r).value)-complexPhase ((2^(h+1) : ℝ)*x)‖ ≤
      ((((cisSquares h r).error*(2+(cisSquares h r).error) : ℚ)) : ℝ)
    rw [cisPairSquare_cast,hp,complexPhase_add]
    push_cast
    exact complex_square_error _ _ _ (complexPhase_norm _) ih

/-- Both the actual complex output and nonlinear error ledger are certified.
The approximate value may have norm different from one. -/
theorem rationalCis_spec (x tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1) :
    let r := rationalCis x tolerance
    ‖rationalCircleCast r.value-complexPhase (x : ℝ)‖ ≤ (r.error : ℝ) ∧
      0 ≤ r.error ∧ r.error ≤ tolerance ∧
      r.terms ≤ 1+arctanFuel (tolerance/(16*2^cisHalvings x : ℚ)) := by
  let h := cisHalvings x
  let y := x/(2^h : ℚ)
  let t := tolerance/(8*2^h : ℚ)
  let r := reducedCis y t
  have hy : |y| ≤ 1/2 := cisHalvings_reduced x
  have ht0 : 0<t := by dsimp [t]; positivity
  have hs := reducedCis_spec y t hy ht0
  have he0 : 0 ≤ r.error := by rw [hs.2.1]; dsimp [negativeExpMagnitude]; positivity
  have hstart : ‖rationalCircleCast r.value-complexPhase (y : ℝ)‖ ≤ (r.error : ℝ) := by
    rw [hs.1,hs.2.1]
    exact cisTaylorPartial_error y hy _
  have hsem := cisSquares_error h r (y : ℝ) hstart
  have hscale : (2^h : ℝ)*(y : ℝ)=(x : ℝ) := by dsimp [y]; push_cast; field_simp
  rw [hscale] at hsem
  have hf := cisSquares_fields h r
  have hb := cisErrorIter_budget r.error tolerance h he0 ht ht1 hs.2.2.2.2.1
  refine ⟨hsem,?_,?_,?_⟩
  · exact hf.1.symm ▸ hb.1
  · exact hf.1.le.trans hb.2
  · change (cisSquares h r).terms ≤ 1+arctanFuel (tolerance/(16*2^h : ℚ))
    rw [hf.2]
    have htHalf : t/2=tolerance/(16*2^h : ℚ) := by dsimp [t]; field_simp; ring
    rw [← htHalf]
    exact hs.2.2.2.1

/-- Original `rationalCircleQuaternion_cast` guarantee for the `CisApproximation` construction; the complete source hypotheses are retained. -/
theorem rationalCircleQuaternion_cast (p : RationalCircleSample) :
    rationalQuaternionCast (rationalCircleQuaternion p)=Quaternion.ofComplex (rationalCircleCast p) := by
  apply Quaternion.ext <;> simp [rationalQuaternionCast,rationalCircleQuaternion,rationalCircleCast,Quaternion.ofComplex,Quaternion.coeComplex]

/-- Original `complexPhase_quaternion` guarantee for the `CisApproximation` construction; the complete source hypotheses are retained. -/
theorem complexPhase_quaternion (x : ℝ) : Quaternion.ofComplex (complexPhase x)=phase x := by
  apply Quaternion.ext <;> simp [Quaternion.ofComplex,Quaternion.coeComplex,complexPhase,phase,iAxis]

/-- Original `norm_ofComplex` guarantee for the `CisApproximation` construction; the complete source hypotheses are retained. -/
theorem norm_ofComplex (z : ℂ) : ‖Quaternion.ofComplex z‖=‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two,pow_two,← Quaternion.normSq_eq_norm_mul_self,Complex.norm_mul_self_eq_normSq]
  simp [Quaternion.normSq_def',Complex.normSq_apply,Quaternion.ofComplex,Quaternion.coeComplex,pow_two]

/-- The finite rational quaternion is the actual pair output of cis, with
zero j/k coordinates. This is the consumer used by the reference program. -/
theorem rationalCis_quaternion_error (x tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1) :
    ‖rationalQuaternionCast (rationalCircleQuaternion (rationalCis x tolerance).value)-phase (x : ℝ)‖ ≤
      ((rationalCis x tolerance).error : ℝ) := by
  rw [rationalCircleQuaternion_cast,← complexPhase_quaternion,← map_sub,norm_ofComplex]
  exact (rationalCis_spec x tolerance ht ht1).1

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
