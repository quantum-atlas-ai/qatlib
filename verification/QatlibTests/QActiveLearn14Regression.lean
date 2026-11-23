module

import Qatlib.Papers.QActiveLearn14.ApproxBudget.ConditionalOutput
import Qatlib.Papers.QActiveLearn14.ApproxBudget.WordError
import Qatlib.Papers.QActiveLearn14.ClassicalAgent.AdaptiveRetry
import Qatlib.Papers.QActiveLearn14.NativeReflect.CheckSign

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.QActiveLearn14Regression

open Qatlib.Foundations.MatrixGeometry.FlagProjection
open Qatlib.Papers.QActiveLearn14.TailedBounds
open Qatlib.Papers.QActiveLearn14.ApproxBudget
open Qatlib.Papers.QActiveLearn14.ClassicalAgent
open Qatlib.Papers.QActiveLearn14.NativeReflect
open scoped Matrix.Norms.L2Operator

/-- The physical flag checks remain two apart on a register with flagged and unflagged states. -/
example : ‖equationCheckMatrix ({true} : Finset Bool) -
    (-equationCheckMatrix ({true} : Finset Bool))‖ = 2 :=
  check_sign_operator_distance {true}

/-- The three-state adaptive law and the first-check conditioned law give different outputs. -/
example : (∑' n, soleUnflaggedHit threeStateKernel 2 ⟨0, by decide⟩ 0 n) ≠
    tailed (fun x => threeStateKernel x 0) ({0, 1} : Finset (Fin 3)) 0 :=
  adaptive_hit_ne_first_tail.2.2

/-- A nonuniform stationary law for the column-constant three-state transition kernel. -/
private noncomputable def weights (i : Fin 3) : ℝ := if i = 0 then 1 / 2 else 1 / 4

/-- The two flags carry half the initial mass, leaving state zero unflagged. -/
private theorem flag_mass : flaggedMass weights ({1, 2} : Finset (Fin 3)) = 1 / 2 := by
  norm_num [flaggedMass, weights, Finset.sum_insert, Finset.sum_singleton]

/-- With one round-selection budget for the entire word, a consumer can apply the prefix
estimate to the three-state coherent input on a joint state space. -/
example (embed : EuclideanSpace ℂ (Fin 3 × Fin 3) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 18))
    (check approx : EuclideanSpace ℂ (Fin 18) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 18))
    (hcheck : ∀ x, check (embed x) = embed (checkFig (pairFlags ({0, 1} : Finset (Fin 3))) x))
    (hcall : ∀ j < 4,
      let S := pairFlags ({0, 1} : Finset (Fin 3))
      let v := pairCoherent weights (fun i _ => weights i)
      ‖approx (embed (checkFig S (runFig S v j))) -
        embed (reflect v (checkFig S (runFig S v j)))‖ ≤ 1 / 16) :
    let S := pairFlags ({0, 1} : Finset (Fin 3))
    let v := pairCoherent weights (fun i _ => weights i)
    let e := ‖((approx.comp check)^[3]) (embed v) - embed (runFig S v 3)‖
    e ≤ 3 / 16 ∧ e ≤ 1 / 4 := by
  constructor
  · convert reflecting_word_error (pairFlags ({0, 1} : Finset (Fin 3)))
      (pairCoherent weights (fun i _ => weights i)) embed check approx hcheck
      (1 / 16) 4 hcall 3 (by decide) using 1
    norm_num
  · have hprecision : ∀ j < 2 ^ 2,
        let S := pairFlags ({0, 1} : Finset (Fin 3))
        let v := pairCoherent weights (fun i _ => weights i)
        ‖approx (embed (checkFig S (runFig S v j))) -
          embed (reflect v (checkFig S (runFig S v j)))‖ ≤ 2 * (1 / 2 : ℝ) ^ (2 + 3) := by
      norm_num at hcall ⊢
      exact hcall
    have h := reflecting_word_precision (pairFlags ({0, 1} : Finset (Fin 3)))
      (pairCoherent weights (fun i _ => weights i)) embed check approx hcheck
      2 3 hprecision 3 (by decide)
    norm_num at h ⊢
    exact h

/-- After one reflection round, perturbations of the coherent word have a well-defined
conditioned law on two flags. The ideal success probability is one half. -/
example (actual : EuclideanSpace ℂ (Fin 3 × Fin 3))
    (hclose : ‖actual - runFig (pairFlags ({1, 2} : Finset (Fin 3)))
      (pairCoherent weights (fun i _ => weights i)) 1‖ ≤ 1 / 8) :
    let S : Finset (Fin 3) := {1, 2}
    0 < mass (pairFlags S) actual ∧
      tvDist (fun i => ∑ j, conditionalBorn (pairFlags S) actual (i, j)) (tailed weights S) ≤
        (1 / 4) / Real.sqrt (1 / 2) := by
  let S : Finset (Fin 3) := {1, 2}
  let v := pairCoherent weights (fun i _ => weights i)
  have hn : ∀ i, 0 ≤ weights i := by intro i; unfold weights; split <;> norm_num
  have hs : ∑ i, weights i = 1 := by norm_num [Fin.sum_univ_three, weights]
  have hm : mass (pairFlags S) v = 1 / 2 := by
    rw [pair_mass weights _ hn (fun j _ => hn j) (fun _ => hs)]
    exact flag_mass
  have hp : 0 < mass (pairFlags S) v := by rw [hm]; norm_num
  have hu := pair_unit weights (fun i _ => weights i) hn hs (fun j _ => hn j) (fun _ => hs)
  have hout : mass (pairFlags S) (runFig (pairFlags S) v 1) = 1 / 2 := by
    rw [figure_mass, run_coeff _ _ hp hu, mass_span _ _ hp, hm]
    let a : ℝ := Real.sqrt (1 / 2)
    have ha : a ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have hac : (a : ℂ) ^ 2 = 1 / 2 := by
      rw [← Complex.ofReal_pow, ha]
      norm_num
    change ‖(coeff (a : ℂ) 1).1 * (a : ℂ) + (coeff (a : ℂ) 1).2‖ ^ 2 = 1 / 2
    simp only [coeff, mul_one, sub_zero, add_zero]
    have hscale : (1 + 2 * (-2 * (a : ℂ)) * (a : ℂ)) * (a : ℂ) +
        2 * (a : ℂ) = (a : ℂ) := by
      linear_combination -4 * (a : ℂ) * hac
    rw [hscale, Complex.norm_real, Real.norm_eq_abs, sq_abs, ha]
  have hgap : (1 / 8 : ℝ) < Real.sqrt (mass (pairFlags S) (runFig (pairFlags S) v 1)) := by
    rw [hout]
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h := coherent_word_conditional_output weights (fun i _ => weights i) ⟨hn, hs⟩
    (fun j _ => hn j) (fun _ => hs) S (by rw [flag_mass]; norm_num) 1 actual (1 / 8)
    hclose hgap
  dsimp only [v] at hout
  rw [hout] at h
  simpa only [show (2 : ℝ) * (1 / 8) = 1 / 4 by norm_num] using h

end QatlibTests.QActiveLearn14Regression
