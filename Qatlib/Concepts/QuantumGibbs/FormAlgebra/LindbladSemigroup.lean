/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupKmsMixing
public import QuantumInfo.ForMathlib.HermitianMat.CFC
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Module

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LindbladFlow.GkslSemigroup

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup

open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable def twoLevelMix (s : ℝ) : ℝ :=
  (1 + s) / 2 * Real.log (1 + s) + (1 - s) / 2 * Real.log (1 - s)

/-- The two-level mixing function is even. -/
theorem twoLevelMix_even (s : ℝ) : twoLevelMix (-s) = twoLevelMix s := by
  have h1 : (1 : ℝ) + -s = 1 - s := by ring
  have h2 : (1 : ℝ) - -s = 1 + s := by ring
  simp only [twoLevelMix, h1, h2]
  ring

/-- The two-level mixing function vanishes at zero. -/
theorem twoLevelMix_zero : twoLevelMix 0 = 0 := by norm_num [twoLevelMix]

/-- For `s` strictly between minus one and one, the difference of the two half-logarithms equals
half the logarithm of their ratio. -/
theorem twoLevelMixDeriv_eq {s : ℝ} (h1 : -1 < s) (h2 : s < 1) :
    1 / 2 * Real.log (1 + s) - 1 / 2 * Real.log (1 - s)
      = 1 / 2 * Real.log ((1 + s) / (1 - s)) := by
  rw [Real.log_div (ne_of_gt (by linarith : (0:ℝ) < 1 + s))
    (ne_of_gt (by linarith : (0:ℝ) < 1 - s))]
  ring

/-- Away from one, the derivative of the ratio of one plus the variable to one minus the
variable is two divided by the squared denominator. -/
theorem hasDerivAt_ratio {s : ℝ} (hs : s ≠ 1) :
    HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) (2 / (1 - s) ^ 2) s := by
  have hf : HasDerivAt (fun x : ℝ => 1 + x) 1 s :=
    (hasDerivAt_id s).const_add (1:ℝ)
  have hg : HasDerivAt (fun x : ℝ => 1 - x) (-1) s :=
    (hasDerivAt_id s).const_sub (1:ℝ)
  have h := hf.div hg (sub_ne_zero_of_ne (Ne.symm hs))
  exact h.congr_deriv (by
    have h0 : 1 * (1 - s) - (1 + s) * (-1) = 2 := by ring
    rw [h0])

/-- On the open interval from minus one to one, the half-logarithmic ratio has derivative the
reciprocal of one minus the square. -/
theorem hasDerivAt_halfLogRatio {s : ℝ} (h1 : -1 < s) (h2 : s < 1) :
    HasDerivAt (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x))) (1 / (1 - s * s)) s := by
  have hr := hasDerivAt_ratio (ne_of_lt h2)
  have hnz : (1 + s) / (1 - s) ≠ 0 :=
    div_ne_zero_iff.mpr ⟨by linarith, by linarith⟩
  have hl := (Real.hasDerivAt_log hnz).comp s hr
  have h := hl.const_mul (1 / 2 : ℝ)
  exact h.congr_deriv (by
    have hd1 : (1:ℝ) - s ≠ 0 := ne_of_gt (by linarith)
    have hd2 : (1:ℝ) + s ≠ 0 := ne_of_gt (by linarith)
    have hd3 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring)

/-- On the open interval from minus one to one, `twoLevelMix` has derivative half the logarithm
of the ratio of one plus the argument to one minus it. -/
theorem hasDerivAt_twoLevelMix {s : ℝ} (h1 : -1 < s) (h2 : s < 1) :
    HasDerivAt twoLevelMix (1 / 2 * Real.log ((1 + s) / (1 - s))) s := by
  have hp1 : (0:ℝ) < 1 + s := by linarith
  have hp2 : (0:ℝ) < 1 - s := by linarith
  have ha : HasDerivAt (fun x : ℝ => (1 + x) / 2 * Real.log (1 + x))
      (1 / 2 * Real.log (1 + s) + 1 / 2) s := by
    have hfun : HasDerivAt (fun x : ℝ => 1 + x) 1 s :=
      (hasDerivAt_id s).const_add (1:ℝ)
    have hlog := (Real.hasDerivAt_log (ne_of_gt hp1)).comp s hfun
    have h := (hfun.div_const (2:ℝ)).mul hlog
    exact h.congr_deriv (by (try simp only [Function.comp_apply]); field_simp)
  have hb : HasDerivAt (fun x : ℝ => (1 - x) / 2 * Real.log (1 - x))
      ((-1) / 2 - 1 / 2 * Real.log (1 - s)) s := by
    have hfun : HasDerivAt (fun x : ℝ => 1 - x) (-1) s :=
      (hasDerivAt_id s).const_sub (1:ℝ)
    have hlog := (Real.hasDerivAt_log (ne_of_gt hp2)).comp s hfun
    have h := (hfun.div_const (2:ℝ)).mul hlog
    exact h.congr_deriv (by simp only [Function.comp_apply]; field_simp; try ring)
  have hsum := ha.add hb
  have hfin : HasDerivAt (fun x : ℝ => (1 + x) / 2 * Real.log (1 + x)
      + (1 - x) / 2 * Real.log (1 - x)) (1 / 2 * Real.log ((1 + s) / (1 - s))) s :=
    hsum.congr_deriv
      (by rw [Real.log_div (ne_of_gt hp1) (ne_of_gt hp2)]; ring)
  exact hfin.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => rfl)

/-- A function with a nonnegative derivative at every point of a convex real set is monotone on
that set. -/
theorem monoOn_of_hasDeriv {f : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hderiv : ∀ x ∈ D, ∃ y, HasDerivAt f y x ∧ 0 ≤ y) : MonotoneOn f D := by
  have hcont : ContinuousOn f D := by
    intro x hx
    obtain ⟨y, hy, -⟩ := hderiv x hx
    exact hy.continuousAt.continuousWithinAt
  refine monotoneOn_of_deriv_nonneg hD hcont ?_ ?_
  · intro x hx
    obtain ⟨y, hy, -⟩ := hderiv x (interior_subset hx)
    exact hy.differentiableAt.differentiableWithinAt
  · intro x hx
    obtain ⟨y, hy, hypos⟩ := hderiv x (interior_subset hx)
    rw [hy.deriv]
    exact hypos

/-- For `s` between zero and one, excluding one, the half-logarithmic ratio is at least `s`. -/
theorem halfLogRatio_ge_self {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    s ≤ 1 / 2 * Real.log ((1 + s) / (1 - s)) := by
  have hmono : MonotoneOn (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x)) - x)
      (Set.Ico 0 (1:ℝ)) := by
    refine monoOn_of_hasDeriv (convex_Ico 0 1) ?_
    intro x hx
    obtain ⟨hxa, hxb⟩ := Set.mem_Ico.mp hx
    have h1 : -1 < x := by linarith
    have h2 : x < 1 := by linarith
    have hd : 0 < 1 - x * x := by nlinarith
    have hdn : (1:ℝ) - x ^ 2 ≠ 0 := by nlinarith
    refine ⟨1 / (1 - x * x) - 1,
      ((hasDerivAt_halfLogRatio h1 h2).sub (hasDerivAt_id x)) |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by
          simp only [Pi.sub_apply, id_eq]), ?_⟩
    have hval : 1 / (1 - x * x) - 1 = x * x / (1 - x * x) := by
      have hd4 : (1:ℝ) - x ^ 2 ≠ 0 := by nlinarith
      field_simp
      ring
    rw [hval]
    exact div_nonneg (mul_nonneg hxa hxa) hd.le
  have h0 : (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x)) - x) 0 = 0 := by norm_num
  have h := hmono (Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩) (Set.mem_Ico.mpr ⟨hs0, hs1⟩) hs0
  simpa using h

/-- For `s` between zero and one, excluding one, `twoLevelMix` is at least half the square of
`s`. -/
theorem twoLevelMix_ge_half_sq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    s ^ 2 / 2 ≤ twoLevelMix s := by
  have hmono : MonotoneOn (fun x : ℝ => twoLevelMix x - x ^ 2 / 2) (Set.Ico 0 (1:ℝ)) := by
    refine monoOn_of_hasDeriv (convex_Ico 0 1) ?_
    intro x hx
    obtain ⟨hxa, hxb⟩ := Set.mem_Ico.mp hx
    have h1 : -1 < x := by linarith
    have h2 : x < 1 := by linarith
    have hge := halfLogRatio_ge_self hxa h2
    have hq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x :=
      (hasDerivAt_pow 2 x).congr_deriv (by norm_num)
    have hraw : HasDerivAt (fun y : ℝ => twoLevelMix y - y ^ 2 / 2)
        (1 / 2 * Real.log ((1 + x) / (1 - x)) - 2 * x / 2) x :=
      ((hasDerivAt_twoLevelMix h1 h2).sub (hq.div_const 2)) |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp only [Pi.sub_apply])
    exact ⟨_, hraw, by linarith⟩
  have h := hmono (Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩) (Set.mem_Ico.mpr ⟨hs0, hs1⟩) hs0
  simp only [twoLevelMix_zero] at h
  norm_num at h
  linarith

/-- Computes the derivative of the difference between the rational entropy-production term and
the half-logarithmic ratio. -/
theorem hasDerivAt_epAux {s : ℝ} (h1 : -1 < s) (h2 : s < 1) :
    HasDerivAt (fun x : ℝ => x / (1 - x * x)
        - 1 / 2 * Real.log ((1 + x) / (1 - x)))
      (2 * s * s / (1 - s * s) ^ 2) s := by
  have hden : HasDerivAt (fun y : ℝ => 1 - y * y) (-(2 * s)) s := by
    have h : HasDerivAt (fun y : ℝ => y * y) (s + s) s :=
      ((hasDerivAt_id s).mul (hasDerivAt_id s)) |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => rfl) |>.congr_deriv
          (by simp only [id_eq]; ring)
    exact (h.const_sub (1:ℝ)).congr_deriv (by ring)
  have hd := (hasDerivAt_id s).div hden (by
    have : 1 - s * s ≠ 0 := by nlinarith
    simpa using this)
  have hcomb := hd.sub (hasDerivAt_halfLogRatio h1 h2)
  exact hcomb.congr_deriv (by
    have hd3 : (1:ℝ) - s ^ 2 ≠ 0 := by nlinarith
    simp only [id_eq]
    field_simp
    ring)

/-- Computes the derivative of the two-level entropy-production expression minus twice
`twoLevelMix`. -/
theorem hasDerivAt_twoLevelEP {s : ℝ} (h1 : -1 < s) (h2 : s < 1) :
    HasDerivAt (fun x : ℝ => x / 2 * Real.log ((1 + x) / (1 - x))
        - 2 * twoLevelMix x)
      (s / (1 - s * s) - 1 / 2 * Real.log ((1 + s) / (1 - s))) s := by
  have hG := hasDerivAt_halfLogRatio h1 h2
  have hg := hasDerivAt_twoLevelMix h1 h2
  have hraw : HasDerivAt (fun y : ℝ => y * (1 / 2 * Real.log ((1 + y) / (1 - y)))
      - 2 * twoLevelMix y)
      (1 * (1 / 2 * Real.log ((1 + s) / (1 - s))) + s * (1 / (1 - s * s))
        - 2 * (1 / 2 * Real.log ((1 + s) / (1 - s)))) s :=
    ((hasDerivAt_id s).mul hG).sub (hg.const_mul 2)
  exact hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by ring) |>.congr_deriv (by ring)

/-- For `s` between zero and one, excluding one, the two-level entropy-production expression
bounds twice `twoLevelMix` from below. -/
theorem twoLevelMix_entropyProduction {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    2 * twoLevelMix s ≤ s / 2 * Real.log ((1 + s) / (1 - s)) := by

  have hpsi1 : ∀ x ∈ Set.Ico 0 (1:ℝ),
      0 ≤ x / (1 - x * x) - 1 / 2 * Real.log ((1 + x) / (1 - x)) := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := Set.mem_Ico.mp hx
    have hmono : MonotoneOn (fun y : ℝ => y / (1 - y * y)
        - 1 / 2 * Real.log ((1 + y) / (1 - y))) (Set.Ico 0 (1:ℝ)) := by
      refine monoOn_of_hasDeriv (convex_Ico 0 1) ?_
      intro y hy
      obtain ⟨hya, hyb⟩ := Set.mem_Ico.mp hy
      have hp : 0 < 1 - y * y := by nlinarith
      exact ⟨_, hasDerivAt_epAux (by linarith) (by linarith),
        div_nonneg (by positivity) (pow_pos hp 2).le⟩
    have h0 : (fun y : ℝ => y / (1 - y * y)
        - 1 / 2 * Real.log ((1 + y) / (1 - y))) 0 = 0 := by norm_num
    have h := hmono (Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩) hx hxa
    simpa using h

  have hmono : MonotoneOn (fun x : ℝ => x / 2 * Real.log ((1 + x) / (1 - x))
      - 2 * twoLevelMix x) (Set.Ico 0 (1:ℝ)) := by
    refine monoOn_of_hasDeriv (convex_Ico 0 1) ?_
    intro x hx
    obtain ⟨hxa, hxb⟩ := Set.mem_Ico.mp hx
    exact ⟨_, hasDerivAt_twoLevelEP (by linarith) (by linarith), hpsi1 x hx⟩
  have h0 : (fun x : ℝ => x / 2 * Real.log ((1 + x) / (1 - x))
      - 2 * twoLevelMix x) 0 = 0 := by norm_num [twoLevelMix]
  have hfin := hmono (Set.mem_Ico.mpr ⟨le_rfl, by norm_num⟩)
    (Set.mem_Ico.mpr ⟨hs0, hs1⟩) hs0
  have h0 : (fun x : ℝ => x / 2 * Real.log ((1 + x) / (1 - x))
      - 2 * twoLevelMix x) 0 = 0 := by norm_num [twoLevelMix]
  rw [h0] at hfin
  simp only [] at hfin
  linarith

/-- For a nonnegative argument below one, scaling the argument by a factor between zero and one
bounds `twoLevelMix` by the square of that factor times its original value. -/
theorem twoLevelMix_contraction {s θ : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : twoLevelMix (θ * s) ≤ θ ^ 2 * twoLevelMix s := by
  rcases eq_or_lt_of_le hθ0 with hθ | hθpos
  · rw [← hθ]
    norm_num [twoLevelMix_zero]
  rcases eq_or_lt_of_le hθ1 with hθ1eq | hθ1lt
  · rw [hθ1eq]
    norm_num

  have hk : ∀ u ∈ Set.Icc θ 1, HasDerivAt (fun v : ℝ => twoLevelMix (v * s) / v ^ 2)
      ((u * s / 2 * Real.log ((1 + u * s) / (1 - u * s))
        - 2 * twoLevelMix (u * s)) / u ^ 3) u := by
    intro u hu
    obtain ⟨hua, hub⟩ := Set.mem_Icc.mp hu
    have hu0 : 0 < u := lt_of_lt_of_le hθpos hua
    have hc1 : -1 < u * s := by nlinarith
    have hc2 : u * s < 1 := by nlinarith
    have hg := hasDerivAt_twoLevelMix hc1 hc2
    have hc0 : HasDerivAt (fun v : ℝ => s * v) s u :=
      ((hasDerivAt_id u).const_mul s) |>.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun v => rfl) |>.congr_deriv
          (by ring)
    have hc : HasDerivAt (fun v : ℝ => v * s) s u :=
      hc0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => by ring)
    have hcomp : HasDerivAt (twoLevelMix ∘ fun v : ℝ => v * s)
        (1 / 2 * Real.log ((1 + u * s) / (1 - u * s)) * s) u := hg.comp u hc
    have hd : HasDerivAt (fun v : ℝ => twoLevelMix (v * s))
        (s * (1 / 2 * Real.log ((1 + u * s) / (1 - u * s)))) u :=
      hcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun v => rfl) |>.congr_deriv (by ring)
    have hq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u :=
      (hasDerivAt_pow 2 u).congr_deriv (by norm_num)
    have hdiv := hd.div hq (pow_ne_zero 2 (ne_of_gt hu0))
    have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hu0)
    exact hdiv.congr_deriv (by
      have hus : (1:ℝ) + u * s ≠ 0 := by nlinarith
      have hus2 : (1:ℝ) - u * s ≠ 0 := by nlinarith
      field_simp)
  have hmono : MonotoneOn (fun u : ℝ => twoLevelMix (u * s) / u ^ 2) (Set.Icc θ 1) := by
    refine monoOn_of_hasDeriv (convex_Icc θ 1) ?_
    intro u hu
    obtain ⟨hua, hub⟩ := Set.mem_Icc.mp hu
    have hu0 : 0 < u := lt_of_lt_of_le hθpos hua
    have hc2 : u * s < 1 := by nlinarith
    have hep := twoLevelMix_entropyProduction (by nlinarith : (0:ℝ) ≤ u * s) hc2
    refine ⟨_, hk u hu, ?_⟩
    exact div_nonneg (by linarith) (pow_pos hu0 3).le
  have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, hθ1⟩)
    (Set.mem_Icc.mpr ⟨hθ1, le_rfl⟩) hθ1
  norm_num at h
  have huθ2 : 0 < θ ^ 2 := sq_pos_iff.mpr (ne_of_gt hθpos)
  exact ((div_le_iff₀ huθ2).mp h).trans_eq (mul_comm (twoLevelMix s) (θ ^ 2))

def EntropyProductionIneq {D : ℕ} (G : GKSL D) (ρstar : Operator D) (α : ℝ) : Prop :=
  0 < α ∧ ∀ τ : Operator D, IsDensityOperator τ → τ.PosDef → ∀ u : ℝ, 0 ≤ u →
    ∃ d : ℝ, HasDerivAt (fun v : ℝ => relativeEntropy (lindbladSemigroup G v τ) ρstar) d u ∧
      d ≤ -2 * α * relativeEntropy (lindbladSemigroup G u τ) ρstar

/-- An entropy-production inequality gives exponential relative-entropy decay at twice its rate
for a positive definite initial density operator. -/
theorem mlsi_relativeEntropy_decay {D : ℕ} (G : GKSL D) {ρstar σ : Operator D}
    (hσ : IsDensityOperator σ) (hσfull : σ.PosDef) {α : ℝ}
    (hep : EntropyProductionIneq G ρstar α) (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρstar
      ≤ Real.exp (-2 * α * t) * relativeEntropy σ ρstar := by
  have hfderiv : ∀ s ∈ Set.Icc (0:ℝ) t, ∃ y, HasDerivAt
      (fun v : ℝ => -(Real.exp (2 * α * v) *
        relativeEntropy (lindbladSemigroup G v σ) ρstar)) y s ∧ 0 ≤ y := by
    intro s hs
    obtain ⟨hs0, -⟩ := Set.mem_Icc.mp hs
    obtain ⟨d, hd, hdle⟩ := hep.2 σ hσ hσfull s hs0
    have he : HasDerivAt (fun v : ℝ => Real.exp (2 * α * v))
        (2 * α * Real.exp (2 * α * s)) s :=
      ((Real.hasDerivAt_exp (2 * α * s)).comp s
        ((hasDerivAt_id s).const_mul (2 * α))).congr_deriv (by ring)
    have hprod := (he.mul hd).neg
    refine ⟨_, hprod, ?_⟩
    have key := mul_le_mul_of_nonneg_left hdle
      (le_of_lt (Real.exp_pos (2 * α * s)))
    nlinarith [key]
  have hmono : MonotoneOn
      (fun v : ℝ => -(Real.exp (2 * α * v) *
        relativeEntropy (lindbladSemigroup G v σ) ρstar)) (Set.Icc (0:ℝ) t) :=
    monoOn_of_hasDeriv (convex_Icc 0 t) hfderiv
  have h0t : (0:ℝ) ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr ⟨le_rfl, ht⟩
  have htt : t ∈ Set.Icc (0:ℝ) t := Set.mem_Icc.mpr ⟨ht, le_rfl⟩
  have hft := neg_le_neg_iff.mp (hmono h0t htt ht)
  simp only [mul_zero, Real.exp_zero, one_mul, lindbladSemigroup_zero_apply] at hft
  have hexp : 0 < Real.exp (2 * α * t) := Real.exp_pos _
  have hEq : Real.exp (2 * α * t) * Real.exp (-2 * α * t) = 1 := by
    have h0 : 2 * α * t + -2 * α * t = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  have hinv : Real.exp (-2 * α * t) = (Real.exp (2 * α * t))⁻¹ :=
    eq_inv_of_mul_eq_one_right hEq
  rw [hinv, ← div_eq_inv_mul]
  refine (le_div_iff₀ hexp).mpr ?_
  rw [mul_comm]
  exact hft

/-- An entropy-production inequality and the assumed entropy-to-distance bound give exponential
trace-distance decay for a positive definite initial density operator. -/
theorem mlsi_traceDistance_mixing {D : ℕ} (G : GKSL D) {ρstar σ : Operator D}
    (hσ : IsDensityOperator σ) (hσfull : σ.PosDef) {α : ℝ}
    (hep : EntropyProductionIneq G ρstar α) {κ : ℝ} (hκ : 0 ≤ κ)
    (hS0 : 0 ≤ κ * relativeEntropy σ ρstar)
    (hpin : ∀ τ : Operator D, IsDensityOperator τ →
      traceDistance τ ρstar ≤ Real.sqrt (κ * relativeEntropy τ ρstar))
    (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρstar
      ≤ Real.exp (-α * t) * Real.sqrt (κ * relativeEntropy σ ρstar) := by
  have hdec := mlsi_relativeEntropy_decay G hσ hσfull hep t ht
  have hτ := lindbladSemigroup_isDensityOperator G t ht σ hσ
  have h1 := hpin _ hτ
  have h2 : κ * relativeEntropy (lindbladSemigroup G t σ) ρstar
      ≤ κ * (Real.exp (-2 * α * t) * relativeEntropy σ ρstar) :=
    mul_le_mul_of_nonneg_left hdec hκ
  have h3 : Real.sqrt (κ * relativeEntropy (lindbladSemigroup G t σ) ρstar)
      ≤ Real.sqrt (κ * (Real.exp (-2 * α * t) * relativeEntropy σ ρstar)) :=
    Real.sqrt_le_sqrt h2
  have hexp2 : Real.exp (-2 * α * t)
      = Real.exp (-α * t) * Real.exp (-α * t) := by
    rw [← Real.exp_add]; ring
  have h4 : Real.sqrt (κ * (Real.exp (-2 * α * t) * relativeEntropy σ ρstar))
      = Real.exp (-α * t) * Real.sqrt (κ * relativeEntropy σ ρstar) := by
    have hc : 0 ≤ Real.exp (-α * t) := (Real.exp_pos (-α * t)).le
    have hxnn : 0 ≤ κ * (Real.exp (-2 * α * t) * relativeEntropy σ ρstar) := by
      have hnn := mul_nonneg (Real.exp_pos (-2 * α * t)).le hS0
      nlinarith [hnn]
    have hy2 : 0 ≤ Real.exp (-α * t) * Real.sqrt (κ * relativeEntropy σ ρstar) :=
      mul_nonneg hc (Real.sqrt_nonneg _)
    refine (Real.sqrt_eq_iff_mul_self_eq hxnn hy2).mpr ?_
    have hrr : Real.sqrt (κ * relativeEntropy σ ρstar)
        * Real.sqrt (κ * relativeEntropy σ ρstar) = κ * relativeEntropy σ ρstar :=
      Real.mul_self_sqrt hS0
    rw [hexp2]
    rw [show Real.exp (-α * t) * Real.sqrt (κ * relativeEntropy σ ρstar)
          * (Real.exp (-α * t) * Real.sqrt (κ * relativeEntropy σ ρstar))
        = Real.exp (-α * t) * Real.exp (-α * t)
          * (Real.sqrt (κ * relativeEntropy σ ρstar)
            * Real.sqrt (κ * relativeEntropy σ ρstar)) by ring,
      hrr]
    ring
  exact h1.trans (h3.trans_eq h4)

/-- Every element of `Fin 2` is zero or one. -/
theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h2 : i.val = 0 ∨ i.val = 1 := by omega
  rcases h2 with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (by omega))

def pauliX : Operator 2 := !![(0 : ℂ), 1; 1, 0]

def pauliY : Operator 2 := !![(0 : ℂ), -Complex.I; Complex.I, 0]

def pauliZ : Operator 2 := !![(1 : ℂ), 0; 0, -1]

/-- The Pauli X matrix is Hermitian. -/
theorem pauliX_hermitian : pauliX.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.conjTranspose_apply, Complex.star_def]

/-- The Pauli Y matrix is Hermitian. -/
theorem pauliY_hermitian : pauliY.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.conjTranspose_apply, Complex.star_def]

/-- The Pauli Z matrix is Hermitian. -/
theorem pauliZ_hermitian : pauliZ.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.conjTranspose_apply, Complex.star_def]

/-- The Pauli X matrix squares to the identity. -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Pauli Y matrix squares to the identity. -/
theorem pauliY_sq : pauliY * pauliY = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- The Pauli Z matrix squares to the identity. -/
theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Multiplying a complex number by the imaginary unit on both sides negates it. -/
theorem I_mul_z_mul_I (z : ℂ) : Complex.I * z * Complex.I = -z := by
  have h : Complex.I * z * Complex.I = (Complex.I * Complex.I) * z := by ring
  rw [h, Complex.I_mul_I]
  ring

/-- Conjugation by Pauli X swaps both row and column indices of a two-dimensional operator. -/
theorem pauliX_mul_mul (X : Operator 2) :
    pauliX * X * pauliX = Matrix.of fun i j => X (![1, 0] i) (![1, 0] j) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- Conjugation by Pauli Y swaps both indices and negates the off-diagonal entries of a
two-dimensional operator. -/
theorem pauliY_mul_mul (X : Operator 2) :
    pauliY * X * pauliY
      = Matrix.of fun i j => (if i = j then (1 : ℂ) else -(1 : ℂ))
          * X (![1, 0] i) (![1, 0] j) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Complex.I_mul_I, I_mul_z_mul_I]

/-- Conjugation by Pauli Z preserves diagonal entries and negates off-diagonal entries. -/
theorem pauliZ_mul_mul (X : Operator 2) :
    pauliZ * X * pauliZ
      = Matrix.of fun i j => (if i = j then (1 : ℂ) else -(1 : ℂ)) * X i j := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- The sum of conjugations by the three Pauli matrices is twice the trace times the identity
minus the original operator. -/
theorem pauli_conjSum (X : Operator 2) :
    pauliX * X * pauliX + pauliY * X * pauliY + pauliZ * X * pauliZ
      = (2 * Matrix.trace X : ℂ) • (1 : Operator 2) - X := by
  rw [pauliX_mul_mul, pauliY_mul_mul, pauliZ_mul_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.trace,
      Fin.sum_univ_two, Matrix.sub_apply] <;>
    ring

noncomputable def depolCoef (γ : ℝ) : ℂ := ((Real.sqrt γ / 2 : ℝ) : ℂ)

/-- The depolarizing coefficient is fixed by complex conjugation. -/
theorem depolCoef_conj (γ : ℝ) : (starRingEnd ℂ) (depolCoef γ) = depolCoef γ :=
  Complex.conj_ofReal (Real.sqrt γ / 2)

/-- For a nonnegative rate, the square of the depolarizing coefficient is one quarter of the
rate. -/
theorem depolCoef_sq {γ : ℝ} (hγ : 0 ≤ γ) :
    depolCoef γ * depolCoef γ = ((γ : ℝ) : ℂ) / 4 := by
  have hss : (Real.sqrt γ) ^ 2 = γ := Real.sq_sqrt hγ
  have key : (Real.sqrt γ / 2 : ℝ) * (Real.sqrt γ / 2 : ℝ) = γ / 4 := by
    field_simp
    rw [hss]
    ring
  show ((Real.sqrt γ / 2 : ℝ) : ℂ) * ((Real.sqrt γ / 2 : ℝ) : ℂ) = _
  rw [← Complex.ofReal_mul, key]
  norm_num

noncomputable def depolarizingGKSL (γ : ℝ) : GKSL 2 where
  ham := 0
  hamHermitian := Matrix.isHermitian_zero
  jumps := fun j => if j = 0 then depolCoef γ • pauliX
    else if j = 1 then depolCoef γ • pauliY
    else if j = 2 then depolCoef γ • pauliZ else 0

/-- The zeroth depolarizing jump is the depolarizing coefficient times Pauli X. -/
theorem depolarizingGKSL_jumps_zero (γ : ℝ) :
    (depolarizingGKSL γ).jumps 0 = depolCoef γ • pauliX := by simp [depolarizingGKSL]

/-- The first depolarizing jump is the depolarizing coefficient times Pauli Y. -/
theorem depolarizingGKSL_jumps_one (γ : ℝ) :
    (depolarizingGKSL γ).jumps 1 = depolCoef γ • pauliY := by simp [depolarizingGKSL]

/-- The second depolarizing jump is the depolarizing coefficient times Pauli Z. -/
theorem depolarizingGKSL_jumps_two (γ : ℝ) :
    (depolarizingGKSL γ).jumps 2 = depolCoef γ • pauliZ := by simp [depolarizingGKSL]

/-- The third depolarizing jump is zero. -/
theorem depolarizingGKSL_jumps_three (γ : ℝ) :
    (depolarizingGKSL γ).jumps 3 = 0 := by simp [depolarizingGKSL]

/-- For a nonnegative rate, the depolarizing generator negates the rate-scaled operator and adds
half the rate times its trace times the identity. -/
theorem lindbladApply_depolarizing (γ : ℝ) (hγ : 0 ≤ γ) (X : Operator 2) :
    lindbladApply (depolarizingGKSL γ) X
      = -(γ : ℂ) • X + ((γ : ℂ) / 2 * Matrix.trace X) • (1 : Operator 2) := by

  have hjump : ∀ P : Operator 2, P.IsHermitian → P * P = 1 →
      (depolCoef γ • P) * X * ((depolCoef γ • P)ᴴ)
        - (1 / 2 : ℂ) • ((depolCoef γ • P)ᴴ * (depolCoef γ • P) * X
          + X * (depolCoef γ • P)ᴴ * (depolCoef γ • P))
        = (depolCoef γ * depolCoef γ) • (P * X * P)
          - (depolCoef γ * depolCoef γ) • X := by
    intro P hP hPP
    have hPeq : Pᴴ = P := hP
    have hcp : (depolCoef γ • P)ᴴ = depolCoef γ • P := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, depolCoef_conj, hPeq]
    simp only [hcp, hPP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc,
      one_mul, mul_one]
    module

  have hsumT : ∑ j : Fin (2 * 2), ((depolarizingGKSL γ).jumps j * X
        * ((depolarizingGKSL γ).jumps j)ᴴ
      - (1 / 2 : ℂ) • (((depolarizingGKSL γ).jumps j)ᴴ * (depolarizingGKSL γ).jumps j * X
        + X * ((depolarizingGKSL γ).jumps j)ᴴ * (depolarizingGKSL γ).jumps j))
      = ((γ : ℂ) / 4) • (pauliX * X * pauliX + pauliY * X * pauliY + pauliZ * X * pauliZ)
        - ((3 : ℂ) * ((γ : ℂ) / 4)) • X := by
    rw [Fin.sum_univ_four, depolarizingGKSL_jumps_zero, depolarizingGKSL_jumps_one,
      depolarizingGKSL_jumps_two, depolarizingGKSL_jumps_three]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, zero_smul, sub_zero]
    rw [hjump pauliX pauliX_hermitian pauliX_sq, hjump pauliY pauliY_hermitian pauliY_sq,
      hjump pauliZ pauliZ_hermitian pauliZ_sq, depolCoef_sq hγ]
    module

  have hham : (-Complex.I) • ((depolarizingGKSL γ).ham * X - X * (depolarizingGKSL γ).ham)
      = 0 := by
    simp [depolarizingGKSL]
  show (-Complex.I) • ((depolarizingGKSL γ).ham * X - X * (depolarizingGKSL γ).ham)
      + ∑ j : Fin (2 * 2), ((depolarizingGKSL γ).jumps j * X
        * ((depolarizingGKSL γ).jumps j)ᴴ
      - (1 / 2 : ℂ) • (((depolarizingGKSL γ).jumps j)ᴴ * (depolarizingGKSL γ).jumps j * X
        + X * ((depolarizingGKSL γ).jumps j)ᴴ * (depolarizingGKSL γ).jumps j))
      = _
  rw [hham, zero_add, hsumT, pauli_conjSum, smul_sub, smul_smul]
  module

/-- The depolarizing generator annihilates the identity for a nonnegative rate. -/
theorem lindbladApply_depolarizing_one (γ : ℝ) (hγ : 0 ≤ γ) :
    lindbladApply (depolarizingGKSL γ) (1 : Operator 2) = 0 := by
  rw [lindbladApply_depolarizing γ hγ 1]
  have htr : Matrix.trace (1 : Operator 2) = 2 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num
  rw [htr]
  module

/-- The depolarizing generator multiplies the traceless part of an operator by the negative
rate. -/
theorem lindbladApply_depolarizing_traceless (γ : ℝ) (hγ : 0 ≤ γ) (X : Operator 2) :
    lindbladApply (depolarizingGKSL γ) (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2))
      = (-(γ : ℂ)) • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)) := by
  have htr : Matrix.trace (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
      Fintype.card_fin]
    field_simp
    norm_num
  rw [lindbladApply_depolarizing γ hγ _, htr]
  module

set_option maxHeartbeats 800000 in

/-- Each positive iterate of the depolarizing generator is the corresponding power of the
negative rate times the traceless part. -/
theorem depolarizing_iterate_succ (γ : ℝ) (hγ : 0 ≤ γ) (X : Operator 2) (k : ℕ) :
    ((⇑(lindbladMap (depolarizingGKSL γ)))^[k + 1]) X
      = ((-(γ : ℂ)) ^ (k + 1))
        • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)) := by
  induction k with
  | zero =>
    show lindbladApply (depolarizingGKSL γ) X = _
    rw [lindbladApply_depolarizing γ hγ X]
    simp only [Nat.zero_add, pow_one]
    module
  | succ k ih =>
    have hL : ⇑(lindbladMap (depolarizingGKSL γ))
        (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2))
        = (-(γ : ℂ))
          • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)) :=
      lindbladApply_depolarizing_traceless γ hγ X
    rw [Function.iterate_succ_apply', ih, map_smul, hL, smul_smul, ← pow_succ]

set_option maxHeartbeats 2000000 in

/-- The depolarizing semigroup preserves the scalar part and multiplies the traceless part by
the exponential of the negative rate times time. -/
theorem lindbladSemigroup_depolarizing_apply (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ)
    (X : Operator 2) :
    lindbladSemigroup (depolarizingGKSL γ) t X
      = ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)
        + ((Real.exp (-(γ * t)) : ℝ) : ℂ)
          • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)) := by
  have hF := lindbladSemigroup_hasSum (depolarizingGKSL γ) t X
  have hwreal : (-(γ : ℂ)) * (t : ℂ) = ((-(γ * t) : ℝ) : ℂ) := by
    push_cast
    ring
  have hexpw : Complex.exp ((-(γ : ℂ)) * (t : ℂ))
      = ((Real.exp (-(γ * t)) : ℝ) : ℂ) := by
    rw [hwreal, ← Complex.ofReal_exp]

  have hexpSeries : HasSum (fun n : ℕ => ((-(γ : ℂ)) * (t : ℂ)) ^ n / Nat.factorial n)
      (Complex.exp ((-(γ : ℂ)) * (t : ℂ))) := by
    have h0 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((-(γ : ℂ)) * (t : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at h0
    simpa only [smul_eq_mul, div_eq_inv_mul, mul_comm] using h0

  have hshift : HasSum (fun k : ℕ => ((-(γ : ℂ)) * (t : ℂ)) ^ (k + 1)
      / Nat.factorial (k + 1))
      (Complex.exp ((-(γ : ℂ)) * (t : ℂ)) - 1) := by
    have h3 : Complex.exp ((-(γ : ℂ)) * (t : ℂ)) - 1
        + ∑ i ∈ Finset.range 1, ((-(γ : ℂ)) * (t : ℂ)) ^ i / Nat.factorial i
        = Complex.exp ((-(γ : ℂ)) * (t : ℂ)) := by
      simp
    refine (hasSum_nat_add_iff
      (f := fun n : ℕ => ((-(γ : ℂ)) * (t : ℂ)) ^ n / Nat.factorial n) 1).mpr ?_
    rw [h3]
    exact hexpSeries

  have htail : ∀ k : ℕ,
      (((t : ℂ) ^ (k + 1) / Nat.factorial (k + 1))
        • ((⇑(lindbladMap (depolarizingGKSL γ)))^[k + 1]) X)
      = (((-(γ : ℂ)) * (t : ℂ)) ^ (k + 1) / Nat.factorial (k + 1))
        • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)) := by
    intro k
    rw [depolarizing_iterate_succ γ hγ X k, smul_smul]
    congr 1
    have hp : ((-(γ : ℂ)) * (t : ℂ)) ^ (k + 1)
        = ((t : ℂ) ^ (k + 1)) * ((-(γ : ℂ)) ^ (k + 1)) := by
      rw [mul_pow]
      ring
    rw [hp]
    ring
  have hTailSum : HasSum (fun k : ℕ =>
      (((-(γ : ℂ)) * (t : ℂ)) ^ (k + 1) / Nat.factorial (k + 1))
        • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2)))
      ((Complex.exp ((-(γ : ℂ)) * (t : ℂ)) - 1)
        • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2))) :=
    hshift.smul_const _

  have hFtail : HasSum (fun n : ℕ => (((t : ℂ) ^ (n + 1) / Nat.factorial (n + 1))
      • ((⇑(lindbladMap (depolarizingGKSL γ)))^[n + 1]) X))
      ((Complex.exp ((-(γ : ℂ)) * (t : ℂ)) - 1)
        • (X - ((Matrix.trace X) / 2 : ℂ) • (1 : Operator 2))) :=
    hTailSum.congr_fun (fun k => htail k)
  have hF0 : (((t : ℂ) ^ 0 / Nat.factorial 0)
      • ((⇑(lindbladMap (depolarizingGKSL γ)))^[0]) X) = X := by
    simp
  have hmain := (hasSum_nat_add_iff
      (f := fun n : ℕ => (((t : ℂ) ^ n / Nat.factorial n)
        • ((⇑(lindbladMap (depolarizingGKSL γ)))^[n]) X)) 1).mp hFtail
  rw [Finset.sum_range_one, hF0, add_comm] at hmain
  have hfinal := hF.unique hmain
  rw [hfinal, hexpw]
  module

/-- Combines exponential relative-entropy decay and trace-distance mixing under the
entropy-production and entropy-to-distance hypotheses. -/
theorem frontier1 {D : ℕ} (G : GKSL D) {ρstar σ : Operator D}
    (hσ : IsDensityOperator σ) (hσfull : σ.PosDef) {α : ℝ}
    (hep : EntropyProductionIneq G ρstar α) {κ : ℝ} (hκ : 0 ≤ κ)
    (hS0 : 0 ≤ κ * relativeEntropy σ ρstar)
    (hpin : ∀ τ : Operator D, IsDensityOperator τ →
      traceDistance τ ρstar ≤ Real.sqrt (κ * relativeEntropy τ ρstar))
    (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρstar
      ≤ Real.exp (-2 * α * t) * relativeEntropy σ ρstar
      ∧ traceDistance (lindbladSemigroup G t σ) ρstar
        ≤ Real.exp (-α * t) * Real.sqrt (κ * relativeEntropy σ ρstar) :=
  ⟨mlsi_relativeEntropy_decay G hσ hσfull hep t ht,
    mlsi_traceDistance_mixing G hσ hσfull hep hκ hS0 hpin t ht⟩

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup
