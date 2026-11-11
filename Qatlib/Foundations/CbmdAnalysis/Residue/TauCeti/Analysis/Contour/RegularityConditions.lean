/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Argument.Lift
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Contour crossing angles and regularity conditions

Defines `crossingAngle`, `basepointAngle`, and the flatness conditions `FlatOfOrder` and
`FlatOfOrderBasepoint`. `ConditionAprime` and `ConditionB` package the geometric and
Laurent-sector hypotheses used at contour singularities.

The angle bounds and resonance lemmas connect these hypotheses to powers of normalized tangent
directions, supporting the contour methods of [WangEtAl2026].

## Main statements

* `crossingAngle_eq_pi`: The crossing angle equals `π` when the two one-sided derivative limits
  coincide and are nonzero.
* `FlatOfOrder.of_le`: Flatness of order `n` implies flatness of every order `m ≤ n` when the
  curve is continuous at the crossing.
* `pow_unit_tangent_eq_of_resonance`: Resonance of the crossing angle implies equality of the
  `k`th powers of the normalized nonzero one-sided tangent limits.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- The crossing angle at `t₀`, obtained from the one-sided derivative limits and reduced to
`[0, 2π)`. -/
def crossingAngle (γ : ℝ → ℂ) (t₀ : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)) - Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)))

/-- The angle between the outgoing tangent at `a` and the reversed incoming tangent at `b`,
reduced to `[0, 2π)`. -/
def basepointAngle (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  toIcoMod Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] b) (deriv γ)) - Complex.arg (limUnder (𝓝[>] a) (deriv γ)))

/-- For nonzero `L`, the argument difference between `-L` and `L`, reduced modulo `2π`, equals
`π`. -/
private theorem toIcoMod_arg_neg_sub_arg {L : ℂ} (hL : L ≠ 0) :
    toIcoMod Real.two_pi_pos 0 (Complex.arg (-L) - Complex.arg L) = Real.pi := by
  have hangle : ((Complex.arg (-L) - Complex.arg L : ℝ) : Real.Angle) = (Real.pi : ℝ) := by
    rw [Real.Angle.coe_sub, Complex.arg_neg_coe_angle hL]
    abel
  rw [Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq.mpr hangle]
  exact (toIcoMod_eq_self Real.two_pi_pos).mpr
    (Set.mem_Ico.mpr ⟨Real.pi_nonneg, by rw [zero_add]; linarith [Real.pi_pos]⟩)

/-- Computes the crossing angle from specified right and left limits of the derivative. -/
theorem crossingAngle_eq_of_tendsto {γ : ℝ → ℂ} {t₀ : ℝ} {L_R L_L : ℂ}
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    crossingAngle γ t₀ =
      toIcoMod Real.two_pi_pos 0 (Complex.arg (-L_L) - Complex.arg L_R) := by
  rw [crossingAngle, h_R.limUnder_eq, h_L.limUnder_eq]

/-- Computes the basepoint angle from the derivative limits to the right of `a` and to the left
of `b`. -/
theorem basepointAngle_eq_of_tendsto {γ : ℝ → ℂ} {a b : ℝ} {L_R L_L : ℂ}
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] a) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] b) (𝓝 L_L)) :
    basepointAngle γ a b =
      toIcoMod Real.two_pi_pos 0 (Complex.arg (-L_L) - Complex.arg L_R) := by
  rw [basepointAngle, h_R.limUnder_eq, h_L.limUnder_eq]

/-- The crossing angle belongs to the half-open interval `[0, 2π)`. -/
theorem crossingAngle_mem_Ico (γ : ℝ → ℂ) (t₀ : ℝ) :
    crossingAngle γ t₀ ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] t₀) (deriv γ)) - Complex.arg (limUnder (𝓝[>] t₀) (deriv γ)))
  rw [zero_add] at h
  rw [crossingAngle]
  exact h

/-- The crossing angle is nonnegative. -/
@[simp] theorem crossingAngle_nonneg (γ : ℝ → ℂ) (t₀ : ℝ) : 0 ≤ crossingAngle γ t₀ :=
  (Set.mem_Ico.mp (crossingAngle_mem_Ico γ t₀)).1

/-- The crossing angle is strictly less than `2π`. -/
@[simp] theorem crossingAngle_lt_two_pi (γ : ℝ → ℂ) (t₀ : ℝ) :
    crossingAngle γ t₀ < 2 * Real.pi :=
  (Set.mem_Ico.mp (crossingAngle_mem_Ico γ t₀)).2

/-- The crossing angle equals `π` when the two one-sided derivative limits coincide and are
nonzero. -/
theorem crossingAngle_eq_pi {γ : ℝ → ℂ} {t₀ : ℝ}
    (h : limUnder (𝓝[<] t₀) (deriv γ) = limUnder (𝓝[>] t₀) (deriv γ))
    (hL : limUnder (𝓝[>] t₀) (deriv γ) ≠ 0) :
    crossingAngle γ t₀ = Real.pi := by
  rw [crossingAngle, h]
  exact toIcoMod_arg_neg_sub_arg hL

/-- Expresses the crossing angle in `Real.Angle` as a sum and difference of arguments of ratios
involving the nonzero tangent limits and auxiliary complex numbers. -/
theorem coe_crossingAngle_eq_arg_neg_div_add_arg_div_sub_arg_div {γ : ℝ → ℂ} {t₀ : ℝ}
    {L_R L_L w_L w_R : ℂ} (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0) (hw_L : w_L ≠ 0) (hw_R : w_R ≠ 0)
    (h_R : Filter.Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) : (crossingAngle γ t₀ : Real.Angle)
      = ((((-L_L) / w_L).arg : ℝ) : Real.Angle) + (((w_R / L_R).arg : ℝ) : Real.Angle)
        - (((w_R / w_L).arg : ℝ) : Real.Angle) := by
  rw [crossingAngle_eq_of_tendsto h_R h_L, Real.Angle.coe_toIcoMod,
    Complex.arg_div_coe_angle (neg_ne_zero.mpr hL_L) hw_L, Complex.arg_div_coe_angle hw_R hL_R,
    Complex.arg_div_coe_angle hw_R hw_L, Real.Angle.coe_sub]
  abel

/-- The basepoint angle belongs to the half-open interval `[0, 2π)`. -/
theorem basepointAngle_mem_Ico (γ : ℝ → ℂ) (a b : ℝ) :
    basepointAngle γ a b ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := toIcoMod_mem_Ico Real.two_pi_pos 0
    (Complex.arg (-limUnder (𝓝[<] b) (deriv γ)) - Complex.arg (limUnder (𝓝[>] a) (deriv γ)))
  rw [zero_add] at h
  rw [basepointAngle]
  exact h

/-- The basepoint angle is nonnegative. -/
@[simp] theorem basepointAngle_nonneg (γ : ℝ → ℂ) (a b : ℝ) : 0 ≤ basepointAngle γ a b :=
  (Set.mem_Ico.mp (basepointAngle_mem_Ico γ a b)).1

/-- The basepoint angle is strictly less than `2π`. -/
@[simp] theorem basepointAngle_lt_two_pi (γ : ℝ → ℂ) (a b : ℝ) :
    basepointAngle γ a b < 2 * Real.pi :=
  (Set.mem_Ico.mp (basepointAngle_mem_Ico γ a b)).2

/-- The basepoint angle equals `π` when the incoming and outgoing derivative limits coincide and
are nonzero. -/
theorem basepointAngle_eq_pi {γ : ℝ → ℂ} {a b : ℝ}
    (h : limUnder (𝓝[<] b) (deriv γ) = limUnder (𝓝[>] a) (deriv γ))
    (hL : limUnder (𝓝[>] a) (deriv γ) ≠ 0) :
    basepointAngle γ a b = Real.pi := by
  rw [basepointAngle, h]
  exact toIcoMod_arg_neg_sub_arg hL

/-- Flatness of order `n` at `t₀`: on each side, the transverse displacement from some nonzero
direction is little-o of the `n`th power of the chord length. -/
def FlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
    (fun t => |((γ t - γ t₀) * star v_plus).im| / ‖v_plus‖)
        =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
    (fun t => |((γ t - γ t₀) * star v_minus).im| / ‖v_minus‖)
        =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n)

/-- Endpoint flatness of order `n`, with separate nonzero directions controlling the transverse
displacements to the right of `a` and to the left of `b`. -/
def FlatOfOrderBasepoint (γ : ℝ → ℂ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
    (fun t => |((γ t - γ a) * star v_plus).im| / ‖v_plus‖) =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
    (fun t => |((γ t - γ b) * star v_minus).im| / ‖v_minus‖) =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n)

/-- Characterizes order-`n` flatness by the existence of two nonzero directions satisfying the
one-sided transverse little-o estimates. -/
theorem flatOfOrder_iff {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ} :
    FlatOfOrder γ t₀ n ↔
      ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
        (fun t => |((γ t - γ t₀) * star v_plus).im| / ‖v_plus‖)
            =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) ∧
        (fun t => |((γ t - γ t₀) * star v_minus).im| / ‖v_minus‖)
            =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ n) :=
  Iff.rfl

/-- Eventual collinearity with nonzero directions on both sides implies flatness of every
specified order. -/
theorem flatOfOrder_of_eventually_collinear {γ : ℝ → ℂ} {t₀ : ℝ} {v_plus v_minus : ℂ}
    (hv_plus : v_plus ≠ 0) (hv_minus : v_minus ≠ 0) (n : ℕ)
    (hplus : ∀ᶠ t in 𝓝[>] t₀, ((γ t - γ t₀) * star v_plus).im = 0)
    (hminus : ∀ᶠ t in 𝓝[<] t₀, ((γ t - γ t₀) * star v_minus).im = 0) :
    FlatOfOrder γ t₀ n := by
  rw [flatOfOrder_iff]
  refine ⟨v_plus, v_minus, hv_plus, hv_minus, ?_, ?_⟩ <;>
    refine (Asymptotics.isLittleO_zero _ _).congr' ?_ Filter.EventuallyEq.rfl
  · filter_upwards [hplus] with t ht
    rw [ht]
    simp
  · filter_upwards [hminus] with t ht
    rw [ht]
    simp

/-- Characterizes endpoint flatness by the two nonzero directions and their one-sided transverse
little-o estimates. -/
theorem flatOfOrderBasepoint_iff {γ : ℝ → ℂ} {a b : ℝ} {n : ℕ} :
    FlatOfOrderBasepoint γ a b n ↔
      ∃ v_plus v_minus : ℂ, v_plus ≠ 0 ∧ v_minus ≠ 0 ∧
        (fun t => |((γ t - γ a) * star v_plus).im| / ‖v_plus‖)
            =o[𝓝[>] a] (fun t => ‖γ t - γ a‖ ^ n) ∧
        (fun t => |((γ t - γ b) * star v_minus).im| / ‖v_minus‖)
            =o[𝓝[<] b] (fun t => ‖γ t - γ b‖ ^ n) :=
  Iff.rfl

/-- Finite crossings of `S` together with flatness at singular crossings and endpoints of at
least the corresponding pole order. -/
structure ConditionAprime (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (S : Finset ℂ) : Prop where

  finite_crossings : ∀ s ∈ S, (Set.uIcc a b ∩ γ ⁻¹' {s}).Finite

  interior : ∀ t₀ ∈ Set.Ioo (min a b) (max a b), γ t₀ ∈ S → ∀ n : ℕ, 1 ≤ n →
    meromorphicOrderAt f (γ t₀) = (-(n : ℤ) : WithTop ℤ) → FlatOfOrder γ t₀ n

  basepoint : γ (min a b) ∈ S → ∀ n : ℕ, 1 ≤ n →
    meromorphicOrderAt f (γ (min a b)) = (-(n : ℤ) : WithTop ℤ) →
      FlatOfOrderBasepoint γ (min a b) (max a b) n

/-- Expands `ConditionAprime` into finite crossings and the interior and endpoint flatness
requirements. -/
theorem conditionAprime_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} :
    ConditionAprime γ a b f S ↔
      (∀ s ∈ S, (Set.uIcc a b ∩ γ ⁻¹' {s}).Finite) ∧
      (∀ t₀ ∈ Set.Ioo (min a b) (max a b), γ t₀ ∈ S → ∀ n : ℕ, 1 ≤ n →
          meromorphicOrderAt f (γ t₀) = (-(n : ℤ) : WithTop ℤ) → FlatOfOrder γ t₀ n) ∧
        (γ (min a b) ∈ S → ∀ n : ℕ, 1 ≤ n →
          meromorphicOrderAt f (γ (min a b)) = (-(n : ℤ) : WithTop ℤ) →
          FlatOfOrderBasepoint γ (min a b) (max a b) n) :=
  ⟨fun h => ⟨h.finite_crossings, h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Condition A-prime is invariant under exchanging the interval endpoints. -/
theorem conditionAprime_comm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {S : Finset ℂ} :
    ConditionAprime γ a b f S ↔ ConditionAprime γ b a f S := by
  rw [conditionAprime_iff, conditionAprime_iff, Set.uIcc_comm, min_comm a b, max_comm a b]

/-- Compatibility of a rational multiple of `π` with a finite Laurent principal part, requiring
angular resonance for its nonzero terms of pole order at least two. -/
structure SectorCompatible (f : ℂ → ℂ) (z₀ : ℂ) (θ : ℝ) : Prop where

  angle_rational : ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)

  laurent_compatible : ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
    (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
      ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val → ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi)

/-- Expands sector compatibility into rationality of the angle and an
analytic-plus-principal-part representation with resonant coefficients. -/
theorem sectorCompatible_iff {f : ℂ → ℂ} {z₀ : ℂ} {θ : ℝ} :
    SectorCompatible f z₀ θ ↔
      (∃ p q : ℕ,
        q ≠ 0 ∧ Nat.Coprime p q ∧ θ = (p : ℝ) * Real.pi / (q : ℝ)) ∧
      ∃ (N : ℕ) (coeff : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
        (∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, coeff k / (z - z₀) ^ (k.val + 1)) ∧
        ∀ k : Fin N, coeff k ≠ 0 → 1 ≤ k.val →
          ∃ m : ℤ, (k.val : ℝ) * θ = (m : ℝ) * (2 * Real.pi) :=
  ⟨fun h => ⟨h.angle_rational, h.laurent_compatible⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Sector compatibility at interior crossings and the basepoint whenever the meromorphic order
is less than `-1`. -/
structure ConditionB (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : Prop where

  interior : ∀ t₀ ∈ Set.Ioo (min a b) (max a b), meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
    SectorCompatible f (γ t₀) (crossingAngle γ t₀)

  basepoint : meromorphicOrderAt f (γ (min a b)) < (-1 : ℤ) →
    SectorCompatible f (γ (min a b)) (basepointAngle γ (min a b) (max a b))

/-- Expands Condition B into its interior crossing and basepoint sector compatibility
requirements. -/
theorem conditionB_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔
      (∀ t₀ ∈ Set.Ioo (min a b) (max a b), meromorphicOrderAt f (γ t₀) < (-1 : ℤ) →
          SectorCompatible f (γ t₀) (crossingAngle γ t₀)) ∧
        (meromorphicOrderAt f (γ (min a b)) < (-1 : ℤ) →
          SectorCompatible f (γ (min a b)) (basepointAngle γ (min a b) (max a b))) :=
  ⟨fun h => ⟨h.interior, h.basepoint⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Condition B is invariant under exchanging the interval endpoints. -/
theorem conditionB_comm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} :
    ConditionB γ a b f ↔ ConditionB γ b a f := by
  rw [conditionB_iff, conditionB_iff, min_comm a b, max_comm a b]

/-- A little-o bound by the `n`th power of a chord length implies the corresponding bound for
every lower power, assuming continuity at the limiting point. -/
private theorem isLittleO_chord_pow_of_le {γ : ℝ → ℂ} {c : ℝ} {u : ℝ → ℝ} {m n : ℕ}
    {l : Filter ℝ} (hmn : m ≤ n) (h_le : l ≤ 𝓝 c) (h_cont : ContinuousAt γ c)
    (h : u =o[l] fun t => ‖γ t - γ c‖ ^ n) : u =o[l] fun t => ‖γ t - γ c‖ ^ m := by
  refine h.trans_isBigO (Asymptotics.IsBigO.of_bound 1 ?_)
  have h_ev : ∀ᶠ t in 𝓝 c, ‖γ t - γ c‖ ≤ 1 := by
    have h1 : Filter.Tendsto (fun t => γ t - γ c) (𝓝 c) (𝓝 (γ c - γ c)) :=
      (h_cont.sub continuousAt_const).tendsto
    rw [sub_self] at h1
    have h0 : Filter.Tendsto (fun t => ‖γ t - γ c‖) (𝓝 c) (𝓝 0) := by
      simpa using h1.norm
    exact h0.eventually_le_const one_pos
  filter_upwards [h_le h_ev] with t ht
  rw [one_mul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _),
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_of_le_one (norm_nonneg _) ht hmn

/-- Flatness of order `n` implies flatness of every order `m ≤ n` when the curve is continuous
at the crossing. -/
theorem FlatOfOrder.of_le {γ : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ} (h : FlatOfOrder γ t₀ n)
    (hmn : m ≤ n) (h_cont : ContinuousAt γ t₀) : FlatOfOrder γ t₀ m := by
  obtain ⟨v_p, v_m, hv_p, hv_m, h_right, h_left⟩ := h
  exact ⟨v_p, v_m, hv_p, hv_m,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont h_right,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont h_left⟩

/-- Endpoint flatness of order `n` implies endpoint flatness of every order `m ≤ n` when the
curve is continuous at both endpoints. -/
theorem FlatOfOrderBasepoint.of_le {γ : ℝ → ℂ} {a b : ℝ} {m n : ℕ}
    (h : FlatOfOrderBasepoint γ a b n) (hmn : m ≤ n)
    (h_cont_a : ContinuousAt γ a) (h_cont_b : ContinuousAt γ b) :
    FlatOfOrderBasepoint γ a b m := by
  obtain ⟨v_p, v_m, hv_p, hv_m, h_right, h_left⟩ := h
  exact ⟨v_p, v_m, hv_p, hv_m,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont_a h_right,
    isLittleO_chord_pow_of_le hmn nhdsWithin_le_nhds h_cont_b h_left⟩

/-- Reduction modulo `2π` subtracts an integer multiple of `2π`. -/
private theorem toIcoMod_two_pi_sub_witness (θ : ℝ) :
    ∃ j : ℤ, toIcoMod Real.two_pi_pos 0 θ = θ - (j : ℝ) * (2 * Real.pi) := by
  refine ⟨toIcoDiv Real.two_pi_pos 0 θ, ?_⟩
  have h_sub := self_sub_toIcoMod Real.two_pi_pos 0 θ
  rw [zsmul_eq_mul] at h_sub
  linarith

/-- Angular resonance forces the `k`th powers of the normalized outgoing and reversed incoming
directions to coincide. -/
private theorem pow_unit_eq_of_angle_resonance {L_R L_L : ℂ} {θ : ℝ} {k : ℕ}
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (hθ : ∃ j : ℤ, θ = (Complex.arg (-L_L) - Complex.arg L_R) - (j : ℝ) * (2 * Real.pi))
    (h_res : ∃ m : ℤ, (k : ℝ) * θ = (m : ℝ) * (2 * Real.pi)) :
    (L_R / (‖L_R‖ : ℂ)) ^ k = ((-L_L) / (‖L_L‖ : ℂ)) ^ k := by
  obtain ⟨j, hj⟩ := hθ
  obtain ⟨m, hm⟩ := h_res
  rw [hj] at hm
  have h_real : (k : ℝ) * Complex.arg L_R
      = (k : ℝ) * Complex.arg (-L_L) + (-((m : ℝ) + (k : ℝ) * (j : ℝ))) * (2 * Real.pi) := by
    linear_combination -hm
  have hnorm : (‖L_L‖ : ℂ) = (‖-L_L‖ : ℂ) := by rw [norm_neg]
  rw [div_norm_eq_exp_arg_mul_I hL_R, hnorm,
    div_norm_eq_exp_arg_mul_I (neg_ne_zero.mpr hL_L), ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(m + (k : ℤ) * j), ?_⟩
  have hC := congrArg (fun x : ℝ => (x : ℂ) * Complex.I) h_real
  push_cast at hC ⊢
  linear_combination hC

/-- Resonance of the crossing angle implies equality of the `k`th powers of the normalized
nonzero one-sided tangent limits. -/
theorem pow_unit_tangent_eq_of_resonance {γ : ℝ → ℂ} {t₀ : ℝ} {L_R L_L : ℂ} {k : ℕ}
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0) (h_R : Filter.Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_res : ∃ m : ℤ, (k : ℝ) * crossingAngle γ t₀ = (m : ℝ) * (2 * Real.pi)) :
    (L_R / (‖L_R‖ : ℂ)) ^ k = ((-L_L) / (‖L_L‖ : ℂ)) ^ k := by
  obtain ⟨j, hj⟩ := toIcoMod_two_pi_sub_witness (Complex.arg (-L_L) - Complex.arg L_R)
  refine pow_unit_eq_of_angle_resonance hL_R hL_L ⟨j, ?_⟩ h_res
  rw [crossingAngle_eq_of_tendsto h_R h_L]
  exact hj

/-- Resonance of the basepoint angle implies equality of the `k`th powers of the normalized
nonzero endpoint tangent limits. -/
theorem pow_unit_tangent_eq_of_basepoint_resonance {γ : ℝ → ℂ} {a b : ℝ} {L_R L_L : ℂ}
    {k : ℕ} (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0) (h_R : Filter.Tendsto (deriv γ) (𝓝[>] a) (𝓝 L_R))
    (h_L : Filter.Tendsto (deriv γ) (𝓝[<] b) (𝓝 L_L))
    (h_res : ∃ m : ℤ, (k : ℝ) * basepointAngle γ a b = (m : ℝ) * (2 * Real.pi)) :
    (L_R / (‖L_R‖ : ℂ)) ^ k = ((-L_L) / (‖L_L‖ : ℂ)) ^ k := by
  obtain ⟨j, hj⟩ := toIcoMod_two_pi_sub_witness (Complex.arg (-L_L) - Complex.arg L_R)
  refine pow_unit_eq_of_angle_resonance hL_R hL_L ⟨j, ?_⟩ h_res
  rw [basepointAngle_eq_of_tendsto h_R h_L]
  exact hj

end TauCeti.Contour

end
end
end Qatlib.Foundations.CbmdAnalysis.Residue
