/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4QuadraticSpeedupWithKnownAStat

/-!
# Exact amplification with known success probability

`zoo_amplitude_amplification_known_a_exact` constructs an ancillary mixing parameter and a
finite instruction program that achieve success probability one when the initial positive
probability is known. The proof analyzes the program as a two dimensional rotation and bounds
its preparation calls by constant multiples of `1 / sqrt a`. See [BrassardEtAl2002] for
background.

## Main statements

* `parameters`: For `0 < a < 1`, the chosen angle and ratio are valid, give an exact final angle
  of `π / 2`, and place the call count between the stated multiples of `1 / sqrt a`.
* `zoo_amplitude_amplification_known_a_exact`: There is a design achieving success probability
  one for every known positive initial success probability `a`, with preparation and inverse
  preparation call count bounded above and below by positive constant multiples of `1 / sqrt a`,
  as in [Brassard et al., Theorem 4][BrassardEtAl2002].

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.AmplifyCore

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace

namespace zoo_amplitude_amplification_known_a_exact

/-- For a unit vector, orthogonal projection is idempotent on its image, its inner product with
the original vector is its squared norm, and that squared norm is at most one. -/
lemma projection {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Submodule ℂ H) [S.HasOrthogonalProjection] (ψ : H)
    (hψ : ‖ψ‖ = 1) :
    S.starProjection (S.starProjection ψ) = S.starProjection ψ ∧
    inner ℂ ψ (S.starProjection ψ) = (‖S.starProjection ψ‖ ^ 2 : ℝ) ∧
    ‖S.starProjection ψ‖ ^ 2 ≤ 1 := by
  have hid : ∀ x, S.starProjection (S.starProjection x) = S.starProjection x :=
    fun x => DFunLike.congr_fun S.isIdempotentElem_starProjection x
  refine ⟨hid ψ, ?_, ?_⟩
  · rw [← hid ψ, ← S.inner_starProjection_left_eq_right, hid ψ,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  · have h := Submodule.norm_sq_eq_add_norm_sq_starProjection ψ S
    rw [hψ] at h
    nlinarith [sq_nonneg (‖ψ - S.starProjection ψ‖)]

/-- The exact amplification program with an initial preparation and ancillary rotation followed
by `m` six instruction amplification blocks. -/
def program (m : ℕ) : List (Fin 6) :=
  [0, 2] ++ (List.replicate m [5, 3, 1, 4, 0, 2]).flatten

/-- The exact amplification program uses `2 * m + 1` preparation or inverse preparation calls. -/
lemma program_calls (m : ℕ) : Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls (program m) = 2 * m + 1 := by
  induction m with
  | zero => simp [program, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls]
  | succ m ih =>
    simp only [program, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls, List.filter_append, List.length_append,
      List.replicate_succ, List.flatten_cons] at *
    norm_num at *
    omega

/-- The linear operator on vector pairs representing a good component reflection followed by the
prepared pair reflection with coefficients `c` and `s`. -/
noncomputable def operator {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (P : H →L[ℂ] H) (c s : ℝ) : (H × H) →ₗ[ℂ] (H × H) where
  toFun v :=
    let w := (v.1, v.2 - (2 : ℂ) • P v.2)
    let t := (2 : ℂ) * ((c : ℂ) * inner ℂ ψ w.1 + (s : ℂ) * inner ℂ ψ w.2)
    (-w.1 + t • ((c : ℂ) • ψ), -w.2 + t • ((s : ℂ) • ψ))
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add, inner_add_right,
      inner_sub_right, inner_smul_right]
    ext <;> dsimp <;> module
  map_smul' z v := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, inner_sub_right, inner_smul_right]
    ext <;> dsimp <;> module

/-- For `0 ≤ r ≤ 1`, execution of one six instruction block equals the pair operator with
coefficients `sqrt (1 - r)` and `sqrt r`. -/
lemma block {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (P : H →L[ℂ] H) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (v : H × H) :
    ([5, 3, 1, 4, 0, 2] : List (Fin 6)).foldl
      (fun v k => Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e P r k v) v =
    operator (A e) P (Real.sqrt (1-r)) (Real.sqrt r) v := by
  have hcs : (Real.sqrt (1-r) : ℂ)^2 + (Real.sqrt r : ℂ)^2 = 1 := by
    have h1 := Real.sq_sqrt (by linarith : 0 ≤ 1-r)
    have h2 := Real.sq_sqrt hr
    exact_mod_cast (show Real.sqrt (1-r)^2 + Real.sqrt r^2 = 1 by linarith)
  have halg (x : ℝ) : algebraMap ℝ ℂ x = (x:ℂ) := rfl
  simp only [List.foldl_cons, List.foldl_nil,
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step]
  dsimp [-Complex.coe_smul]
  simp only [map_add, map_sub, map_smul, map_neg, A.apply_symm_apply,
    inner_add_right, inner_smul_right, ← A.inner_map_eq_flip]
  apply Prod.ext <;> dsimp [operator, -Complex.coe_smul] <;>
    simp only [inner_sub_right, inner_smul_right] <;>
    match_scalars <;>
    (try simp only [halg, ← A.inner_map_eq_flip]) <;>
    solve | ring | linear_combination hcs | linear_combination -hcs |
      linear_combination 2*hcs

/-- The stated action on good and bad vectors yields the sine and cosine ratio formula after `m`
iterations. -/
lemma rotation {E : Type} [AddCommGroup E] [Module ℂ E]
    (Q : E →ₗ[ℂ] E) (g b : E) (θ a : ℝ)
    (hsq : Real.sin θ ^ 2 = a) (hcq : Real.cos θ ^ 2 = 1-a)
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0)
    (hg : Q g = (1-2*(a:ℂ)) • g - (2*(a:ℂ)) • b)
    (hb : Q b = (2*(1-(a:ℂ))) • g + (1-2*(a:ℂ)) • b)
    (m : ℕ) :
    (Q : E → E)^[m] (g+b) =
      ((Real.sin ((2*(m:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ) • g +
      ((Real.cos ((2*(m:ℝ)+1)*θ) / Real.cos θ : ℝ) : ℂ) • b := by
  induction m with
  | zero => simp [hs, hc]
  | succ m ih =>
    have hα : (2*((m+1:ℕ):ℝ)+1)*θ = (2*(m:ℝ)+1)*θ+2*θ := by push_cast; ring
    have hsin := zoo_counting_rankone_known_success_amplification_sin_rec
      (α := (2*(m:ℝ)+1)*θ) rfl rfl hcq rfl hs hc
    have hcos := zoo_counting_rankone_known_success_amplification_cos_rec
      (α := (2*(m:ℝ)+1)*θ) rfl rfl hsq hcq hs hc
    rw [Function.iterate_succ_apply', ih, map_add, map_smul, map_smul, hg, hb, hα,
      hsin, hcos]
    push_cast
    module

/-- The natural ceiling iteration count `ceil (π / (4 * arcsin (sqrt a)) - 1 / 2)` for exact
amplification. -/
noncomputable def iterations (a : ℝ) : ℕ :=
  Nat.ceil (Real.pi / (4 * Real.arcsin (Real.sqrt a)) - 1/2)

/-- The adjusted success angle `π / (4 * iterations a + 2)`. -/
noncomputable def angle (a : ℝ) : ℝ := Real.pi / (4*(iterations a : ℝ)+2)

/-- The ancillary success scaling factor `sin (angle a)^2 / a`. -/
noncomputable def ratio (a : ℝ) : ℝ := Real.sin (angle a)^2 / a

/-- For `0 < a < 1`, the chosen angle and ratio are valid, give an exact final angle of `π / 2`,
and place the call count between the stated multiples of `1 / sqrt a`. -/
lemma parameters (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    0 < angle a ∧ angle a < Real.pi/2 ∧
    0 ≤ ratio a ∧ ratio a ≤ 1 ∧
    ratio a * a = Real.sin (angle a)^2 ∧
    (2*(iterations a : ℝ)+1)*angle a = Real.pi/2 ∧
    1/Real.sqrt a ≤ (2*(iterations a : ℝ)+1) ∧
    (2*(iterations a : ℝ)+1) ≤ (Real.pi/2+2)/Real.sqrt a := by
  let θ := Real.arcsin (Real.sqrt a)
  let m := iterations a
  have hπ := Real.pi_pos
  have hs0 := Real.sqrt_pos_of_pos ha
  have hs1 : Real.sqrt a < 1 := by simpa using Real.sqrt_lt_sqrt ha.le ha1
  have hsin : Real.sin θ = Real.sqrt a := Real.sin_arcsin (by linarith) hs1.le
  have ht0 : 0 < θ := Real.arcsin_pos.mpr hs0
  have ht1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have ht4 : 0 < 4*θ := by positivity
  have hx : 0 < Real.pi/(4*θ)-1/2 := by
    have := (lt_div_iff₀ ht4).mpr (show (1/2:ℝ)*(4*θ) < Real.pi by linarith)
    linarith
  have hmlo : Real.pi/(4*θ)-1/2 ≤ (m:ℝ) := Nat.le_ceil _
  have hmhi : (m:ℝ) < Real.pi/(4*θ)-1/2+1 := Nat.ceil_lt_add_one hx.le
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le hx hmlo
  have hn : 0 < 4*(m:ℝ)+2 := by positivity
  have hlo : Real.pi/2 ≤ (2*(m:ℝ)+1)*θ := by
    have := (div_le_iff₀ ht4).mp (show Real.pi/(4*θ) ≤ (m:ℝ)+1/2 by linarith)
    nlinarith
  have hhi : (2*(m:ℝ)+1)*θ < Real.pi/2+2*θ := by
    have := (lt_div_iff₀ ht4).mp (show (m:ℝ)-1/2 < Real.pi/(4*θ) by linarith)
    nlinarith
  have hd0 : 0 < angle a := div_pos hπ hn
  have hd1 : angle a < Real.pi/2 := by
    change Real.pi/(4*(m:ℝ)+2) < Real.pi/2
    rw [div_lt_iff₀ hn]
    nlinarith
  have hdθ : angle a ≤ θ := by
    change Real.pi/(4*(m:ℝ)+2) ≤ θ
    rw [div_le_iff₀ hn]
    nlinarith
  have hsd0 : 0 ≤ Real.sin (angle a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd0.le (by linarith)
  have hsd : Real.sin (angle a) ≤ Real.sqrt a := by
    rw [← hsin]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) ht1.le hdθ
  have hsd2 : Real.sin (angle a)^2 ≤ a := by
    nlinarith [Real.sq_sqrt ha.le]
  have hphase : (2*(m:ℝ)+1)*angle a = Real.pi/2 := by
    dsimp [angle]
    change (2*(m:ℝ)+1)*(Real.pi/(4*(m:ℝ)+2)) = Real.pi/2
    field_simp
    ring
  refine ⟨hd0, hd1, div_nonneg (sq_nonneg _) ha.le,
    (div_le_one ha).mpr hsd2, div_mul_cancel₀ _ ha.ne', hphase, ?_, ?_⟩
  · rw [div_le_iff₀ hs0]
    have htSin := Real.mul_le_sin ht0.le ht1.le
    rw [hsin] at htSin
    have htSin' : 2*θ ≤ Real.pi*Real.sqrt a := by
      have := (div_le_iff₀ hπ).mp (show 2*θ/Real.pi ≤ Real.sqrt a by
        simpa [div_mul_eq_mul_div] using htSin)
      linarith
    have hmul := mul_le_mul_of_nonneg_left htSin' (show 0 ≤ 2*(m:ℝ)+1 by positivity)
    apply (mul_le_mul_iff_right₀ hπ).mp
    nlinarith
  · rw [le_div_iff₀ hs0]
    have hsinle : Real.sqrt a ≤ θ := by rw [← hsin]; exact Real.sin_le ht0.le
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m from (show 0 < m by exact_mod_cast hmpos))
    have hmul := mul_nonneg (show 0 ≤ 2*(m:ℝ)-1 by linarith) (sub_nonneg.mpr hsinle)
    nlinarith

/-- On the specified pair components, the pair operator has the Grover coefficient action with
effective success probability `s^2 * a`. -/
lemma action {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (P : H →L[ℂ] H) (c s a : ℝ)
    (hψ : ‖ψ‖ = 1) (hP : P (P ψ) = P ψ)
    (hinner : inner ℂ ψ (P ψ) = (a:ℂ)) (hcs : c^2+s^2=1) :
    let g : H × H := (0, (s:ℂ) • P ψ)
    let b : H × H := ((c:ℂ) • ψ, (s:ℂ) • (ψ-P ψ))
    operator ψ P c s g = (1-2*((s^2*a:ℝ):ℂ)) • g - (2*((s^2*a:ℝ):ℂ)) • b ∧
    operator ψ P c s b = (2*(1-((s^2*a:ℝ):ℂ))) • g +
      (1-2*((s^2*a:ℝ):ℂ)) • b := by
  have hcsC : (c:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast hcs
  constructor <;> apply Prod.ext <;>
    simp [operator, map_sub, hP, hinner, hψ] <;>
    match_scalars <;>
    solve | ring | linear_combination 2*(c:ℂ)*hcsC | linear_combination 2*(s:ℂ)*hcsC

/-- Executing the exact amplification program equals iterating the pair operator on the prepared
and mixed initial pair. -/
lemma execution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (P : H →L[ℂ] H) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (m : ℕ) :
    Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e P r (program m) =
      (operator (A e) P (Real.sqrt (1-r)) (Real.sqrt r) : H × H → H × H)^[m]
        ((Real.sqrt (1-r):ℂ) • A e, (Real.sqrt r:ℂ) • A e) := by
  have hfold : ∀ (m : ℕ) (v : H × H),
      ((List.replicate m [5, 3, 1, 4, 0, 2]).flatten : List (Fin 6)).foldl
        (fun v k => Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step A e P r k v) v =
      (operator (A e) P (Real.sqrt (1-r)) (Real.sqrt r) : H × H → H × H)^[m] v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro v
      rw [List.replicate_succ, List.flatten_cons, List.foldl_append, block A e P r hr hr1,
        ih, Function.iterate_succ_apply]
  simp only [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run, program,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  simpa [Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step] using hfold m
    ((Real.sqrt (1-r):ℂ) • A e, (Real.sqrt r:ℂ) • A e)

/-- When the adjusted angle reaches `π / 2` after `m` iterations, the executed pair has total
squared norm one and good projected squared norm one. -/
lemma exact_state {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H ≃ₗᵢ[ℂ] H) (e : H) (P : H →L[ℂ] H) (a r δ : ℝ) (m : ℕ)
    (hψ : ‖A e‖ = 1) (hP : P (P (A e)) = P (A e))
    (ha : ‖P (A e)‖^2 = a) (hi : inner ℂ (A e) (P (A e)) = (a:ℂ))
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hd0 : 0 < δ) (hd1 : δ < Real.pi/2)
    (hra : r*a = Real.sin δ^2) (hm : (2*(m:ℝ)+1)*δ = Real.pi/2) :
    let v := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e P r (program m)
    ‖v.1‖^2 + ‖v.2‖^2 = 1 ∧ ‖P v.1‖^2 + ‖P v.2‖^2 = 1 := by
  let c := Real.sqrt (1-r)
  let s := Real.sqrt r
  let ψ := A e
  let g : H × H := (0, (s:ℂ) • P ψ)
  let b : H × H := ((c:ℂ) • ψ, (s:ℂ) • (ψ-P ψ))
  have hcs : c^2+s^2=1 := by dsimp [c,s]; rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hr]; ring
  have hs2 : s^2=r := Real.sq_sqrt hr
  have hsq : Real.sin δ^2 = s^2*a := by rw [hs2, hra]
  have hcq : Real.cos δ^2 = 1-s^2*a := by nlinarith [Real.sin_sq_add_cos_sq δ]
  have hspos : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_pos])
  have hcpos : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd1⟩
  obtain ⟨hg,hb⟩ := action ψ P c s a hψ hP hi hcs
  have hrot := rotation (operator ψ P c s) g b δ (s^2*a) hsq hcq hspos.ne' hcpos.ne' hg hb m
  have hsplit : g+b = ((c:ℂ) • ψ, (s:ℂ) • ψ) := by
    apply Prod.ext <;> dsimp [g,b] <;> module
  rw [hsplit, hm, Real.sin_pi_div_two, Real.cos_pi_div_two] at hrot
  simp only [zero_div, Complex.ofReal_zero, zero_smul, add_zero] at hrot
  have hv : Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A e P r (program m) =
      (0, ((1/Real.sin δ:ℝ):ℂ) • ((s:ℂ) • P ψ)) := by
    rw [execution A e P r hr hr1]
    simpa only [g, Prod.smul_mk, smul_zero] using hrot
  have hn : ‖((1/Real.sin δ:ℝ):ℂ) • ((s:ℂ) • P ψ)‖^2 = 1 := by
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, one_pow]
    change 1/Real.sin δ^2 * (s^2 * ‖P (A e)‖^2) = 1
    rw [ha, ← hsq]
    exact one_div_mul_cancel (pow_ne_zero _ hspos.ne')
  (try dsimp only)
  rw [hv]
  simpa [map_smul, show P (P ψ) = P ψ from hP] using And.intro hn hn

/-- Chooses the mixing ratio and exact amplification program from `a`, using a single
preparation when `a = 1`. -/
noncomputable def design (a : ℝ) : ℝ × List (Fin 6) :=
  if a = 1 then (0, [0]) else (ratio a, program (iterations a))

end zoo_amplitude_amplification_known_a_exact

/-- There is a design achieving success probability one for every known positive initial success
probability `a`, with preparation and inverse preparation call count bounded above and below
by positive constant multiples of `1 / sqrt a`, as in [Brassard et al., Theorem
4][BrassardEtAl2002]. -/
theorem zoo_amplitude_amplification_known_a_exact :
    ∃ (design : ℝ → ℝ × List (Fin 6)) (c C : ℝ),
  0 < c ∧ 0 < C ∧
  ∀ (ι H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis ι ℂ H) (i0 : ι)
    (label : ι → ℤ) (A : H ≃ₗᵢ[ℂ] H) (χ : ℤ → Bool) (a : ℝ),
    let P := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection b label χ;
    a = ‖P (A (b i0))‖ ^ 2 →
    0 < a →
    let d := design a;
    let v := Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A (b i0) P d.1 d.2;
    0 ≤ d.1 ∧ d.1 ≤ 1 ∧
    ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 = 1 ∧
    ‖P v.1‖ ^ 2 + ‖P v.2‖ ^ 2 = 1 ∧
    c / Real.sqrt a ≤ (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls d.2 : ℝ) ∧
    (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls d.2 : ℝ) ≤ C / Real.sqrt a := by
  refine ⟨zoo_amplitude_amplification_known_a_exact.design, 1, Real.pi/2+2,
    by norm_num, by positivity, ?_⟩
  intro ι H _ _ _ b i0 label A χ a P ha ha0
  let S :=
      (Submodule.span ℂ ((fun i : ι => b i) '' {i : ι | χ (label i) = true})).topologicalClosure
  have hψ : ‖A (b i0)‖ = 1 := by rw [A.norm_map]; exact b.orthonormal.1 i0
  have hproj := zoo_amplitude_amplification_known_a_exact.projection S (A (b i0)) hψ
  change P (P (A (b i0))) = P (A (b i0)) ∧
    inner ℂ (A (b i0)) (P (A (b i0))) = (‖P (A (b i0))‖^2:ℝ) ∧
    ‖P (A (b i0))‖^2 ≤ 1 at hproj
  by_cases ha1 : a = 1
  · have hmass : ‖P (A (b i0))‖^2 = 1 := ha.symm.trans ha1
    simp [zoo_amplitude_amplification_known_a_exact.design, ha1,
      Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.step, Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls, hψ, hmass]
    linarith [Real.pi_pos]
  · have halt : a < 1 := lt_of_le_of_ne (by linarith [hproj.2.2]) ha1
    obtain ⟨hd0,hd1,hr0,hr1,hra,hm,hlo,hhi⟩ :=
      zoo_amplitude_amplification_known_a_exact.parameters a ha0 halt
    have hstate := zoo_amplitude_amplification_known_a_exact.exact_state
      A (b i0) P a
      (zoo_amplitude_amplification_known_a_exact.ratio a)
      (zoo_amplitude_amplification_known_a_exact.angle a)
      (zoo_amplitude_amplification_known_a_exact.iterations a)
      hψ hproj.1 ha.symm (by rw [ha]; exact hproj.2.1) hr0 hr1 hd0 hd1 hra hm
    simp only [zoo_amplitude_amplification_known_a_exact.design, if_neg ha1]
    refine ⟨hr0,hr1,hstate.1,hstate.2,?_,?_⟩
    · simpa only [zoo_amplitude_amplification_known_a_exact.program_calls,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlo
    · simpa only [zoo_amplitude_amplification_known_a_exact.program_calls,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hhi

end Qatlib.Concepts.AmplitudeCore.AmplifyCore
