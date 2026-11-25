/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanQuotientPeriod

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# The phase return of the Bateman magnetic flow

[Kedia2013TyingKnots], discussion of Fig. 2.
The weighted circle action acts freely and transitively on the fibers
of the quotient of coprime levels. After a lap on the quotient, ODE
uniqueness turns the return into a fixed weighted rotation of the
entire normalized trajectory.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open scoped ComplexConjugate

/-- Opposite phase weights keep the product label fixed. -/
noncomputable def batemanFiberRotate (p q : ℕ) (θ : Circle) (z : ℂ × ℂ) : ℂ × ℂ :=
  ((θ : ℂ) ^ q * z.1, z.2 / (θ : ℂ) ^ p)

/-- The weighted action is free and transitive at fixed nonzero radii
and fixed complex product when the two powers are coprime. -/
theorem existsUnique_batemanFiberRotate {p q : ℕ} (hpq : Nat.Coprime p q)
    {z w : ℂ × ℂ} (hz₁ : z.1 ≠ 0) (hw₂ : w.2 ≠ 0)
    (hr₁ : ‖z.1‖ = ‖w.1‖) (hr₂ : ‖z.2‖ = ‖w.2‖)
    (hg : z.1 ^ p * z.2 ^ q = w.1 ^ p * w.2 ^ q) :
    ∃! θ : Circle, batemanFiberRotate p q θ z = w := by
  let u : Circle := ⟨w.1 / z.1, by
    change w.1 / z.1 ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right, norm_div, ← hr₁, div_self (norm_ne_zero_iff.mpr hz₁)]⟩
  let v : Circle := ⟨z.2 / w.2, by
    change z.2 / w.2 ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right, norm_div, hr₂, div_self (norm_ne_zero_iff.mpr hw₂)]⟩
  have hp : u ^ p = v ^ q := by
    apply Circle.ext
    change (w.1 / z.1) ^ p = (z.2 / w.2) ^ q
    rw [div_pow, div_pow]
    field_simp [pow_ne_zero p hz₁, pow_ne_zero q hw₂]
    linear_combination -hg
  have he (θ : Circle) :
      batemanFiberRotate p q θ z = w ↔ θ ^ q = u ∧ θ ^ p = v := by
    have hθ : (θ : ℂ) ^ p ≠ 0 := pow_ne_zero p (Circle.coe_ne_zero θ)
    constructor
    · intro h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      refine ⟨Circle.ext ?_, Circle.ext ?_⟩
      · change (θ : ℂ) ^ q = w.1 / z.1
        exact (eq_div_iff hz₁).2 h₁
      · change (θ : ℂ) ^ p = z.2 / w.2
        have hmul := (div_eq_iff hθ).1 h₂
        exact (eq_div_iff hw₂).2 (by simpa only [mul_comm] using hmul.symm)
    · rintro ⟨h₁, h₂⟩
      apply Prod.ext
      · exact (eq_div_iff hz₁).1 (congrArg (fun a : Circle => (a : ℂ)) h₁)
      · have hmul := (eq_div_iff hw₂).1 (congrArg (fun a : Circle => (a : ℂ)) h₂)
        exact (div_eq_iff hθ).2 (by simpa only [Circle.coe_pow, mul_comm] using hmul.symm)
  simpa only [he] using exists_unique_common_phase hpq u v hp

/-- The magnetic polynomial field is equivariant for weighted
rotations along a fiber. -/
theorem batemanSphereMagnetic_fiberRotate {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (θ : Circle) (z : ℂ × ℂ) :
    batemanSphereMagnetic p q (batemanFiberRotate p q θ z) =
      batemanFiberRotate p q θ (batemanSphereMagnetic p q z) := by
  let u := θ ^ q
  let v := (θ ^ p)⁻¹
  have huv : (u : ℂ) ^ p * (v : ℂ) ^ q = 1 := by
    simp only [u, v, Circle.coe_inv, Circle.coe_pow, inv_pow, ← pow_mul, mul_comm q p]
    exact mul_inv_cancel₀ (pow_ne_zero _ (Circle.coe_ne_zero θ))
  have h := batemanSphereMagnetic_phase hp hq u v huv z
  simpa only [batemanFiberRotate, u, v, Circle.coe_pow, Circle.coe_inv, div_eq_mul_inv,
    mul_comm ((θ : ℂ) ^ p)⁻¹] using h

/-- A trajectory with all points rotated by the same weighted phase
satisfies the same autonomous magnetic equation. -/
theorem hasDerivAt_batemanFiberRotate {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (θ : Circle) {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s) :
    HasDerivAt (fun t => batemanFiberRotate p q θ (w t))
      (batemanSphereMagnetic p q (batemanFiberRotate p q θ (w s))) s := by
  have h₁ : HasDerivAt (fun t => (w t).1) (batemanSphereMagnetic p q (w s)).1 s := hw.fst
  have h₂ : HasDerivAt (fun t => (w t).2) (batemanSphereMagnetic p q (w s)).2 s := hw.snd
  rw [batemanSphereMagnetic_fiberRotate hp hq]
  exact HasDerivAt.prodMk (h₁.const_mul ((θ : ℂ) ^ q)) (h₂.div_const ((θ : ℂ) ^ p))

/-- The sphere magnetic field is smooth as a real polynomial field. -/
theorem contDiff_batemanSphereMagnetic (p q : ℕ) :
    ContDiff ℝ ⊤ (batemanSphereMagnetic p q) := by
  have hconj : ContDiff ℝ ⊤ (conj : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold batemanSphereMagnetic batemanSphereElectric batemanSphereFactor
  fun_prop

/-- On a coprime strict intermediate real level, points with identical
quotient coordinates differ by a unique weighted phase rotation. -/
theorem existsUnique_batemanFiberRotate_of_quotient_eq
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    {c : ℝ} (h₀ : c ≠ 0) {z w : ℂ × ℂ}
    (hz : z ∈ poweredSphereRealLevel p q c) (hw : w ∈ poweredSphereRealLevel p q c)
    (he : batemanMagneticQuotient p q z = batemanMagneticQuotient p q w) :
    ∃! θ : Circle, batemanFiberRotate p q θ z = w := by
  have hgr := hz.2.trans hw.2.symm
  have hgi : (z.1 ^ p * z.2 ^ q).im = (w.1 ^ p * w.2 ^ q).im := by
    have h := congrArg Complex.im he
    simpa [batemanMagneticQuotient, Complex.add_im, Complex.mul_im] using h
  have hN₁ : Complex.normSq z.1 = Complex.normSq w.1 := by
    have h := congrArg Complex.re he
    simpa [batemanMagneticQuotient, Complex.add_re, Complex.mul_re] using h
  have hN₂ : Complex.normSq z.2 = Complex.normSq w.2 := by linarith [hz.1, hw.1]
  have hz₁ : z.1 ≠ 0 := by
    intro hn
    exact h₀ (by simpa [hn, zero_pow hp.ne'] using hz.2.symm)
  have hw₂ : w.2 ≠ 0 := by
    intro hn
    exact h₀ (by simpa [hn, zero_pow hq.ne'] using hw.2.symm)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hN₁ hN₂
  have hn₁ := (pow_left_inj₀ (norm_nonneg z.1) (norm_nonneg w.1)
    (by decide : (2 : ℕ) ≠ 0)).1 hN₁
  have hn₂ := (pow_left_inj₀ (norm_nonneg z.2) (norm_nonneg w.2)
    (by decide : (2 : ℕ) ≠ 0)).1 hN₂
  exact existsUnique_batemanFiberRotate hpq hz₁ hw₂ hn₁ hn₂ (Complex.ext hgr hgi)

/-- On each global normalized trajectory the time shift by a quotient
lap equals one fixed weighted phase rotation at every point. -/
theorem batemanMagneticQuotient_fiber_return
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) {w : ℝ → ℂ × ℂ}
    (hw : ∀ t, HasDerivAt w (batemanSphereMagnetic p q (w t)) t)
    (hlevel : ∀ t, w t ∈ poweredSphereRealLevel p q c) :
    let T := batemanMagneticQuotientPeriod hp hq h₀ hc
    ∃! θ : Circle, ∀ t, w (t + T) = batemanFiberRotate p q θ (w t) := by
  let T := batemanMagneticQuotientPeriod hp hq h₀ hc
  obtain ⟨_, hper, _⟩ := batemanMagneticQuotient_periodic hp hq h₀ hc hw hlevel
  have he : batemanMagneticQuotient p q (w 0) = batemanMagneticQuotient p q (w T) := by
    simpa only [zero_add] using (hper 0).symm
  obtain ⟨θ, hθ, huniq⟩ := existsUnique_batemanFiberRotate_of_quotient_eq hp hq hpq h₀
    (hlevel 0) (hlevel T) he
  let V := batemanSphereMagnetic p q
  let f := fun t : ℝ => w (t + T)
  let g := fun t : ℝ => batemanFiberRotate p q θ (w t)
  let D := Metric.closedBall (0 : ℂ × ℂ) 1
  obtain ⟨K, hK⟩ := (contDiff_batemanSphereMagnetic p q).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : ℂ × ℂ) 1) (isCompact_closedBall (0 : ℂ × ℂ) 1)
  have hD (t : ℝ) : w t ∈ D := by
    change dist (w t) 0 ≤ 1
    rw [dist_zero_right, Prod.norm_def, max_le_iff]
    have h := (hlevel t).1
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
    constructor
    · by_contra! hgt
      have ht := pow_lt_pow_left₀ hgt (by norm_num : 0 ≤ (1 : ℝ)) (by decide : (2 : ℕ) ≠ 0)
      nlinarith
    · by_contra! hgt
      have ht := pow_lt_pow_left₀ hgt (by norm_num : 0 ≤ (1 : ℝ)) (by decide : (2 : ℕ) ≠ 0)
      nlinarith
  have hRnorm (x : ℂ × ℂ) : ‖batemanFiberRotate p q θ x‖ = ‖x‖ := by
    simp [batemanFiberRotate, Prod.norm_def, norm_pow]
  have hF (t : ℝ) : HasDerivAt f (V (f t)) t ∧ f t ∈ D := by
    refine ⟨?_, hD (t + T)⟩
    have hshift : HasDerivAt (fun s : ℝ => s + T) 1 t := by
      simpa only [id_eq] using (hasDerivAt_id t).add_const T
    have hs := (hw (t + T)).scomp t hshift
    change HasDerivAt f ((1 : ℝ) • V (f t)) t at hs
    simpa only [one_smul] using hs
  have hG (t : ℝ) : HasDerivAt g (V (g t)) t ∧ g t ∈ D := by
    refine ⟨hasDerivAt_batemanFiberRotate hp hq θ (hw t), ?_⟩
    have ht := hD t
    change dist (w t) 0 ≤ 1 at ht
    change dist (batemanFiberRotate p q θ (w t)) 0 ≤ 1
    rwa [dist_zero_right, hRnorm, ← dist_zero_right]
  have hf₀ : f 0 = g 0 := by simpa only [f, g, zero_add] using hθ.symm
  have hfg : f = g :=
    ODE_solution_unique_univ (s := fun _ => D) (v := fun _ => V) (fun _ => hK) hF hG hf₀
  refine ⟨θ, congrFun hfg, ?_⟩
  intro u hu
  apply huniq
  simpa only [zero_add] using (hu 0).symm

/-- The identity phase fixes both coordinates. -/
theorem batemanFiberRotate_one (p q : ℕ) (z : ℂ × ℂ) :
    batemanFiberRotate p q 1 z = z := by
  simp [batemanFiberRotate]

/-- Composition of two fiber rotations is multiplication of their phases. -/
theorem batemanFiberRotate_mul (p q : ℕ) (θ φ : Circle) (z : ℂ × ℂ) :
    batemanFiberRotate p q (θ * φ) z =
      batemanFiberRotate p q θ (batemanFiberRotate p q φ z) := by
  apply Prod.ext
  · simp [batemanFiberRotate, mul_pow, mul_assoc]
  · simp [batemanFiberRotate, mul_pow, div_div, mul_comm]

/-- After an integer number of forward laps, the return phase is
the same power of the one-lap phase. -/
theorem batemanFiberRotate_laps (p q : ℕ) {T : ℝ} {θ : Circle}
    {w : ℝ → ℂ × ℂ} (h : ∀ t, w (t + T) = batemanFiberRotate p q θ (w t))
    (n : ℕ) (t : ℝ) :
    w (t + (n : ℝ) * T) = batemanFiberRotate p q (θ ^ n) (w t) := by
  induction n with
  | zero => simp [batemanFiberRotate_one]
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = t + (n : ℝ) * T + T by push_cast; ring,
      h, ih, ← batemanFiberRotate_mul, pow_succ']

/-- A finite-order return phase gives a periodic normalized trajectory. -/
theorem batemanFiberRotate_periodic_of_pow_eq_one (p q : ℕ) {T : ℝ} {θ : Circle}
    {w : ℝ → ℂ × ℂ} (h : ∀ t, w (t + T) = batemanFiberRotate p q θ (w t))
    {n : ℕ} (hn : θ ^ n = 1) :
    Function.Periodic w ((n : ℝ) * T) := by
  intro t
  rw [batemanFiberRotate_laps p q h n t, hn, batemanFiberRotate_one]

/-- The phase formula also holds for backward laps, with inverse rotation. -/
theorem batemanFiberRotate_laps_int (p q : ℕ) {T : ℝ} {θ : Circle}
    {w : ℝ → ℂ × ℂ} (h : ∀ t, w (t + T) = batemanFiberRotate p q θ (w t))
    (n : ℤ) (t : ℝ) :
    w (t + (n : ℝ) * T) = batemanFiberRotate p q (θ ^ n) (w t) := by
  cases n with
  | ofNat n =>
    change w (t + (((n : ℕ) : ℤ) : ℝ) * T) = batemanFiberRotate p q (θ ^ (n : ℤ)) (w t)
    simpa only [Int.cast_natCast, zpow_natCast] using batemanFiberRotate_laps p q h n t
  | negSucc n =>
    let m := n + 1
    have hm := batemanFiberRotate_laps p q h m (t - (m : ℝ) * T)
    rw [sub_add_cancel] at hm
    have htime : t + ((Int.negSucc n : ℤ) : ℝ) * T = t - (m : ℝ) * T := by
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, m]
      ring
    rw [htime, zpow_negSucc, hm, ← batemanFiberRotate_mul, inv_mul_cancel,
      batemanFiberRotate_one]

/-- An infinite-order phase has powers dense in the unit circle. -/
private theorem denseRange_batemanReturnPhase (θ : Circle)
    (hθ : ¬ ∃ n : ℕ, 0 < n ∧ θ ^ n = 1) :
    DenseRange (fun n : ℤ => θ ^ n) := by
  have hc₁ : (1 : ℝ) ≠ 0 := one_ne_zero
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let e := AddCircle.homeomorphCircle hc₁
  let a := e.symm θ
  have ha : AddCircle.toCircle a = θ := by
    rw [← AddCircle.homeomorphCircle_apply hc₁]
    exact e.apply_symm_apply θ
  have hOrder : addOrderOf a = 0 := by
    by_contra! h
    refine hθ ⟨addOrderOf a, Nat.pos_of_ne_zero h, ?_⟩
    have hb := congrArg AddCircle.toCircle (addOrderOf_nsmul_eq_zero a)
    rwa [AddCircle.toCircle_nsmul, ha, AddCircle.toCircle_zero] at hb
  have hd := (AddCircle.denseRange_zsmul_iff).2 hOrder
  have he := e.surjective.denseRange.comp hd e.continuous
  have hh (n : ℤ) : e (n • a) = θ ^ n := by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zsmul, ha]
  have heq : (e ∘ fun n : ℤ => n • a) = (fun n : ℤ => θ ^ n) := funext hh
  exact heq ▸ he

/-- For coprime powers, complete normalized magnetic trajectories on a
strict intermediate real level are periodic or have dense image in
the entire level. The two alternatives follow from the order of the
one-lap phase rotation. -/
theorem batemanSphereMagnetic_periodic_or_dense
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) {w : ℝ → ℂ × ℂ}
    (hw : ∀ t, HasDerivAt w (batemanSphereMagnetic p q (w t)) t)
    (hlevel : ∀ t, w t ∈ poweredSphereRealLevel p q c) :
    (∃ T : ℝ, 0 < T ∧ Function.Periodic w T) ∨
      closure (Set.range w) = poweredSphereRealLevel p q c := by
  let T := batemanMagneticQuotientPeriod hp hq h₀ hc
  obtain ⟨hT, _, hrange⟩ := batemanMagneticQuotient_periodic hp hq h₀ hc hw hlevel
  obtain ⟨θ, hret, _⟩ := batemanMagneticQuotient_fiber_return hp hq hpq h₀ hc hw hlevel
  by_cases hθ : ∃ n : ℕ, 0 < n ∧ θ ^ n = 1
  · obtain ⟨n, hn, hpw⟩ := hθ
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact Or.inl ⟨(n : ℝ) * T, mul_pos hnR hT, batemanFiberRotate_periodic_of_pow_eq_one p q hret hpw⟩
  · right
    have hClosed : IsClosed (poweredSphereRealLevel p q c) :=
      (isClosed_eq ((Complex.continuous_normSq.comp continuous_fst).add
        (Complex.continuous_normSq.comp continuous_snd)) continuous_const).inter
        (isClosed_eq (Complex.continuous_re.comp ((continuous_fst.pow p).mul (continuous_snd.pow q)))
          continuous_const)
    refine Set.Subset.antisymm (closure_minimal (Set.range_subset_iff.mpr hlevel) hClosed) ?_
    intro z hz
    have hm : batemanMagneticQuotient p q z ∈
        Set.range (fun t => batemanMagneticQuotient p q (w t)) := by
      rw [hrange, ← hz.2]
      exact batemanMagneticQuotient_mem_oval p q z hz.1
    obtain ⟨t, ht⟩ := hm
    obtain ⟨a, ha, _⟩ := existsUnique_batemanFiberRotate_of_quotient_eq hp hq hpq h₀
      (hlevel t) hz ht
    let f := fun b : Circle => batemanFiberRotate p q b (w t)
    have hf : Continuous f := by
      have hb : Continuous (fun b : Circle => (b : ℂ)) := continuous_subtype_val
      exact ((hb.pow q).mul_const _).prodMk
        (continuous_const.div (hb.pow p) (fun b => pow_ne_zero p (Circle.coe_ne_zero b)))
    have hza : f a ∈ closure (f '' Set.range (fun n : ℤ => θ ^ n)) :=
      mem_closure_image hf.continuousAt (denseRange_batemanReturnPhase θ hθ a)
    have hsub : f '' Set.range (fun n : ℤ => θ ^ n) ⊆ Set.range w := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨t + (n : ℝ) * T, batemanFiberRotate_laps_int p q hret n t⟩
    rw [show z = f a from ha.symm]
    exact closure_mono hsub hza

end Qatlib.Papers.KnotLight13.TorusFamily
