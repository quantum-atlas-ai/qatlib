/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false

/-! Supplement Lemma `lemma:gap` of arXiv:2503.20498v1 (threshold lemma behind
Corollary `corollary:gap`): if two `[0,1]`-valued random variables satisfy a
relative expectation gap `E[X1] ≥ (1+ε) E[X0]` and each is either zero or at
least `a_b`, then some threshold `t ∈ [a0, 1]` separates their upper tails:
`Pr[X1 > t+δ/2] ≥ (1+ε/4)(Pr[X0 > t] + (ε/8) E[X1])`. The paper proves this
by integration by parts on the CDFs (layer cake), a dichotomy on where the
excess mass sits, and a dyadic grid argument. We formalize the same proof
using the Lebesgue layer-cake identity; the witness `t` is produced as a real
number (the point `a0` itself or a grid point `a0 + (j+1)δ/2`), while the
paper additionally asks it to be rational, which holds in the application
where `a0` and `δ` are rational. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Qatlib.Papers.RandCertLiu25.MainResults.GapLemma

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Strict upper-tail probability of a real random variable. -/
def surv (X : Ω → ℝ) (t : ℝ) : ℝ := (μ {ω | t < X ω}).toReal

/-- Weak upper-tail probability of a real random variable. -/
def survBar (X : Ω → ℝ) (t : ℝ) : ℝ := (μ {ω | t ≤ X ω}).toReal

variable {μ}

/-- The strict survival function is antitone in the threshold. -/
theorem surv_antitone [IsProbabilityMeasure μ] (X : Ω → ℝ) : Antitone (surv μ X) := by
  intro s t hst
  have hsub : {ω : Ω | t < X ω} ⊆ {ω : Ω | s < X ω} :=
    fun ω hω => lt_of_le_of_lt hst hω
  show (μ {ω : Ω | t < X ω}).toReal ≤ (μ {ω : Ω | s < X ω}).toReal
  have hne : μ {ω : Ω | t < X ω} ≠ ⊤ := by
    have h1 : μ {ω : Ω | t < X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [measure_univ] at h1
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hne' : μ {ω : Ω | s < X ω} ≠ ⊤ := by
    have h1 : μ {ω : Ω | s < X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [measure_univ] at h1
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  exact (ENNReal.toReal_le_toReal hne hne').mpr (measure_mono hsub)

/-- The weak survival function is antitone in the threshold. -/
theorem survBar_antitone [IsProbabilityMeasure μ] (X : Ω → ℝ) : Antitone (survBar μ X) := by
  intro s t hst
  have hsub : {ω : Ω | t ≤ X ω} ⊆ {ω : Ω | s ≤ X ω} :=
    fun ω hω => le_trans hst hω
  show (μ {ω : Ω | t ≤ X ω}).toReal ≤ (μ {ω : Ω | s ≤ X ω}).toReal
  have hne : μ {ω : Ω | t ≤ X ω} ≠ ⊤ := by
    have h1 : μ {ω : Ω | t ≤ X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [measure_univ] at h1
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  have hne' : μ {ω : Ω | s ≤ X ω} ≠ ⊤ := by
    have h1 : μ {ω : Ω | s ≤ X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [measure_univ] at h1
    exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
  exact (ENNReal.toReal_le_toReal hne hne').mpr (measure_mono hsub)

/-- The strict and weak survival functions differ only in that the latter
also counts the atom at the threshold; both are nonnegative. -/
theorem surv_nonneg (X : Ω → ℝ) (t : ℝ) : 0 ≤ surv μ X t := ENNReal.toReal_nonneg

/-- Layer-cake identity for a `[0,1]`-valued random variable on a probability
space: the expectation equals the integral of its strict survival function
over `[0,1]`. This replaces the paper's integration-by-parts identity. -/
theorem integral_eq_surv [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    (hr : ∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) :
    ∫ ω, X ω ∂μ = ∫ t in Set.Icc (0:ℝ) 1, surv μ X t := by
  classical
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
  have hset : MeasurableSet {q : ℝ × Ω | q.1 < X q.2} :=
    measurableSet_lt measurable_fst (hm.comp measurable_snd)
  have hgint : Integrable (fun q => Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) q)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod μ) :=
    (integrable_const (1:ℝ)).indicator hset
  have hω : ∀ t : ℝ, (∫ ω, Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω) ∂μ)
      = surv μ X t := by
    intro t
    have hA : MeasurableSet {ω : Ω | t < X ω} := hm measurableSet_Ioi
    have hpt : ∀ ω : Ω, Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω)
        = Set.indicator {ω : Ω | t < X ω} (fun _ => (1:ℝ)) ω := by
      intro ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_indicator hA,
      setIntegral_const]
    simp [surv, Measure.real_def]
  have hωt : ∀ ω : Ω, (∫ t in Set.Icc (0:ℝ) 1,
        Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω) ∂volume) = X ω := by
    intro ω
    have h0 : (0:ℝ) ≤ X ω := (hr ω).1
    have h1 : X ω ≤ 1 := (hr ω).2
    have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1, Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω)
        = Set.indicator (Set.Iio (X ω)) (fun _ => (1:ℝ)) t := by
      intro t _
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio]
    have hIio : MeasurableSet (Set.Iio (X ω)) := measurableSet_Iio
    have hseteq : Set.Icc (0:ℝ) 1 ∩ Set.Iio (X ω) = Set.Ico (0:ℝ) (X ω) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h0t, _⟩, hxt⟩
        exact ⟨h0t, hxt⟩
      · rintro ⟨h0t, hxt⟩
        exact ⟨⟨h0t, le_of_lt (lt_of_lt_of_le hxt h1)⟩, hxt⟩
    rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => hpt t ht), setIntegral_indicator hIio,
      hseteq, setIntegral_const]
    have hvol : volume.real (Set.Ico (0:ℝ) (X ω)) = X ω := by
      show (volume (Set.Ico (0:ℝ) (X ω))).toReal = X ω
      rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol]
    simp
  have hkey := integral_prod (μ := volume.restrict (Set.Icc (0:ℝ) 1)) (ν := μ)
    (fun q => Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) q) hgint
  have hkey' := integral_prod_symm (μ := volume.restrict (Set.Icc (0:ℝ) 1)) (ν := μ)
    (fun q => Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) q) hgint
  have hrhs : (∫ t, ∫ ω, Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω) ∂μ
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))) = ∫ t in Set.Icc (0:ℝ) 1, surv μ X t :=
    integral_congr_ae (Filter.Eventually.of_forall hω)
  have hlhs : (∫ ω, ∫ t, Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω)
      ∂(volume.restrict (Set.Icc (0:ℝ) 1)) ∂μ) = ∫ ω, X ω ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    simp only []
    have hrest : (∫ t, Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω)
        ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
        = ∫ t in Set.Icc (0:ℝ) 1,
            Set.indicator {q : ℝ × Ω | q.1 < X q.2} (fun _ => (1:ℝ)) (t, ω) ∂volume := rfl
    rw [hrest, hωt ω]
  rw [← hrhs, ← hkey, hkey', hlhs]

section Decomposition

/-- On a probability space the survival probabilities are at most one. -/
theorem surv_le_one [IsProbabilityMeasure μ] (X : Ω → ℝ) (t : ℝ) : surv μ X t ≤ 1 := by
  have hle : μ {ω : Ω | t < X ω} ≤ 1 := by
    have h1 : μ {ω : Ω | t < X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rwa [measure_univ] at h1
  exact ENNReal.toReal_le_coe_of_le_coe hle

/-- Bounded measurable integrand on a measurable set of finite volume. -/
theorem integrableOn_surv [IsProbabilityMeasure μ] (X : Ω → ℝ) (s : Set ℝ)
    (_hs : MeasurableSet s) (hvol : volume s ≠ ⊤) :
    IntegrableOn (surv μ X) s volume := by
  haveI hfin : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hvol
  have hmeas : Measurable (surv μ X) := (surv_antitone (μ := μ) X).measurable
  refine Integrable.mono (integrable_const (1:ℝ)) hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have h0 : 0 ≤ surv (μ := μ) X t := surv_nonneg (μ := μ) X t
  rw [Real.norm_eq_abs, abs_of_nonneg h0, norm_one]
  exact surv_le_one (μ := μ) X t

/-- Cell-sum identity: summing the integrals of a function over consecutive
half-open cells of length `d` reconstructs the integral over the union
interval. -/
theorem sum_setIntegral_Ioc (f : ℝ → ℝ)
    (hint : ∀ u v : ℝ, IntegrableOn f (Set.Ioc u v) volume) (u d : ℝ) (hd0 : 0 ≤ d) :
    ∀ n : ℕ, (∑ j ∈ Finset.range n, ∫ t in Set.Ioc (u + j*d) (u + (j+1)*d), f t ∂volume)
      = ∫ t in Set.Ioc u (u + n*d), f t ∂volume := by
  intro n
  induction n with
  | zero =>
      show (0:ℝ) = ∫ t in Set.Ioc u (u + ((0:ℕ):ℝ)*d), f t ∂volume
      rw [Nat.cast_zero, zero_mul, add_zero, Set.Ioc_self, setIntegral_empty]
  | succ n ih =>
      have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hnd : (0:ℝ) ≤ (n:ℝ)*d := mul_nonneg hnn hd0
      have hu : u + (n:ℝ)*d ≤ u + ((n:ℝ)+1)*d := by linarith
      have hd : Disjoint (Set.Ioc u (u + (n:ℝ)*d)) (Set.Ioc (u + (n:ℝ)*d) (u + ((n:ℝ)+1)*d)) :=
        Set.disjoint_left.mpr (fun x hx => by
          have hA := Set.mem_Ioc.mp hx
          intro h2
          have hB := Set.mem_Ioc.mp h2
          linarith [hA.1, hA.2, hB.1, hB.2])
      have hunion : Set.Ioc u (u + ((n:ℝ)+1)*d)
          = Set.Ioc u (u + (n:ℝ)*d) ∪ Set.Ioc (u + (n:ℝ)*d) (u + ((n:ℝ)+1)*d) :=
        (Set.Ioc_union_Ioc_eq_Ioc (by linarith) hu).symm
      rw [Nat.cast_succ, Finset.sum_range_succ, ih, hunion,
        setIntegral_union hd measurableSet_Ioc (hint _ _) (hint _ _)]

/-- An antitone integrand over a cell is bounded above by its value at the
left endpoint times the cell length. -/
theorem cell_le (s : ℝ → ℝ) (hs : Antitone s) (u v : ℝ) (huv : u ≤ v)
    (hint : IntegrableOn s (Set.Ioc u v) volume) :
    (∫ t in Set.Ioc u v, s t ∂volume) ≤ (v - u) * s u := by
  have hc : IntegrableOn (fun _ => s u) (Set.Ioc u v) volume := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc u v)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact integrable_const _
  have hv : volume.real (Set.Ioc u v) = v - u := by
    show (volume (Set.Ioc u v)).toReal = v - u
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  calc (∫ t in Set.Ioc u v, s t ∂volume)
      ≤ (∫ t in Set.Ioc u v, s u ∂volume) := by
          exact setIntegral_mono_on hint hc measurableSet_Ioc (fun t ht => hs ht.1.le)
    _ = (v - u) * s u := by rw [setIntegral_const, hv, smul_eq_mul]

/-- An antitone integrand plus a nonnegative constant over a cell is bounded
below by its value at the right endpoint plus the constant, times the cell
length. -/
theorem cell_ge (s : ℝ → ℝ) (hs : Antitone s) (c : ℝ) (u v : ℝ) (huv : u ≤ v)
    (hint : IntegrableOn (fun t => s t + c) (Set.Ioc u v) volume) :
    (v - u) * (s v + c) ≤ ∫ t in Set.Ioc u v, (s t + c) ∂volume := by
  have hc : IntegrableOn (fun _ => s v + c) (Set.Ioc u v) volume := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc u v)) :=
      isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact integrable_const _
  have hv : volume.real (Set.Ioc u v) = v - u := by
    show (volume (Set.Ioc u v)).toReal = v - u
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  calc (v - u) * (s v + c)
      = (∫ t in Set.Ioc u v, (s v + c) ∂volume) := by
          rw [setIntegral_const, hv, smul_eq_mul]
    _ ≤ ∫ t in Set.Ioc u v, (s t + c) ∂volume := by
          refine setIntegral_mono_on hc hint measurableSet_Ioc (fun t ht => ?_)
          have hst : s v ≤ s t := hs ht.2
          simp only [Set.mem_Ioc] at ht
          linarith

/-- The expectation decomposes as the atom mass `a·Pr[X ≥ a]` (using the
support condition `0 < X → a ≤ X`) plus the tail integral of the strict
survival function over `(a, 1]`. -/
theorem integral_eq_decomp [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    (hr : ∀ ω, X ω ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hsupp : ∀ ω, 0 < X ω → a ≤ X ω) :
    ∫ ω, X ω ∂μ = a * survBar μ X a + ∫ t in Set.Ioc a 1, surv μ X t ∂volume := by
  classical
  rw [integral_eq_surv (μ := μ) hm hr]
  have hsplit : Set.Icc (0:ℝ) 1 = Set.Ico (0:ℝ) a ∪ (Set.Ioc a 1 ∪ ({a} : Set ℝ)) := by
    ext t
    simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ico, Set.mem_Ioc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, h1t⟩
      rcases lt_trichotomy t a with h | h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl ⟨h, h1t⟩)
    · rintro (⟨h0, hta⟩ | ⟨hta, h1t⟩ | h)
      · exact ⟨h0, by have : a ≤ 1 := ha1; linarith⟩
      · exact ⟨by have : 0 < a := ha0; linarith, h1t⟩
      · exact ⟨by rw [h]; linarith, by rw [h]; exact ha1⟩
  have hi1 : IntegrableOn (surv μ X) (Set.Ico (0:ℝ) a) volume :=
    integrableOn_surv X _ measurableSet_Ico
      (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hi2 : IntegrableOn (surv μ X) (Set.Ioc a 1) volume :=
    integrableOn_surv X _ measurableSet_Ioc
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hi3 : IntegrableOn (surv μ X) ({a} : Set ℝ) volume :=
    integrableOn_surv X ({a} : Set ℝ) (measurableSet_singleton a)
      (by rw [Real.volume_singleton]; simp)
  have hd1 : Disjoint (Set.Ico (0:ℝ) a) (Set.Ioc a 1 ∪ ({a} : Set ℝ)) :=
    Set.disjoint_left.mpr (fun x hx => by
      rcases Set.mem_Ico.mp hx with ⟨-, hta⟩
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_singleton_iff]
      rintro (⟨hta', -⟩ | hxa)
      · linarith
      · linarith)
  have hd2 : Disjoint (Set.Ioc a 1) ({a} : Set ℝ) :=
    Set.disjoint_left.mpr (fun x hx => by
      rcases Set.mem_Ioc.mp hx with ⟨hta, -⟩
      simp only [Set.mem_singleton_iff]
      rintro rfl
      linarith)
  have hco : (∫ t in Set.Ico (0:ℝ) a, surv μ X t ∂volume) = a * survBar μ X a := by
    have hcongr : ∀ t ∈ Set.Ico (0:ℝ) a, surv μ X t = survBar μ X a := by
      rintro t ht
      have hta : t < a := ht.2
      have h0t : (0:ℝ) ≤ t := ht.1
      have hset : {ω : Ω | t < X ω} = {ω : Ω | a ≤ X ω} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h
          rcases lt_or_ge (X ω) a with hxa | hxa
          · exact absurd (hsupp ω (by linarith)) (by linarith)
          · exact hxa
        · intro h
          linarith
      simp [surv, survBar, hset]
    have h1 : (∫ t in Set.Ico (0:ℝ) a, surv μ X t ∂volume)
        = volume.real (Set.Ico (0:ℝ) a) • survBar μ X a := by
      rw [setIntegral_congr_fun measurableSet_Ico hcongr, setIntegral_const]
    have hv : volume.real (Set.Ico (0:ℝ) a) = a := by
      show (volume (Set.Ico (0:ℝ) a)).toReal = a
      rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [h1, hv, smul_eq_mul]
  have hpt : (∫ t in ({a} : Set ℝ), surv μ X t ∂volume) = 0 := by
    have hc : ∀ t ∈ ({a} : Set ℝ), surv μ X t = surv μ X a := by
      rintro t rfl
      rfl
    have h1 : (∫ t in ({a} : Set ℝ), surv μ X t ∂volume)
        = volume.real ({a} : Set ℝ) • surv μ X a := by
      rw [setIntegral_congr_fun (measurableSet_singleton a) hc, setIntegral_const]
    have hv : volume.real ({a} : Set ℝ) = 0 := by
      show (volume ({a} : Set ℝ)).toReal = 0
      rw [Real.volume_singleton]
      simp
    rw [h1, hv]
    simp
  rw [hsplit,
    setIntegral_union hd1 (MeasurableSet.union measurableSet_Ioc
      (measurableSet_singleton a)) hi1 (integrableOn_union.mpr ⟨hi2, hi3⟩),
    setIntegral_union hd2 (measurableSet_singleton a) hi2 hi3, hco, hpt]
  ring

end Decomposition

section Main

/-- Case A of the dichotomy in `exists_threshold_gap`: when the mass at the
base point `a0` already dominates (`hsA`), the threshold `t = a0` itself
witnesses the tail gap, using only monotonicity of the survival functions. -/
theorem caseA_conclusion [IsProbabilityMeasure μ] (ε δ a0 : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (ha0 : 0 < a0)
    (ha1le : a0 + δ ≤ (1 + ε/8) * a0)
    {X0 X1 : Ω → ℝ} {c : ℝ} (hcnn : 0 ≤ c)
    (hSleSB0 : surv μ X0 a0 ≤ survBar μ X0 a0)
    (hsA : (1 + ε/2) * a0 * (survBar μ X0 a0 + c) ≤ (a0 + δ) * survBar μ X1 (a0 + δ)) :
    surv μ X1 (a0 + δ/2) ≥ (1 + ε/4) * (surv μ X0 a0 + c) := by
  have hf41 : (0:ℝ) ≤ 1 + ε/4 := by linarith
  have hfac : (1 + ε/4) * (1 + ε/8) ≤ 1 + ε/2 := by nlinarith [hε, hε1]
  have hmono : survBar (μ := μ) X1 (a0 + δ) ≤ surv (μ := μ) X1 (a0 + δ/2) := by
    have hsub : {ω : Ω | a0 + δ ≤ X1 ω} ⊆ {ω : Ω | a0 + δ/2 < X1 ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      linarith
    have hne1 : μ {ω : Ω | a0 + δ ≤ X1 ω} ≠ ⊤ := by
      have h1 : μ {ω : Ω | a0 + δ ≤ X1 ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rw [measure_univ] at h1
      exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
    have hne2 : μ {ω : Ω | a0 + δ/2 < X1 ω} ≠ ⊤ := by
      have h1 : μ {ω : Ω | a0 + δ/2 < X1 ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rw [measure_univ] at h1
      exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.one_lt_top)
    show (μ {ω : Ω | a0 + δ ≤ X1 ω}).toReal ≤ (μ {ω : Ω | a0 + δ/2 < X1 ω}).toReal
    exact (ENNReal.toReal_le_toReal hne1 hne2).mpr (measure_mono hsub)
  have hkey1 : (1 + ε/4) * (a0 + δ) ≤ (1 + ε/2) * a0 := by
    have hA : (1 + ε/4) * (a0 + δ) ≤ (1 + ε/4) * ((1 + ε/8) * a0) :=
      mul_le_mul_of_nonneg_left ha1le hf41
    have hB : (1 + ε/4) * ((1 + ε/8) * a0) ≤ (1 + ε/2) * a0 := by
      nlinarith [hfac, ha0, hε, hε1]
    linarith
  have hafac2 : (0:ℝ) < a0 + δ := by linarith
  have hP0nn : (0:ℝ) ≤ survBar (μ := μ) X0 a0 := ENNReal.toReal_nonneg
  have hPnn : (0:ℝ) ≤ survBar (μ := μ) X0 a0 + c := by linarith [hP0nn, hcnn]
  have hall : (1 + ε/4) * (survBar (μ := μ) X0 a0 + c) ≤ survBar (μ := μ) X1 (a0 + δ) := by
    have hstep : (1 + ε/4) * (a0 + δ) * (survBar (μ := μ) X0 a0 + c)
        ≤ (a0 + δ) * survBar (μ := μ) X1 (a0 + δ) := by
      have h1 : (1 + ε/4) * (a0 + δ) * (survBar (μ := μ) X0 a0 + c)
          ≤ (1 + ε/2) * a0 * (survBar (μ := μ) X0 a0 + c) :=
        mul_le_mul_of_nonneg_right hkey1 hPnn
      exact le_trans h1 hsA
    by_contra hlt
    push_neg at hlt
    have hmul : (a0 + δ) * survBar (μ := μ) X1 (a0 + δ)
        < (a0 + δ) * ((1 + ε/4) * (survBar (μ := μ) X0 a0 + c)) :=
      mul_lt_mul_of_pos_left hlt hafac2
    have hexp : (a0 + δ) * ((1 + ε/4) * (survBar (μ := μ) X0 a0 + c))
        = (1 + ε/4) * (a0 + δ) * (survBar (μ := μ) X0 a0 + c) := by ring
    rw [hexp] at hmul
    linarith [hmul, hstep]
  have hsumle : surv (μ := μ) X0 a0 + c ≤ survBar (μ := μ) X0 a0 + c := by linarith [hSleSB0]
  have hS : (1 + ε/4) * (surv (μ := μ) X0 a0 + c)
      ≤ (1 + ε/4) * (survBar (μ := μ) X0 a0 + c) :=
    mul_le_mul_of_nonneg_left hsumle hf41
  linarith [hS, hall, hmono]

set_option maxHeartbeats 1000000 in
/-- Supplement Lemma `lemma:gap` (main threshold lemma): under the relative
expectation gap `E[X1] ≥ (1+ε)E[X0]` and the support conditions, some real
threshold `t ∈ [a0, 1]` separates the upper tails with a factor `1+ε/4` and
an additive `ε/8 · E[X1]` term. The paper states the same conclusion with a
rational `t`; here `t` is `a0` itself (case A) or the grid point
`a0 + (j+1)δ/2` (case B), which is rational whenever `a0` and `δ` are. -/
theorem exists_threshold_gap [IsProbabilityMeasure μ]
    (ε δ a0 : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (ha0 : 0 < a0) (ha01 : a0 ≤ 1)
    (ha1le : a0 + δ ≤ (1 + ε/8) * a0)
    {X0 X1 : Ω → ℝ} (hm0 : Measurable X0) (hm1 : Measurable X1)
    (hr0 : ∀ ω, X0 ω ∈ Set.Icc (0:ℝ) 1) (hr1 : ∀ ω, X1 ω ∈ Set.Icc (0:ℝ) 1)
    (hs0 : ∀ ω, 0 < X0 ω → a0 ≤ X0 ω) (hs1 : ∀ ω, 0 < X1 ω → a0 + δ ≤ X1 ω)
    (hE : (1 + ε) * (∫ ω, X0 ω ∂μ) ≤ ∫ ω, X1 ω ∂μ) :
    ∃ t : ℝ, a0 ≤ t ∧ t ≤ 1 ∧
      surv μ X1 (t + δ/2) ≥ (1 + ε/4) * (surv μ X0 t + ε/8 * (∫ ω, X1 ω ∂μ)) := by
  classical
  set E0 := ∫ ω, X0 ω ∂μ with hE0d
  set E1 := ∫ ω, X1 ω ∂μ with hE1d
  have hE0nn : 0 ≤ E0 := integral_nonneg (fun ω => (hr0 ω).1)
  have hE1nn : 0 ≤ E1 := integral_nonneg (fun ω => (hr1 ω).1)
  set c := ε/8 * E1 with hcd
  have hcnn : 0 ≤ c := by nlinarith
  have hfac : (1 + ε/4) * (1 + ε/8) ≤ 1 + ε/2 := by nlinarith
  -- the factor lemma, uses ε ≤ 1
  have hfac2 : 0 < a0 + δ := by linarith
  have hSBnn : ∀ X : Ω → ℝ, 0 ≤ survBar (μ := μ) X (a0 + δ) := fun X => ENNReal.toReal_nonneg
  have hSBnn0 : ∀ X : Ω → ℝ, 0 ≤ survBar (μ := μ) X a0 := fun X => ENNReal.toReal_nonneg
  have hSnn : ∀ (X : Ω → ℝ) (t : ℝ), 0 ≤ surv (μ := μ) X t := fun X _ => ENNReal.toReal_nonneg
  have hSleSB : ∀ (X : Ω → ℝ) (t : ℝ), surv (μ := μ) X t ≤ survBar (μ := μ) X t := by
    intro X t
    have hsub : {ω : Ω | t < X ω} ⊆ {ω : Ω | t ≤ X ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact le_of_lt hω
    exact ENNReal.toReal_le_toReal
      (ne_of_lt (lt_of_le_of_lt (by
        have h1 : μ {ω : Ω | t < X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        rwa [measure_univ] at h1) ENNReal.one_lt_top))
      (ne_of_lt (lt_of_le_of_lt (by
        have h1 : μ {ω : Ω | t ≤ X ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        rwa [measure_univ] at h1) ENNReal.one_lt_top)) |>.mpr (measure_mono hsub)
  -- Step 1: strengthen the expectation gap
  have hnn1 : (0:ℝ) ≤ 1 - ε/4 := by nlinarith
  have hstep1 : E1 ≥ (1 - ε/4)*(1 + ε)*E0 + (ε/4)*E1 := by
    have h1 : (1 - ε/4)*E1 ≥ (1 - ε/4)*((1+ε)*E0) :=
      mul_le_mul_of_nonneg_left hE hnn1
    have e1 : (1 - ε/4)*E1 = E1 - (ε/4)*E1 := by ring
    rw [e1] at h1
    linarith
  have hchain : E1 ≥ (1 + ε/2)*(E0 + c) := by
    have key1 : (1 - ε/4)*(1 + ε)*E0 ≥ (1 + ε/2)*E0 := by
      have hR : (1 - ε/4)*(1 + ε) ≥ 1 + ε/2 := by nlinarith
      nlinarith [hR, hE0nn]
    have key2 : (ε/4)*E1 ≥ (1 + ε/2)*(ε/8*E1) := by
      have e4 : (1 + ε/2)*(ε/8*E1) = (ε/8)*E1 + (ε*ε/16)*E1 := by ring
      rw [e4]
      nlinarith [hE1nn, hε1]
    have e3 : (1 + ε/2)*(E0 + c) = (1 + ε/2)*E0 + (1 + ε/2)*c := by ring
    have e5 : c = ε/8*E1 := hcd
    rw [e3, e5]
    nlinarith [hstep1, key1, key2, hε, hE0nn]
  -- Step 2: case split on whether the upper support point reaches 1
  by_cases ha11 : a0 + δ ≤ 1
  · -- main branch
    have dec0 := integral_eq_decomp (μ := μ) hm0 hr0 ha0 ha01 hs0
    have dec1 := integral_eq_decomp (μ := μ) hm1 hr1 hfac2 ha11 hs1
    rw [← hE0d] at dec0
    rw [← hE1d] at dec1
    -- integrability on cells
    have hint1 : ∀ u v : ℝ, IntegrableOn (surv (μ := μ) X1) (Set.Ioc u v) volume :=
      fun u v => integrableOn_surv X1 _ measurableSet_Ioc
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hint0 : ∀ u v : ℝ, IntegrableOn (surv (μ := μ) X0) (Set.Ioc u v) volume :=
      fun u v => integrableOn_surv X0 _ measurableSet_Ioc
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hint2 : ∀ u v : ℝ, IntegrableOn (fun t => surv (μ := μ) X0 t + c) (Set.Ioc u v) volume :=
      fun u v => (hint0 u v).add (by
        haveI : IsFiniteMeasure (volume.restrict (Set.Ioc u v)) :=
          isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        exact integrable_const c)
    -- nonnegativity of tail integrals
    have I0nn : 0 ≤ ∫ t in Set.Ioc a0 1, surv (μ := μ) X0 t ∂volume := by
      refine setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun t => hSnn X0 t))
    have I1nn : 0 ≤ ∫ t in Set.Ioc (a0+δ) 1, surv (μ := μ) X1 t ∂volume := by
      refine setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun t => hSnn X1 t))
    -- light budget: E0 + c ≥ a0*(P̄0 + c)
    have hbud0 : a0*(survBar (μ := μ) X0 a0 + c) ≤ E0 + c := by
      nlinarith [dec0, I0nn, ha01, hSBnn0 X0, hcnn]
    -- the ceiling grid
    have hMnn : 0 ≤ 2*(1 - a0)/δ := div_nonneg (by linarith) (le_of_lt hδ)
    have hMge : 2*(1 - a0)/δ ≤ ((Nat.ceil (2*(1 - a0)/δ)):ℝ) := Nat.le_ceil _
    have hMlt : ((Nat.ceil (2*(1 - a0)/δ)):ℝ) < 2*(1 - a0)/δ + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one hMnn
    rcases le_or_gt 3 (Nat.ceil (2*(1 - a0)/δ)) with hM3 | hM3
    · -- grid branch
      obtain ⟨M, hMge, hMlt, hM3⟩ : ∃ M : ℕ, 2*(1-a0)/δ ≤ ((M:ℝ))
          ∧ ((M:ℝ)) < 2*(1-a0)/δ + 1 ∧ 3 ≤ M :=
        ⟨Nat.ceil (2*(1-a0)/δ), Nat.le_ceil _, by exact_mod_cast Nat.ceil_lt_add_one hMnn, hM3⟩
      have hd : (0:ℝ) < δ/2 := by linarith
      have huvt : (0:ℝ) ≤ δ/2 := le_of_lt hd
      have hdne' : δ ≠ 0 := ne_of_gt hδ
      have hdne2 : δ/2 ≠ 0 := by linarith
      have h2eq : 2*(1-a0)/δ = (1-a0)/(δ/2) := by field_simp
      have hdfield : (1-a0)/(δ/2) * (δ/2) = 1-a0 := by field_simp
      rw [h2eq] at hMge hMlt
      have hαM1 : (1:ℝ) ≤ a0 + (M:ℝ)*(δ/2) := by
        have h1 : (1-a0)/(δ/2) * (δ/2) ≤ (M:ℝ)*(δ/2) :=
          mul_le_mul_of_nonneg_right hMge huvt
        rw [hdfield] at h1
        linarith
      have hcast2 : ((M-2:ℕ):ℝ) = (M:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      have hM2nn : (0:ℝ) ≤ ((M-2:ℕ):ℝ)*(δ/2) := mul_nonneg (Nat.cast_nonneg _) huvt
      have hαM2 : a0 + ((M-2:ℕ):ℝ)*(δ/2) ≤ 1 := by
        have h1 : (M:ℝ)*(δ/2) < (1-a0) + δ/2 := by nlinarith [hMlt, hd, hdfield]
        have hgoal : a0 + ((M-2:ℕ):ℝ)*(δ/2) = a0 + (M:ℝ)*(δ/2) - δ := by
          rw [hcast2]; ring
        rw [hgoal]
        linarith
      obtain ⟨I1, hI1d⟩ : ∃ x : ℝ, x = ∫ t in Set.Ioc (a0+δ) 1, surv (μ := μ) X1 t ∂volume :=
        ⟨_, rfl⟩
      rw [← hI1d] at dec1 I1nn
      obtain ⟨I0, hI0d⟩ : ∃ x : ℝ, x = ∫ t in Set.Ioc a0 1, surv (μ := μ) X0 t ∂volume :=
        ⟨_, rfl⟩
      rw [← hI0d] at dec0 I0nn
      obtain ⟨SG, hSGd⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.range (M-2), ∫ s in Set.Ioc
          ((a0+δ) + (k:ℝ)*(δ/2)) ((a0+δ) + ((k+1:ℕ):ℝ)*(δ/2)), surv (μ := μ) X1 s ∂volume :=
        ⟨_, rfl⟩
      obtain ⟨SH, hSHd⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.range (M-2), ∫ s in Set.Ioc
          (a0 + (k:ℝ)*(δ/2)) (a0 + ((k+1:ℕ):ℝ)*(δ/2)), (fun s => surv (μ := μ) X0 s + c) s ∂volume :=
        ⟨_, rfl⟩
      have hGsum : SG = (∫ t in Set.Ioc (a0+δ) ((a0+δ) + ((M-2:ℕ):ℝ)*(δ/2)),
          surv (μ := μ) X1 t ∂volume) := by
        rw [hSGd]
        simp only [Nat.cast_succ]
        exact sum_setIntegral_Ioc (surv (μ := μ) X1) hint1 (a0+δ) (δ/2) huvt (M-2)
      have hGend : (a0+δ) + ((M-2:ℕ):ℝ)*(δ/2) = a0 + (M:ℝ)*(δ/2) := by
        rw [hcast2]; ring
      have hdisj1 : Disjoint (Set.Ioc (a0+δ) 1) (Set.Ioc 1 (a0 + (M:ℝ)*(δ/2))) :=
        Set.disjoint_left.mpr (fun x hx => by
          have hA := Set.mem_Ioc.mp hx
          intro h2
          have hB := Set.mem_Ioc.mp h2
          linarith [hA.1, hA.2, hB.1, hB.2])
      have hI1leSG : I1 ≤ SG := by
        rw [hGsum, hGend]
        have hsplit : Set.Ioc (a0+δ) (a0 + (M:ℝ)*(δ/2))
            = Set.Ioc (a0+δ) 1 ∪ Set.Ioc 1 (a0 + (M:ℝ)*(δ/2)) :=
          (Set.Ioc_union_Ioc_eq_Ioc ha11 hαM1).symm
        rw [hsplit, setIntegral_union hdisj1 measurableSet_Ioc (hint1 _ _) (hint1 _ _)]
        have h2 : (0:ℝ) ≤ ∫ t in Set.Ioc 1 (a0 + (M:ℝ)*(δ/2)), surv (μ := μ) X1 t ∂volume :=
          setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun t => hSnn X1 t))
        linarith [hI1d, h2]
      have hHsum : SH = (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)),
          (fun t => surv (μ := μ) X0 t + c) t ∂volume) := by
        rw [hSHd]
        simp only [Nat.cast_succ]
        exact sum_setIntegral_Ioc (fun t => surv (μ := μ) X0 t + c) hint2 a0 (δ/2) huvt (M-2)
      have hconstA : IntegrableOn (fun _ => (c:ℝ))
          (Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2))) volume := by
        haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)))) :=
          isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        exact integrable_const c
      have hA1 : (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)),
              (fun t => surv (μ := μ) X0 t + c) t ∂volume)
          = (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)), surv (μ := μ) X0 t ∂volume)
            + (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)), (c:ℝ) ∂volume) :=
        integral_add (hint0 _ _) hconstA
      have hcvolA : (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)), (c:ℝ) ∂volume)
          = c * ((M-2:ℕ):ℝ)*(δ/2) := by
        rw [setIntegral_const]
        have hv : volume.real (Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2))) = ((M-2:ℕ):ℝ)*(δ/2) := by
          show (volume (Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)))).toReal = ((M-2:ℕ):ℝ)*(δ/2)
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hM2nn])]
          ring
        rw [hv, smul_eq_mul]
        ring
      have hM0le : a0 ≤ a0 + ((M-2:ℕ):ℝ)*(δ/2) := by linarith [hM2nn]
      have hdisj0 : Disjoint (Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)))
          (Set.Ioc (a0 + ((M-2:ℕ):ℝ)*(δ/2)) 1) :=
        Set.disjoint_left.mpr (fun x hx => by
          have hA := Set.mem_Ioc.mp hx
          intro h2
          have hB := Set.mem_Ioc.mp h2
          linarith [hA.1, hA.2, hB.1, hB.2])
      have hI0split : I0 = (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)),
            surv (μ := μ) X0 t ∂volume)
          + (∫ t in Set.Ioc (a0 + ((M-2:ℕ):ℝ)*(δ/2)) 1, surv (μ := μ) X0 t ∂volume) := by
        rw [hI0d]
        have hsplit0 : Set.Ioc a0 1
            = Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)) ∪ Set.Ioc (a0 + ((M-2:ℕ):ℝ)*(δ/2)) 1 :=
          (Set.Ioc_union_Ioc_eq_Ioc hM0le hαM2).symm
        rw [hsplit0, setIntegral_union hdisj0 measurableSet_Ioc (hint0 _ _) (hint0 _ _)]
      have hI0nnB : (0:ℝ) ≤ ∫ t in Set.Ioc (a0 + ((M-2:ℕ):ℝ)*(δ/2)) 1,
          surv (μ := μ) X0 t ∂volume :=
        setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun t => hSnn X0 t))
      have hcbeta : c * ((M-2:ℕ):ℝ)*(δ/2) + a0 * c ≤ c := by
        have h1 : c * ((M-2:ℕ):ℝ)*(δ/2) + a0 * c = c * (((M-2:ℕ):ℝ)*(δ/2) + a0) := by ring
        have h2 : ((M-2:ℕ):ℝ)*(δ/2) + a0 ≤ 1 := by linarith [hαM2]
        have h3 : c * (((M-2:ℕ):ℝ)*(δ/2) + a0) ≤ c * (1:ℝ) :=
          mul_le_mul_of_nonneg_left h2 hcnn
        have h4 : c * (1:ℝ) = c := by ring
        rw [h1]
        linarith [h3, h4]
      have hbudB : a0 * (survBar (μ := μ) X0 a0 + c) + SH ≤ E0 + c := by
        have h1 : SH = (∫ t in Set.Ioc a0 (a0 + ((M-2:ℕ):ℝ)*(δ/2)), surv (μ := μ) X0 t ∂volume)
            + c * ((M-2:ℕ):ℝ)*(δ/2) := by
          rw [hHsum, hA1, hcvolA]
        have h0 : (0:ℝ) ≤ survBar (μ := μ) X0 a0 := hSBnn0 X0
        have ha0c : a0 * (survBar (μ := μ) X0 a0 + c) = a0 * survBar (μ := μ) X0 a0 + a0 * c :=
          mul_add a0 _ _
        rw [ha0c, h1]
        linarith [dec0, hI0split, hI0nnB, hcbeta, h0]
      rcases le_or_gt ((1 + ε/2) * a0 * (survBar (μ := μ) X0 a0 + c))
          ((a0+δ) * survBar (μ := μ) X1 (a0+δ)) with hsA | hsA
      · -- case A: the base point a0 itself witnesses the gap
        exact ⟨a0, le_refl a0, ha01,
          caseA_conclusion (μ := μ) ε δ a0 hε hε1 hδ ha0 ha1le hcnn (hSleSB X0 a0) hsA⟩
      · -- case B: some dyadic cell beats the average
        have hf12 : (0:ℝ) ≤ 1 + ε/2 := by linarith
        have hchainB : (1 + ε/2) * (E0 + c) ≤ (a0+δ) * survBar (μ := μ) X1 (a0+δ) + SG := by
          linarith [hchain, dec1, hI1leSG]
        obtain ⟨j, hjr, hjgood⟩ : ∃ j ∈ Finset.range (M-2),
            (1 + ε/2) * (∫ s in Set.Ioc (a0 + (j:ℝ)*(δ/2)) (a0 + ((j+1:ℕ):ℝ)*(δ/2)),
                (fun s => surv (μ := μ) X0 s + c) s ∂volume)
            ≤ (∫ s in Set.Ioc ((a0+δ) + (j:ℝ)*(δ/2)) ((a0+δ) + ((j+1:ℕ):ℝ)*(δ/2)),
                surv (μ := μ) X1 s ∂volume) := by
          by_contra hcon
          have hallt : ∀ k ∈ Finset.range (M-2),
              (∫ s in Set.Ioc ((a0+δ) + (k:ℝ)*(δ/2)) ((a0+δ) + ((k+1:ℕ):ℝ)*(δ/2)),
                  surv (μ := μ) X1 s ∂volume)
              < (1 + ε/2) * (∫ s in Set.Ioc (a0 + (k:ℝ)*(δ/2)) (a0 + ((k+1:ℕ):ℝ)*(δ/2)),
                  (fun s => surv (μ := μ) X0 s + c) s ∂volume) := by
            intro k hk
            by_contra hnk
            push_neg at hnk
            exact hcon ⟨k, hk, hnk⟩
          have h1' : (∑ k ∈ Finset.range (M-2), ∫ s in Set.Ioc ((a0+δ) + (k:ℝ)*(δ/2))
                  ((a0+δ) + ((k+1:ℕ):ℝ)*(δ/2)), surv (μ := μ) X1 s ∂volume)
              ≤ (∑ k ∈ Finset.range (M-2), (1 + ε/2) * ∫ s in Set.Ioc (a0 + (k:ℝ)*(δ/2))
                  (a0 + ((k+1:ℕ):ℝ)*(δ/2)), (fun s => surv (μ := μ) X0 s + c) s ∂volume) :=
            Finset.sum_le_sum (fun k hk => le_of_lt (hallt k hk))
          rw [← Finset.mul_sum, ← hSGd, ← hSHd] at h1'
          have hL : (1 + ε/2) * (a0 * (survBar (μ := μ) X0 a0 + c) + SH)
              ≤ (1 + ε/2) * (E0 + c) :=
            mul_le_mul_of_nonneg_left hbudB hf12
          have hR : (a0+δ) * survBar (μ := μ) X1 (a0+δ) + SG
              < (1 + ε/2) * (a0 * (survBar (μ := μ) X0 a0 + c) + SH) := by
            have hexp : (1 + ε/2) * (a0 * (survBar (μ := μ) X0 a0 + c) + SH)
                = (1 + ε/2) * a0 * (survBar (μ := μ) X0 a0 + c) + (1 + ε/2) * SH := by ring
            have hA' : (a0+δ) * survBar (μ := μ) X1 (a0+δ)
                < (1 + ε/2) * a0 * (survBar (μ := μ) X0 a0 + c) := hsA
            rw [hexp]
            linarith [hA', h1']
          linarith [hL, hchainB, hR]
        -- cell bounds at the good index
        have hj1e : ((j+1:ℕ):ℝ)*(δ/2) = (j:ℝ)*(δ/2) + δ/2 := by
          rw [Nat.cast_succ j]; ring
        have huvG : (a0+δ) + (j:ℝ)*(δ/2) ≤ (a0+δ) + ((j+1:ℕ):ℝ)*(δ/2) := by
          rw [hj1e]; linarith [huvt]
        have hvG : ((a0+δ) + ((j+1:ℕ):ℝ)*(δ/2)) - ((a0+δ) + (j:ℝ)*(δ/2)) = δ/2 := by
          rw [hj1e]; ring
        have hcellG0 : (∫ s in Set.Ioc ((a0+δ) + (j:ℝ)*(δ/2)) ((a0+δ) + ((j+1:ℕ):ℝ)*(δ/2)),
                surv (μ := μ) X1 s ∂volume)
            ≤ (((a0+δ) + ((j+1:ℕ):ℝ)*(δ/2)) - ((a0+δ) + (j:ℝ)*(δ/2)))
              * surv (μ := μ) X1 ((a0+δ) + (j:ℝ)*(δ/2)) :=
          cell_le (surv (μ := μ) X1) (surv_antitone X1) _ _ huvG (hint1 _ _)
        rw [hvG] at hcellG0
        have huvH : a0 + (j:ℝ)*(δ/2) ≤ a0 + ((j+1:ℕ):ℝ)*(δ/2) := by
          rw [hj1e]; linarith [huvt]
        have hvH : (a0 + ((j+1:ℕ):ℝ)*(δ/2)) - (a0 + (j:ℝ)*(δ/2)) = δ/2 := by
          rw [hj1e]; ring
        have hcellH0 : ((a0 + ((j+1:ℕ):ℝ)*(δ/2)) - (a0 + (j:ℝ)*(δ/2)))
              * (surv (μ := μ) X0 (a0 + ((j+1:ℕ):ℝ)*(δ/2)) + c)
            ≤ (∫ s in Set.Ioc (a0 + (j:ℝ)*(δ/2)) (a0 + ((j+1:ℕ):ℝ)*(δ/2)),
                (fun s => surv (μ := μ) X0 s + c) s ∂volume) :=
          cell_ge (surv (μ := μ) X0) (surv_antitone X0) c _ _ huvH (hint2 _ _)
        rw [hvH] at hcellH0
        obtain ⟨t, htd⟩ : ∃ t : ℝ, t = a0 + ((j+1:ℕ):ℝ)*(δ/2) := ⟨_, rfl⟩
        rw [← htd] at hcellH0 hjgood
        have htid : (a0+δ) + (j:ℝ)*(δ/2) = t + δ/2 := by rw [htd, hj1e]; ring
        have hkey : (δ/2) * ((1+ε/2) * (surv (μ := μ) X0 t + c))
            ≤ (δ/2) * surv (μ := μ) X1 ((a0+δ) + (j:ℝ)*(δ/2)) := by
          have e1 : (δ/2) * ((1+ε/2) * (surv (μ := μ) X0 t + c))
              = (1+ε/2) * ((δ/2) * (surv (μ := μ) X0 t + c)) := by ring
          have e2 : (1+ε/2) * ((δ/2) * (surv (μ := μ) X0 t + c))
              ≤ (1+ε/2) * (∫ s in Set.Ioc (a0 + (j:ℝ)*(δ/2)) t,
                  (fun s => surv (μ := μ) X0 s + c) s ∂volume) :=
            mul_le_mul_of_nonneg_left hcellH0 hf12
          linarith [e1, e2, hjgood, hcellG0]
        rw [htid] at hkey
        have hfinal : (1+ε/2) * (surv (μ := μ) X0 t + c) ≤ surv (μ := μ) X1 (t + δ/2) :=
          le_of_mul_le_mul_left hkey hd
        have hj1nn : (0:ℝ) ≤ ((j+1:ℕ):ℝ)*(δ/2) := mul_nonneg (Nat.cast_nonneg _) huvt
        have htge : a0 ≤ t := by rw [htd]; linarith [hj1nn]
        have hjle : j + 1 ≤ M - 2 := by
          have h1 := Finset.mem_range.mp hjr
          omega
        have hcastle : ((j+1:ℕ):ℝ) ≤ ((M-2:ℕ):ℝ) := by exact_mod_cast hjle
        have htle : t ≤ 1 := by
          rw [htd]
          have h1 : ((j+1:ℕ):ℝ)*(δ/2) ≤ ((M-2:ℕ):ℝ)*(δ/2) :=
            mul_le_mul_of_nonneg_right hcastle huvt
          linarith [h1, hαM2]
        refine ⟨t, htge, htle, ?_⟩
        have hW : (0:ℝ) ≤ surv (μ := μ) X0 t + c := by
          have h1 := hSnn X0 t
          linarith [h1, hcnn]
        have hfac' : (1 + ε/4) * (surv (μ := μ) X0 t + c)
            ≤ (1+ε/2) * (surv (μ := μ) X0 t + c) := by
          nlinarith [hW, hε]
        linarith [hfac', hfinal]
    · -- fallback branch: the grid degenerates and a1 = 1
      have hMle : Nat.ceil (2*(1 - a0)/δ) ≤ 2 := by omega
      have hxle : 2*(1 - a0)/δ ≤ 2 := le_trans hMge (by exact_mod_cast hMle)
      have hqδ : 2*(1 - a0)/δ * δ = 2*(1 - a0) := by field_simp
      have ha1e : a0 + δ = 1 := by
        have h1 : 2*(1 - a0) ≤ 2*δ := by
          have h2 : 2*(1 - a0)/δ * δ ≤ 2*δ := mul_le_mul_of_nonneg_right hxle (le_of_lt hδ)
          rw [hqδ] at h2
          linarith
        linarith [h1, ha11]
      have I1z : (∫ t in Set.Ioc (a0+δ) 1, surv (μ := μ) X1 t ∂volume) = 0 := by
        rw [ha1e, Set.Ioc_self, setIntegral_empty]
      -- E1 = 1 * P̄1
      have hP1dom : (1 + ε/2)*a0*(survBar (μ := μ) X0 a0 + c) ≤ (a0+δ)*survBar (μ := μ) X1 (a0+δ) := by
        have h1 : (a0+δ)*survBar (μ := μ) X1 (a0+δ) = E1 := by
          rw [dec1, I1z]; ring
        nlinarith [h1, hchain, hbud0]
      exact ⟨a0, le_refl a0, ha01,
        caseA_conclusion (μ := μ) ε δ a0 hε hε1 hδ ha0 ha1le hcnn (hSleSB X0 a0) hP1dom⟩
  · -- degenerate branch: a1 > 1 forces X1 = 0 and E0 = 0
    have ha1gt : 1 < a0 + δ := by linarith
    have hX1z : ∀ ω, X1 ω = 0 := by
      intro ω
      rcases eq_or_lt_of_le (hr1 ω).1 with h | h
      · exact h.symm
      · exfalso
        have hX1le : X1 ω ≤ 1 := (hr1 ω).2
        have h2 := hs1 ω h
        linarith
    have hE1z : E1 = 0 := by
      rw [hE1d]
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun ω => by rw [hX1z ω]))]
      simp
    have hE0z : E0 = 0 := by nlinarith [hE, hE0nn, hE1z]
    have hP0z : survBar (μ := μ) X0 a0 = 0 := by
      have dec0 := integral_eq_decomp (μ := μ) hm0 hr0 ha0 ha01 hs0
      have hI0nn : 0 ≤ ∫ t in Set.Ioc a0 1, surv (μ := μ) X0 t ∂volume := by
        refine setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun t => ?_))
        exact hSnn X0 t
      have hleE : a0 * survBar (μ := μ) X0 a0 ≤ E0 := by
        rw [hE0d, dec0]
        linarith
      nlinarith [ha0, hleE, hE0z, hSBnn0 X0]
    refine ⟨a0, le_refl a0, ha01, ?_⟩
    have hS1z : surv (μ := μ) X1 (a0 + δ/2) = 0 := by
      have h0 : μ {ω : Ω | a0 + δ/2 < X1 ω} = 0 := by
        have hsub : {ω : Ω | a0 + δ/2 < X1 ω} ⊆ (∅ : Set Ω) := by
          intro ω hω
          have h : a0 + δ/2 < X1 ω := Set.mem_setOf.mp hω
          have hpos : (0:ℝ) < X1 ω := by
            rcases hr1 ω with ⟨h0, _⟩
            linarith
          have h2 := hs1 ω hpos
          rw [hX1z ω] at h2
          exfalso
          linarith
        simpa using measure_mono (μ := μ) hsub
      simp [surv, h0]
    have hS0z : surv (μ := μ) X0 a0 = 0 := by
      have hle : surv (μ := μ) X0 a0 ≤ 0 := by
        have h1 := hSleSB X0 a0
        rw [hP0z] at h1
        linarith
      exact le_antisymm hle (hSnn X0 a0)
    have hc0 : c = 0 := by rw [hcd, hE1z]; simp
    rw [hS1z, hS0z, hc0]
    simp

end Main

end GapLemma
