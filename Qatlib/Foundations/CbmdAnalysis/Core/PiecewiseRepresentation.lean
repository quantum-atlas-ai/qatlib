/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.FastLCU
import Qatlib.Foundations.CbmdAnalysis.Core.AuxSeriesIdentity
import Mathlib.Analysis.Matrix.Order

/-!
# Evolutions from finite piecewise-continuous inputs

`FinitePiecewiseContinuousOn` records a finite partition and continuous cell extensions that
agree with the original input inside each cell. Clamping the extensions produces global
continuous pieces whose assembled fields recover the input almost everywhere, preserving closed
constraints such as Hermiticity and positive semidefiniteness.

The induced matrix `evolution` is absolutely continuous, satisfies the original evolution
equation almost everywhere, and is independent of the chosen representation. Endpoint
analyticity, norm bounds, real-parameter unitarity, and the resulting sampling identities and
finite LCU bounds connect these inputs to [WangEtAl2026].

## Main statements

* `FinitePiecewiseContinuousOn.evolution_unique_ae`: proves uniqueness for the original input
  equation.
* `FinitePiecewiseContinuousOn.evolution_partition_independent`: identifies evolutions from
  different partitions.
* `FinitePiecewiseContinuousOn.fast_lcu_original_input`: gives finite LCU bounds for the
  original input.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CBMD
open Set MeasureTheory Filter Matrix
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
/-- A point between the first and last partition times that differs from every partition time
belongs to an open partition cell. -/
private theorem exists_partition_cell (τ : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Icc (τ 0) (τ n)) (hne : ∀ j ≤ n, t ≠ τ j) :
    ∃ j < n, t ∈ Ioo (τ j) (τ (j + 1)) := by
  induction n with
  | zero => exact False.elim ((hne 0 le_rfl) (le_antisymm ht.2 ht.1))
  | succ n ih =>
    by_cases hn : t < τ n
    · obtain ⟨j, hj, hc⟩ := ih ⟨ht.1, hn.le⟩ (fun j hj => hne j (by omega))
      exact ⟨j, by omega, hc⟩
    · exact ⟨n, Nat.lt_succ_self n, lt_of_le_of_ne (not_lt.mp hn) (Ne.symm (hne n (by omega))),
        lt_of_le_of_ne ht.2 (hne (n + 1) le_rfl)⟩

/-- A finite strictly increasing partition from `a` to `b` with cell extensions continuous on
each closed cell and agreeing with `F` on its interior. Values of `F` at partition points
need not agree with the extensions. -/
structure FinitePiecewiseContinuousOn {E : Type*} [TopologicalSpace E]
    (F : ℝ → E) (a b : ℝ) where
  count : ℕ
  time : ℕ → ℝ
  strict : StrictMono time
  start : time 0 = a
  finish : time count = b
  extension : ℕ → ℝ → E
  continuous_cell : ∀ j < count, ContinuousOn (extension j) (Icc (time j) (time (j + 1)))
  agrees : ∀ j < count, ∀ t ∈ Ioo (time j) (time (j + 1)), extension j t = F t

namespace FinitePiecewiseContinuousOn
variable {E : Type*} [TopologicalSpace E] [Zero E]
variable {F : ℝ → E} {a b : ℝ}

/-- The cell extension evaluated at time clamped to its closed cell when `j < P.count`, and the
zero value for all other indices. -/
def clampedPiece (P : FinitePiecewiseContinuousOn F a b) (j : ℕ) (t : ℝ) : E :=
  if j < P.count then P.extension j (min (P.time (j + 1)) (max (P.time j) t)) else 0

omit [Zero E] in

/-- Clamping a real time between consecutive partition times produces a point in that closed
cell. -/
theorem clamp_mem (P : FinitePiecewiseContinuousOn F a b) (j : ℕ) (t : ℝ) :
    min (P.time (j + 1)) (max (P.time j) t) ∈ Icc (P.time j) (P.time (j + 1)) := by
  exact ⟨le_min (P.strict.monotone (Nat.le_succ j)) (le_max_left _ _), min_le_left _ _⟩

/-- Every clamped piece is continuous on the whole real line. -/
theorem clampedPiece_continuous (P : FinitePiecewiseContinuousOn F a b) (j : ℕ) :
    Continuous (P.clampedPiece j) := by
  unfold clampedPiece
  split_ifs with hj
  · exact (P.continuous_cell j hj).comp_continuous
      (continuous_const.min (continuous_const.max continuous_id)) (P.clamp_mem j)
  · exact continuous_const

/-- On the interior of a represented cell, the corresponding clamped piece equals the original
input. -/
theorem clampedPiece_eq (P : FinitePiecewiseContinuousOn F a b) (j : ℕ) (hj : j < P.count)
    {t : ℝ} (ht : t ∈ Ioo (P.time j) (P.time (j + 1))) : P.clampedPiece j t = F t := by
  simp only [clampedPiece, hj, ↓reduceIte, max_eq_right ht.1.le, min_eq_right ht.2.le]
  exact P.agrees j hj t ht

/-- If the original input lies in a closed set containing zero throughout the interval, every
clamped piece lies in that set at every time. -/
theorem clampedPiece_mem_closed (P : FinitePiecewiseContinuousOn F a b)
    (S : Set E) (hS : IsClosed S) (hzero : (0 : E) ∈ S)
    (hF : ∀ t ∈ Icc a b, F t ∈ S) (j : ℕ) (t : ℝ) : P.clampedPiece j t ∈ S := by
  by_cases hj : j < P.count
  · have hmaps : MapsTo (P.extension j) (Ioo (P.time j) (P.time (j + 1))) S := by
      intro u hu
      rw [P.agrees j hj u hu]
      apply hF u
      constructor
      · rw [← P.start]
        exact (P.strict.monotone (Nat.zero_le j)).trans hu.1.le
      · rw [← P.finish]
        exact hu.2.le.trans (P.strict.monotone (by omega))
    have hc : closure (Ioo (P.time j) (P.time (j + 1))) =
        Icc (P.time j) (P.time (j + 1)) := closure_Ioo (P.strict (Nat.lt_succ_self j)).ne
    have hm := hmaps.closure_of_continuousOn (by rw [hc]; exact P.continuous_cell j hj)
    rw [hc, hS.closure_eq] at hm
    simpa only [clampedPiece, hj, ↓reduceIte] using! hm (P.clamp_mem j t)
  · simpa only [clampedPiece, hj, ↓reduceIte] using! hzero

/-- The field assembled from the clamped pieces equals the original input almost everywhere on
`Icc a b`. -/
theorem assembledField_ae_eq (P : FinitePiecewiseContinuousOn F a b) :
    ∀ᵐ t : ℝ, t ∈ Icc a b → assembledField P.clampedPiece P.time P.count t = F t := by
  have hnull := ((Finset.range (P.count + 1)).image P.time).finite_toSet.countable.ae_notMem volume
  filter_upwards [hnull] with t ht hmem
  have hne (j : ℕ) (hj : j ≤ P.count) : t ≠ P.time j := by
    intro he
    apply ht
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨j, by omega, he.symm⟩
  have ht' : t ∈ Icc (P.time 0) (P.time P.count) := by simpa only [P.start, P.finish] using! hmem
  obtain ⟨j, hj, hc⟩ :=
      Qatlib.Foundations.CbmdAnalysis.Core.CBMD.exists_partition_cell P.time P.count t ht' hne
  rw [assembledField_eq_on_piece P.clampedPiece P.time P.strict.monotone P.count j hj hc]
  exact P.clampedPiece_eq j hj hc

end FinitePiecewiseContinuousOn

/-- A normed-space-valued function with a finite piecewise-continuous representation is interval
integrable. -/
theorem FinitePiecewiseContinuousOn.intervalIntegrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E} {a b : ℝ}
    (P : FinitePiecewiseContinuousOn F a b) : IntervalIntegrable F volume a b := by
  have hi := IntervalIntegrable.trans_iterate
    (fun j hj => assembledField_intervalIntegrable_piece P.clampedPiece
      P.clampedPiece_continuous P.time P.strict.monotone P.count j hj)
  rw [P.start, P.finish] at hi
  apply hi.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  have hab : a ≤ b := by
    simpa only [P.start, P.finish] using! P.strict.monotone (Nat.zero_le P.count)
  filter_upwards [P.assembledField_ae_eq] with t ht hmem
  rw [uIoc_of_le hab] at hmem
  exact ht ⟨hmem.1.le, hmem.2⟩

/-- Taking the first component of an assembled pair-valued field commutes with assembling its
component fields. -/
private theorem assembledField_fst {E G : Type*} [Zero E] [Zero G]
    (F : ℕ → ℝ → E × G) (τ : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (assembledField F τ n t).1 = assembledField (fun j u => (F j u).1) τ n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [assembledField]; split_ifs <;> simp only [ih]

/-- Taking the second component of an assembled pair-valued field commutes with assembling its
component fields. -/
private theorem assembledField_snd {E G : Type*} [Zero E] [Zero G]
    (F : ℕ → ℝ → E × G) (τ : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    (assembledField F τ n t).2 = assembledField (fun j u => (F j u).2) τ n t := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [assembledField]; split_ifs <;> simp only [ih]

namespace FinitePiecewiseContinuousOn
variable {I : Type} [Fintype I] [DecidableEq I]
variable {H L : ℝ → Matrix I I ℂ} {a b : ℝ}

/-- The first component of the clamped piece for the pair-valued input `(H, L)`. -/
def hPiece (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (j : ℕ) (t : ℝ) :
    Matrix I I ℂ := (P.clampedPiece j t).1

/-- The second component of the clamped piece for the pair-valued input `(H, L)`. -/
def lPiece (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (j : ℕ) (t : ℝ) :
    Matrix I I ℂ := (P.clampedPiece j t).2

omit [Fintype I] [DecidableEq I] in

/-- Every clamped `H` piece is continuous on the real line. -/
theorem hPiece_continuous (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (j : ℕ) :
    Continuous (P.hPiece j) := (P.clampedPiece_continuous j).fst

omit [Fintype I] [DecidableEq I] in

/-- Every clamped `L` piece is continuous on the real line. -/
theorem lPiece_continuous (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (j : ℕ) :
    Continuous (P.lPiece j) := (P.clampedPiece_continuous j).snd

omit [Fintype I] [DecidableEq I] in

/-- If `H` is Hermitian throughout the original interval, each clamped `H` piece is Hermitian at
every time. -/
theorem hPiece_hermitian (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (j : ℕ) (t : ℝ) : (P.hPiece j t).IsHermitian := by
  have hc : IsClosed {M : Matrix I I ℂ | M.IsHermitian} := by
    simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using!
      (isClosed_eq (continuous_star : Continuous (fun M : Matrix I I ℂ => star M)) continuous_id)
  exact P.clampedPiece_mem_closed {v : Matrix I I ℂ × Matrix I I ℂ | v.1.IsHermitian}
    (hc.preimage continuous_fst) (by simp [Matrix.IsHermitian]) hH j t

omit [DecidableEq I] in

/-- If `L` is positive semidefinite throughout the original interval, each clamped `L` piece is
positive semidefinite at every time. -/
theorem lPiece_positive (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (j : ℕ) (t : ℝ) : (P.lPiece j t).PosSemidef := by
  have hherm : IsClosed {M : Matrix I I ℂ | M.IsHermitian} := by
    simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using!
      (isClosed_eq (continuous_star : Continuous (fun M : Matrix I I ℂ => star M)) continuous_id)
  have hc : IsClosed {M : Matrix I I ℂ | M.PosSemidef} := by
    simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and, Set.setOf_forall]
    apply hherm.inter
    apply isClosed_iInter
    intro x
    have hq : Continuous (fun M : Matrix I I ℂ => star x ⬝ᵥ (M *ᵥ x)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    have hz : IsClosed {z : ℂ | 0 ≤ z} := by
      simp only [Complex.nonneg_iff, Set.setOf_and]
      exact (isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_eq continuous_const Complex.continuous_im)
    exact hz.preimage hq
  exact P.clampedPiece_mem_closed {v : Matrix I I ℂ × Matrix I I ℂ | v.2.PosSemidef}
    (hc.preimage continuous_snd) (by simpa using! (Matrix.PosSemidef.zero : (0 : Matrix I I ℂ).PosSemidef)) hL j t

omit [Fintype I] [DecidableEq I] in

/-- The fields assembled from the clamped `H` and `L` pieces equal the original fields
simultaneously almost everywhere on the interval. -/
theorem fields_ae_eq (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) :
    ∀ᵐ t : ℝ, t ∈ Icc a b →
      assembledField P.hPiece P.time P.count t = H t ∧
      assembledField P.lPiece P.time P.count t = L t := by
  filter_upwards [P.assembledField_ae_eq] with t ht hmem
  have he := ht hmem
  exact ⟨by simpa only [assembledField_fst, hPiece] using! congrArg Prod.fst he,
    by simpa only [assembledField_snd, lPiece] using! congrArg Prod.snd he⟩

/-- The original field `L` is interval integrable when the pair `(H, L)` has a finite
piecewise-continuous representation. -/
theorem original_l_intervalIntegrable
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) :
    IntervalIntegrable L volume a b := by
  have hi := IntervalIntegrable.trans_iterate
    (fun j hj => assembledField_intervalIntegrable_piece P.lPiece
      P.lPiece_continuous P.time P.strict.monotone P.count j hj)
  rw [P.start, P.finish] at hi
  apply hi.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  have hab : a ≤ b := by
    simpa only [P.start, P.finish] using! P.strict.monotone (Nat.zero_le P.count)
  filter_upwards [P.fields_ae_eq] with t ht hmem
  rw [uIoc_of_le hab] at hmem
  exact (ht ⟨hmem.1.le, hmem.2⟩).2

/-- The norm of the original field `L` is interval integrable when `(H, L)` has a finite
piecewise-continuous representation. -/
theorem original_l_norm_intervalIntegrable
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) :
    IntervalIntegrable (fun t => ‖L t‖) volume a b := P.original_l_intervalIntegrable.norm

/-- The integral of `‖L t‖` over the original interval equals the piecewise Dyson budget of the
clamped `L` pieces. -/
theorem budget_eq (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) :
    (∫ t in a..b, ‖L t‖) = dysonPiecewiseBudget P.lPiece P.time P.count := by
  rw [← assembledField_norm_integral P.lPiece P.lPiece_continuous P.time P.strict.monotone]
  rw [P.start, P.finish]
  apply intervalIntegral.integral_congr_ae
  have hab : a ≤ b := by
    simpa only [P.start, P.finish] using! P.strict.monotone (Nat.zero_le P.count)
  filter_upwards [P.fields_ae_eq] with t ht hmem
  rw [uIoc_of_le hab] at hmem
  rw [(ht ⟨hmem.1.le, hmem.2⟩).2]

/-- The assembled Dyson evolution built from the globally continuous clamped pieces of the pair
`(H, L)`. -/
def evolution (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (z : ℂ) (t : ℝ) : Matrix I I ℂ := assembledDyson P.hPiece P.lPiece P.time P.count z t

/-- The represented evolution equals the identity at the original initial time `a`. -/
theorem evolution_initial (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (z : ℂ) :
    P.evolution z a = 1 := by
  simpa only [P.start, evolution] using!
    assembledDyson_initial P.hPiece P.lPiece P.time P.strict.monotone P.count z

/-- The represented evolution is absolutely continuous on the original interval. -/
theorem evolution_absolutelyContinuous
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (z : ℂ) :
    AbsolutelyContinuousOnInterval (P.evolution z) a b :=
  assembledDyson_absolutelyContinuous P.hPiece P.lPiece P.hPiece_continuous P.lPiece_continuous
    P.time P.strict P.count z a b

/-- The represented evolution satisfies `U' = -i (H + z L) U` almost everywhere on the original
interval. -/
theorem evolution_hasDerivAt_ae
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (z : ℂ) :
    ∀ᵐ t : ℝ, t ∈ Icc a b →
      HasDerivAt (P.evolution z) (-(Complex.I • (H t + z • L t) * P.evolution z t)) t := by
  have hd := assembledDyson_hasDerivAt_ae P.hPiece P.lPiece P.hPiece_continuous P.lPiece_continuous
    P.time P.strict P.count z
  simp only [P.start, P.finish] at hd
  filter_upwards [hd, P.fields_ae_eq] with t ht he hmem
  simpa only [(he hmem).1, (he hmem).2, evolution] using! ht hmem

/-- Every absolutely continuous solution of the original parameter-dependent evolution equation
with identity initial value agrees with the represented evolution on `Icc a b`. -/
theorem evolution_unique_ae
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (z : ℂ) (f : ℝ → Matrix I I ℂ) (hf : AbsolutelyContinuousOnInterval f a b)
    (hinit : f a = 1)
    (hode : ∀ᵐ t : ℝ, t ∈ Icc a b →
      HasDerivAt f (-(Complex.I • (H t + z • L t) * f t)) t) :
    EqOn f (P.evolution z) (Icc a b) := by
  have hd : ∀ᵐ t : ℝ, t ∈ Icc (P.time 0) (P.time P.count) →
      HasDerivAt f (-(Complex.I • (assembledField P.hPiece P.time P.count t +
        z • assembledField P.lPiece P.time P.count t) * f t)) t := by
    simp only [P.start, P.finish]
    filter_upwards [hode, P.fields_ae_eq] with t ht he hmem
    simpa only [(he hmem).1, (he hmem).2] using! ht hmem
  have hu := assembledDyson_unique_ae P.hPiece P.lPiece P.hPiece_continuous P.lPiece_continuous
    P.time P.strict P.count z f (by simpa only [P.start, P.finish] using! hf)
    (by simpa only [P.start] using! hinit) hd
  simpa only [P.start, P.finish, evolution] using! hu

/-- The represented evolution at the final time `b` is complex differentiable in its parameter. -/
theorem evolution_differentiable_parameter
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) :
    Differentiable ℂ (fun z => P.evolution z b) := by
  simpa only [P.finish, evolution] using!
    assembledDyson_differentiable_parameter P.hPiece P.lPiece P.hPiece_continuous
      P.lPiece_continuous P.time P.strict P.count

/-- For Hermitian `H` and positive semidefinite `L` on the original interval, the endpoint norm
is at most `exp (max z.im 0 * ∫ t in a..b, ‖L t‖)`. -/
theorem evolution_norm_le
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (z : ℂ) :
    ‖P.evolution z b‖ ≤ Real.exp (max z.im 0 * ∫ t in a..b, ‖L t‖) := by
  have he := assembledDyson_endpoint P.hPiece P.lPiece P.time P.strict P.count z
  have hb := dysonPiecewise_norm_le P.hPiece P.lPiece P.hPiece_continuous P.lPiece_continuous
    (P.hPiece_hermitian hH) (P.lPiece_positive hL) P.time P.strict.monotone P.count z
  rw [← he, ← P.budget_eq] at hb
  simpa only [P.finish, evolution] using! hb

/-- For Hermitian `H` and positive semidefinite `L` on the original interval, the represented
endpoint evolution is unitary at every real parameter. -/
theorem evolution_real_unitary
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hL : ∀ t ∈ Icc a b, (L t).PosSemidef) (x : ℝ) :
    P.evolution (x : ℂ) b ∈ Matrix.unitaryGroup I ℂ := by
  have he := assembledDyson_endpoint P.hPiece P.lPiece P.time P.strict P.count (x : ℂ)
  have hu := dysonPiecewise_real_unitary P.hPiece P.lPiece P.hPiece_continuous P.lPiece_continuous
    (P.hPiece_hermitian hH) (fun j u => (P.lPiece_positive hL j u).isHermitian) P.time P.count x
  rw [← he] at hu
  simpa only [P.finish, evolution] using! hu

/-- Two finite piecewise-continuous representations of the same input pair give identical
evolutions on the original interval. -/
theorem evolution_partition_independent
    (P Q : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) (z : ℂ) :
    EqOn (P.evolution z) (Q.evolution z) (Icc a b) :=
  Q.evolution_unique_ae z (P.evolution z) (P.evolution_absolutelyContinuous z)
    (P.evolution_initial z) (P.evolution_hasDerivAt_ae z)

/-- At parameter `-i`, the represented evolution satisfies `U' = -(L + i H) U` almost everywhere
on the original interval. -/
theorem evolution_target_hasDerivAt_ae
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b) :
    ∀ᵐ t : ℝ, t ∈ Icc a b →
      HasDerivAt (P.evolution (-Complex.I))
        (-((L t + Complex.I • H t) * P.evolution (-Complex.I) t)) t := by
  have he (t : ℝ) : Complex.I • (H t + -Complex.I • L t) = L t + Complex.I • H t := by
    simp only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    exact add_comm _ _
  simpa only [he] using! P.evolution_hasDerivAt_ae (-Complex.I)

/-- Every absolutely continuous solution of `U' = -(L + i H) U` with identity initial value
agrees with the represented evolution at parameter `-i` on the original interval. -/
theorem evolution_target_unique_ae
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (f : ℝ → Matrix I I ℂ) (hf : AbsolutelyContinuousOnInterval f a b)
    (hinit : f a = 1)
    (hode : ∀ᵐ t : ℝ, t ∈ Icc a b →
      HasDerivAt f (-((L t + Complex.I • H t) * f t)) t) :
    EqOn f (P.evolution (-Complex.I)) (Icc a b) := by
  apply P.evolution_unique_ae (-Complex.I) f hf hinit
  have he (t : ℝ) : Complex.I • (H t + -Complex.I • L t) = L t + Complex.I • H t := by
    simp only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    exact add_comm _ _
  simpa only [he] using! hode

set_option backward.isDefEq.respectTransparency true in

/-- For Hermitian `H`, positive semidefinite `L`, and a finite nonempty auxiliary pole set
avoiding the target and sampling lattice, the compatible budget bound yields absolute
summability of the sample series and the stated target-minus-series-minus-residues identity
[WangEtAl2026]. -/
theorem matrix_series_original_input
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hL : ∀ t ∈ Icc a b, (L t).PosSemidef)
    (s : Finset ℂ) (hs : s.Nonempty) (hsTarget : -Complex.I ∉ s)
    {spacing : ℝ} (ha : 0 < spacing)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / spacing : ℝ) : ℂ))
    (hbudget : (∫ t in a..b, ‖L t‖) ≤ 2 * Real.pi * spacing) :
    let U := fun z => P.evolution z b
    Summable (fun k : ℤ => ‖auxSample s spacing U k‖) ∧
    U (-Complex.I) - (∑' k : ℤ, auxSample s spacing U k) -
      (∑ p ∈ s,
        (((Real.exp (-2 * Real.pi * spacing) - 1 : ℝ) : ℂ) /
          ((Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (spacing : ℂ) * p) - 1) *
            auxDeletedPoleProduct s p)) • U p) = 0 := by
  let U : ℂ → Matrix I I ℂ := fun z => P.evolution z b
  have hr (x : ℝ) : ‖U (x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.ofReal_im, max_self, zero_mul, Real.exp_zero] using!
      P.evolution_norm_le hH hL (x : ℂ)
  have hsummable := auxWeight_smul_norm_summable s hs ha U hr
  have hidentity := aux_kernel_series_identity_paper s hs hsTarget ha hsLattice hbudget U
    P.evolution_differentiable_parameter (P.evolution_norm_le hH hL)
  exact ⟨hsummable, hidentity⟩

set_option backward.isDefEq.respectTransparency true in

/-- For `0 < δ ≤ 1`, the original piecewise-continuous input with Hermitian `H` and positive
semidefinite `L` has the prescribed finite LCU approximation within `δ`, with unitary real
samples and the stated coefficient, frequency, and sample-count bounds [WangEtAl2026]. -/
theorem fast_lcu_original_input
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hL : ∀ t ∈ Icc a b, (L t).PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let ρ := ∫ t in a..b, ‖L t‖
    let m := kernelOrder (δ / 2)
    let spacing := kernelSpacing ρ (δ / 2) m
    let K := kernelCutoff spacing (δ / 2)
    let U := fun z => P.evolution z b
    let B := max 0 (Real.log (kernelTailConstant / (δ / 2)) / 2) + 2
    ‖U (-Complex.I) - integerLCUSum m spacing K U‖ ≤ δ ∧
    (∀ k : ℤ, U (((k : ℝ) / spacing : ℝ) : ℂ) ∈ Matrix.unitaryGroup I ℂ) ∧
    (∑ k ∈ Finset.Icc (-(K : ℤ)) K, ‖integerWeight m spacing ((k : ℝ) / spacing)‖) ≤
      5 * integerWeightConstant ∧
    (∀ k ∈ Finset.Icc (-(K : ℤ)) K,
      |(k : ℝ) / spacing| < 2 * max 0 (Real.log (kernelTailConstant / (δ / 2)) / 2) + 5) ∧
    (Finset.Icc (-(K : ℤ)) K).card = 2 * K + 1 ∧
    ((Finset.Icc (-(K : ℤ)) K).card : ℝ) <
      4 * (1 + (ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + B) /
        (2 * Real.pi)) * B + 3 := by
  (try dsimp only)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact integerLCU_target_error_le _ hδ hδ1 _
      P.evolution_differentiable_parameter (P.evolution_norm_le hH hL)
  · exact fun k => P.evolution_real_unitary hH hL _
  · exact integerWeight_lattice_norm_sum_le _ (kernelSpacing_ge_one _ _ _) _
  · exact kernelRetained_frequency_lt (kernelSpacing_ge_one _ _ _) _
  · exact kernelCutoff_card _ _
  · apply kernelLCU_card_log_bound _ _ hδ hδ1
    apply intervalIntegral.integral_nonneg_of_forall _ (fun t => norm_nonneg _)
    simpa only [P.start, P.finish] using! P.strict.monotone (Nat.zero_le P.count)

end FinitePiecewiseContinuousOn
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
