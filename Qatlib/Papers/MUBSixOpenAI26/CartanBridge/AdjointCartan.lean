/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.Counting
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.Matrix.Mul

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Corollary `cor:adjoint-cartan`

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`introduction.tex` (Corollary `cor:adjoint-cartan`) together with the Cartan
construction of Section 5.

Paper statement: the maximal number of pairwise same-adjoint-closed,
Killing-orthogonal Cartan subalgebras of the traceless part `sl_6(ℂ)` is three.

The paper's route:
* to each orthonormal basis `b` of `ℂ^6` attach the five traceless rank-one
  projectors `P_i - I/6`; their span `𝔥(b)` is a Cartan subalgebra of `sl_6`;
* if `b` and `c` are mutually unbiased, every `P_i - I/6` of `b` is trace
  orthogonal to every `P_j - I/6` of `c`, because
  `tr((P_i - I/6)(P_j - I/6)) = |⟨b_i, c_j⟩|² - 1/6 = 0`;
* the Killing form of `sl_6` is `K(X,Y) = 12 · tr(XY)`, so trace orthogonality
  is Killing orthogonality;
* the adjoint-Cartan correspondence of Boykin, Sitharam, Tiep, and Wocjan (2005, Thm. 5.2) turns `k` pairwise
  such Cartan subalgebras into `k` MUBs, whence four Cartans would give four MUBs.

Formalization boundary: everything except the last bullet is proved here from
the frozen MUB API. The correspondence is an explicit hypothesis
(`CartanMUBDuality`), so the corollary is proved as the implication
"correspondence ⇒ maximum is three", with attainment constructed from
`lem:three-mub-six`.
-/

set_option autoImplicit false

open scoped Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- Complex `6 × 6` matrices, the ambient algebra `M_6(ℂ)`. -/
abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) ℂ

/-- Ambient amplitude vectors of `ℂ^6` (the traceless part `sl_6(ℂ)` is not
needed as a subtype: all Cartan data below is built from traceless projectors and
the Killing form is computed on `M_6(ℂ)`). -/
abbrev State6 : Type := QState (Fin 6)

/-- `1/6` as a complex number (the trace normalization of a rank-one projector). -/
noncomputable def eps6 : ℂ := (1 / 6 : ℂ)

/-- `star eps6 = eps6`: the normalization is real. -/
theorem star_eps6 : star eps6 = eps6 := by
  norm_num [eps6]

/-- The rank-one projector `b b†`, written as `(i,j) ↦ b_i · conj(b_j)`. -/
noncomputable def vectorProjector (b : State6) : Mat6 :=
  Matrix.vecMulVec b (star b)

/-- The off-diagonal rank-one matrix `b c†`. -/
noncomputable def crossProjector (b c : State6) : Mat6 :=
  Matrix.vecMulVec b (star c)

/-- The traceless rank-one projector `b b† - I/6` attached to a unit vector `b`
(each column of a basis gives one Cartan generator). -/
noncomputable def tracelessProjector (b : State6) : Mat6 :=
  vectorProjector b - eps6 • (1 : Mat6)

/-- `tr(b b†) = ⟨b, b⟩`. -/
theorem trace_vectorProjector (b : State6) :
    (vectorProjector b).trace = Inner b b := by
  show (Matrix.vecMulVec b (star b)).trace = star b ⬝ᵥ b
  rw [Matrix.trace_vecMulVec, dotProduct_comm]

/-- `tr(b c†) = conj ⟨b, c⟩`. -/
theorem trace_crossProjector (b c : State6) :
    (crossProjector b c).trace = star (Inner b c) := by
  show (Matrix.vecMulVec b (star c)).trace = star (star b ⬝ᵥ c)
  rw [Matrix.trace_vecMulVec, Matrix.dotProduct_star, dotProduct_comm]

/-- Rank-one multiplication `(b c†)(d e†) = ⟨c, d⟩ · b e†` (written with the
`ℂ`-bilinear form `star c ⬝ᵥ d`, which is `Inner c d`). -/
theorem crossProjector_mul (b c d e : State6) :
    crossProjector b c * crossProjector d e = (star c ⬝ᵥ d) • crossProjector b e := by
  show Matrix.vecMulVec b (star c) * Matrix.vecMulVec d (star e) =
    (star c ⬝ᵥ d) • Matrix.vecMulVec b (star e)
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

/-- `tr((b b†)(c c†)) = ‖⟨b, c⟩‖²`; the key trace identity behind Cartan
Killing orthogonality (`introduction.tex`, Corollary `cor:adjoint-cartan`). -/
theorem trace_vectorProjector_mul (b c : State6) :
    (vectorProjector b * vectorProjector c).trace = (Complex.normSq (Inner b c) : ℂ) := by
  have hmul : vectorProjector b * vectorProjector c = (star b ⬝ᵥ c) • crossProjector b c := by
    show Matrix.vecMulVec b (star b) * Matrix.vecMulVec c (star c) =
      (star b ⬝ᵥ c) • Matrix.vecMulVec b (star c)
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  rw [hmul, Matrix.trace_smul, trace_crossProjector]
  show Inner b c • star (Inner b c) = (Complex.normSq (Inner b c) : ℂ)
  rw [smul_eq_mul]
  simpa [Complex.star_def] using Complex.mul_conj (Inner b c)

/-- `tr(b b† - I/6) = ⟨b, b⟩ - 1`. -/
theorem trace_tracelessProjector (b : State6) :
    (tracelessProjector b).trace = Inner b b - 1 := by
  show (vectorProjector b - eps6 • (1 : Mat6)).trace = Inner b b - 1
  simp only [Matrix.trace_sub, Matrix.trace_smul, trace_vectorProjector, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  norm_num [eps6]

/-- Expansion of the product of two traceless projectors. -/
theorem tracelessProjector_mul_expand (b c : State6) :
    tracelessProjector b * tracelessProjector c =
      vectorProjector b * vectorProjector c - eps6 • vectorProjector b -
        eps6 • vectorProjector c + eps6 • (eps6 • (1 : Mat6)) := by
  simp only [tracelessProjector]
  rw [sub_mul, mul_sub, mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.one_mul]
  abel

/-- `tr((P_b - I/6)(P_c - I/6)) = ‖⟨b, c⟩‖² - 1/6` for unit `b, c`. -/
theorem trace_tracelessProjector_mul (b c : State6)
    (hb : Inner b b = 1) (hc : Inner c c = 1) :
    (tracelessProjector b * tracelessProjector c).trace =
      (Complex.normSq (Inner b c) : ℂ) - 1 / 6 := by
  rw [tracelessProjector_mul_expand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, trace_vectorProjector_mul,
    trace_vectorProjector, Matrix.trace_one, Fintype.card_fin]
  rw [hb, hc]
  simp only [smul_eq_mul]
  norm_num [eps6]

/-- The Killing form of `sl_6(ℂ)` is `K(X,Y) = 12 · tr(XY)` (`cor:adjoint-cartan`). -/
noncomputable def killingForm (X Y : Mat6) : ℂ := 12 * (X * Y).trace

/-- Since `12 ≠ 0`, Killing orthogonality is exactly trace orthogonality. -/
theorem killingForm_eq_zero_iff (X Y : Mat6) :
    killingForm X Y = 0 ↔ (X * Y).trace = 0 := by
  rw [killingForm]
  constructor
  · intro h
    have h12 : (12 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h).resolve_left h12
  · intro h
    rw [h, mul_zero]

/-- The diagonal Cartan subalgebra attached to a basis `b`: the span of its five
traceless rank-one projectors. -/
noncomputable def diagCartan (b : Fin 6 → State6) : Submodule ℂ Mat6 :=
  Submodule.span ℂ (Set.range fun i : Fin 6 => tracelessProjector (b i))

/-- Two subspaces are Killing-orthogonal when every cross trace vanishes. -/
def KillingOrthogonal (h k : Submodule ℂ Mat6) : Prop :=
  ∀ X ∈ h, ∀ Y ∈ k, (X * Y).trace = 0

/-- A subspace is closed under the adjoint (conjugate transpose). -/
def AdjointClosed (h : Submodule ℂ Mat6) : Prop :=
  ∀ X ∈ h, Matrix.conjTranspose X ∈ h

/-- Each traceless projector is Hermitian, hence fixed by the adjoint. -/
theorem tracelessProjector_conjTranspose (b : State6) :
    Matrix.conjTranspose (tracelessProjector b) = tracelessProjector b := by
  rw [tracelessProjector, vectorProjector, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_one, star_eps6]
  simp

/-- `𝔥(b)` is closed under the adjoint. -/
theorem diagCartan_adjointClosed (b : Fin 6 → State6) :
    AdjointClosed (diagCartan b) := by
  intro X hX
  refine Submodule.span_induction (p := fun X _ => Matrix.conjTranspose X ∈ diagCartan b)
    ?_ ?_ ?_ ?_ hX
  · rintro X ⟨i, rfl⟩
    show Matrix.conjTranspose (tracelessProjector (b i)) ∈ diagCartan b
    rw [tracelessProjector_conjTranspose]
    exact Submodule.subset_span ⟨i, rfl⟩
  · show Matrix.conjTranspose (0 : Mat6) ∈ diagCartan b
    rw [Matrix.conjTranspose_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    show Matrix.conjTranspose (x + y) ∈ diagCartan b
    rw [Matrix.conjTranspose_add]
    exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    show Matrix.conjTranspose (r • x) ∈ diagCartan b
    rw [Matrix.conjTranspose_smul]
    exact Submodule.smul_mem _ _ hx

/-- Orthonormal columns are unit vectors. -/
theorem inner_self_of_orthonormal {k : ℕ} {B : Family k} (hB : IsFamily B)
    (r : Fin k) (i : Fin 6) : Inner (B r i) (B r i) = 1 := by
  rw [hB.1 r i i, ite_eq_left rfl]

/-- Corollary `cor:adjoint-cartan`, constructive half: mutually unbiased bases
give pairwise Killing-orthogonal, same-adjoint-closed Cartan subalgebras. -/
theorem diagCartan_killingOrthogonal {k : ℕ} {B : Family k} (hB : IsFamily B)
    {r s : Fin k} (hrs : r ≠ s) :
    KillingOrthogonal (diagCartan (B r)) (diagCartan (B s)) := by
  intro X hX Y hY
  refine Submodule.span_induction₂ (p := fun X Y _ _ => (X * Y).trace = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hX hY
  · rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    show (tracelessProjector (B r i) * tracelessProjector (B s j)).trace = 0
    rw [trace_tracelessProjector_mul (B r i) (B s j)
        (inner_self_of_orthonormal hB r i) (inner_self_of_orthonormal hB s j),
      hB.2 r s hrs i j]
    push_cast
    norm_num
  · intro y _
    show ((0 : Mat6) * y).trace = 0
    rw [Matrix.zero_mul, Matrix.trace_zero]
  · intro x _
    show (x * (0 : Mat6)).trace = 0
    rw [Matrix.mul_zero, Matrix.trace_zero]
  · intro x y z _ _ _ hpx hpz
    show ((x + y) * z).trace = 0
    rw [Matrix.add_mul, Matrix.trace_add, hpx, hpz, add_zero]
  · intro x y z _ _ _ hpx hpz
    show (x * (y + z)).trace = 0
    rw [Matrix.mul_add, Matrix.trace_add, hpx, hpz, add_zero]
  · intro r x y _ _ hp
    show ((r • x) * y).trace = 0
    rw [Matrix.smul_mul, Matrix.trace_smul, hp, smul_zero]
  · intro r x y _ _ hp
    show (x * (r • y)).trace = 0
    rw [Matrix.mul_smul, Matrix.trace_smul, hp, smul_zero]

/-- A family of `k` pairwise Killing-orthogonal, same-adjoint-closed Cartan
subalgebras (each the diagonal Cartan of a basis). -/
def HasCartanFamily (k : ℕ) : Prop :=
  ∃ B : Family k, IsFamily B ∧
    (∀ r, AdjointClosed (diagCartan (B r))) ∧
    ∀ r s, r ≠ s → KillingOrthogonal (diagCartan (B r)) (diagCartan (B s))

/-- Three pairwise Killing-orthogonal, same-adjoint-closed Cartan subalgebras
exist (from `lem:three-mub-six`). -/
theorem hasCartanFamily_three : HasCartanFamily 3 := by
  obtain ⟨B, hB⟩ := three_mub_bases_in_dimension_six
  exact ⟨B, hB, fun r => diagCartan_adjointClosed (B r),
    fun _ _ hrs => diagCartan_killingOrthogonal hB hrs⟩

/-- The maximum number of pairwise Killing-orthogonal, same-adjoint-closed
Cartan subalgebras of the traceless part is `k`. -/
def CartanMaximumIs (k : ℕ) : Prop :=
  HasCartanFamily k ∧ ∀ m : ℕ, HasCartanFamily m → m ≤ k

/-- The adjoint-Cartan correspondence of Boykin, Sitharam, Tiep, and Wocjan (2005, Thm. 5.2) in the direction used
for the upper bound: `m` pairwise Killing-orthogonal, same-adjoint-closed Cartan
subalgebras of `sl_6(ℂ)` yield `m` pairwise unbiased bases. -/
structure CartanMUBDuality where
  cartanToFamily : ∀ m : ℕ, HasCartanFamily m → HasMUBFamily m

/-- Corollary `cor:adjoint-cartan`, upper bound: under the adjoint-Cartan
correspondence and the exclusion of four MUBs, there are at most three pairwise
Killing-orthogonal, same-adjoint-closed Cartan subalgebras. -/
theorem adjoint_cartan_le_three (D : CartanMUBDuality) (hno : NoFourMUBs)
    {m : ℕ} (hm : HasCartanFamily m) : m ≤ 3 :=
  le_three_of_no_four hno (D.cartanToFamily m hm)

/-- Corollary `cor:adjoint-cartan`: the maximum number of pairwise
same-adjoint-closed, Killing-orthogonal Cartan subalgebras of the traceless part
is three. -/
theorem adjoint_cartan_max_three (D : CartanMUBDuality) (hno : NoFourMUBs) :
    CartanMaximumIs 3 :=
  ⟨hasCartanFamily_three, fun _ hm => adjoint_cartan_le_three D hno hm⟩

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
