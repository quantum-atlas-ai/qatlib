/-
Copyright (c) 2026 qatlas-lean-lib contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic

@[expose] public section



/-! # Checked stability and conditional entrywise bounds for arXiv:1704.06774v3.
No quantum walk, graph, or measured runtime is constructed by the scalar cost definitions.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.TreeSizeEst17.MainResults

/-- §4 (p. 12) repetition count used in the proof of Lemma 1: `t = ⌈(1/C)·log²(1/ε_min)⌉`
estimation runs, each costing `⌈(1/δ_min)·log(2t/ε_min)⌉` repetitions of controlled-`U`. -/
noncomputable def lemmaOneRepetitions (C δmin εmin : ℝ) : ℝ :=
  let t : ℝ := Nat.ceil ((1 / C) * (Real.log (1 / εmin)) ^ 2)
  t * Nat.ceil ((1 / δmin) * Real.log (2 * t / εmin))

/-- §5 (p. 13): queries charged by the local diffusion step `D_u` of `R_A`/`R_B`: two queries
for the in/out degrees and at most `d` queries for the neighbour vertices, i.e. `d + 2`. -/
noncomputable def localDiffusionQueries (d : ℝ) : ℝ := d + 2

/-- §5 (p. 13): gates charged by the local diffusion step: `O(d)` local unitaries, each on an
`O(log V)`-qubit register, i.e. proportional to `d log V`. -/
noncomputable def localDiffusionGates (d V : ℝ) : ℝ := d * Real.log V

/-- **Lemma 3** (arXiv:1704.06774v3, p. 5, §5 p. 12–13).

The reflections `R_A` and `R_B` of §3.2 are implemented with `O(d)` queries and `O(d log V)`
non-query gates.  We record the paper's protocol costs `localDiffusionQueries d = d + 2` and
`localDiffusionGates d V = d log V` and prove that they are `O(d)` resp. `O(d log V)`.

The circuit synthesis itself (the unitaries `U_j`, the conditional XOR steps and the diffusion
`D = U_ψ(I − 2|0⟩⟨0|)U_ψ⁻¹` of §5) is the algorithmic content and is not modelled here; the
statement below is the resulting cost accounting, fully proved. -/
theorem source_lemma_three
    (d V : ℝ) (hd : 1 ≤ d) (_hV : 1 ≤ V) :
    (∃ cq : ℝ, 0 < cq ∧ localDiffusionQueries d ≤ cq * d) ∧
      ∃ cg : ℝ, 0 < cg ∧ localDiffusionGates d V ≤ cg * d * Real.log V := by
  constructor
  · refine ⟨3, by norm_num, ?_⟩
    unfold localDiffusionQueries
    nlinarith [hd]
  · refine ⟨1, by norm_num, ?_⟩
    unfold localDiffusionGates
    nlinarith

/-- §3.2 (p. 5): the parameter `C = 4/9` is the overlap lower bound supplied by Lemma 4. -/
noncomputable def lemmaOneOverlap : ℝ := 4 / 9

/-- Algorithm 1 (p. 6) applied to Lemma 1 with `C = 4/9`, `δ_min = δ^{1.5}/(24√(3nT₀))`,
`ε_min = ε`: the number of repetitions of controlled-`R_B R_A`. -/
noncomputable def dagAlgorithmRepetitions (n T0 δ ε : ℝ) : ℝ :=
  lemmaOneRepetitions lemmaOneOverlap (δ ^ (1.5 : ℝ) / (24 * Real.sqrt (3 * n * T0))) ε

/-- Total query cost of Algorithm 1 (p. 6): a controlled-`R_B R_A` step costs `O(d)` queries
(Lemma 3) and is repeated `dagAlgorithmRepetitions` times. -/
noncomputable def dagAlgorithmQueries (n T0 δ ε d : ℝ) : ℝ :=
  dagAlgorithmRepetitions n T0 δ ε * localDiffusionQueries d

/-! ## Lemma 16  — stability of `1/sin²(θ/2)` (fully proved) -/

/-- **Lemma 16** (arXiv:1704.06774v3, p. 19, proved p. 19–20).

If `θ̂ ∈ (0, π/2)` and `|θ − θ̂| ≤ ε sin(θ/2)` for some `ε ∈ (0,1)` (and `θ ∈ (0,π)` so that
`sin(θ/2) > 0`), then `|1/sin²(θ̂/2) − 1/sin²(θ/2)| ≤ 6ε / sin²(θ/2)`.

Proof route (as in the paper): `σ = sin(θ/2)`, `t = sin(θ̂/2)`.  `sin` is 1-Lipschitz, so
`|t − σ| ≤ εσ/2`, hence `σ(1−ε/2) ≤ t ≤ σ(1+ε/2)`.  Then `|σ² − t²| ≤ 6ε t²` (from
`t ≤ σ(1+ε/2)` and `6(1−ε/2)² ≥ 1+ε/4` for `ε ∈ (0,1)`), giving both one-sided bounds. -/
theorem source_lemma_sixteen
    (θ θhat ε : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hθh0 : 0 < θhat) (hθhπ : θhat < Real.pi / 2)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hclose : |θ - θhat| ≤ ε * Real.sin (θ / 2)) :
    |1 / Real.sin (θhat / 2) ^ 2 - 1 / Real.sin (θ / 2) ^ 2|
      ≤ 6 * ε / Real.sin (θ / 2) ^ 2 := by
  set s := Real.sin (θ / 2) with hs_def
  set t := Real.sin (θhat / 2) with ht_def
  have hs_pos : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have ht_pos : 0 < t := by
    rw [ht_def]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hclose' : |θ - θhat| ≤ ε * s := by rw [hs_def]; exact hclose
  -- `|t − s| ≤ ε s / 2` from the Lipschitz bound for `sin`
  have hdist : |t - s| ≤ ε * s / 2 := by
    have h1 : |t - s| ≤ |θhat / 2 - θ / 2| := by
      rw [ht_def, hs_def]
      exact Real.abs_sin_sub_sin_le _ _
    have h2 : |θhat / 2 - θ / 2| = |θ - θhat| / 2 := by
      have hq : θhat / 2 - θ / 2 = (θhat - θ) / 2 := by ring
      rw [hq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [abs_sub_comm]
    rw [h2] at h1
    nlinarith [h1, hclose', hε0.le]
  -- two-sided bounds on `t`
  have ht_le : t ≤ s * (1 + ε / 2) := by
    have h := (abs_le.mp hdist).2
    nlinarith [hs_pos]
  have ht_ge : s * (1 - ε / 2) ≤ t := by
    have h := (abs_le.mp hdist).1
    nlinarith [hs_pos]
  -- the elementary polynomial inequality `1 + ε/4 ≤ 6 (1 − ε/2)²` on `(0,1)`
  have hsix : (1 : ℝ) + ε / 4 ≤ 6 * (1 - ε / 2) ^ 2 := by
    nlinarith [hε0, hε1]
  -- `|s² − t²| ≤ 6 ε t²`
  have hT2lower : s ^ 2 * (1 - ε / 2) ^ 2 ≤ t ^ 2 := by
    have hge := mul_le_mul ht_ge ht_ge
      (mul_nonneg hs_pos.le (by linarith [hε1])) ht_pos.le
    nlinarith [hge]
  have hbound_abs : |s ^ 2 - t ^ 2| ≤ 6 * ε * t ^ 2 := by
    have hfac : s ^ 2 - t ^ 2 = (s - t) * (s + t) := by ring
    have h1 : |s - t| ≤ ε * s / 2 := by rw [abs_sub_comm]; exact hdist
    have h2 : |s + t| ≤ s * (2 + ε / 2) := by
      rw [abs_of_pos (by linarith [hs_pos, ht_pos])]
      nlinarith [ht_le, hs_pos]
    have h3 : |s ^ 2 - t ^ 2| ≤ (ε * s / 2) * (s * (2 + ε / 2)) := by
      rw [hfac, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (mul_nonneg hε0.le hs_pos.le) (by norm_num))
    have h4 : (ε * s / 2) * (s * (2 + ε / 2)) = ε * s ^ 2 * (1 + ε / 4) := by ring
    have h5 : ε * s ^ 2 * (1 + ε / 4) ≤ ε * s ^ 2 * (6 * (1 - ε / 2) ^ 2) := by
      have hεs : 0 ≤ ε * s ^ 2 := mul_nonneg hε0.le (sq_nonneg s)
      exact mul_le_mul_of_nonneg_left hsix hεs
    have h6 : ε * s ^ 2 * (6 * (1 - ε / 2) ^ 2) = 6 * ε * (s ^ 2 * (1 - ε / 2) ^ 2) := by
      ring
    have h7 : 6 * ε * (s ^ 2 * (1 - ε / 2) ^ 2) ≤ 6 * ε * t ^ 2 := by
      exact mul_le_mul_of_nonneg_left hT2lower (by nlinarith [hε0])
    calc |s ^ 2 - t ^ 2| ≤ (ε * s / 2) * (s * (2 + ε / 2)) := h3
      _ = ε * s ^ 2 * (1 + ε / 4) := h4
      _ ≤ ε * s ^ 2 * (6 * (1 - ε / 2) ^ 2) := h5
      _ = 6 * ε * (s ^ 2 * (1 - ε / 2) ^ 2) := h6
      _ ≤ 6 * ε * t ^ 2 := h7
  have hle_sq : s ^ 2 - t ^ 2 ≤ 6 * ε * t ^ 2 := (abs_le.mp hbound_abs).2
  have hge_sq : t ^ 2 - s ^ 2 ≤ 6 * ε * t ^ 2 := by
    have h := (abs_le.mp hbound_abs).1
    linarith
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs_pos 2
  have ht2 : (0 : ℝ) < t ^ 2 := pow_pos ht_pos 2
  have hden : (0 : ℝ) < t ^ 2 * s ^ 2 := mul_pos ht2 hs2
  -- `1/t² − 1/s² ≤ 6ε/s²`
  have hfirst : 1 / t ^ 2 - 1 / s ^ 2 ≤ 6 * ε / s ^ 2 := by
    rw [div_sub_div (1:ℝ) (1:ℝ) (ne_of_gt ht2) (ne_of_gt hs2)]
    rw [div_le_div_iff₀ hden hs2]
    have := mul_le_mul_of_nonneg_right hle_sq (le_of_lt hs2)
    nlinarith [this]
  -- `1/s² − 1/t² ≤ 6ε/s²`
  have hsecond : 1 / s ^ 2 - 1 / t ^ 2 ≤ 6 * ε / s ^ 2 := by
    rw [div_sub_div (1:ℝ) (1:ℝ) (ne_of_gt hs2) (ne_of_gt ht2)]
    rw [div_le_div_iff₀ (mul_pos hs2 ht2) hs2]
    have := mul_le_mul_of_nonneg_right hge_sq (le_of_lt hs2)
    nlinarith [this]
  rw [abs_le]
  constructor <;> linarith [hfirst, hsecond]

/-- The discriminant matrix `L = M_A^* M_B` of §6.1 / Lemma 22 (p. 29): for real matrices the
adjoint is the transpose. -/
def discriminantMatrix {A B : ℕ} (Ma : Matrix (Fin A) (Fin B) ℝ) (Mb : Matrix (Fin A) (Fin B) ℝ) :
    Matrix (Fin B) (Fin B) ℝ := Matrix.transpose Ma * Mb

/-- **Lemma 22** (arXiv:1704.06774v3, p. 29, §6.8), definitional form: the discriminant matrix
equals `M_A^* M_B`.  For real matrices `M_A^* = M_Aᵀ`, so this is the definition unfolding. -/
theorem source_lemma_twentytwo {A B : ℕ} (Ma Mb : Matrix (Fin A) (Fin B) ℝ) :
    discriminantMatrix Ma Mb = Matrix.transpose Ma * Mb := rfl

/-! ## Lemma 14  — entrywise two-sided bounds for `K` -/

/-- Core inequality of Lemma 14 (arXiv:1704.06774v3, p. 17, §6.8): the entrywise two-sided bound
`α² a[i] a[j] ≤ K[i,j] ≤ (α² + n) a[i] a[j]`, derived from the Lemma 23 form `hK` and the
Corollary 2 sandwich `hlo`/`hhi`. -/
theorem lemma_fourteen_core
    (A : ℕ) (alpha n d1 : ℝ) (a : Fin A → ℝ) (N K : Matrix (Fin A) (Fin A) ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hK : ∀ i j, K i j = a i * a j * (N i j - (d1)⁻¹))
    (hlo : ∀ i j, alpha ^ 2 ≤ N i j - (d1)⁻¹)
    (hhi : ∀ i j, N i j - (d1)⁻¹ ≤ alpha ^ 2 + n) :
    ∀ i j, alpha ^ 2 * a i * a j ≤ K i j ∧ K i j ≤ (alpha ^ 2 + n) * a i * a j := by
  intro i j
  rw [hK i j]
  have hnn : 0 ≤ a i * a j := mul_nonneg (ha i) (ha j)
  have h1 : alpha ^ 2 * (a i * a j) ≤ (N i j - (d1)⁻¹) * (a i * a j) :=
    mul_le_mul_of_nonneg_right (hlo i j) hnn
  have h2 : (N i j - (d1)⁻¹) * (a i * a j) ≤ (alpha ^ 2 + n) * (a i * a j) :=
    mul_le_mul_of_nonneg_right (hhi i j) hnn
  constructor <;> nlinarith [h1, h2]

/-- **Lemma 14** (arXiv:1704.06774v3, p. 17, §6.8).

For all `i, j ∈ [A]`: `α² a[i] a[j] ≤ K[i,j] ≤ (α² + n) a[i] a[j]`, and when `i = 1` or
`j = 1` one has `K[i,j] = α² a[i] a[j]`.

The hypotheses `hK` (Lemma 23: `K[i,j] = a[i]a[j](N[i,j] − 1/d₁)`), `hlo`/`hhi` (the Corollary 2
bounds `α² ≤ N[i,j] − 1/d₁ ≤ α² + n`) and `hbound` (Corollary 1's first-row/column identity) are
exactly the paper's inputs, so the proof below is the paper's deduction. -/
theorem source_lemma_fourteen
    (A : ℕ) (alpha n d1 : ℝ) (a : Fin A → ℝ) (N K : Matrix (Fin A) (Fin A) ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hK : ∀ i j, K i j = a i * a j * (N i j - (d1)⁻¹))
    (hlo : ∀ i j, alpha ^ 2 ≤ N i j - (d1)⁻¹)
    (hhi : ∀ i j, N i j - (d1)⁻¹ ≤ alpha ^ 2 + n)
    (hbound : ∀ i j, (i.val = 0 ∨ j.val = 0) → K i j = alpha ^ 2 * a i * a j) :
    (∀ i j, alpha ^ 2 * a i * a j ≤ K i j ∧ K i j ≤ (alpha ^ 2 + n) * a i * a j) ∧
      (∀ i j, (i.val = 0 ∨ j.val = 0) → K i j = alpha ^ 2 * a i * a j) :=
  ⟨lemma_fourteen_core A alpha n d1 a N K ha hK hlo hhi, hbound⟩

/-! ## Lemma 15  — `K` bounds in terms of `d`, and the top eigenvalue -/

/-- **Lemma 15**, Eq. (6) (arXiv:1704.06774v3, p. 17, §6.3).

The entries `K[i,j]` satisfy `α² √(d_i d_j) ≤ K[i,j] ≤ √(d_i d_j)(α² + n)`.

Obtained from Lemma 14 (`source_lemma_fourteen`) using `a[i] a[j] = √(d_i d_j)` (`haa`). -/
theorem source_lemma_fifteen
    (A : ℕ) (alpha n d1 : ℝ) (a d : Fin A → ℝ) (N K : Matrix (Fin A) (Fin A) ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hK : ∀ i j, K i j = a i * a j * (N i j - (d1)⁻¹))
    (hlo : ∀ i j, alpha ^ 2 ≤ N i j - (d1)⁻¹)
    (hhi : ∀ i j, N i j - (d1)⁻¹ ≤ alpha ^ 2 + n)
    (haa : ∀ i j, a i * a j = Real.sqrt (d i * d j)) :
    ∀ i j, alpha ^ 2 * Real.sqrt (d i * d j) ≤ K i j ∧
      K i j ≤ Real.sqrt (d i * d j) * (alpha ^ 2 + n) := by
  intro i j
  have h := lemma_fourteen_core A alpha n d1 a N K ha hK hlo hhi i j
  have hh := haa i j
  constructor
  · nlinarith [h.1, hh]
  · have h2 := h.2
    have e : (alpha ^ 2 + n) * a i * a j = Real.sqrt (d i * d j) * (alpha ^ 2 + n) := by
      rw [← hh]; ring
    rw [e] at h2
    exact h2


end Qatlib.Papers.TreeSizeEst17.MainResults
