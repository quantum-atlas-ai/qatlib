/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# PauliAlgebra source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.VarianceScaling.PauliAlgebra

/-! ## Finite-ensemble algebra: expectation, variance, covariance -/

variable {Θ : Type*} [Fintype Θ]

/-- Covariance of two real functions of a finite parameter ensemble,
`Cov_θ[f,g] = E_θ[(f − E f)(g − E g)]`. -/
def cov (pθ : FinDist Θ) (f g : Θ → ℝ) : ℝ :=
  pθ.expect (fun θ => (f θ - pθ.expect f) * (g θ - pθ.expect g))

/-- Expectation is additive. -/
theorem expect_sub (p : FinDist Θ) (f g : Θ → ℝ) :
    p.expect (fun θ => f θ - g θ) = p.expect f - p.expect g := by
  unfold FinDist.expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun θ _ => by ring)

/-- Expectation is additive (sum form). -/
theorem expect_add (p : FinDist Θ) (f g : Θ → ℝ) :
    p.expect (fun θ => f θ + g θ) = p.expect f + p.expect g := by
  unfold FinDist.expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun θ _ => by ring)

/-- Expectation of a constant is the constant (the masses sum to one). -/
theorem expect_const (p : FinDist Θ) (c : ℝ) : p.expect (fun _ => c) = c := by
  unfold FinDist.expect
  change (∑ x, p.prob x * c) = c
  rw [← Finset.sum_mul, p.sum_one, one_mul]

/-- Expectation commutes with scalar multiplication. -/
theorem expect_scale (p : FinDist Θ) (c : ℝ) (f : Θ → ℝ) :
    p.expect (fun θ => c * f θ) = c * p.expect f := by
  unfold FinDist.expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun θ _ => by ring)

/-- **Variance is translation-invariant:** `Var[f + c] = Var[f]`. -/
theorem variance_shift (p : FinDist Θ) (f : Θ → ℝ) (c : ℝ) :
    p.variance (fun θ => f θ + c) = p.variance f := by
  have hE : p.expect (fun θ => f θ + c) = p.expect f + c := by
    rw [expect_add, expect_const]
  unfold FinDist.variance
  rw [hE]
  unfold FinDist.expect
  exact Finset.sum_congr rfl (fun θ _ => by ring)

/-- **Bilinear expansion of the variance:** `Var[f − 2g] = Var f + 4 Var g − 4 Cov(f,g)`.
This is the algebraic content of Supplemental Proposition 3, Eq. (297). -/
theorem variance_sub2 (p : FinDist Θ) (f g : Θ → ℝ) :
    p.variance (fun θ => f θ - 2 * g θ)
      = p.variance f + 4 * p.variance g - 4 * cov p f g := by
  have hE : p.expect (fun θ => f θ - 2 * g θ) = p.expect f - 2 * p.expect g := by
    rw [show (fun θ => f θ - 2 * g θ) = (fun θ => f θ - (2 * g θ)) from rfl, expect_sub,
      expect_scale]
  have hfun : (fun θ => ((f θ - 2 * g θ) - p.expect (fun θ => f θ - 2 * g θ)) ^ 2)
      = (fun θ => (f θ - p.expect f) ^ 2 + 4 * (g θ - p.expect g) ^ 2
          - 4 * ((f θ - p.expect f) * (g θ - p.expect g))) := by
    funext θ
    rw [hE]
    ring
  unfold FinDist.variance cov
  rw [hfun]
  have hlin : p.expect (fun θ => (f θ - p.expect f) ^ 2 + 4 * (g θ - p.expect g) ^ 2
        - 4 * ((f θ - p.expect f) * (g θ - p.expect g)))
      = p.expect (fun θ => (f θ - p.expect f) ^ 2)
        + 4 * p.expect (fun θ => (g θ - p.expect g) ^ 2)
        - 4 * p.expect (fun θ => (f θ - p.expect f) * (g θ - p.expect g)) := by
    rw [show (fun θ => (f θ - p.expect f) ^ 2 + 4 * (g θ - p.expect g) ^ 2
          - 4 * ((f θ - p.expect f) * (g θ - p.expect g)))
        = (fun θ => ((f θ - p.expect f) ^ 2 + 4 * (g θ - p.expect g) ^ 2)
            - (4 * ((f θ - p.expect f) * (g θ - p.expect g)))) from rfl,
      expect_sub, expect_add, expect_scale, expect_scale]
  rw [hlin]

/-- **Supplemental Proposition 3, Eq. (297).**  For the MMD loss of the Pauli-rotation ansatz
`L(θ) = M(ρθ,ρθ) − 2 M(ρθ,ρp̃) + M(ρp̃,ρp̃)`, whose last term is `θ`-independent, the variance over
the parameter ensemble is
`Var[M(ρθ,ρθ)] + 4 Var[M(ρθ,ρp̃)] − 4 Cov[M(ρθ,ρθ), M(ρθ,ρp̃)]`. -/
theorem mmd_variance (pθ : FinDist Θ)
    (mqq mqp : Θ → ℝ) (c : ℝ) :
    pθ.variance (fun θ => mqq θ - 2 * mqp θ + c)
      = pθ.variance mqq + 4 * pθ.variance mqp - 4 * cov pθ mqq mqp := by
  rw [show (fun θ => mqq θ - 2 * mqp θ + c) = (fun θ => (mqq θ - 2 * mqp θ) + c) from rfl,
    variance_shift, variance_sub2]

/-! ## Eq. (299): independence kills the covariance -/

/-- The product of two finite distributions. -/
def prodDist {X Y : Type*} [Fintype X] [Fintype Y] (p : FinDist X) (q : FinDist Y) :
    FinDist (X × Y) where
  prob z := p.prob z.1 * q.prob z.2
  nonneg z := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, p.sum_one, q.sum_one, mul_one]

/-- The mass function of the product distribution, by definition. -/
@[simp] theorem prodDist_prob {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FinDist X) (q : FinDist Y) (z : X × Y) :
    (prodDist p q).prob z = p.prob z.1 * q.prob z.2 := rfl

/-- **Factorisation of the expectation** under a product distribution. -/
theorem expect_prodDist {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FinDist X) (q : FinDist Y) (f : X → ℝ) (g : Y → ℝ) :
    (prodDist p q).expect (fun z => f z.1 * g z.2) = p.expect f * q.expect g := by
  unfold FinDist.expect
  rw [Fintype.sum_prod_type]
  simp only [prodDist_prob]
  have hfac : ∀ a b, (p.prob a * q.prob b) * (f a * g b)
      = (p.prob a * f a) * (q.prob b * g b) := fun a b => by ring
  simp only [hfac]
  rw [← Fintype.sum_mul_sum]

/-- **Supplemental Proposition 3, Eq. (299).**  Functions of independent coordinates of a product
ensemble are uncorrelated: `Cov[f(θ₁), g(θ₂)] = 0`.  This is the mechanism behind the paper's
statement that the covariance between the purity and overlap terms vanishes because they depend on
independent parameter blocks. -/
theorem indep_cov_zero {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (p : FinDist X) (q : FinDist Y) (f : X → ℝ) (g : Y → ℝ) :
    cov (prodDist p q) (fun z => f z.1) (fun z => g z.2) = 0 := by
  have h1 : (prodDist p q).expect (fun z => f z.1) = p.expect f := by
    have h := expect_prodDist p q f (fun _ => (1 : ℝ))
    rw [expect_const] at h
    simpa using h
  have h2 : (prodDist p q).expect (fun z => g z.2) = q.expect g := by
    have h := expect_prodDist p q (fun _ => (1 : ℝ)) g
    rw [expect_const] at h
    simpa using h
  have hz1 : p.expect (fun a => f a - p.expect f) = 0 := by
    simpa only [FinDist.expect] using FinDist.sum_sub_mean p f
  have hz2 : q.expect (fun b => g b - q.expect g) = 0 := by
    simpa only [FinDist.expect] using FinDist.sum_sub_mean q g
  unfold cov
  rw [h1, h2]
  rw [show (prodDist p q).expect (fun z => (f z.1 - p.expect f) * (g z.2 - q.expect g))
      = p.expect (fun a => f a - p.expect f) * q.expect (fun b => g b - q.expect g) from
    expect_prodDist p q (fun a => f a - p.expect f) (fun b => g b - q.expect g)]
  rw [hz1, hz2, mul_zero]

/-! ## Eqs. (298) and (300): the Clifford light-cone formulas -/

/-- The coefficient `c_σ(A) = (1 − p_σ)^{n−|A|} p_σ^{|A|}` of Eq. (298). -/
def cSigmaCoef (n : ℕ) (pσ : ℝ) (A : Finset (Fin n)) : ℝ :=
  (1 - pσ) ^ (n - A.card) * pσ ^ A.card

/-- The average light cone `Δ^{(avg)}_B = E_{αc∼Dc}[Δ_B(αc)]` of Eq. (296), with `Dc` uniform on
the `2^M` Clifford-angle settings encoded as `Fin M → Bool`. -/
def avgLightCone {M : ℕ} (Δ : (Fin M → Bool) → ℕ) : ℝ :=
  ((2 : ℝ) ^ M)⁻¹ * ∑ αc : Fin M → Bool, (Δ αc : ℝ)

/-- The overlap variance of Eq. (298):
`Var_θ[M(ρθ,ρp̃)] = Σ_{A≠∅} (c_σ(A) z_A(P̃))² E_{αc}[(1/3)^{Δ_{Z_A}(αc)}]`. -/
def overlapVariance (n M : ℕ) (pσ : ℝ) (z : Finset (Fin n) → ℝ)
    (Δ : Finset (Fin n) → (Fin M → Bool) → ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.Nonempty),
    (cSigmaCoef n pσ A * z A) ^ 2 *
      (((2 : ℝ) ^ M)⁻¹ * ∑ αc : Fin M → Bool, (1 / 3 : ℝ) ^ (Δ A αc))

/-- **Supplemental Proposition 3, Eq. (298), nonnegativity.**  Every summand of the overlap
variance is a square times a nonnegative light-cone factor, so `overlapVariance ≥ 0` — the
elementary side-condition of Eq. (298). -/
theorem overlap_nonneg (n M : ℕ) (pσ : ℝ) (z : Finset (Fin n) → ℝ)
    (Δ : Finset (Fin n) → (Fin M → Bool) → ℕ) : 0 ≤ overlapVariance n M pσ z Δ := by
  unfold overlapVariance
  refine Finset.sum_nonneg fun A _ => ?_
  have hcone : (0 : ℝ) ≤ ((2 : ℝ) ^ M)⁻¹ * ∑ αc : Fin M → Bool, (1 / 3 : ℝ) ^ (Δ A αc) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  exact mul_nonneg (sq_nonneg _) hcone

/-- **Supplemental Proposition 3, Eq. (298), Clifford-average form.**  The paper states the
overlap variance as a single weighted sum over nonempty `A` of `(c_σ(A) z_A)²` times the Clifford
average of `(1/3)^{Δ_{Z_A}}`.  Exchanging the `A`-sum with the Clifford sum shows that the same
quantity is the uniform average over Clifford settings `αc` of the *total* weighted Fourier mass
`Σ_{A≠∅} (c_σ(A) z_A)² (1/3)^{Δ_{Z_A}(αc)}` — i.e. the `D_c`-average commutes with the Fourier
sum, as used in Eq. (298). -/
theorem overlap_average (n M : ℕ) (pσ : ℝ) (z : Finset (Fin n) → ℝ)
    (Δ : Finset (Fin n) → (Fin M → Bool) → ℕ) :
    overlapVariance n M pσ z Δ
      = ((2 : ℝ) ^ M)⁻¹ * ∑ αc : Fin M → Bool,
          ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.Nonempty),
            (cSigmaCoef n pσ A * z A) ^ 2 * (1 / 3 : ℝ) ^ (Δ A αc) := by
  have hL : overlapVariance n M pσ z Δ
      = ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.Nonempty),
          ∑ αc : Fin M → Bool,
            ((2 : ℝ) ^ M)⁻¹ *
              ((cSigmaCoef n pσ A * z A) ^ 2 * (1 / 3 : ℝ) ^ (Δ A αc)) := by
    unfold overlapVariance
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun αc _ => by ring
  have hR : ((2 : ℝ) ^ M)⁻¹ * ∑ αc : Fin M → Bool,
        ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.Nonempty),
          (cSigmaCoef n pσ A * z A) ^ 2 * (1 / 3 : ℝ) ^ (Δ A αc)
      = ∑ αc : Fin M → Bool,
          ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.Nonempty),
            ((2 : ℝ) ^ M)⁻¹ *
              ((cSigmaCoef n pσ A * z A) ^ 2 * (1 / 3 : ℝ) ^ (Δ A αc)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun αc _ => ?_
    rw [Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]

/-- The `D̃_c(σ)`-weighted purity lower-bound expression of Eq. (300),
`E_{(A,αc),(A′,α′c)∼D̃c}[(1/3)^{Δ+Δ′} ((1/5)^{9|sup∩sup|}(1/3)^{n(·)} − 1)]`, written out with
the uniform Clifford average over `Fin M → Bool` and the `c_σ`-weighted choice of `A, A′`. -/
def purityLower (n M : ℕ) (pσ : ℝ)
    (Δ : Finset (Fin n) → (Fin M → Bool) → ℕ)
    (supp : Finset (Fin n) → (Fin M → Bool) → Finset (Fin n))
    (diffCnt : Finset (Fin n) → (Fin M → Bool) → Finset (Fin n) → (Fin M → Bool) → ℕ) : ℝ :=
  ∑ A : Finset (Fin n), ∑ B : Finset (Fin n), ∑ αc : Fin M → Bool, ∑ α'c : Fin M → Bool,
    (((2 : ℝ) ^ M)⁻¹ * ((2 : ℝ) ^ M)⁻¹) *
      (cSigmaCoef n pσ A * cSigmaCoef n pσ B) *
      ((1 / 3 : ℝ) ^ (Δ A αc + Δ B α'c)) *
      (((1 / 5 : ℝ) ^ (9 * (supp A αc ∩ supp B α'c).card) *
        (1 / 3 : ℝ) ^ diffCnt A αc B α'c) - 1)

/-- **The bracket of Eq. (300) is nonpositive.**  Both bases `1/5` and `1/3` are at most one, so
whenever the intersection count and the disagreement count are nonnegative integers the bracket
`(1/5)^{9|sup∩sup|}(1/3)^{n(·)} − 1` never exceeds zero.  This matters because it shows that the
printed final `≥ 0` in Eq. (300) cannot follow from the printed expression when the `D̃_c` weights
are nonnegative; see `suppProp3_gap`. -/
theorem bracket_nonpos (c k : ℕ) :
    (1 / 5 : ℝ) ^ (9 * c) * (1 / 3 : ℝ) ^ k - 1 ≤ 0 := by
  have h1 : (1 / 5 : ℝ) ^ (9 * c) ≤ 1 := by
    apply pow_le_one₀ <;> norm_num
  have h2 : (1 / 3 : ℝ) ^ k ≤ 1 := by
    apply pow_le_one₀ <;> norm_num
  have h3 : (0 : ℝ) ≤ (1 / 5 : ℝ) ^ (9 * c) := by positivity
  have h4 : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ k := by positivity
  have h5 : (1 / 5 : ℝ) ^ (9 * c) * (1 / 3 : ℝ) ^ k ≤ 1 := by
    calc (1 / 5 : ℝ) ^ (9 * c) * (1 / 3 : ℝ) ^ k ≤ 1 * 1 :=
          mul_le_mul h1 h2 h4 (by norm_num)
      _ = 1 := by ring
  linarith

/-! ## Theorem 3: light cone and Fourier mass imply polynomial trainability -/

/-- `f = Ω(1/poly(n))`: there are `d : ℕ` and `c > 0` with `c n^{−d} ≤ f n` eventually. -/
def IsPolyOmega (f : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in Filter.atTop, c * (n : ℝ) ^ (-(d : ℤ)) ≤ f n

/-- **Products of polynomially large sequences are polynomially large.** -/
theorem IsPolyOmega.mul {f g : ℕ → ℝ} (hf : IsPolyOmega f) (hg : IsPolyOmega g) :
    IsPolyOmega (fun n => f n * g n) := by
  obtain ⟨d1, c1, hc1, h1⟩ := hf
  obtain ⟨d2, c2, hc2, h2⟩ := hg
  refine ⟨d1 + d2, c1 * c2, mul_pos hc1 hc2, ?_⟩
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with n hn1 hn2 hn
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsplit : (n : ℝ) ^ (-(((d1 + d2 : ℕ)) : ℤ))
      = (n : ℝ) ^ (-(d1 : ℤ)) * (n : ℝ) ^ (-(d2 : ℤ)) := by
    rw [show (-(((d1 + d2 : ℕ)) : ℤ)) = (-(d1 : ℤ)) + (-(d2 : ℤ)) by push_cast; ring]
    exact zpow_add₀ hn0.ne' _ _
  rw [hsplit]
  have h1n : (0 : ℝ) ≤ (n : ℝ) ^ (-(d1 : ℤ)) := zpow_nonneg hn0.le _
  have h2n : (0 : ℝ) ≤ (n : ℝ) ^ (-(d2 : ℤ)) := zpow_nonneg hn0.le _
  have hfnn : (0 : ℝ) ≤ f n := le_trans (mul_nonneg hc1.le h1n) hn1
  calc c1 * c2 * ((n : ℝ) ^ (-(d1 : ℤ)) * (n : ℝ) ^ (-(d2 : ℤ)))
      = (c1 * (n : ℝ) ^ (-(d1 : ℤ))) * (c2 * (n : ℝ) ^ (-(d2 : ℤ))) := by ring
    _ ≤ f n * g n := mul_le_mul hn1 hn2 (mul_nonneg hc2.le h2n) hfnn

/-- **Eq. (301): `Δ^{(avg)}_A ∈ O(log n)`.**  The average light cone grows at most logarithmically
in the number of qubits. -/
def IsLogBounded (Δ : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ (n : ℕ) in Filter.atTop, (Δ n : ℝ) ≤ C * Real.log (n : ℝ)

/-- A logarithmic bound on the light cone gives a polynomial survival lower bound. -/
theorem log_cone_poly {Δ : ℕ → ℕ} (h : IsLogBounded Δ) :
    IsPolyOmega (fun n => (1 / 3 : ℝ) ^ (Δ n)) := by
  obtain ⟨C, hC, hcone⟩ := h
  let d : ℕ := Nat.ceil (C * Real.log 3)
  have hd : C * Real.log 3 ≤ (d : ℝ) := Nat.le_ceil _
  refine ⟨d, 1, one_pos, ?_⟩
  filter_upwards [hcone, Filter.eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc : (Δ n : ℝ) * Real.log 3 ≤ (d : ℝ) * Real.log (n : ℝ) := by
    calc
      (Δ n : ℝ) * Real.log 3 ≤ (C * Real.log (n : ℝ)) * Real.log 3 :=
        mul_le_mul_of_nonneg_right hn hlog3.le
      _ = (C * Real.log 3) * Real.log (n : ℝ) := by ring
      _ ≤ (d : ℝ) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hd hlogn
  rw [one_mul]
  apply (Real.log_le_log_iff (zpow_pos hn0 _) (by positivity)).mp
  rw [Real.log_zpow, Real.log_pow]
  have hlog : Real.log ((1 : ℝ) / 3) = -Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hlog]
  push_cast
  nlinarith

/-- A polynomial Fourier mass and logarithmic cone imply a conditional variance lower bound. -/
theorem pauli_trainable (var z2 : ℕ → ℝ) (Δ : ℕ → ℕ)
    (hlog : IsLogBounded Δ) (hz : IsPolyOmega z2)
    (hvar : ∀ᶠ n in Filter.atTop, z2 n * (1 / 3 : ℝ) ^ (Δ n) ≤ var n) :
    IsPolyOmega var := by
  have hprod : IsPolyOmega (fun n => z2 n * (1 / 3 : ℝ) ^ (Δ n)) :=
    IsPolyOmega.mul hz (log_cone_poly hlog)
  obtain ⟨d, c, hc, h⟩ := hprod
  refine ⟨d, c, hc, ?_⟩
  filter_upwards [h, hvar] with n hn1 hn2
  exact hn1.trans hn2

end Qatlib.Papers.Trainability23.VarianceScaling.PauliAlgebra
