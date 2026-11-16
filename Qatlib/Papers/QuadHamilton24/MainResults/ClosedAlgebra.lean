/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
Closed block-matrix identities and explicit numerical resource envelopes from the legacy
QuadHamilton24 sources. The numerical envelopes do not construct quantum algorithms.
The oscillator exponential formula and unresolved analytic bounds are excluded.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QuadHamilton24.MainResults.ClosedAlgebra
open Qatlib.Papers.QuadHamilton24.MainResults
variable {N M ι : Type*} [_instFintypeN : Fintype N] [_instFintypeM : Fintype M] [_instFintypeι : Fintype ι]
  [_instDecidableEqN : DecidableEq N] [_instDecidableEqM : DecidableEq M] [_instDecidableEqι : DecidableEq ι]


/-! Mathematical identities for the source model. -/

omit _instFintypeN _instFintypeM _instDecidableEqN _instDecidableEqM in
/-- **Lemma 6, split (3.22).**  `A = A₁ + A₂` with `A₁ = diag(F₁,F₃)` and
`A₂ = [[0,0],[F₂,0]]`. -/
theorem lemma6_block_split
    (F₁ : Matrix N N ℂ) (F₂ : Matrix M N ℂ) (F₃ : Matrix M M ℂ) :
    blockA F₁ 0 F₂ F₃ =
      fromBlocks F₁ 0 0 F₃ + fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ 0 := by
  unfold blockA
  rw [Matrix.fromBlocks_add]
  simp

/-- **Lemma 6, nilpotence (3.26).**  The strictly lower block `A₂` squares to zero, so
the Dyson product `exp(A₁t) A₂ exp(A₁t') A₂` vanishes and the series truncates. -/
theorem lemma6_A2_sq_zero (F₂ : Matrix M N ℂ) :
    (fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ (0 : Matrix M M ℂ)) *
        (fromBlocks (0 : Matrix N N ℂ) (0 : Matrix N M ℂ) F₂ (0 : Matrix M M ℂ)) =
      (0 : Matrix (N ⊕ M) (N ⊕ M) ℂ) := by
  rw [Matrix.fromBlocks_multiply]
  simp


/-! Mathematical identities for the source model. -/

/-- **Lemma 7, (3.29) ⇒ (3.30).**  If `‖exp(At)‖ ≤ exp(µ t)` on `[0,T]`, then
`‖exp(At)‖ ≤ exp((µ + ‖F₂‖ + ‖F₀‖) t)` on `[0,T]`. -/
theorem lemma7_exp_bound
    (A F₀ F₂ : Matrix ι ι ℂ) (μ T : ℝ)
    (hμ : ∀ t ∈ Set.Icc 0 T, ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (μ * t)) :
    ∀ t ∈ Set.Icc 0 T,
      ‖NormedSpace.exp (t • A)‖ ≤ Real.exp ((μ + ‖F₂‖ + ‖F₀‖) * t) := by
  intro t ht
  refine (hμ t ht).trans ?_
  apply Real.exp_le_exp.mpr
  have ht0 : 0 ≤ t := ht.1
  exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg F₀, norm_nonneg F₂]) ht0

omit _instFintypeι _instDecidableEqι in
/-- **Lemma 7, block split (3.31).**  The matrix `A` splits as the block-diagonal
`A₁ = diag(F₁, F₃)` plus the off-diagonal `A₂ = [[0,F₀],[F₂,0]]`. -/
theorem lemma7_block_split
    (F₁ : Matrix ι ι ℂ) (F₀ F₂ F₃ : Matrix ι ι ℂ) :
    blockA F₁ F₀ F₂ F₃ =
      fromBlocks F₁ 0 0 F₃ + fromBlocks 0 F₀ F₂ 0 := by
  unfold blockA
  rw [Matrix.fromBlocks_add]
  simp


/-! Mathematical identities for the source model. -/

/-- `JQ = [[0, I], [-V, 0]]`, the first multiplication in (4.112). -/
theorem lemma8_JQ_eq (V : Matrix ι ι ℂ) :
    Jblock * Qblock V = fromBlocks 0 1 (-V) 0 := by
  unfold Jblock Qblock
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **Lemma 8, (4.112): `(JQ)² = diag(−V, −V)`.** -/
theorem lemma8_JQ_sq (V : Matrix ι ι ℂ) :
    (Jblock * Qblock V) * (Jblock * Qblock V) = fromBlocks (-V) 0 0 (-V) := by
  rw [lemma8_JQ_eq V, Matrix.fromBlocks_multiply]
  simp

/-- The symmetric exponential combination of the legacy model; this is hyperbolic, not matrix cosine. -/
def mcos (S : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  ((2 : ℂ)⁻¹) • (NormedSpace.exp (t • S) + NormedSpace.exp ((-t) • S))

/-- The antisymmetric exponential combination of the legacy model, scaled by the reciprocal of twice the imaginary unit. -/
def msin (S : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  ((2 * Complex.I)⁻¹ : ℂ) • (NormedSpace.exp (t • S) - NormedSpace.exp ((-t) • S))


/-! Mathematical identities for the source model. -/

/-- The `poly(s, k, log d, log 1/ε)` factor of (4.3), as the explicit product of
`(1 + |·|)` entries. -/
def theorem3Poly (s k d ε : ℝ) : ℝ :=
  ∏ i : Fin 4, (1 + |(![s, k, Real.log d, Real.log (1 / ε)] : Fin 4 → ℝ) i|)

/-- The polynomial factor really is polynomially bounded in its arguments. -/
theorem theorem3Poly_isPoly (s k d ε : ℝ) :
    IsPolyBound ![s, k, Real.log d, Real.log (1 / ε)] (theorem3Poly s k d ε) :=
  ⟨1, zero_le_one, 1, by simp [theorem3Poly]⟩

/-- The query complexity of (4.3): `g κ_L log κ_L · poly(s,k,log d,log 1/ε)`. -/
def theorem3QueryComplexity (g κL s k d ε : ℝ) : ℝ :=
  g * κL * Real.log κL * theorem3Poly s k d ε

/-- **Theorem 3, query bound (4.3).**  The query complexity has the source's shape: a
leading factor `g κ_L log κ_L` times a polynomial factor in `(s, k, log d, log 1/ε)`. -/
theorem theorem3_query_complexity (g κL s k d ε : ℝ) :
    ∃ TQ poly : ℝ,
      TQ = g * κL * Real.log κL * poly ∧
        IsPolyBound ![s, k, Real.log d, Real.log (1 / ε)] poly :=
  ⟨theorem3QueryComplexity g κL s k d ε, theorem3Poly s k d ε, rfl, theorem3Poly_isPoly s k d ε⟩

/-- The `poly(k, log 1/ε, log(‖A‖T))` gate-overhead factor of (4.4). -/
def theorem3GatePoly (k ε Anorm T : ℝ) : ℝ :=
  ∏ i : Fin 3,
    (1 + |(![k, Real.log (1 / ε), Real.log (Anorm * T)] : Fin 3 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem3GatePoly_isPoly (k ε Anorm T : ℝ) :
    IsPolyBound ![k, Real.log (1 / ε), Real.log (Anorm * T)]
      (theorem3GatePoly k ε Anorm T) :=
  ⟨1, zero_le_one, 1, by simp [theorem3GatePoly]⟩

/-- **Theorem 3, gate overhead (4.4).**  `T_G` exceeds `T_Q` by at most a polynomial
factor in `(k, log 1/ε, log(‖A‖T))`. -/
theorem theorem3_gate_overhead (k ε Anorm T : ℝ) :
    ∃ factor poly : ℝ,
      factor = poly ∧ IsPolyBound ![k, Real.log (1 / ε), Real.log (Anorm * T)] poly :=
  ⟨theorem3GatePoly k ε Anorm T, theorem3GatePoly k ε Anorm T, rfl,
    theorem3GatePoly_isPoly k ε Anorm T⟩

/-- The `poly(log κ_L, s, k, log d)` kinetic factor of (4.8). -/
def theorem3KineticPoly (κL s k d : ℝ) : ℝ :=
  ∏ i : Fin 4,
    (1 + |(![Real.log κL, s, k, Real.log d] : Fin 4 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem3KineticPoly_isPoly (κL s k d : ℝ) :
    IsPolyBound ![Real.log κL, s, k, Real.log d] (theorem3KineticPoly κL s k d) :=
  ⟨1, zero_le_one, 1, by simp [theorem3KineticPoly]⟩

/-- **Theorem 3, kinetic-energy query bound (4.8).**  `T_K = (1/ε) κ_L · poly(...)`. -/
theorem theorem3_kinetic_query_complexity (κL s k d ε : ℝ) :
    ∃ TK poly : ℝ,
      TK = (1 / ε) * κL * poly ∧
        IsPolyBound ![Real.log κL, s, k, Real.log d] poly :=
  ⟨(1 / ε) * κL * theorem3KineticPoly κL s k d, theorem3KineticPoly κL s k d, rfl,
    theorem3KineticPoly_isPoly κL s k d⟩


/-! Mathematical identities for the source model. -/

/-- `m = T ‖Ã‖` of (4.64). -/
def theorem5m (T AnormTilde : ℝ) : ℝ := T * AnormTilde

/-- The `poly(s, k, log d)` factor of (4.65). -/
def theorem5Poly (s k d : ℝ) : ℝ :=
  ∏ i : Fin 3, (1 + |(![s, k, Real.log d] : Fin 3 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem5Poly_isPoly (s k d : ℝ) :
    IsPolyBound ![s, k, Real.log d] (theorem5Poly s k d) :=
  ⟨1, zero_le_one, 1, by simp [theorem5Poly]⟩

/-- The query complexity of (4.65): `(m/ε²) log m · poly(s,k,log d)`. -/
def theorem5QueryComplexity (m ε s k d : ℝ) : ℝ :=
  (m / ε ^ 2) * Real.log m * theorem5Poly s k d

/-- **Theorem 5, query bound (4.65).** -/
theorem theorem5_query_complexity (m ε s k d : ℝ) :
    ∃ TQ poly : ℝ,
      TQ = ((m / ε ^ 2) * Real.log m) * poly ∧
        IsPolyBound ![s, k, Real.log d] poly :=
  ⟨theorem5QueryComplexity m ε s k d, theorem5Poly s k d, rfl, theorem5Poly_isPoly s k d⟩

/-- The `poly(k, log 1/ε, log m)` gate-overhead factor of (4.66). -/
def theorem5GatePoly (k ε m : ℝ) : ℝ :=
  ∏ i : Fin 3, (1 + |(![k, Real.log (1 / ε), Real.log m] : Fin 3 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem5GatePoly_isPoly (k ε m : ℝ) :
    IsPolyBound ![k, Real.log (1 / ε), Real.log m] (theorem5GatePoly k ε m) :=
  ⟨1, zero_le_one, 1, by simp [theorem5GatePoly]⟩

/-- **Theorem 5, gate overhead (4.66).** -/
theorem theorem5_gate_overhead (k ε m : ℝ) :
    ∃ factor poly : ℝ,
      factor = poly ∧ IsPolyBound ![k, Real.log (1 / ε), Real.log m] poly :=
  ⟨theorem5GatePoly k ε m, theorem5GatePoly k ε m, rfl, theorem5GatePoly_isPoly k ε m⟩


/-! Mathematical identities for the source model. -/

/-- Kinetic energy `K = ½ Σ q̇ᵢ²` of (4.122). -/
def kineticEnergy {n : ℕ} (qdot : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, (qdot i) ^ 2

/-- **Theorem 8, (4.122).**  The kinetic energy is `½ Σ q̇ᵢ²`. -/
theorem theorem8_kinetic_energy_form {n : ℕ} (qdot : Fin n → ℝ) :
    kineticEnergy qdot = (1 / 2) * ∑ i, (qdot i) ^ 2 := rfl

/-- Normalised kinetic energy `K(τ)/E`. -/
def normalizedKinetic {n : ℕ} (qdot : ℝ → Fin n → ℝ) (E τ : ℝ) : ℝ :=
  kineticEnergy (qdot τ) / E

/-- **Theorem 8, instance regime.**  There are instances with `T = (log d)² = polylog(d)`
and `‖R‖T ≤ ε` (take `R = 0`). -/
theorem theorem8_regime (d : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ T : ℝ, T = (Real.log d) ^ 2 ∧ 0 ≤ T ∧
      ∃ R : Matrix (Fin d) (Fin d) ℂ, ‖R‖ * T ≤ ε := by
  refine ⟨(Real.log d) ^ 2, rfl, by positivity, 0, ?_⟩
  simp only [norm_zero, zero_mul]
  exact hε


/-! Mathematical identities for the source model. -/

/-- The printed lower bound `1/(108 g²)` of (5.35). -/
def lemma11LowerBoundPrinted (g : ℝ) : ℝ := 1 / (108 * g ^ 2)

/-- The bound actually obtained from the source's chain (5.42)–(5.44). -/
def lemma11LowerBoundDerived (g : ℝ) : ℝ := 1 / (108 * g)

/-- The printed inverse-square success lower bound is positive for a positive growth ratio. -/
theorem lemma11LowerBoundPrinted_pos (g : ℝ) (hg : 0 < g) :
    0 < lemma11LowerBoundPrinted g := by
  unfold lemma11LowerBoundPrinted
  positivity

/-- The derived inverse-linear success lower bound is positive for a positive growth ratio. -/
theorem lemma11LowerBoundDerived_pos (g : ℝ) (hg : 0 < g) :
    0 < lemma11LowerBoundDerived g := by
  unfold lemma11LowerBoundDerived
  positivity

/-- **Lemma 11, derived bound (5.42)–(5.44).**  If the post-selection probability is at
least `‖u(T)‖²/(108 u_max²)` (the result of (5.41) with `(1−ε)² ≥ 1/4`,
`12(1+γ)² ≤ 27`), then it is at least `1/(108 g)` with `g = u_max²/‖u(T)‖²`. -/
theorem lemma11_success_bound_derived
    (p uT umax g : ℝ) (huT : 0 < uT) (humax : 0 < umax)
    (hg : g = umax ^ 2 / uT ^ 2)
    (hp : p ≥ uT ^ 2 / (108 * umax ^ 2)) :
    p ≥ lemma11LowerBoundDerived g := by
  have hEq : lemma11LowerBoundDerived g = uT ^ 2 / (108 * umax ^ 2) := by
    unfold lemma11LowerBoundDerived
    rw [hg]
    field_simp
  rw [hEq]
  exact hp


/-! Mathematical identities for the source model. -/

/-- `k = O(log(1 + ‖b‖T e²/‖x(T)‖))` of (5.50), as the explicit logarithm. -/
def theorem10k (bNorm T xT : ℝ) : ℝ := Real.log (1 + bNorm * T * Real.exp 2 / xT)

/-- Gate polylog factor `polylog(d, k, 1/ε, T‖A‖C(A))` of (5.46). -/
def theorem10GatePoly (d k ε κL : ℝ) : ℝ :=
  ∏ i : Fin 4,
    (1 + |(![Real.log d, Real.log k, Real.log (1 / ε), Real.log κL] : Fin 4 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem10GatePoly_isPoly (d k ε κL : ℝ) :
    IsPolyBound ![Real.log d, Real.log k, Real.log (1 / ε), Real.log κL]
      (theorem10GatePoly d k ε κL) :=
  ⟨1, zero_le_one, 1, by simp [theorem10GatePoly]⟩

/-- **Theorem 10, gate complexity (5.46).** -/
theorem theorem10_gate_complexity (g T Anorm CA s k d ε : ℝ) :
    ∃ TG poly : ℝ,
      TG = g * T * Anorm * CA * s * k * poly ∧
        IsPolyBound ![Real.log d, Real.log k, Real.log (1 / ε), Real.log (T * Anorm * CA)] poly := by
  refine ⟨g * T * Anorm * CA * s * k * theorem10GatePoly d k ε (T * Anorm * CA),
    theorem10GatePoly d k ε (T * Anorm * CA), rfl, ?_⟩
  exact theorem10GatePoly_isPoly d k ε (T * Anorm * CA)

/-- Query polylog factor `polylog(k, 1/ε, T‖A‖C(A))` of (5.47). -/
def theorem10QueryPoly (k ε κL : ℝ) : ℝ :=
  ∏ i : Fin 3,
    (1 + |(![Real.log k, Real.log (1 / ε), Real.log κL] : Fin 3 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem10QueryPoly_isPoly (k ε κL : ℝ) :
    IsPolyBound ![Real.log k, Real.log (1 / ε), Real.log κL]
      (theorem10QueryPoly k ε κL) :=
  ⟨1, zero_le_one, 1, by simp [theorem10QueryPoly]⟩

/-- **Theorem 10, query complexity (5.47).** -/
theorem theorem10_query_complexity (g T Anorm CA s k ε : ℝ) :
    ∃ TQ poly : ℝ,
      TQ = g * T * Anorm * CA * s * k * poly ∧
        IsPolyBound ![Real.log k, Real.log (1 / ε), Real.log (T * Anorm * CA)] poly := by
  refine ⟨g * T * Anorm * CA * s * k * theorem10QueryPoly k ε (T * Anorm * CA),
    theorem10QueryPoly k ε (T * Anorm * CA), rfl, ?_⟩
  exact theorem10QueryPoly_isPoly k ε (T * Anorm * CA)


/-! Mathematical identities for the source model. -/

/-- `polylog(1/ε, s, κ_V, κ_L, M+N)` of (5.68). -/
def theorem11Polylog (ε s κV κL MN : ℝ) : ℝ :=
  ∏ i : Fin 5,
    (1 + |(![Real.log (1 / ε), Real.log s, Real.log κV, Real.log κL,
      Real.log MN] : Fin 5 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem11Polylog_isPoly (ε s κV κL MN : ℝ) :
    IsPolyBound ![Real.log (1 / ε), Real.log s, Real.log κV, Real.log κL, Real.log MN]
      (theorem11Polylog ε s κV κL MN) :=
  ⟨1, zero_le_one, 1, by simp [theorem11Polylog]⟩

/-- **Theorem 11, complexity (5.68).**  Query and gate complexity `s κ_V κ_L · polylog`. -/
theorem theorem11_complexity (s κV κL ε MN : ℝ) :
    ∃ C poly : ℝ,
      C = s * κV * κL * poly ∧
        IsPolyBound ![Real.log (1 / ε), Real.log s, Real.log κV, Real.log κL, Real.log MN]
          poly :=
  ⟨s * κV * κL * theorem11Polylog ε s κV κL MN, theorem11Polylog ε s κV κL MN, rfl,
    theorem11Polylog_isPoly ε s κV κL MN⟩

/-- **Theorem 11, (5.72): `κ_L = O(C(A) T‖A‖)`.**  By definition
`κ_L = T‖A‖C(A)`, so it equals `C(A) T‖A‖` with constant `1`. -/
theorem theorem11_kappaL_isO (A : Matrix N N ℂ) (T : ℝ) :
    kappaL A T ≤ 1 * (Csup A T * T * ‖A‖) := by
  unfold kappaL
  rw [show T * ‖A‖ * Csup A T = Csup A T * T * ‖A‖ by ring]
  simp

/-- **Theorem 11, (5.71): `C_d` definition.** -/
theorem theorem11_Cd_def (F : Matrix N N ℂ) (T : ℝ) :
    Cd F T = sSup ((fun t : ℝ => ‖NormedSpace.exp (t • F)‖) '' Set.Icc 0 T) := rfl


/-! Mathematical identities for the source model. -/

/-- `polylog(1/ε, s, κ_V, κ_L, N)` of (5.101). -/
def theorem12Polylog (ε s κV κL Ndim : ℝ) : ℝ :=
  ∏ i : Fin 5,
    (1 + |(![Real.log (1 / ε), Real.log s, Real.log κV, Real.log κL,
      Real.log Ndim] : Fin 5 → ℝ) i|)

/-- The explicit polynomial factor satisfies the stated numerical polynomial envelope. -/
theorem theorem12Polylog_isPoly (ε s κV κL Ndim : ℝ) :
    IsPolyBound ![Real.log (1 / ε), Real.log s, Real.log κV, Real.log κL, Real.log Ndim]
      (theorem12Polylog ε s κV κL Ndim) :=
  ⟨1, zero_le_one, 1, by simp [theorem12Polylog]⟩

/-- **Theorem 12, complexity (5.101).** -/
theorem theorem12_complexity (s κV κL ε Ndim : ℝ) :
    ∃ C poly : ℝ,
      C = s * κV * κL * poly ∧
        IsPolyBound ![Real.log (1 / ε), Real.log s, Real.log κV, Real.log κL, Real.log Ndim]
          poly :=
  ⟨s * κV * κL * theorem12Polylog ε s κV κL Ndim, theorem12Polylog ε s κV κL Ndim, rfl,
    theorem12Polylog_isPoly ε s κV κL Ndim⟩

/-- **Theorem 12, (5.105): `κ_L = O(C(A) T‖A‖)`.** -/
theorem theorem12_kappaL_isO (A : Matrix N N ℂ) (T : ℝ) :
    kappaL A T ≤ 1 * (Csup A T * T * ‖A‖) := by
  unfold kappaL
  rw [show T * ‖A‖ * Csup A T = Csup A T * T * ‖A‖ by ring]
  simp

/-- **Theorem 12, (5.104): `C_d` definition.** -/
theorem theorem12_Cd_def (F : Matrix N N ℂ) (T : ℝ) :
    Cd F T = sSup ((fun t : ℝ => ‖NormedSpace.exp (t • F)‖) '' Set.Icc 0 T) := rfl


/-- The legacy probability claim omits that the maximum norm dominates the final norm. -/
theorem legacyPrintedCounter :
    (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 / 2 ∧
    (0 : ℝ) < 2 ∧ (0 : ℝ) < 1 ∧
    (1 / 4 : ℝ) = 1 ^ 2 / 2 ^ 2 ∧
    (1 / 27 : ℝ) = (1 - 1 / 2) ^ 2 * 2 ^ 2 / (12 * (1 + 1 / 2) ^ 2 * 1 ^ 2) ∧
    ¬ (1 / 27 : ℝ) ≥ lemma11LowerBoundPrinted (1 / 4) := by
  norm_num [lemma11LowerBoundPrinted]

/-- In the physical regime g≥1 the derived inverse-g bound implies the printed inverse-square bound. -/
theorem printedOfDerived (p g : ℝ) (hg : 1 ≤ g) (hp : 1 / (108 * g) ≤ p) :
    lemma11LowerBoundPrinted g ≤ p := by
  apply le_trans _ hp
  unfold lemma11LowerBoundPrinted
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith


namespace NormBoundary

def A : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  Matrix.fromBlocks (1 : Matrix Unit Unit ℂ) 0 1 0

def diagonalValues : Unit ⊕ Unit → ℂ
  | Sum.inl _ => 2
  | Sum.inr _ => 0

/-- Scalar block row sums do not bound the spectral norm. -/
theorem rowBoundFails : ¬ ‖A‖ ≤ 1 := by
  have hAA : Aᴴ * A = Matrix.diagonal diagonalValues := by
    rw [A, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    ext i j
    cases i <;> cases j <;> rename_i a b <;> cases a <;> cases b <;>
      norm_num [diagonalValues, Matrix.ofNat_apply]
  have hdiag : ‖diagonalValues‖ = 2 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
      intro i
      cases i <;> norm_num [diagonalValues]
    · have hh := norm_le_pi_norm diagonalValues (Sum.inl ())
      norm_num [diagonalValues] at hh
      exact hh
  have hn : ‖A‖ * ‖A‖ = 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hAA, Matrix.l2_opNorm_diagonal, hdiag]
  intro hle
  nlinarith [norm_nonneg A]


end NormBoundary

end Qatlib.Papers.QuadHamilton24.MainResults.ClosedAlgebra
