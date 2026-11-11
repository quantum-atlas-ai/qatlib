/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.LatticeModel.SourceLattice

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — Gaussian smoothing, tails and state-truncation lemmas

Fixed arXiv:2310.00644v2.

* c024 Lemma 50, p.27 + Appendix A.2: the state (10) is `2^{-Ω(n)}`-close to the state (11).
* c025 Lemma 64, p.35 + Appendix A.3: the state (14) is `2^{-Ω(n)}`-close to the state (15).
* c026 Lemma 66, p.35 + Appendix A.4: the state (16) is `2^{-Ω(n)}`-close to the state (17).
* c029 Lemma 72, p.42: `∑_{x∈L*} ρ_{1/σ}(x−u) < ρ_{1/σ}(u−κ_{L*}(u)) + ε` for `σ > 2η_ε(L)`.
* c030 Lemma 73, p.42: the sharpened bound with `σ > 2√2 η_ε(L)` and the extra term
  `ε·ρ_{√2/σ}(κ_{L*}(u)−u)`.

The paper's `ρ_s(x) = exp(-π‖x‖²/s²)` is `gaussScalar s ‖x‖`; lattices are represented by
integer (resp. rational) bases (see `LatticeModel.SourceLattice`), and the smoothing
parameter is defined exactly as in Definition 14, p.12.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- `w` is a closest point of `S` to `u` (ties broken arbitrarily, as the paper allows). -/
def IsClosestPoint {n : ℕ} (S : Set (Fin n → ℝ)) (u w : Fin n → ℝ) : Prop :=
  w ∈ S ∧ ∀ x ∈ S, vecDistR u w ≤ vecDistR u x

/-- The set of points of the dual lattice spanned by the rational basis `B`. -/
def dualLatticeSet {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : Set (Fin n → ℝ) :=
  Set.range (dualPointR B)

/-- Definition 14, p.12: the smoothing parameter `η_ε(L)` is the smallest `s > 0` with
`ρ_{1/s}(L* \ {0}) ≤ ε`, i.e. `∑_{x∈L*, x≠0} exp(-π s²‖x‖²) ≤ ε`. -/
def smoothingParameter {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (ε : ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧
    (∑' k : Fin n → ℤ, if k = 0 then 0 else gaussScalar s⁻¹ (vecNormR (dualPointR B k))) ≤ ε}

/-- The state of Eq. (10)/(11), p.26: amplitudes `ρ_α(j)·ρ_{βq}(x + j·e)` on
`|j⟩|(v+j·s) mod q⟩|(Aᵀv+x) mod q⟩`, with the third-register sum over integer `x`
restricted by the predicate `P`. `P = fun _ => True` gives Eq. (10); the truncation
`‖x‖ < λ₁(L_q(A))/2` gives Eq. (11). -/
def edcpGaussianState {n m q : ℕ} [NeZero q] (A : Matrix (Fin n) (Fin m) (ZMod q))
    (α βq : ℝ) (s : Fin n → ZMod q) (e : Fin m → ZMod q)
    (P : (Fin m → ℤ) → Prop) :
    QState (ZMod q × (Fin n → ZMod q) × (Fin m → ZMod q)) := by
  classical
  exact fun p => (gaussianWeight α ((p.1).val : ℝ) : ℂ) *
    (∑' (v : Fin n → ZMod q) (x : Fin m → ℤ),
      if (P x ∧ (∀ i, p.2.1 i = v i + (p.1 : ZMod q) * s i) ∧
          (∀ j, p.2.2 j = matVecT A v j + ((x j : ℤ) : ZMod q))) then
        (gaussianWeightVec βq (fun j => (x j : ℝ) + ((p.1).val : ℝ) * ((e j).val : ℝ)) : ℂ)
      else 0)

/-- **Lemma 50, p.27 (Appendix A.2).** If `(βq√m + αγqm)·√(log(βq)) < λ₁(L_q(A))/2` and
`βq > √m`, then the state (10) is `2^{-Ω(n)}`-close in trace distance to the state (11)
(the third register restricted to `‖x‖ < λ₁(L_q(A))/2`).

Gap: the proof (Appendix A.2) shows that two distinct pairs `(v,x)`, `(v',x')` with
`Aᵀv+x ≡ Aᵀv'+x' (mod q)` and `‖x‖,‖x'‖ < λ₁/2` force `v = v'`, `x = x'`, using Lemma 18
and Banaszczyk's bound (Lemma 11); neither the lattice minimum bound nor Banaszczyk's tail
bound is in the library. Candidate dependencies: `qary_shortest_vector_large` (Lemma 18),
`ProbabilityCore.Concentration` for Gaussian tails, and `poisson_summation_formula`. -/
def lemma50_truncation {n m q : ℕ} [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ZMod q)) {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) {lamHalf : ℝ} (hlam : 0 < lamHalf)
    (hcond : (β * (q : ℝ) * Real.sqrt (m : ℝ) + α * γ * (q : ℝ) * (m : ℝ)) *
        Real.sqrt (Real.log (β * (q : ℝ))) < lamHalf / 2)
    (hβm : Real.sqrt (m : ℝ) < β * (q : ℝ))
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) : Prop := ∃ err : ℕ → ℝ, ExpSmall err ∧
      traceDistance
        (outerProduct (edcpGaussianState A α (β * (q : ℝ)) s e (fun _ => True)))
        (outerProduct (edcpGaussianState A α (β * (q : ℝ)) s e
          (fun x => vecNormR (fun j => (x j : ℝ)) < lamHalf))) ≤ err n

/-- The `S|LWE⟩^phase`-type inner state of Eq. (18), p.45: amplitude `ρ_σ(e)` on
`|⟨s,a⟩ + ⟨x',v⟩ + e mod q⟩`, with `e` ranging over `Z_{qR}/R` (represented by
`ZMod (q*R)` and placed in the `Z_q` register). -/
def cvpPhaseStateUnshifted {n q R : ℕ} [NeZero q] [NeZero R]
    (B : Matrix (Fin n) (Fin n) ℤ) (r σ : ℝ) (a s : Fin n → ZMod q) (x' : Fin n → ℝ)
    (P : (Fin n → ℝ) → Prop) : QState ((Fin n → ZMod R) × ZMod q) := by
  classical
  exact fun p => ∑' k : Fin n → ℤ,
    (if P (latticePointR B k) ∧
        (∀ i, (latticePointZ B k i).natAbs = (p.1 i).val) then
      (gaussianWeightVec r (latticePointR B k) : ℂ) else 0) *
    (∑' u : ZMod (q * R),
      if p.2 = (∑ i, a i * s i) + realToZMod q (innerR x' (latticePointR B k)) +
          ((u.val : ℕ) : ZMod q) then
        (gaussScalar σ ((u.val : ℝ) / (R : ℝ)) : ℂ) else 0)

/-- The state of Eq. (15)/(19), p.35/45: amplitude `ρ_σ(u − ⟨x',v⟩)` on
`|⟨s,a⟩ + u mod q⟩` (change of variable `u ← ⟨x',v⟩ + e`). -/
def cvpPhaseStateShifted {n q R : ℕ} [NeZero q] [NeZero R]
    (B : Matrix (Fin n) (Fin n) ℤ) (r σ : ℝ) (a s : Fin n → ZMod q) (x' : Fin n → ℝ)
    (P : (Fin n → ℝ) → Prop) : QState ((Fin n → ZMod R) × ZMod q) := by
  classical
  exact fun p => ∑' k : Fin n → ℤ,
    (if P (latticePointR B k) ∧
        (∀ i, (latticePointZ B k i).natAbs = (p.1 i).val) then
      (gaussianWeightVec r (latticePointR B k) : ℂ) else 0) *
    (∑' u : ZMod (q * R),
      if p.2 = (∑ i, a i * s i) + ((u.val : ℕ) : ZMod q) then
        (gaussScalar σ ((u.val : ℝ) / (R : ℝ) - innerR x' (latticePointR B k)) : ℂ)
      else 0)

/-- **Lemma 64, p.35 (Appendix A.3).** Suppose `q/2 > αq√n + σ√n`, `R > 2√(nr log r)`,
`r > 2qη_ε(L)` for `ε < 2^{-n}`. Then the state (14) is `2^{-Ω(n)}`-close to the state (15).

The hypothesis `r > 2qη_ε(L)` is carried as `2·q·η < r` for a parameter `η = η_ε(L)`; the
smoothing parameter itself is `smoothingParameter` applied to the dual basis (not available
here because the dual basis of `L` is not a separate argument). Gap: Banaszczyk's tail bound
(Lemma 11) and the lattice-point count of Appendix A.3. Candidate dependencies:
`smoothing_tail_bound` (Lemma 72), `ProbabilityCore.Concentration`. -/
def lemma64_state_close {n q R : ℕ} [NeZero q] [NeZero R]
    (B : Matrix (Fin n) (Fin n) ℤ) (a s : Fin n → ZMod q) (x' : Fin n → ℝ) {α σ r ε η : ℝ}
    (hα : 0 < α) (hσ : 0 < σ) (hr : 0 < r) (hε : 0 < ε)
    (hε2 : ε < (2 : ℝ) ^ (-(n : ℝ))) (hη : 2 * (q : ℝ) * η < r)
    (hq : (q : ℝ) / 2 > α * (q : ℝ) * Real.sqrt (n : ℝ) + σ * Real.sqrt (n : ℝ))
    (hR : 2 * Real.sqrt ((n : ℝ) * r * Real.log r) < (R : ℝ))
    (P : (Fin n → ℝ) → Prop) : Prop := ∃ err : ℕ → ℝ, ExpSmall err ∧
      traceDistance
        (outerProduct (cvpPhaseStateUnshifted (R := R) B r σ a s x' P))
        (outerProduct (cvpPhaseStateShifted (R := R) B r σ a s x' P)) ≤ err n

/-- `ω_R = e^{2πi/R}`, the QFT root of unity on `Z_R` (p.35). -/
def omegaR (R : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (R : ℂ))

/-- The first register of the state (16), p.35: after `QFT_R` the amplitude at `y` is
`∑_{v∈qL+La} ρ_r(v)·ω_R^{⟨v,y⟩}`. -/
def eq16FirstRegister {n R : ℕ} [NeZero R] (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ)
    (P : (Fin n → ℝ) → Prop) : QState (Fin n → ZMod R) := by
  classical
  exact fun y => ∑' k : Fin n → ℤ,
    if P (latticePointR B k) then
      (gaussianWeightVec r (latticePointR B k) : ℂ) *
        (omegaR R) ^ (∑ i, (latticePointZ B k i).natAbs * (y i).val)
    else 0

/-- The first register of the state (17), p.35: amplitude `ρ_√Σ(z)·exp(2πi⟨a,κ(y/R)⟩)`. -/
def eq17FirstRegister {n R : ℕ} [NeZero R] (Sigma : ℝ) (a : Fin n → ℝ)
    (zOf kappaOf : (Fin n → ZMod R) → Fin n → ℝ) : QState (Fin n → ZMod R) :=
  fun y => (gaussianWeightVec (Real.sqrt Sigma) (zOf y) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (innerR a (kappaOf y) : ℂ))

/-- **Lemma 66, p.35 (Appendix A.4).** Suppose `ε < 2^{-n}`, `R > 2√(nr log r)`,
`r > 4qη_ε(L)` and `σ ≥ αq`. Then the state (16) is `2^{-Ω(n)}`-close to the state (17),
where `Σ = I_r n² + x'x'ᵀ/σ²`, `z(y) = y/R − κ_{(qL)*}(y/R)` and `κ` is a closest-vector
map into `S`.

Gap: the Poisson-summation step producing `ρ_√Σ(z)` and the phase `e^{2πi⟨a,κ(y/R)⟩}`
(Appendix A.4), which rests on Lemma 73. Candidate dependencies: `smoothing_tail_bound_sharp`
(Lemma 73) and `poisson_summation_formula` (Lemma 10). -/
def lemma66_state_close {n R : ℕ} [NeZero R] (B : Matrix (Fin n) (Fin n) ℤ)
    (Bd : Matrix (Fin n) (Fin n) ℚ) {r σ α q ε : ℝ}
    (S : Set (Fin n → ℝ)) (Sigma : ℝ) (hSigma : 0 < Sigma) (a : Fin n → ℝ)
    (zOf kappaOf : (Fin n → ZMod R) → Fin n → ℝ)
    (hz : ∀ y, zOf y = fun i => ((y i).val : ℝ) / (R : ℝ) - kappaOf y i)
    (hκ : ∀ y, IsClosestPoint S (fun i => ((y i).val : ℝ) / (R : ℝ)) (kappaOf y))
    (hα : 0 < α) (hσ : 0 < σ) (hr : 0 < r) (hε : 0 < ε)
    (hε2 : ε < (2 : ℝ) ^ (-(n : ℝ))) (hη : 4 * (q : ℝ) * smoothingParameter Bd ε < r)
    (hq : α * (q : ℝ) ≤ σ)
    (hR : 2 * Real.sqrt ((n : ℝ) * r * Real.log r) < (R : ℝ))
    (P : (Fin n → ℝ) → Prop) : Prop := ∃ err : ℕ → ℝ, ExpSmall err ∧
      traceDistance (outerProduct (eq16FirstRegister (R := R) B r P))
        (outerProduct (eq17FirstRegister Sigma a zOf kappaOf)) ≤ err n

/-- **Lemma 72, p.42 (Appendix A.1).** For a lattice `L*⊆ℝⁿ` with `σ > 2η_ε(L)` and any
`u ∈ ℝⁿ`,
`∑_{x∈L*} ρ_{1/σ}(x−u) < ρ_{1/σ}(u−κ_{L*}(u)) + ε`.

The proof (Appendix A.1) is a pure triangle-inequality estimate reducing the sum over
`x ≠ κ(u)` to `ρ_{2/σ}(L*\{0}) < ε`. Gap: the reduction to the smoothing parameter and the
definition of `η_ε` as an infimum need the Poisson-summation/covering arguments
(Definition 12 and Lemma 17); only the final inequality is stated here. Candidate
dependencies: `poisson_summation_formula` (Lemma 10), `ProbabilityCore.Concentration`. -/
def smoothing_tail_bound {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℚ)
    (κ : (Fin n → ℝ) → Fin n → ℝ) (u : Fin n → ℝ) {ε σ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hσ : 2 * smoothingParameter Bd ε < σ)
    (hκ : IsClosestPoint (dualLatticeSet Bd) u (κ u)) : Prop := dualSumR Bd (fun x => gaussScalar σ⁻¹ (vecDistR x u)) <
      gaussScalar σ⁻¹ (vecDistR u (κ u)) + ε

/-- **Lemma 73, p.42 (Appendix A.1).** Sharper tail bound: for `σ > 2√2 η_ε(L)` and any
`u ∈ ℝⁿ`,
`∑_{x∈L*} ρ_{1/σ}(x−u) < ρ_{1/σ}(κ_{L*}(u)−u) + ε·ρ_{√2/σ}(κ_{L*}(u)−u)`.

Gap: same as Lemma 72, with the `1/8` improvement of the norm estimate
`‖x−u‖² − ‖κ(u)−u‖² ≥ (1/8)‖x−κ(u)‖²`. Candidate dependencies:
`poisson_summation_formula` (Lemma 10). -/
def smoothing_tail_bound_sharp {n : ℕ} (Bd : Matrix (Fin n) (Fin n) ℚ)
    (κ : (Fin n → ℝ) → Fin n → ℝ) (u : Fin n → ℝ) {ε σ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hσ : 2 * Real.sqrt 2 * smoothingParameter Bd ε < σ)
    (hκ : IsClosestPoint (dualLatticeSet Bd) u (κ u)) : Prop := dualSumR Bd (fun x => gaussScalar σ⁻¹ (vecDistR x u)) <
      gaussScalar σ⁻¹ (vecDistR u (κ u)) +
        ε * gaussScalar (Real.sqrt 2 / σ) (vecDistR u (κ u))

end Qatlib.Papers.QuantumLWE25.MainResults
