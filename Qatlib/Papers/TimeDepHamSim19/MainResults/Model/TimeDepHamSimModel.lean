/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Time-dependent Hamiltonian simulation: shared paper-layer model

**Fixed paper version.** arXiv:1906.07115 (Haah, Hastings, Kothari, Low, *Quantum
algorithm for simulating real time evolution of lattice Hamiltonians*).  All theorem and
equation numbers below refer to the `1906.07115.txt` text in the qatlas asset store (the
qatlas asset markdown/status service is currently returning 503, see issue #4; the fixed
PDF/text pair was used instead).

This module fixes the notation shared by every claim file under
`QuantumAlgorithmDev.Papers.TimeDepHamSim19.MainResults`.  Nothing here is specific to one
claim; it is the paper's ``mathematical setting'' (Sections 2–3), expressed with the
Frozen time-ordered exponential `orderedEvolution`.

## Main definitions

* `Op D` — the algebra of `D × D` complex matrices, `D = 2 ^ n` for `n` qubits;
* `opNorm A`, `maxNorm A` — spectral norm `‖A‖_∞` and max-entry norm `‖A‖_max`;
* `hamL1`, `hamMaxL1`, `hamMaxLinf`, `hamL1One` — the four integral norms
  `‖H‖_{∞,1}`, `‖H‖_{max,1}`, `‖H‖_{max,∞}`, `‖H‖_{∞,1,1}` of Section 2;
* `evo H s t` — the time-ordered exponential `E(t,s) = exp_T(-i ∫_s^t H)`;
* `unitaryChannel E`, `channelDiamond`, `channelDiamondDist` — the channel `E(·)E†` and
  the diamond norm / diamond distance of paper equation (17) (normalisation with **no**
  factor `1/2`, matching the paper);
* `qdriftWeight`, `qdriftChannel`, `chainedQdrift` — continuous qDRIFT (49), (70), (165)
  and its long-time chained version (71);
* `lcWeight`, `lcQdriftChannel`, `chainedLCQdrift` — the LC version (86), (95);
* `avgHam`, `avgEvo` — the average Hamiltonian `H_av = t⁻¹∫H` and `E_av(t) = e^{-itH_av}`;
* `productFormulaEvo`, `segmentQueryCount`, `discreteQueryCount` — the explicit
  product-formula propagation and the query-count expressions of Theorem 4;
* `alphaL11`, `lcuHam`, `dysonTruncation` — LCU data and the truncated Dyson series.

The predicate vocabulary `IsHermitianOn`, `NonzeroOn`, `PiecewiseContinuous`, `SparseOn`
captures the paper's standing hypotheses.

## Proven auxiliary lemmas

`opNorm_nonneg`, `maxNorm_nonneg`, `maxNorm_entry_le`, `hamL1_nonneg`,
`hamMaxL1_nonneg`, `hamL1One_nonneg`, `qdriftWeight_nonneg`, `channelDiamondDist_self`,
`channelDiamondDist_nonneg`, `chainSegments_zero` are proved completely here; they are
used by several claim files.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators ENNReal

namespace Qatlib.Papers.TimeDepHamSim19.MainResults

/-- Complex `D × D` matrices: the paper's operator space on a `D`-dimensional Hilbert
space (`D = 2 ^ n` for `n` qubits).  This is definitionally the Frozen `Operator D`
(`QuantumAlgorithm.Concepts.MbqcFlow.FlowDecision.Operator`). -/
abbrev Op (D : ℕ) : Type := Matrix (Fin D) (Fin D) ℂ

/-- A time-dependent Hamiltonian on a `D`-dimensional space: a matrix-valued function of
time. -/
abbrev Ham (D : ℕ) : Type := ℝ → Op D

/-- Spectral (`∞`-) norm of an operator, `‖A‖_∞` in the paper. -/
def opNorm {D : ℕ} (A : Op D) : ℝ := ‖A‖

/-- Max-entry norm `‖A‖_max = max_{j,k} |A_{jk}|` of Section 2.  It is the sup of the
`ℝ≥0`-valued entrywise norms, so that the empty matrix (dimension `0`) has max-norm `0`. -/
def maxNorm {D : ℕ} (A : Op D) : ℝ :=
  ((((Finset.univ : Finset (Fin D × Fin D)).sup
    (fun p : Fin D × Fin D => ‖A p.1 p.2‖₊) : NNReal)) : ℝ)

/-- The integral `∫_0^t f` of a real-valued function on a time interval. -/
def intervalL1 (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, f τ

/-- `‖H‖_{∞,1} = ∫_0^t ‖H(τ)‖_∞ dτ`. -/
def hamL1 {D : ℕ} (H : Ham D) (t : ℝ) : ℝ := intervalL1 (fun τ => opNorm (H τ)) t

/-- `‖H‖_{max,1} = ∫_0^t ‖H(τ)‖_max dτ`. -/
def hamMaxL1 {D : ℕ} (H : Ham D) (t : ℝ) : ℝ := intervalL1 (fun τ => maxNorm (H τ)) t

/-- `‖H‖_{max,∞} = sup_{τ ∈ [0,t]} ‖H(τ)‖_max`. -/
def hamMaxLinf {D : ℕ} (H : Ham D) (t : ℝ) : ℝ :=
  sSup ((fun τ => maxNorm (H τ)) '' Set.Icc 0 t)

/-- `‖H‖_{∞,1,1} = ∑_{l=1}^{L} ∫_0^t ‖H_l(τ)‖_∞ dτ` for an `L`-term decomposition. -/
def hamL1One {D L : ℕ} (Hl : Fin L → Ham D) (t : ℝ) : ℝ :=
  ∑ l : Fin L, ∫ τ in (0 : ℝ)..t, opNorm (Hl l τ)

/-- The Hamiltonian is Hermitian at every point of `[0,t]` (quantum-mechanical
self-adjointness). -/
def IsHermitianOn {D : ℕ} (H : Ham D) (t : ℝ) : Prop :=
  ∀ τ, 0 ≤ τ → τ ≤ t → (H τ).IsHermitian

/-- The Hamiltonian is nonzero at every point of `[0,t]`. -/
def NonzeroOn {D : ℕ} (H : Ham D) (t : ℝ) : Prop :=
  ∀ τ, 0 ≤ τ → τ ≤ t → H τ ≠ 0

/-- The Hamiltonian is continuous except on a finite set of times (paper's standing
hypothesis ``continuous except at a finite number of points''). -/
def PiecewiseContinuous {D : ℕ} (H : Ham D) (t : ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ τ, 0 ≤ τ → τ ≤ t → τ ∉ (S : Set ℝ) → ContinuousAt H τ

/-- `H` is `d`-sparse at every time: every row and every column of `H τ` has at most `d`
nonzero entries.  Phrased with an explicit finite support set per row/column, so no
decidability of `ℂ` is needed. -/
def SparseOn {D : ℕ} (H : Ham D) (t : ℝ) (d : ℕ) : Prop :=
  (∀ τ, 0 ≤ τ → τ ≤ t → ∀ i : Fin D,
      ∃ S : Finset (Fin D), S.card ≤ d ∧ ∀ j, H τ i j ≠ 0 → j ∈ S) ∧
  (∀ τ, 0 ≤ τ → τ ≤ t → ∀ j : Fin D,
      ∃ S : Finset (Fin D), S.card ≤ d ∧ ∀ i, H τ i j ≠ 0 → i ∈ S)

/-- A division `0 = t₀ < t₁ < ⋯ < t_r = t` of `[0,t]` into `r` subintervals, indexed by
`ℕ` so that recursive chaining is structural. -/
def IsDivision (tdiv : ℕ → ℝ) (r : ℕ) (t : ℝ) : Prop :=
  tdiv 0 = 0 ∧ tdiv r = t ∧ ∀ i j : ℕ, i < j → j ≤ r → tdiv i < tdiv j

namespace IsDivision

/-- The zero property in the paper model. -/
theorem zero {tdiv : ℕ → ℝ} {r : ℕ} {t : ℝ} (h : IsDivision tdiv r t) : tdiv 0 = 0 :=
  h.1

/-- The last property in the paper model. -/
theorem last {tdiv : ℕ → ℝ} {r : ℕ} {t : ℝ} (h : IsDivision tdiv r t) : tdiv r = t :=
  h.2.1

/-- The strict property in the paper model. -/
theorem strict {tdiv : ℕ → ℝ} {r : ℕ} {t : ℝ} (h : IsDivision tdiv r t)
    {i j : ℕ} (hij : i < j) (hj : j ≤ r) : tdiv i < tdiv j :=
  h.2.2 i j hij hj

end IsDivision

/-- The time-ordered exponential `E(t,s) = exp_T(-i ∫_s^t H)`, defined as the Frozen
`orderedEvolution` for the generator `-iH`.  Because the Frozen generator convention is
`A = -iH` (the propagator solves `d/dt U = -A(t) U`), we pass `fun τ => I • H τ`. -/
def evo {D : ℕ} (H : Ham D) (s t : ℝ) : Op D :=
  Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
    (fun τ => Complex.I • H τ) s t

/-- The quantum channel `E(·) = E ρ E†` associated with a unitary `E`. -/
def unitaryChannel {D : ℕ} (E : Op D) : Op D → Op D :=
  fun ρ => E * ρ * E.conjTranspose

/-- Amplification `Φ ⊗ id_r` of a channel by an `r`-dimensional reference register.  A raw
input `X` on `ℂ^r ⊗ ℂ^D` is cut into `D × D` blocks `ρ_{ij}`, each of which is pushed
through `Φ`. -/
def amplify {D : ℕ} (Φ : Op D → Op D) (r : ℕ)
    (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ :=
  fun p q => Φ (fun a b => X (p.1, a) (q.1, b)) p.2 q.2

/-- The diamond norm of a channel, paper equation (17): supremum over all finite
reference dimensions `r` and all raw inputs of trace norm `≤ 1` of the trace norm of the
amplified output.  No factor `1/2`, matching the paper's convention. -/
def channelDiamond {D : ℕ} (Φ : Op D → Op D) : ENNReal :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ,
    if Matrix.traceNorm X ≤ 1 then ENNReal.ofReal (Matrix.traceNorm (amplify Φ r X)) else 0

/-- The diamond-norm distance between two channels, `‖Φ - Ψ‖_◇`, defined by the same
supremum applied to the difference of the amplified outputs.  This is the quantity bounded
in Theorems 5, 7, 8, 5₀, 7′, 11₀ and 12. -/
def channelDiamondDist {D : ℕ} (Φ Ψ : Op D → Op D) : ENNReal :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ,
    if Matrix.traceNorm X ≤ 1 then
      ENNReal.ofReal (Matrix.traceNorm (amplify Φ r X - amplify Ψ r X)) else 0

/-! ## Proven basic facts about the norms and the diamond distance -/

theorem opNorm_nonneg {D : ℕ} (A : Op D) : 0 ≤ opNorm A := norm_nonneg A

/-- The quantity `maxNorm` is nonnegative. -/
theorem maxNorm_nonneg {D : ℕ} (A : Op D) : 0 ≤ maxNorm A := by
  unfold maxNorm
  exact NNReal.coe_nonneg _

/-- The max Norm entry le property in the paper model. -/
theorem maxNorm_entry_le {D : ℕ} (A : Op D) (p : Fin D × Fin D) :
    ‖A p.1 p.2‖ ≤ maxNorm A := by
  unfold maxNorm
  have h : ‖A p.1 p.2‖₊ ≤ (Finset.univ : Finset (Fin D × Fin D)).sup
      (fun p : Fin D × Fin D => ‖A p.1 p.2‖₊) :=
    Finset.le_sup (f := fun p : Fin D × Fin D => ‖A p.1 p.2‖₊) (Finset.mem_univ p)
  exact_mod_cast h

/-- The quantity `hamL1` is nonnegative. -/
theorem hamL1_nonneg {D : ℕ} (H : Ham D) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hamL1 H t := by
  unfold hamL1 intervalL1
  exact intervalIntegral.integral_nonneg ht (fun τ _ => opNorm_nonneg (H τ))

/-- The quantity `hamMaxL1` is nonnegative. -/
theorem hamMaxL1_nonneg {D : ℕ} (H : Ham D) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hamMaxL1 H t := by
  unfold hamMaxL1 intervalL1
  exact intervalIntegral.integral_nonneg ht (fun τ _ => maxNorm_nonneg (H τ))

/-- The quantity `hamL1One` is nonnegative. -/
theorem hamL1One_nonneg {D L : ℕ} (Hl : Fin L → Ham D) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ hamL1One Hl t := by
  unfold hamL1One
  exact Finset.sum_nonneg (fun l _ =>
    intervalIntegral.integral_nonneg ht (fun τ _ => opNorm_nonneg (Hl l τ)))

/-- The qDRIFT probability weight `p(τ) = ‖H(τ)‖_∞ / ‖H‖_{∞,1}` of (49) is nonnegative. -/
def qdriftWeight {D : ℕ} (H : Ham D) (t τ : ℝ) : ℝ := opNorm (H τ) / hamL1 H t

/-- The quantity `qdriftWeight` is nonnegative. -/
theorem qdriftWeight_nonneg {D : ℕ} (H : Ham D) {t : ℝ} (ht : 0 ≤ t) (τ : ℝ) :
    0 ≤ qdriftWeight H t τ := by
  unfold qdriftWeight
  exact div_nonneg (opNorm_nonneg _) (hamL1_nonneg H ht)

/-- The diamond distance of a channel from itself vanishes. -/
theorem channelDiamondDist_self {D : ℕ} (Φ : Op D → Op D) : channelDiamondDist Φ Φ = 0 := by
  unfold channelDiamondDist
  simp only [sub_self, Matrix.traceNorm_zero, ENNReal.ofReal_zero]
  simp

/-- The quantity `channelDiamondDist` is nonnegative. -/
theorem channelDiamondDist_nonneg {D : ℕ} (Φ Ψ : Op D → Op D) :
    0 ≤ channelDiamondDist Φ Ψ := bot_le

/-- Arithmetic step behind equation (72)/(97) of the paper: if the number of segments `r`
is at least `4 s² / ε` then the error `4 s² / r` is at most `ε`.  This is the
`r ≥ 4⌈‖H‖²_{∞,1}/ε⌉ ⟹ error ≤ ε` implication used in Theorems 7 and 7′. -/
theorem four_mul_sq_div_le {s ε r : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (h : 4 * s ^ 2 / ε ≤ r) : 4 * s ^ 2 / r ≤ ε := by
  rw [div_le_iff₀ hr]
  have h' : 4 * s ^ 2 ≤ r * ε := (div_le_iff₀ hε).mp h
  linarith

/-! ## Continuous qDRIFT (Section 3) -/

/-- The exponential `e^{-i H(τ) / w}` appearing in the qDRIFT mixture, written through the
frozen `HamiltonianEvolution` at time `w⁻¹`. -/
def expmGen {D : ℕ} (H : Ham D) (τ w : ℝ) : Op D :=
  Qatlib.Foundations.PureStateMath.HamiltonianEvolution (H τ) w⁻¹

/-- The normalised qDRIFT weight on a single time interval `[a,b]`,
`‖H(τ)‖ / ∫_a^b ‖H‖`. -/
def segWeight {D : ℕ} (H : Ham D) (a b τ : ℝ) : ℝ :=
  opNorm (H τ) / ∫ s in a..b, opNorm (H s)

/-- A single continuous-qDRIFT segment `U(b,a)` of equation (49) (with the normalisation
of `p` over `[a,b]`), applied to a raw input `ρ`. -/
def qdriftSegment {D : ℕ} (H : Ham D) (a b : ℝ) (ρ : Op D) : Op D :=
  ∫ τ in a..b, ((segWeight H a b τ : ℝ) : ℂ) •
    (expmGen H τ (segWeight H a b τ) * ρ *
      (expmGen H τ (segWeight H a b τ)).conjTranspose)

/-- The continuous qDRIFT channel `U(t,0)` of (49)/(70)/(165). -/
def qdriftChannel {D : ℕ} (H : Ham D) (t : ℝ) : Op D → Op D :=
  fun ρ => qdriftSegment H 0 t ρ

/-- Chain a family of segment channels over a division, in time order: the last segment is
applied last. -/
def chainSegments {D : ℕ} (seg : ℝ → ℝ → Op D → Op D) : ℕ → (ℕ → ℝ) → Op D → Op D
  | 0, _, ρ => ρ
  | n + 1, tdiv, ρ => seg (tdiv 0) (tdiv 1) (chainSegments seg n (fun j => tdiv (j + 1)) ρ)

/-- The chain Segments zero property in the paper model. -/
@[simp] theorem chainSegments_zero {D : ℕ} (seg : ℝ → ℝ → Op D → Op D) (tdiv : ℕ → ℝ)
    (ρ : Op D) : chainSegments seg 0 tdiv ρ = ρ := rfl

/-- The long-time chained qDRIFT channel `∏_{j<r} U(t_{j+1}, t_j)ρU(t_{j+1}, t_j)†` of
Theorem 7 (71). -/
def chainedQdrift {D : ℕ} (H : Ham D) (r : ℕ) (tdiv : ℕ → ℝ) : Op D → Op D :=
  chainSegments (qdriftSegment H) r tdiv

/-! ## LC qDRIFT (Section 3.2, Theorems 5₀/7′) -/

/-- The LC probability weight `p_l(τ) = ‖H_l(τ)‖ / ‖H‖_{∞,1,1}` restricted to a segment
`[a,b]` (the denominator is `∑_k ∫_a^b ‖H_k‖`). -/
def lcWeight {D L : ℕ} (Hl : Fin L → Ham D) (a b τ : ℝ) (l : Fin L) : ℝ :=
  opNorm (Hl l τ) / ∑ k : Fin L, ∫ s in a..b, opNorm (Hl k s)

/-- A single LC-qDRIFT segment of (86)/(95), applied to a raw input `ρ`. -/
def lcQdriftSegment {D L : ℕ} (Hl : Fin L → Ham D) (a b : ℝ) (ρ : Op D) : Op D :=
  ∑ l : Fin L, ∫ τ in a..b, ((lcWeight Hl a b τ l : ℝ) : ℂ) •
    (expmGen (Hl l) τ (lcWeight Hl a b τ l) * ρ *
      (expmGen (Hl l) τ (lcWeight Hl a b τ l)).conjTranspose)

/-- The LC-qDRIFT channel `U(t,0)` of (86). -/
def lcQdriftChannel {D L : ℕ} (Hl : Fin L → Ham D) (t : ℝ) : Op D → Op D :=
  fun ρ => lcQdriftSegment Hl 0 t ρ

/-- The long-time chained LC-qDRIFT channel of Theorem 7′ (96). -/
def chainedLCQdrift {D L : ℕ} (Hl : Fin L → Ham D) (r : ℕ) (tdiv : ℕ → ℝ) : Op D → Op D :=
  chainSegments (lcQdriftSegment Hl) r tdiv

/-! ## Averaging (Section 4) -/

/-- The average Hamiltonian `H_av = t⁻¹ ∫_0^t H(τ) dτ`. -/
def avgHam {D : ℕ} (H : Ham D) (t : ℝ) : Op D :=
  ((t : ℂ))⁻¹ • ∫ τ in (0 : ℝ)..t, H τ

/-- `E_av(t) = e^{-i t H_av}`. -/
def avgEvo {D : ℕ} (H : Ham D) (t : ℝ) : Op D :=
  Qatlib.Foundations.PureStateMath.HamiltonianEvolution (avgHam H t) t

/-! ## Product-formula propagation and query counts (Theorem 4) -/

/-- The `k`-th frozen step `e^{-i(t/r)H(k t/r)}` of the product formula (29). -/
def productFormulaStep {D : ℕ} (H : Ham D) (t : ℝ) (r k : ℕ) : Op D :=
  Qatlib.Foundations.PureStateMath.HamiltonianEvolution
    (H (((k : ℕ) : ℝ) * t / (r : ℝ))) (t / (r : ℝ))

/-- The `r`-step frozen product formula `∏_{k<r} e^{-i(t/r)H(k t/r)}` of (29), with the
steps composed in the written order `U_0 U_1 ⋯ U_{r-1}`. -/
def productFormulaEvo {D : ℕ} (H : Ham D) (t : ℝ) : ℕ → Op D
  | 0 => 1
  | r + 1 => productFormulaEvo H t r * productFormulaStep H t (r + 1) r

/-- The fractional-query count `T = ∑_k d² ‖H(k t/r)‖_max (t/r)` of equation (37). -/
def segmentQueryCount {D : ℕ} (d : ℕ) (H : Ham D) (t : ℝ) (r : ℕ) : ℝ :=
  ∑ k : Fin r, (d : ℝ) ^ 2 * maxNorm (H (((k : ℕ) : ℝ) * t / (r : ℝ))) * (t / (r : ℝ))

/-- The discrete-query count obtained from the fractional count `T` by the conversion
`T · log(T/ε) / log log(T/ε)` of equation (27). -/
def discreteQueryCount {D : ℕ} (d : ℕ) (H : Ham D) (t ε : ℝ) (r : ℕ) : ℝ :=
  (1 + segmentQueryCount d H t r) *
      Real.log ((1 + segmentQueryCount d H t r) / ε) /
    Real.log (Real.log ((1 + segmentQueryCount d H t r) / ε))

/-! ## LCU data and Dyson truncation (Theorems 10, 10′) -/

/-- `‖α‖_{1,1} = ∫_0^t ∑_l |α_l(τ)| dτ`, the LCU coefficient norm of (104). -/
def alphaL11 {L : ℕ} (α : Fin L → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, ∑ l : Fin L, |α l τ|

/-- The Hamiltonian `∑_l α_l(τ) H_l` assembled from LCU coefficients and terms. -/
def lcuHam {D L : ℕ} (α : Fin L → ℝ → ℝ) (Hl : Fin L → Op D) : Ham D :=
  fun τ => ∑ l : Fin L, ((α l τ : ℝ) : ℂ) • Hl l

/-- The truncation of the Dyson series of `E(t,s)` to its first `N` iterated integrals
(the object a Dyson-series algorithm evaluates). -/
def dysonTruncation {D : ℕ} (H : Ham D) (s t : ℝ) (N : ℕ) : Op D :=
  (Finset.range N).sum (fun n =>
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedDysonTerm
      (fun τ => Complex.I • H τ) s n t)

end Qatlib.Papers.TimeDepHamSim19.MainResults
