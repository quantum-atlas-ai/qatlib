/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.SlowHamSim26.GevreyTools.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / FourierTrunc — Fourier–Floquet model

Fixed source: arXiv:2608.17653v1, §4 (pp. 18–26).  This file fixes the objects
shared by Lemma 4.1–Theorem 4.5:

* `fourierCoeff T H m` is the Fourier coefficient `H̃_m` of (4.17),
  `(2T)⁻¹ ∫₀^{2T} H(t) e^{-imωt} dt` with `ω = π/T` (so that `H` has period
  `2T` and `e^{imωt}` has period `2T`);
* `floquetIndexVal L i` enumerates the truncated index set
  `D^L = {-L+1, …, L}` of (4.43) by `i : Fin (2L)`;
* `Heff T L Hm` is the explicit effective Hamiltonian (4.46) acting on
  `D^L ⊗ ℂ^d`;
* `timeEvol A t = exp(-i t A)` is the matrix exponential;
* `Ssum ρ ζ` is the sum `S(ζ)` of (4.34) and `betaRate` is the constant `β`
  of (4.45).

States are bare amplitude vectors `Fin d → ℂ` with the Euclidean `l2norm`; the
paper's `⟨l|·|l'⟩` is the `(l,l')` block of `floquetBlock`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.FourierTrunc

open scoped Matrix.Norms.L2Operator
open MeasureTheory

/-! ### Fourier coefficients (§4.1, Eq. (4.17)) -/

/-- Fixed arXiv:2608.17653v1, §4.1, Eq. (4.17): the Floquet frequency
`ω = π/T` for a `2T`-periodic Hamiltonian. -/
def omega (T : ℝ) : ℝ := Real.pi / T

/-- Fixed arXiv:2608.17653v1, Eq. (4.17): the Fourier coefficient
`H̃_m = (2T)⁻¹ ∫₀^{2T} H(t) e^{-imωt} dt` of a `T`-time-dependent Hamiltonian
(such an `H` is `2T`-periodic after the paper's rescaling). -/
def fourierCoeff {d : ℕ} (T : ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℂ) (m : ℤ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / (2 * T)) • ∫ t in (0 : ℝ)..(2 * T),
    Complex.exp (-(m : ℂ) * Complex.I * (omega T : ℂ) * (t : ℂ)) • H t

/-- Fixed arXiv:2608.17653v1, Eq. (4.34): the sum
`S(ζ) = Σ_{m=0}^∞ e^{-m^{1/ρ}/ζ}`. -/
def Ssum (ρ ζ : ℝ) : ℝ :=
  ∑' m : ℕ, Real.exp (-((m : ℝ) ^ (1 / ρ)) / ζ)

/-! ### Truncated Floquet index set (§4.2) -/

/-- Fixed arXiv:2608.17653v1, Eq. (4.43): the enumeration of
`D^L = {-L+1, -L+2, …, L}` by `Fin (2L)`, sending `i` to `i - L + 1`. -/
def floquetIndexVal (L : ℕ) (i : Fin (2 * L)) : ℤ := (i : ℤ) - (L : ℤ) + 1

/-- Fixed arXiv:2608.17653v1, Lemma 5.1: the modular subtraction `l ⊖ l'` in
`D^L`, i.e. the representative in `{-L+1, …, L}` of `x` modulo `2L`; the index
argument only witnesses `0 < 2L`. -/
def wrapIndex {L : ℕ} (i0 : Fin (2 * L)) (x : ℤ) : Fin (2 * L) :=
  ⟨((x - (-(L : ℤ) + 1)) % (2 * (L : ℤ))).toNat, by
    have hpos : 0 < 2 * L := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
    have hn : (0 : ℤ) < 2 * (L : ℤ) := by
      have h1 : (0 : ℤ) < ((2 * L : ℕ) : ℤ) := by exact_mod_cast hpos
      simpa using h1
    have hnn : 0 ≤ (x - (-(L : ℤ) + 1)) % (2 * (L : ℤ)) := Int.emod_nonneg _ (ne_of_gt hn)
    rw [Int.toNat_lt hnn]
    simpa using Int.emod_lt_of_pos (x - (-(L : ℤ) + 1)) hn⟩

/-- Fixed arXiv:2608.17653v1, Eq. (4.46): the effective Hamiltonian
`H_eff^L = Σ_l |l⟩⟨l| ⊗ (H̃_0 - lω) + Σ_{l, m≠0, l+m∈D^L} |l⟩⟨l+m| ⊗ H̃_m`,
written as a `(D^L × ℂ^d)` block matrix.  Its `(i,j)` block is `H̃_{l_i-l_j}`
and the diagonal blocks carry the linear potential `-l_i ω`. -/
def Heff {d : ℕ} (T : ℝ) (L : ℕ) (Hm : ℤ → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (Hm 0 - Matrix.scalar (Fin d) ((floquetIndexVal L p.1 : ℂ) * (omega T : ℂ))) p.2 q.2
    else Hm (floquetIndexVal L p.1 - floquetIndexVal L q.1) p.2 q.2

/-- Fixed arXiv:2608.17653v1, Eq. (4.48): the matrix exponential
`e^{-itA}` used for the evolution operator `e^{-i H_eff t}`. -/
def timeEvol {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • A)

/-- The `(i,j)` block `⟨l_i|·|l_j⟩` of an operator on the truncated
Floquet space `D^L ⊗ ℂ^d`, as a `d × d` matrix. -/
def floquetBlock {d L : ℕ}
    (A : Matrix (Fin (2 * L) × Fin d) (Fin (2 * L) × Fin d) ℂ)
    (i j : Fin (2 * L)) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => A ⟨i, a⟩ ⟨j, b⟩

/-! ### The transition-rate constant `β` (Eq. (4.45)) -/

/-- Fixed arXiv:2608.17653v1, Eq. (4.45): the transition-rate constant
`β = h₂ (Σ_{m≥1} e^{-m^{1/ρ}/(2ζ)} + h₃ (log(⌈A/π⌉ - 1) + 1) + h₄)`. -/
def betaRate (ρ ζ A h2 h3 h4 : ℝ) : ℝ :=
  h2 * ((∑' m : ℕ, Real.exp (-(((m : ℝ) + 1) ^ (1 / ρ)) / (2 * ζ))) +
    h3 * (Real.log ((Nat.ceil (A / Real.pi) : ℕ) - 1) + 1) + h4)

/-! ### States and norms -/

/-- Amplitude vector of a `d`-dimensional system (the paper's Hilbert space
`H ≅ ℂ^d`). -/
abbrev Vec (d : ℕ) := Fin d → ℂ

/-- The Euclidean norm of a state, `‖ψ‖ = √(Σ_i ‖ψ_i‖²)`. -/
def l2norm {d : ℕ} (ψ : Vec d) : ℝ := Real.sqrt (∑ i, ‖ψ i‖ ^ 2)

end Qatlib.Papers.SlowHamSim26.FourierTrunc
