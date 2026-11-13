/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import QuantumInfo.Measurements.POVM
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Qatlib.Foundations.PureStateMath.Reflection

set_option backward.isDefEq.respectTransparency false

/-!
# QDecoding23 — core object model

Source: Chailloux--Tillich, *The Quantum Decoding Problem*, fixed arXiv:2310.20651v1
(2023-10-31).  This module fixes the paper's vocabulary on real, reusable objects of the
development library rather than inventing a parallel quantum library:

* `FVec 𝔽 n` is the ambient vector space `F_q^n` (the paper's `𝔽_q` is any finite field
  `𝔽`, with `q = |𝔽|` — the paper only needs `q = p^s` and never the prime-field structure
  directly);
* the additive characters `χ_y(x)` are built from a primitive additive character of `𝔽`
  (`AddChar`, Mathlib), so that `χ_y(x) = ψ (∑ᵢ xᵢ yᵢ)`, matching Definition 19;
* the quantum Fourier transform, the shift `X_b` and the phase `Z_b` operators act on the
  `QState (FVec 𝔽 n)` of `Qatlib.Concepts.MbqcFlow.FlowDecision`;
* the q-ary symmetric channel weights `bernoulliCoeff`, the codeword noise state
  `qaryNoiseState`, and the row-code `codeFrom G` follow Definitions 7--16;
* `bornProb` is the Born statistic `⟨ψ|A|ψ⟩` of an effect `A` on a pure state `ψ`;
* the paper's `o(1)` / `2^{-Ω(n)}` / `Ω(1)` are encoded as the explicit predicates
  `TendsToZero`, `ExpSmall`, `OmegaOne`.

Boundary: this is the *object* layer.  No theorem below asserts a statement that is not
literally in the paper; all algorithm-complexity (poly-time implementability) content is
flagged in the per-claim comments rather than silently dropped.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QDecoding23.MainResults

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

/-! ## §1. The vector space `F_q^n`, characters, QFT, shift/phase operators -/

/-- The vector space `F_q^n`: length-`n` vectors over the finite field `𝔽`. -/
abbrev FVec (𝔽 : Type) (n : ℕ) : Type := Fin n → 𝔽

/-- The field size `q = |𝔽|`. -/
abbrev fieldSize (𝔽 : Type) [Fintype 𝔽] : ℕ := Fintype.card 𝔽

/-- Definition 19: the character `χ_y(x) = ψ (∑ᵢ xᵢ · yᵢ)`, where `ψ` is a primitive
additive character of `𝔽` (the paper's `e^{2πi tr(x·y)/p}`). -/
def charFun {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] (ψ : AddChar 𝔽 ℂ) {n : ℕ}
    (x y : FVec 𝔽 n) : ℂ :=
  ψ (∑ i, x i * y i)

/-- The normalization `1/√(q^n)` of the QFT (Definition 20). -/
def qftScale (𝔽 : Type) [Fintype 𝔽] (n : ℕ) : ℝ :=
  (Real.sqrt ((Fintype.card 𝔽 : ℝ) ^ n))⁻¹

/-- Definition 20: the quantum Fourier transform on `F_q^n`,
`(QFT g)(y) = q^{-n/2} ∑ₓ χₓ(y) g(x)` (using the symmetry `χₓ(y) = χ_y(x)`, Prop. 9.2). -/
def qft {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] (ψ : AddChar 𝔽 ℂ) {n : ℕ}
    (g : QState (FVec 𝔽 n)) : QState (FVec 𝔽 n) :=
  fun y => (qftScale 𝔽 n : ℂ) * ∑ x, charFun ψ x y * g x

/-- Definition 21: the shift operator `X_b |x⟩ = |x + b⟩`, acting on amplitude vectors as
`(X_b g)(y) = g(y - b)`. -/
def shiftOp {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] {n : ℕ}
    (b : FVec 𝔽 n) (g : QState (FVec 𝔽 n)) : QState (FVec 𝔽 n) :=
  fun y => g (y - b)

/-- Definition 21: the phase operator `Z_b |x⟩ = χ_x(b)|x⟩`, acting pointwise. -/
def phaseOp {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] (ψ : AddChar 𝔽 ℂ) {n : ℕ}
    (b : FVec 𝔽 n) (g : QState (FVec 𝔽 n)) : QState (FVec 𝔽 n) :=
  fun x => charFun ψ x b * g x

/-- The computational basis vector `|x₀⟩` on `F_q^n`. -/
def basisVec {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (x₀ : FVec 𝔽 n) : QState (FVec 𝔽 n) :=
  fun y => if y = x₀ then 1 else 0

/-! ## §2. Hamming weight and the q-ary symmetric channel -/

/-- The Hamming weight `|e|` (Definition 13 context). -/
def hammingWeight {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (e : FVec 𝔽 n) : ℕ :=
  (Finset.univ.filter (fun i => e i ≠ 0)).card

/-- Definition 7 / Definition 9: the q-ary symmetric-channel weight
`(ω/(q-1))^{|e|} (1-ω)^{n-|e|}`. -/
def bernoulliCoeff {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ω : ℝ) (e : FVec 𝔽 n) : ℝ :=
  (ω / ((Fintype.card 𝔽 : ℝ) - 1)) ^ (hammingWeight e) *
    (1 - ω) ^ (n - hammingWeight e)

/-- Definition 13: the codeword state `|ψ_c⟩ = ∑ₑ √(b(e)) |c + e⟩` of the q-ary symmetric
channel, with real square-root amplitude `√(bernoulliCoeff ω (y - c))` at `y`. -/
def qaryNoiseState {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ω : ℝ) (c : FVec 𝔽 n) : QState (FVec 𝔽 n) :=
  fun y => ((Real.sqrt (bernoulliCoeff ω (y - c)) : ℝ) : ℂ)

/-! ## §3. Linear codes and their duals -/

/-- The row code `C = {mG : m ∈ F_q^k}` of a generating matrix `G`: the `𝔽`-span of the rows
of `G` (Definitions 10 / 13). -/
def codeFrom {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {k n : ℕ}
    (G : Matrix (Fin k) (Fin n) 𝔽) : Submodule 𝔽 (FVec 𝔽 n) :=
  Submodule.span 𝔽 (Set.range (fun i : Fin k => (fun j : Fin n => G i j)))

/-- The standard bilinear pairing `⟨x,y⟩ = ∑ᵢ xᵢ yᵢ` on `F_q^n`. -/
def dotBilin {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] {ι : Type} [Fintype ι]
    (x y : ι → 𝔽) : 𝔽 :=
  ∑ i, x i * y i

/-- The dual code `C^⊥ = {y : ∀ c ∈ C, ⟨c,y⟩ = 0}` with respect to `dotBilin`. -/
def dualCode {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] {ι : Type} [Fintype ι]
    (C : Submodule 𝔽 (ι → 𝔽)) : Submodule 𝔽 (ι → 𝔽) where
  carrier := { y | ∀ c ∈ C, dotBilin c y = 0 }
  zero_mem' := by
    intro c _
    simp [dotBilin]
  add_mem' := by
    intro a b ha hb c hc
    have h : dotBilin c (a + b) = dotBilin c a + dotBilin c b := by
      simp only [dotBilin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    show dotBilin c (a + b) = 0
    rw [h, ha c hc, hb c hc, add_zero]
  smul_mem' := by
    intro r a ha c hc
    have h : dotBilin c (r • a) = r * dotBilin c a := by
      simp only [dotBilin, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    show dotBilin c (r • a) = 0
    rw [h, ha c hc, mul_zero]

/-- Definition 17: the puncturing restriction map `c ↦ c|_J` onto the coordinates in `J`. -/
def restrictLM {𝔽 : Type} [Field 𝔽] {n : ℕ} (J : Finset (Fin n)) :
    (Fin n → 𝔽) →ₗ[𝔽] (J → 𝔽) where
  toFun c := fun i => c i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The submodule of vectors supported inside `J` (zero outside `J`). -/
def supportedIn {𝔽 : Type} [Field 𝔽] {n : ℕ} (J : Finset (Fin n)) :
    Submodule 𝔽 (Fin n → 𝔽) where
  carrier := { c | ∀ i, i ∉ J → c i = 0 }
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro a b ha hb i hi
    simp only [Pi.add_apply, Set.mem_setOf_eq] at *
    rw [ha i hi, hb i hi, add_zero]
  smul_mem' := by
    intro r a ha i hi
    simp only [Pi.smul_apply, smul_eq_mul, Set.mem_setOf_eq] at *
    rw [ha i hi, mul_zero]

/-- Definition 17: the punctured code `C_J = {c|_J : c ∈ C}`. -/
def puncturedCode {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] {n : ℕ}
    (C : Submodule 𝔽 (Fin n → 𝔽)) (J : Finset (Fin n)) : Submodule 𝔽 (J → 𝔽) :=
  C.map (restrictLM J)

/-- Definition 17: the shortened code `C^J = {c|_J : c ∈ C, c = 0 outside J}`. -/
def shortenedCode {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] {n : ℕ}
    (C : Submodule 𝔽 (Fin n → 𝔽)) (J : Finset (Fin n)) : Submodule 𝔽 (J → 𝔽) :=
  (C ⊓ supportedIn J).map (restrictLM J)

/-! ## §4. Born statistics and the asymptotic vocabulary -/

/-- The Born probability `⟨ψ|A|ψ⟩` of a Hermitian effect `A` on the pure state `ψ`. -/
def bornProb {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (A : Matrix (FVec 𝔽 n) (FVec 𝔽 n) ℂ) (ψ : QState (FVec 𝔽 n)) : ℝ :=
  (Qatlib.Foundations.PureStateMath.Inner ψ (A *ᵥ ψ)).re

/-- `f = o(1)` as `n → ∞`. -/
def TendsToZero (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n| ≤ ε

/-- `f = 2^{-Ω(n)}`, i.e. `f n ≤ 2^{-c n}` eventually for some `c > 0`. -/
def ExpSmall (f : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∃ N, ∀ n ≥ N, f n ≤ Real.rpow 2 (-(c * (n : ℝ)))

/-- `f = Ω(1)`, i.e. eventually above a positive constant. -/
def OmegaOne (f : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∃ N, ∀ n ≥ N, c ≤ f n

/-- `solves-with-probability p`: a threshold predicate for success probabilities. -/
def EventuallyAtLeast (f : ℕ → ℝ) (p : ℕ → ℝ) : Prop :=
  ∃ N, ∀ n ≥ N, p n ≤ f n

/-- The q-ary relative entropy `h_q` of Definition 2, on `[0,1]`. -/
def qaryEntropy (q : ℝ) (x : ℝ) : ℝ :=
  -x * Real.log (x / (q - 1)) / Real.log q - (1 - x) * Real.log (1 - x) / Real.log q

end Qatlib.Papers.QDecoding23.MainResults
