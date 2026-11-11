/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

set_option backward.isDefEq.respectTransparency false

/-!
# Kuperberg 2013, Proposition 3.1: Fourier block structure and uniform measurement

Source: Greg Kuperberg, *Another subexponential-time quantum algorithm for the dihedral
hidden subgroup problem*, arXiv:1112.3333v1 (TQC 2013), Proposition 3.1, Section 3.2,
page 4 (txt line 245, PDF p. 4).

The proposition concerns a finite abelian group `A`, a finite label set `J`, a family of
injective functions `f j : A → X` of the shift form `f j a = f0 (a + ψ j)` (the paper
writes `f j a = f0 (a + φ_j(s))`; we absorb the hidden shift `φ_j(s)` into `ψ j`), and
the channel `E` that discards the `X` register after writing `f`, applied to the state
`ρ = σ ⊗ |A⟩⟨A|` of eq. (1) (with the uniform pure state on `C[A]`, i.e. the maximally
mixed state on `A`).

The paper proves two facts:
1. `E(ρ)` is block diagonal with respect to the eigenspaces of the measurement of the
   Fourier mode `|b̂⟩` (the characters `AddChar A ℂ`);
2. that measurement is uniformly distributed.

We formalize both:
* `prop31_blockDiagonal_formula`: applying `E(ρ)` to the Fourier mode
  `|k⟩ ⊗ |χ⟩` produces only character `χ`, with the explicit label-to-label coefficient
  `(σ j k / |A|) · χ(ψ j - ψ k)`.  The corollary `prop31_blockDiagonal_sector` states
  that the image is a `J`-linear combination of the same Fourier mode `χ`, i.e. no
  different character mixes in.
* `prop31_measurement_uniform`: the Born weight of the character projector
  `fourierSectorProjector χ` on `E(ρ)` is `1 / |A|`, for every `χ`, whenever
  `trace σ = 1`.

Proof route (following the paper): translation invariance of `ρ` and of `E` makes `E(ρ)`
a convolution operator `convMatrix g` with kernel `g j k d`, whose Fourier transform is
diagonal in the character label; injectivity of `f0` makes the `j = k` slice supported at
`d = 0`, which gives the uniform character weight through character orthogonality.

Related Frozen development: `QuantumAlgorithm.Papers.DihHSPSieve03.RecordExtract.dihedralRecordLaw`
proves the concrete record law of the dihedral sieve circuit (fiber weights `1/2^n` and
the one-query register decomposition).  That is the concrete dihedral instance of the
state produced here, not the same proposition; it is referenced as partial support for
claim c003 rather than reused as a hypothesis.
-/

set_option autoImplicit false

open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.DihedralHSP13.MainResults.RecordExtract

open Matrix

/-! ## §1. Fourier modes and the sector projector on `J × A` -/

section Fourier

variable {J A : Type*} [Fintype J] [DecidableEq J] [AddCommGroup A] [Fintype A]
  [DecidableEq A]

/-- The Fourier mode `|k⟩ ⊗ |χ⟩` of the register `C[J] ⊗ C[A]`: label `k` together with
the additive character `χ`.  This is the paper's `|j⟩|b̂⟩` basis vector. -/
noncomputable def fourierVec (k : J) (χ : AddChar A ℂ) : J × A → ℂ :=
  fun p => if p.1 = k then (χ p.2 : ℂ) else 0

/-- The spectral projector of the character `χ`, i.e. the orthogonal projector onto the
eigenspace `C[J] ⊗ |b̂⟩` of the Fourier-mode measurement.  It acts as the identity on
`C[J]` and as `|A|⁻¹ conj(χ a) χ c` on `C[A]`. -/
noncomputable def fourierSectorProjector (χ : AddChar A ℂ) :
    Matrix (J × A) (J × A) ℂ :=
  fun p q => if p.1 = q.1 then (1 / (Fintype.card A : ℂ)) * conj (χ p.2) * χ q.2 else 0

/-- Character orthogonality in the form used below: `∑ a, conj(χ a) χ a = |A|`. -/
theorem sum_char_conj_mul (χ : AddChar A ℂ) :
    (∑ a, (conj (χ a) : ℂ) * χ a) = (Fintype.card A : ℂ) := by
  have h := AddChar.wInner_cWeight_self (R := ℂ) χ
  rw [RCLike.wInner_cWeight_eq_expect] at h
  simp only [RCLike.inner_apply] at h
  rw [Fintype.expect_eq_sum_div_card] at h
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h' : (∑ a, χ a * (conj (χ a) : ℂ)) = (Fintype.card A : ℂ) := by
    rw [div_eq_iff hcard] at h
    simpa using h
  calc
    (∑ a, (conj (χ a) : ℂ) * χ a) = ∑ a, χ a * (conj (χ a) : ℂ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_comm]
    _ = (Fintype.card A : ℂ) := h'

end Fourier

/-! ## §2. Convolution operators and their Fourier block structure -/

section Convolution

variable {J A : Type*} [Fintype J] [DecidableEq J] [AddCommGroup A] [Fintype A]
  [DecidableEq A]

/-- A translation-invariant operator on `C[J] ⊗ C[A]`, written as a convolution with
kernel `g j k d` acting on the difference `c - a` of the `A` registers.  This is the
general form of `E(ρ)` established in the paper's proof from translation invariance. -/
def convMatrix (g : J → J → A → ℂ) : Matrix (J × A) (J × A) ℂ :=
  fun p q => g p.1 q.1 (q.2 - p.2)

/-- Shifting the summation variable turns the convolution kernel into the character
weight `(∑ d, h d χ d) · χ a`. -/
theorem sum_shift_chi (h : A → ℂ) (a : A) (χ : AddChar A ℂ) :
    (∑ c, h (c - a) * χ c) = (∑ d, h d * χ d) * χ a := by
  have hc : ∀ c : A, (χ c : ℂ) = χ a * χ (c - a) := by
    intro c
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  calc
    (∑ c, h (c - a) * χ c) = ∑ c, h (c - a) * (χ a * χ (c - a)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hc c]
    _ = ∑ c, χ a * (h (c - a) * χ (c - a)) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = χ a * ∑ c, h (c - a) * χ (c - a) := by
      rw [Finset.mul_sum]
    _ = χ a * ∑ d, h d * χ d := by
      congr 1
      simpa only [Equiv.subRight_apply] using
        Equiv.sum_comp (Equiv.subRight a) (fun d => h d * χ d)
    _ = (∑ d, h d * χ d) * χ a := by
      rw [mul_comm]

/-- **Fourier block structure (abstract form).**  A convolution operator maps the Fourier
mode `|k⟩ ⊗ |χ⟩` to the mode with the *same* character `χ`, with label coefficients
`∑ d, g j k d χ d`.  This is the operator-level content of "block diagonal with respect to
the eigenspaces of the `|b̂⟩` measurement". -/
theorem convMatrix_mulVec_fourierVec (g : J → J → A → ℂ) (k : J) (χ : AddChar A ℂ) :
    (convMatrix g).mulVec (fourierVec k χ) =
      fun p => (∑ d, g p.1 k d * χ d) * χ p.2 := by
  funext p
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have hinner : ∀ j : J,
      (∑ a, convMatrix g p (j, a) * fourierVec k χ (j, a)) =
        if j = k then (∑ d, g p.1 k d * χ d) * χ p.2 else 0 := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      simp only [convMatrix, fourierVec, if_true]
      exact sum_shift_chi (fun d => g p.1 j d) p.2 χ
    · have h0 : ∀ a : A, fourierVec k χ (j, a) = 0 := by
        intro a
        simp only [fourierVec, if_neg hjk]
      simp only [h0, mul_zero, Finset.sum_const_zero]
      exact (if_neg hjk).symm
  rw [Finset.sum_eq_single k]
  · simpa using hinner k
  · intro j _ hjk
    rw [hinner j, if_neg hjk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Evaluating a kernel against a single character value. -/
theorem sum_ite_single (d0 : A) (c : ℂ) (χ : AddChar A ℂ) :
    (∑ d, (if d = d0 then c else 0) * χ d) = c * χ d0 := by
  rw [Finset.sum_eq_single d0]
  · simp
  · intro d _ hd
    rw [if_neg hd, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ d0) h

end Convolution

/-! ## §3. The discarded-output channel `E` on `ρ = σ ⊗ |A⟩⟨A|` -/

section Channel

variable {J A X : Type*} [Fintype J] [DecidableEq J] [AddCommGroup A] [Fintype A]
  [DecidableEq A]

/-- The channel `E` of the paper: write `f j a` into the output register and discard it.
On density matrices this is `E(ρ)(p,q) = ρ(p,q)` when the written values agree and `0`
otherwise (equivalently, the Kraus decomposition `K_y = diag(1_{f = y})`). -/
noncomputable def discardMatrix (f : J → A → X) (R : Matrix (J × A) (J × A) ℂ) :
    Matrix (J × A) (J × A) ℂ := by
  classical
  exact fun p q => if f p.1 p.2 = f q.1 q.2 then R p q else 0

/-- The hidden-shift family `f j a = f0 (a + ψ j)` of the paper (with the shift
`φ_j(s)` absorbed into `ψ j`). -/
def fShift (f0 : A → X) (ψ : J → A) : J → A → X :=
  fun j a => f0 (a + ψ j)

/-- Equation (1): `ρ = σ ⊗ |A⟩⟨A|`, with the uniform pure state on `C[A]`, i.e. the
maximally mixed state `1/|A|` on each `A`-entry. -/
noncomputable def rho (σ : Matrix J J ℂ) : Matrix (J × A) (J × A) ℂ :=
  fun p q => σ p.1 q.1 / (Fintype.card A : ℂ)

/-- The kernel of `E(ρ)` for the shift family: `g j k d = σ j k / |A|` when
`d = ψ j - ψ k`, and `0` otherwise.  This is exactly the convolution form produced by
translation invariance; injectivity of `f0` gives the support condition. -/
noncomputable def shiftKernel (σ : Matrix J J ℂ) (ψ : J → A) : J → J → A → ℂ :=
  fun j k d => if d = ψ j - ψ k then σ j k / (Fintype.card A : ℂ) else 0

/-- **Translation invariance, concretely.**  On `ρ = σ ⊗ uniform`, the discarded-output
channel is the convolution operator with kernel `shiftKernel`. -/
theorem discardMatrix_rho_eq_convMatrix (f0 : A → X) (hf0 : Function.Injective f0)
    (ψ : J → A) (σ : Matrix J J ℂ) :
    discardMatrix (fShift f0 ψ) (rho σ) = convMatrix (shiftKernel σ ψ) := by
  classical
  ext p q
  simp only [discardMatrix, convMatrix, rho, fShift, shiftKernel]
  rw [hf0.eq_iff]
  have hiff : (p.2 + ψ p.1 = q.2 + ψ q.1) ↔ (q.2 - p.2 = ψ p.1 - ψ q.1) := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (ψ p.1) p.2, eq_comm]
  rw [hiff]
  by_cases h : q.2 - p.2 = ψ p.1 - ψ q.1 <;> simp [h]

/-- **Proposition 3.1, first part (explicit form).**  The output `E(ρ)` applied to the
Fourier mode `|k⟩|b̂ = χ⟩` stays in the same character sector `χ`, with the label
coefficient `(σ j k / |A|) · χ(ψ j - ψ k)`. -/
theorem prop31_blockDiagonal_formula (f0 : A → X) (hf0 : Function.Injective f0)
    (ψ : J → A) (σ : Matrix J J ℂ) (k : J) (χ : AddChar A ℂ) :
    (discardMatrix (fShift f0 ψ) (rho σ)).mulVec (fourierVec k χ) =
      fun p => ((σ p.1 k / (Fintype.card A : ℂ)) * χ (ψ p.1 - ψ k)) * χ p.2 := by
  rw [discardMatrix_rho_eq_convMatrix f0 hf0 ψ σ, convMatrix_mulVec_fourierVec]
  funext p
  congr 1
  simpa only [shiftKernel] using
    sum_ite_single (ψ p.1 - ψ k) (σ p.1 k / (Fintype.card A : ℂ)) χ

/-- **Proposition 3.1, first part (sector form).**  The image of the Fourier mode
`|k⟩|b̂ = χ⟩` under `E(ρ)` is a `J`-linear combination of Fourier modes with the *same*
character `χ` only: `E(ρ)` is block diagonal with respect to the eigenspaces of the
`|b̂⟩` measurement. -/
theorem prop31_blockDiagonal_sector (f0 : A → X) (hf0 : Function.Injective f0)
    (ψ : J → A) (σ : Matrix J J ℂ) (k : J) (χ : AddChar A ℂ) :
    ∃ c : J → ℂ,
      (discardMatrix (fShift f0 ψ) (rho σ)).mulVec (fourierVec k χ) =
        fun p => c p.1 * χ p.2 :=
  ⟨fun j => (σ j k / (Fintype.card A : ℂ)) * χ (ψ j - ψ k),
    prop31_blockDiagonal_formula f0 hf0 ψ σ k χ⟩

end Channel

/-! ## §4. Uniformity of the Fourier-mode measurement -/

section Uniform

variable {J A X : Type*} [Fintype J] [DecidableEq J] [AddCommGroup A] [Fintype A]
  [DecidableEq A]

/-- **Uniformity from a diagonal `A`-slice.**  If an operator restricted to equal labels
is diagonal in the `A` register with diagonal values `d j`, then every character sector
carries Born weight `∑ j, d j`.  This isolates the sum bookkeeping of the paper's second
argument ("injectivity of `f_j` makes `|a⟩` uniform, so `|b̂⟩` is uniform too"). -/
theorem uniform_from_diagonal (d : J → ℂ) (R : Matrix (J × A) (J × A) ℂ)
    (hR : ∀ (j : J) (a c : A), R (j, c) (j, a) = if a = c then d j else 0)
    (χ : AddChar A ℂ) :
    Matrix.trace (fourierSectorProjector χ * R) = ∑ j, d j := by
  classical
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ a, (1 / (Fintype.card A : ℂ)) * conj (χ a) * χ a) = 1 := by
    calc
      (∑ a, (1 / (Fintype.card A : ℂ)) * conj (χ a) * χ a)
          = (1 / (Fintype.card A : ℂ)) * ∑ a, conj (χ a) * χ a := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (1 / (Fintype.card A : ℂ)) * (Fintype.card A : ℂ) := by
            rw [sum_char_conj_mul]
      _ = 1 := by
            rw [one_div, inv_mul_cancel₀ hcard]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    fourierSectorProjector]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
    have hstep : ∀ a : A,
        (∑ c, ((1 / (Fintype.card A : ℂ)) * conj (χ a) * χ c) * R (j, c) (j, a))
          = ((1 / (Fintype.card A : ℂ)) * conj (χ a) * χ a) * d j := by
      intro a
      rw [Finset.sum_eq_single a]
      · simp [hR j a a]
      · intro c _ hc
        rw [hR j a c, if_neg (Ne.symm hc), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ a) h
    calc
      (∑ a, ∑ c, ((1 / (Fintype.card A : ℂ)) * conj (χ a) * χ c) * R (j, c) (j, a))
          = ∑ a, ((1 / (Fintype.card A : ℂ)) * conj (χ a) * χ a) * d j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hstep a]
      _ = (∑ a, (1 / (Fintype.card A : ℂ)) * conj (χ a) * χ a) * d j := by
            rw [Finset.sum_mul]
      _ = d j := by
            rw [hsum, one_mul]
  · intro k _ hkj
    have hzero : ∀ a c : A,
        ((if j = k then (1 / (Fintype.card A : ℂ)) * conj (χ a) * χ c else 0)) *
          R (k, c) (j, a) = 0 := by
      intro a c
      rw [if_neg (Ne.symm hkj), zero_mul]
    simp only [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => hzero a c)),
      Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The diagonal `A`-slice of `E(ρ)`: for equal labels `j`, injectivity of `f0` forces
`a = c`, and the value is `σ j j / |A|`. -/
theorem discardMatrix_rho_diagonal (f0 : A → X) (hf0 : Function.Injective f0)
    (ψ : J → A) (σ : Matrix J J ℂ) (j : J) (a c : A) :
    discardMatrix (fShift f0 ψ) (rho σ) (j, c) (j, a) =
      if a = c then σ j j / (Fintype.card A : ℂ) else 0 := by
  classical
  simp only [discardMatrix, rho, fShift]
  rw [hf0.eq_iff]
  have hiff : (c + ψ j = a + ψ j) ↔ a = c := by
    constructor
    · intro h
      exact (add_right_cancel h).symm
    · intro h
      rw [h]
  rw [hiff]
  by_cases h : a = c <;> simp [h]

/-- **Proposition 3.1, second part.**  For a state `σ` on `C[J]` with `trace σ = 1`, the
Fourier-mode measurement on `E(ρ)` is uniform: every character `χ` has Born weight
`1 / |A|`. -/
theorem prop31_measurement_uniform (f0 : A → X) (hf0 : Function.Injective f0)
    (ψ : J → A) (σ : Matrix J J ℂ) (hσ : Matrix.trace σ = 1) (χ : AddChar A ℂ) :
    Matrix.trace (fourierSectorProjector χ *
        discardMatrix (fShift f0 ψ) (rho σ)) = 1 / (Fintype.card A : ℂ) := by
  rw [uniform_from_diagonal (fun j => σ j j / (Fintype.card A : ℂ)) _
    (discardMatrix_rho_diagonal f0 hf0 ψ σ) χ]
  rw [← Finset.sum_div]
  have ht : (∑ j, σ j j) = 1 := by
    simpa [Matrix.trace, Matrix.diag_apply] using hσ
  rw [ht]

end Uniform

end Qatlib.Papers.DihedralHSP13.MainResults.RecordExtract
