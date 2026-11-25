/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel
public import Qatlib.Papers.UnambigMeas25.MainResults.Fourier
public import Qatlib.Papers.UnambigMeas25.MainResults.Combinatorics.CosetCount

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Reformulation of `ρ(S)` as a linear program — Section 3.1–3.2

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025).

This file states Theorem 1 (p. 15), Proposition 7 (p. 12), Lemma 1 (p. 12),
Lemma 2 (p. 13), Proposition 8 (p. 14), Proposition 9 (p. 16), Proposition 10
(p. 16) and Proposition 11 (p. 17) in the vocabulary of
`MainResults.Definitions.UnambigMeasModel`.

Scope note: the results below are defined as propositions.  Their mathematical
proofs are described in the comments but are outside the scope of this file.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults.Reformulation

open Matrix BigOperators
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-! ### Auxiliary objects used by Propositions 8, 10, 11 -/

/-- The block `F_H = ∑_y F_{H,y}` of Proposition 8. -/
def FHSum {n : ℕ} (M : Measurement n) (k : ℕ) (H : Lam n k) : Op n :=
  ∑ y : (Fin k → ZMod 2), M.w k H y

/-- The subspace `W_{H,y}` of Definition 19: vectors orthogonal to every
`|ψ_x⟩` with `Hx ≠ y`. -/
def WSet {n k : ℕ} (S : SymFamily n) (H : Lam n k) (y : Fin k → ZMod 2) :
    Set (StateVec n) :=
  {φ | ∀ x : F2 n, matVec H.1 x ≠ y → braKet φ (S.ψ x) = 0}

/-- The symmetrisation `F̄_{H,y} = 2^{-n} ∑_a X_a F_{H,y+Ha} X_a` of Lemma 2. -/
def symmetrize {n : ℕ} (M : Measurement n) : Measurement n where
  w k H y := ((2 : ℂ) ^ n)⁻¹ •
    ∑ a : F2 n, Xop a * M.w k H (y + matVec H.1 a) * Xop a

/-- The explicit basis vector `|A_s^{H,y}⟩` of Proposition 11, Equation (8). -/
def AHVec {n k : ℕ} (S : SymFamily n) (H : Lam n k) (y : Fin k → ZMod 2)
    (v : (Fin (n - k) → ZMod 2) → F2 n) (s : Fin (n - k) → ZMod 2) :
    StateVec n :=
  fun i => ∑ u : Fin k → ZMod 2,
    (S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
      fourierBasis (transposeVec H.1 u + v s) i

/-! ### Theorem 1 and Proposition 7 -/

/-- **Theorem 1** (arXiv:2510.07298v2, p. 15).  For a symmetric family `S`,
`ρ(S)` equals the maximum, over symmetric measurements `{F_{H,y}} ∈ Γ_s(S)`, of
`∑_{k,H,y,i} C(k) |α̂_i|² ⟨b_i|F_{H,y}|b_i⟩`.

Source: Theorem 1, p. 15.  Proof route: Proposition 7 rewrites `ρ(S)` as a
maximum over `Γ_s(S)` of `ρ₂`; Proposition 8 rewrites `Tr(F_H |ψ_0⟩⟨ψ_0|)` as
the Fourier-diagonal sum; the last line replaces `F_H = ∑_y F_{H,y}` by the
individual `F_{H,y}`.  The statement is the paper's displayed identity with
`sSup` encoding the maximum (the paper does not discuss whether the maximum is
attained; `sSup` is the faithful order-theoretic reading). -/
def theorem1 {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (_hC : ∀ k, 0 ≤ C k) : Prop :=
  rho S C = thm1Value S C
  -- Paper: arXiv:2510.07298v2, Theorem 1, p. 15.
  -- Key steps: (i) Lemma 1 replaces the average over x by the value at ψ_0;
  -- (ii) Lemma 2 shows every measurement can be symmetrised without changing
  -- ρ₂, so the maximum may be taken over Γ_s(S);
  -- (iii) Proposition 8 identifies Tr(F_H |ψ_0⟩⟨ψ_0|) with
  --       ∑_i |α̂_i|² ⟨b_i|F_H|b_i⟩ = ∑_{i,y} |α̂_i|² ⟨b_i|F_{H,y}|b_i⟩.
  -- The supremum comparison over Γ and Γ_s and the trace/Fourier diagonal
  -- identity connect `rho`, `rho2Max` and `thm1Value` through `FHSum`.
  -- The argument uses Proposition 8, Lemmas 1 and 2, trace cyclicity
  -- (`Matrix.trace_mul_comm`) and orthonormality of `fourierBasis`;
  -- these connections are not derived in this file.

/-- **Proposition 7** (arXiv:2510.07298v2, p. 12).  `ρ(S)` is the maximum of
`ρ₂(S, {F})` over symmetric measurements `Γ_s(S)`.

Source: Proposition 7, p. 12.  Proof: Lemma 1 (`ρ = ρ₂` on `Γ_s`) plus Lemma 2
(every `Γ(S)` element symmetrises into `Γ_s(S)` with the same `ρ₂` value). -/
def proposition7 {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (_hC : ∀ k, 0 ≤ C k) : Prop :=
  rho S C = rho2Max S C
  -- Paper: arXiv:2510.07298v2, Proposition 7, p. 12.
  -- Key steps: Γ_s(S) ⊆ Γ(S) gives ≥; Lemma 2 gives the reverse inequality.
  -- The comparison uses `score = rho2` on Γ_s (Lemma 1 below) and
  -- Γ_s ⊆ Γ; these supremum inequalities are not proved in this file.

/-- **Lemma 1** (arXiv:2510.07298v2, p. 12).  For `{F} ∈ Γ_s(S)`,
`ρ(S,{F}) = ρ₂(S,{F})`.

Source: Lemma 1, p. 12.  Proof: change variables in the average over `x`,
using `X_x F_{H,y} X_x = F_{H,y+Hx}` and summing over `a = y + Hx`; for each
`(H,y)` this produces `2^{n-k}` copies, cancelling the `2^{-n}` factor. -/
def lemma1 {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (M : Measurement n)
    (_hM : GammaS S M) : Prop :=
  score S C M = rho2 S C M
  -- Paper: arXiv:2510.07298v2, Lemma 1, p. 12.
  -- Key steps: Tr(X_x F X_x |ψ_0⟩⟨ψ_0|) = Tr(F |ψ_x⟩⟨ψ_x|) (cyclicity);
  -- Γ_s gives X_x F_{H,y} X_x = F_{H,y+Hx}; reindex y ↦ a = y + Hx, which
  -- runs over F₂^k exactly 2^{n-k} times as x ranges over its fibre.
  -- Scope note: the trace-cyclicity calculation for `expect`, the `Xop`
  -- shift action on `S.ψ` and the fibre count relating `score` to `rho2`
  -- are outside the scope of this file.

/-- **Lemma 2** (arXiv:2510.07298v2, p. 13).  If `{F} ∈ Γ(S)` then its
symmetrisation `F̄_{H,y} = 2^{-n}∑_a X_a F_{H,y+Ha} X_a` lies in `Γ_s(S)`.

Source: Lemma 2, p. 13.  Proof: positive semidefiniteness is preserved by
conjugation and convex combinations; completeness follows from `∑ X_a X_a = 2^n I`;
unambiguity uses `H(x+a) ≠ y+Ha`; the covariance identity uses the change of
variable `a' = a + b`. -/
def lemma2 {n : ℕ} (S : SymFamily n) (M : Measurement n) (_hM : Gamma S M) : Prop :=
  GammaS S (symmetrize M)
  -- Paper: arXiv:2510.07298v2, Lemma 2, p. 13.
  -- Key steps: PosSemidef of `X_a F X_a` and of finite sums; `X_a = X_aᴴ`;
  -- `X_b X_a = X_{a+b}`; `X_a S.ψ x = S.ψ (x+a)`; the unambiguity premise
  -- `H(x+a) ≠ y+Ha` is equivalent to `Hx ≠ y`.
  -- The positive-semidefinite closure properties are expressed by
  -- `Matrix.PosSemidef.conjTranspose_mul_mul_same` and `Matrix.PosSemidef.sum`.
  -- Scope note: applying these properties in this model and establishing
  -- the multiplication identity `Xop a * Xop b = Xop (a+b)` over ZMod 2
  -- are outside the scope of this file.

/-! ### Proposition 8 and Proposition 9 -/

/-- **Proposition 8** (arXiv:2510.07298v2, p. 14).  For `{F} ∈ Γ_s(S)`, the
Fourier transform of `F_H = ∑_y F_{H,y}` is diagonal, with diagonal entry
`2^k ⟨b_i|F_{H,y}|b_i⟩` independent of `y`.

Source: Proposition 8, p. 14.  Proof: write `y = Hb` and average
`F_{H,Ha} = X_{a+b} F_{H,y} X_{a+b}` over `a`; the phase sum
`∑_a (-1)^{(a+b)·(i+j)}` vanishes unless `i = j`, where it equals `2^n`. -/
def proposition8 {n : ℕ} (S : SymFamily n) (M : Measurement n)
    (_hM : GammaS S M) (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2)
    (i j : F2 n) : Prop :=
  opFourier (FHSum M k H) i j =
      if i = j then (2 : ℂ) ^ k * opFourier (M.w k H y) i i else 0
  -- Paper: arXiv:2510.07298v2, Proposition 8, p. 14.
  -- Key steps: Γ_s gives F_{H,Ha} = X_{a+b} F_{H,y} X_{a+b} for Hb = y;
  -- `Zop b` is diagonal, so (F̂_H)_{i,j} = 2^{-(n-k)} ∑_a (-1)^{(a+b)·(i+j)} (F̂_{H,y})_{i,j};
  -- the character sum is 0 for i ≠ j and 2^n for i = j.
  -- Scope note: character orthogonality over ZMod 2,
  -- `∑_a χ a (i+j) = 2^n if i=j else 0`, and the transformation of
  -- `opFourier` under `Xop`/`Zop` are outside the scope of this file.

/-- **Proposition 9** (arXiv:2510.07298v2, p. 16).  Under full dual support the
`2^n` states `|ψ_x⟩` are linearly independent; every subfamily indexed by `T` is
independent, so its span has dimension `|T|`.

Source: Proposition 9, p. 16.  Proof: `∑_x (-1)^{x·y_0}|ψ_x⟩ = 2^n α̂_{y_0}|b_{y_0}⟩`;
since `α̂_{y_0} ≠ 0`, every Fourier basis vector lies in the span. -/
def proposition9 {n : ℕ} (S : SymFamily n) (_hfull : FullDualSupport S) : Prop :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range S.ψ)) = 2 ^ n ∧
      ∀ T : Finset (F2 n),
        Module.finrank ℂ (Submodule.span ℂ (S.ψ '' (T : Set (F2 n)))) = T.card
  -- Paper: arXiv:2510.07298v2, Proposition 9, p. 16.
  -- Key steps: the character inversion identity above exhibits every dual basis
  -- vector in the span; the dual basis is a basis of ℂ^{F₂ⁿ}; independence of a
  -- subfamily follows because the map x ↦ ψ_x is injective modulo the basis.
  -- The inversion identity supplies linear independence of `S.ψ`; the
  -- dimension step is expressed by `Module.finrank_span_eq_card` and
  -- `LinearIndependent.finrank_span_eq_card`.
  -- Scope note: establishing the basis property of `fourierBasis` and this
  -- linear-independence argument is outside the scope of this file.

/-! ### Propositions 10 and 11 -/

/-- **Proposition 10** (arXiv:2510.07298v2, p. 16).  Under full dual support,
every `F_{H,y} ∈ Γ(S)` is a nonnegative sum of pairwise orthogonal
rank-one projectors whose vectors lie in `W_{H,y}`.

Source: Proposition 10, p. 16.  Proof: take the spectral decomposition of the
positive semidefinite `F_{H,y}`; the unambiguity condition forces each
eigenvector to be orthogonal to every `|ψ_x⟩` with `Hx ≠ y`. -/
def proposition10 {n : ℕ} (S : SymFamily n) (_hfull : FullDualSupport S)
    (M : Measurement n) (_hM : Gamma S M) (k : ℕ) (H : Lam n k)
    (y : Fin k → ZMod 2) : Prop :=
  ∃ (m : ℕ), m ≤ 2 ^ (n - k) ∧
      ∃ (mu : Fin m → ℝ) (B : Fin m → StateVec n),
        (∀ i, 0 ≤ mu i) ∧
        (∀ i, B i ∈ WSet S H y) ∧
        (∀ i j, i ≠ j → braKet (B i) (B j) = 0) ∧
        M.w k H y = ∑ i : Fin m, (mu i : ℂ) • outer (B i)
  -- Paper: arXiv:2510.07298v2, Proposition 10, p. 16.
  -- Key steps: spectral theorem for PSD matrices; Equation (7)
  -- Tr(F |ψ_x⟩⟨ψ_x|) = 0 gives ⟨ψ_x|B_i⟩ = 0 for Hx ≠ y;
  -- dim W_{H,y} = 2^{n-k} by Proposition 9.
  -- The spectral decomposition and nonnegative eigenvalues are expressed by
  -- `Matrix.IsHermitian.spectral_theorem` and `Matrix.PosSemidef.eigenvalues_nonneg`.
  -- Positivity transfers `expect (S.ψ x) (M.w ...) = 0` to orthogonality
  -- of each eigenvector with `S.ψ x`.
  -- Scope note: constructing the orthonormal eigenbasis in this function-space
  -- model and carrying out that transfer are outside the scope of this file.

/-- **Proposition 11** (arXiv:2510.07298v2, p. 17).  For every dual-coset
parametrisation `D_H(s) = {Hᵀu + v_s}`, the vectors `|A_s^{H,y}⟩` of Eq. (8)
form an orthogonal basis of `W_{H,y}`.

Source: Proposition 11, p. 17, Equation (8).  Proof: distinct `s` give disjoint
supports, hence orthogonality; the scalar product with `|ψ_x⟩` is
`(-1)^{x·v_s} ∑_u (-1)^{(Hx+y)·u} = 0` when `Hx ≠ y`; dimension counting gives a
basis. -/
def proposition11 {n : ℕ} (S : SymFamily n) (_hfull : FullDualSupport S)
    (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2)
    (G : MatZ (n - k) n) (v : (Fin (n - k) → ZMod 2) → F2 n)
    (_hv : ∀ s, {x : F2 n | matVec G x = s} =
      Set.range (fun u : Fin k → ZMod 2 => transposeVec H.1 u + v s)) : Prop :=
  (∀ s s', s ≠ s' → braKet (AHVec S H y v s) (AHVec S H y v s') = 0) ∧
      (∀ s, AHVec S H y v s ∈ WSet S H y) ∧
      (∀ s, AHVec S H y v s ≠ 0) ∧
      (∀ φ : StateVec n, φ ∈ WSet S H y →
        ∃ c : (Fin (n - k) → ZMod 2) → ℂ,
          φ = ∑ s : Fin (n - k) → ZMod 2, c s • AHVec S H y v s)
  -- Paper: arXiv:2510.07298v2, Proposition 11, p. 17, Equation (8).
  -- Key steps: (i) supp(A_s) ⊆ D_H(s), so distinct s are orthogonal;
  -- (ii) ⟨A_s|ψ_x⟩ = (-1)^{x·v_s} ∑_{u∈F₂^k} (-1)^{(Hx+y)·u}, which vanishes
  --      when Hx ≠ y by character orthogonality;
  -- (iii) each A_s ≠ 0 because α̂ is nowhere zero (full dual support);
  -- (iv) the 2^{n-k} orthogonal vectors span the 2^{n-k}-dimensional W_{H,y}.
  -- Scope note: the character-orthogonality argument over `Fin k → ZMod 2`,
  -- the use of disjoint supports and the dimension count are outside the
  -- scope of this file.

end Qatlib.Papers.UnambigMeas25.MainResults.Reformulation

section

/-!
## Fourier coefficients of the basis vectors `|A_s^{H,y}⟩`

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025), Eq. (8) p. 17 and the first line of the proof
of Theorem 2, p. 17.

`Reformulation.AHVec` is the explicit basis vector
`|A_s^{H,y}⟩ = ∑_u (α̂_{Hᵀu + v_s})⁻¹ (-1)^{y·u} |b_{Hᵀu + v_s}⟩` of Proposition 11.
This module computes its overlap with the Fourier basis vector `|b_i⟩`:

`|⟨b_i|A_s^{H,y}⟩|² = 1/|α̂_i|²` if `i = Hᵀu + v_s` for some `u`, and `0` otherwise,

which is the coefficient fact used in the proofs of Theorem 2 and Proposition 13.
The two ingredients are the orthonormality of the Fourier basis and the
injectivity of `u ↦ Hᵀu + v_s`, which holds because `H` has full rank `k`; the
phases `(-1)^{y·u}` have unit modulus and drop out of the modulus squared.

Note that the paper's map `s ↦ v_s` is an arbitrary coset section here, so the
statement holds for every `v : (Fin (n-k) → ZMod 2) → 𝔽₂ⁿ`.

Boundary: the computation is conditional on `H` having full rank, i.e. on `H`
being an element of `Λ_k`. The dependence on `S` is only through the Fourier
coefficients `α̂`; no normalisation of `S` is used or needed. The orthogonality
statement of Proposition 11 between different cosets `s ≠ s'` is not covered.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults

open Matrix BigOperators
open Qatlib.Papers.UnambigMeas25.MainResults
open Qatlib.Papers.UnambigMeas25.MainResults.Reformulation
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-! ### The Fourier basis is the hat-ket of `Fourier.hatKet` -/

/-- `√(2^n) = (√2)^n`, so the normalisation used by `fourierBasis` agrees with
the one used by `Fourier.hatKet`. -/
lemma sqrt_two_pow_eq (n : ℕ) : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- The inverse normalisation of `fourierBasis` is the one of `Fourier.hatKet`. -/
lemma sqrtTwoPow_inv_eq (n : ℕ) :
    (sqrtTwoPow n)⁻¹ = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
  unfold sqrtTwoPow
  rw [sqrt_two_pow_eq]
  push_cast
  rw [inv_pow]

/-- `fourierBasis` is the Fourier ket `hatKet` of `Qatlib/Papers/UnambigMeas25/MainResults/Fourier.lean`. -/
lemma fourierBasis_eq_hatKet (n : ℕ) (i : F2 n) : fourierBasis i = hatKet i := by
  funext j
  show (sqrtTwoPow n)⁻¹ * chi i j = _
  rw [hatKet_apply, sqrtTwoPow_inv_eq, dotF2_comm]
  rfl

/-! ### Orthonormality of the Fourier basis -/

/-- The Fourier basis is orthonormal: `⟨b_i|b_j⟩ = δ_{i,j}`. -/
lemma braKet_fourierBasis (n : ℕ) (i j : F2 n) :
    braKet (fourierBasis i) (fourierBasis j) = if i = j then 1 else 0 := by
  rw [fourierBasis_eq_hatKet, fourierBasis_eq_hatKet]
  exact innerVec_hatKet i j

/-- Orthonormality in the explicit sum form used below. -/
lemma sum_conj_fourierBasis (n : ℕ) (i j : F2 n) :
    (∑ t, (starRingEnd ℂ) (fourierBasis i t) * fourierBasis j t) =
      if i = j then 1 else 0 :=
  braKet_fourierBasis n i j

/-- Every phase `(-1)^{a·b}` has unit modulus. -/
lemma normSq_chi {n : ℕ} (a b : F2 n) : Complex.normSq (chi a b) = 1 := by
  unfold chi
  split_ifs <;> simp

/-! ### Injectivity of the transpose action of a full-rank matrix -/

/-- For `H ∈ Λ_k`, the transpose action `u ↦ Hᵀu` is injective: the transpose of
a full-rank `k × n` matrix has trivial kernel. -/
lemma transposeVec_injective {n k : ℕ} (H : Lam n k) :
    Function.Injective (transposeVec H.1) := by
  have hrank : Matrix.rank ((H.1)ᵀ) = k := by
    rw [Matrix.rank_transpose]
    exact H.2
  have hfin : Module.finrank (ZMod 2) (LinearMap.ker ((H.1)ᵀ).mulVecLin) = 0 := by
    have h := CosetCount.finrank_ker_eq ((H.1)ᵀ)
    rw [hrank, Nat.sub_self] at h
    exact h
  have hsub : Subsingleton (LinearMap.ker ((H.1)ᵀ).mulVecLin) :=
    Module.finrank_zero_iff.mp hfin
  have hzero : ∀ u : Fin k → ZMod 2, transposeVec H.1 u = 0 → u = 0 := by
    intro u hu
    have hmem : u ∈ LinearMap.ker ((H.1)ᵀ).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext j
      have hj := congrFun hu j
      simpa [transposeVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using hj
    exact Subtype.ext_iff.mp
      (Subsingleton.elim (⟨u, hmem⟩ : LinearMap.ker _) ⟨0, (LinearMap.ker _).zero_mem⟩)
  intro u u' h
  have hsub : transposeVec H.1 (u - u') = 0 := by
    have hlin : transposeVec H.1 (u - u')
        = transposeVec H.1 u - transposeVec H.1 u' := by
      funext j
      simp [transposeVec, Finset.sum_sub_distrib, mul_sub]
    rw [hlin, h, sub_self]
  exact sub_eq_zero.mp (hzero (u - u') hsub)

/-! ### The coefficient lemma -/

/-- `⟨b_i|` applied to a single Fourier basis term. -/
lemma braKet_fourierBasis_mul {n : ℕ} (i w : F2 n) (c : ℂ) :
    braKet (fourierBasis i) (fun t => c * fourierBasis w t) =
      c * (if i = w then 1 else 0) := by
  have hsplit : braKet (fourierBasis i) (fun t => c * fourierBasis w t)
      = c * braKet (fourierBasis i) (fourierBasis w) := by
    rw [braKet, braKet, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hsplit, braKet_fourierBasis]

/-- **Equation (8), p. 17 / Theorem 2, p. 17, first line.**  The squared overlap
of the Fourier basis vector `|b_i⟩` with the basis vector `|A_s^{H,y}⟩` of
Proposition 11 is `1/|α̂_i|²` when `i` lies in the dual coset `D_H(s)`, encoded as
`i = Hᵀu + v_s`, and `0` otherwise. -/
theorem AHVec_normSq_inner {n k : ℕ} (S : SymFamily n) (H : Lam n k)
    (y : Fin k → ZMod 2) (v : (Fin (n - k) → ZMod 2) → F2 n)
    (s : Fin (n - k) → ZMod 2) (i : F2 n) :
    Complex.normSq (braKet (fourierBasis i) (AHVec S H y v s)) =
      if ∃ u : Fin k → ZMod 2, i = transposeVec H.1 u + v s
        then (Complex.normSq (S.hat i))⁻¹ else 0 := by
  have hstep : braKet (fourierBasis i) (AHVec S H y v s)
      = ∑ u : Fin k → ZMod 2,
          ((S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u) *
            (if i = transposeVec H.1 u + v s then 1 else 0) := by
    show (∑ t, (starRingEnd ℂ) (fourierBasis i t) *
        (∑ u : Fin k → ZMod 2,
          (S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
            fourierBasis (transposeVec H.1 u + v s) t)) = _
    calc (∑ t, (starRingEnd ℂ) (fourierBasis i t) *
          (∑ u : Fin k → ZMod 2,
            (S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
              fourierBasis (transposeVec H.1 u + v s) t))
        = ∑ t, ∑ u : Fin k → ZMod 2,
            (starRingEnd ℂ) (fourierBasis i t) *
              ((S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
                fourierBasis (transposeVec H.1 u + v s) t) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
      _ = ∑ u : Fin k → ZMod 2, ∑ t,
            (starRingEnd ℂ) (fourierBasis i t) *
              ((S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
                fourierBasis (transposeVec H.1 u + v s) t) :=
          Finset.sum_comm
      _ = ∑ u : Fin k → ZMod 2,
            ((S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u) *
              (if i = transposeVec H.1 u + v s then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro u _
          have hcomm : (∑ t, (starRingEnd ℂ) (fourierBasis i t) *
                ((S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
                  fourierBasis (transposeVec H.1 u + v s) t))
              = (S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u *
                  (∑ t, (starRingEnd ℂ) (fourierBasis i t) *
                    fourierBasis (transposeVec H.1 u + v s) t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
          rw [hcomm, sum_conj_fourierBasis]
  rw [hstep]
  split_ifs with hex
  · obtain ⟨u₀, hu₀⟩ := hex
    have huniq : ∀ u : Fin k → ZMod 2, i = transposeVec H.1 u + v s → u = u₀ := by
      intro u hu
      refine transposeVec_injective H ?_
      have : transposeVec H.1 u + v s = transposeVec H.1 u₀ + v s := by rw [← hu, ← hu₀]
      exact add_right_cancel this
    rw [Finset.sum_eq_single u₀]
    · rw [show transposeVec H.1 u₀ + v s = i from hu₀.symm, ite_eq_left rfl, mul_one,
        Complex.normSq_mul, Complex.normSq_inv, normSq_chi, mul_one]
    · intro u _ hne
      have hne' : ¬ (i = transposeVec H.1 u + v s) := fun hc => hne (huniq u hc)
      rw [ite_eq_right hne', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ u₀) h
  · have hzero : ∀ u : Fin k → ZMod 2,
        ((S.hat (transposeVec H.1 u + v s))⁻¹ * chi y u) *
          (if i = transposeVec H.1 u + v s then 1 else 0) = 0 := by
      intro u
      rw [ite_eq_right (fun hc => hex ⟨u, hc⟩), mul_zero]
    rw [Finset.sum_eq_zero (fun u _ => hzero u)]
    simp

end Qatlib.Papers.UnambigMeas25.MainResults

end
