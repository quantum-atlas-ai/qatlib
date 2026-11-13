/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel

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
def theorem1 {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) : Prop :=
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
def proposition7 {n : ℕ} (S : SymFamily n) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) : Prop :=
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
    (hM : GammaS S M) : Prop :=
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
def lemma2 {n : ℕ} (S : SymFamily n) (M : Measurement n) (hM : Gamma S M) : Prop :=
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
    (hM : GammaS S M) (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2)
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
def proposition9 {n : ℕ} (S : SymFamily n) (hfull : FullDualSupport S) : Prop :=
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
def proposition10 {n : ℕ} (S : SymFamily n) (hfull : FullDualSupport S)
    (M : Measurement n) (hM : Gamma S M) (k : ℕ) (H : Lam n k)
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
def proposition11 {n : ℕ} (S : SymFamily n) (hfull : FullDualSupport S)
    (k : ℕ) (H : Lam n k) (y : Fin k → ZMod 2)
    (G : MatZ (n - k) n) (v : (Fin (n - k) → ZMod 2) → F2 n)
    (hv : ∀ s, {x : F2 n | matVec G x = s} =
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
