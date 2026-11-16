/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section


/-!
# Closed arithmetic and counting results for ProdFormula24

These are the retained zero-extension and iteration-count proofs, together with
the bounded rooted-tuple count and the zeroth joint-moment consequence.
They do not assert Hamiltonian simulation or locality error bounds.
The fixed paper is arXiv:2403.08729v3.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ProdFormula24.MainResults.LocalityAlpha

/-- Rooted tuples whose other coordinates lie in a bounded ball have at most the product count. -/
theorem lemma8_localityTupleCount {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (ball : Λ → Finset Λ) (B : ℕ) (hcard : ∀ i, (ball i).card ≤ B) (p : ℕ) :
    (Finset.univ.filter (fun f : Fin (p + 1) → Λ =>
      ∀ m : Fin (p + 1), f m ∈ ball (f 0))).card ≤ Fintype.card Λ * B ^ p := by
  classical
  let S := Finset.univ.filter (fun f : Fin (p + 1) → Λ =>
    ∀ m : Fin (p + 1), f m ∈ ball (f 0))
  let e : S → Σ x : Λ, (Fin p → ↥(ball x)) := fun f =>
    ⟨f.1 0, fun j => ⟨f.1 j.succ, (Finset.mem_filter.mp f.2).2 j.succ⟩⟩
  have he : Function.Injective e := by
    intro f g h
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact congrArg Sigma.fst h
    · have hz := congrArg (fun z : Σ x : Λ, (Fin p → ↥(ball x)) => (z.2 k).1) h
      exact hz
  calc
    S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card (Σ x : Λ, (Fin p → ↥(ball x))) :=
      Fintype.card_le_of_injective e he
    _ = ∑ x : Λ, (ball x).card ^ p := by simp [Fintype.card_sigma]
    _ ≤ ∑ _x : Λ, B ^ p := by
      exact Finset.sum_le_sum (fun x _ => Nat.pow_le_pow_left (hcard x) p)
    _ = Fintype.card Λ * B ^ p := by simp


/-- **Corollary 9 (Iteration count), arXiv:2403.08729v3, Corollary 9, p. 11.**
If a single THRIFT step of duration `T/r` has error at most
`C · n · (T/r)^{p+1}`, then choosing the number of intervals
`r ≥ (C n T^{p+1} / ε)^{1/p}` makes the total error `r · C n (T/r)^{p+1}` at
most `ε`.  This is the arithmetic core of the `r`-fold iteration. -/
theorem corollary9_iterationCount
    (C n T ε : ℝ) (p r : ℕ)
    (hC : 0 < C) (hn : 0 < n) (hT : 0 < T) (hε : 0 < ε)
    (_hp : 0 < p) (hr : 0 < (r : ℝ))
    (hstep : (r : ℝ) ^ p ≥ C * n * T ^ (p + 1) / ε) :
    (r : ℝ) * (C * n * (T / r) ^ (p + 1)) ≤ ε := by
  have hrp : (0 : ℝ) < (r : ℝ) ^ p := by positivity
  have hbase : 0 < C * n * T ^ (p + 1) := by positivity
  -- From the step condition: `C n T^{p+1} ≤ ε r^p`.
  have hle : C * n * T ^ (p + 1) ≤ ε * (r : ℝ) ^ p := by
    have := (div_le_iff₀ hε).mp hstep
    nlinarith
  -- Rewrite the total error as `C n T^{p+1} / r^p`.
  have hrewrite : (r : ℝ) * (C * n * (T / r) ^ (p + 1))
      = C * n * T ^ (p + 1) / (r : ℝ) ^ p := by
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr
    rw [div_pow]
    field_simp
    ring
  rw [hrewrite, div_le_iff₀ hrp]
  linarith [hle]

end Qatlib.Papers.ProdFormula24.MainResults.LocalityAlpha

namespace Qatlib.Papers.ProdFormula24.MainResults.MomentLemmas

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The operator commutator `[A, B] = A * B - B * A`. -/
def opCommutator (A B : Matrix I I ℂ) : Matrix I I ℂ := A * B - B * A

/-- **Lemma 12 (Zero-extension / linearity), arXiv:2403.08729v3, Lemma 12, p. 22.**
Let `T` be a bilinear form on pairs of matrix-valued functions `(H₁, H₂)` that is
additive in its first argument (as any commutator integral `∫∫ F [H₁(x), H₂(y)]`
is).  If `T(H₁, H₂) = 0` for every `H₁` with `[H₀, H₁(0)] ≠ 0`, then also
`T(H₁, H₂) = 0` for every `H₁` with `[H₀, H₁(0)] = 0`.

The proof picks an auxiliary `A` with `[H₀, A(0)] ≠ 0`, forms
`H₁' = H₁ + A` so that `[H₀, H₁'(0)] = [H₀, H₁(0)] + [H₀, A(0)] = [H₀, A(0)] ≠ 0`,
and uses additivity to cancel `T(A, H₂)`.  Fully proved. -/
theorem lemma12_zeroExtension
    (T : (ℝ → Matrix I I ℂ) → (ℝ → Matrix I I ℂ) → Matrix I I ℂ)
    (hadd : ∀ H1 H1' H2, T (H1 + H1') H2 = T H1 H2 + T H1' H2)
    (H0 : Matrix I I ℂ) (H2 : ℝ → Matrix I I ℂ)
    (A H1 : ℝ → Matrix I I ℂ)
    (hA : opCommutator H0 (A 0) ≠ 0)
    (hH1 : opCommutator H0 (H1 0) = 0)
    (hvanish : ∀ G : ℝ → Matrix I I ℂ, opCommutator H0 (G 0) ≠ 0 → T G H2 = 0) :
    T H1 H2 = 0 := by
  -- `[H₀, (H₁ + A)(0)] = [H₀, H₁(0)] + [H₀, A(0)] = [H₀, A(0)] ≠ 0`.
  have hcomm : opCommutator H0 ((H1 + A) 0)
      = opCommutator H0 (H1 0) + opCommutator H0 (A 0) := by
    simp only [Pi.add_apply]
    unfold opCommutator
    noncomm_ring
  have hGA : opCommutator H0 ((H1 + A) 0) ≠ 0 := by
    rw [hcomm, hH1, zero_add]
    exact hA
  -- Additivity: `T(H₁ + A, H₂) = T(H₁,H₂) + T(A,H₂)`.
  have h1 : T (H1 + A) H2 = 0 := hvanish (H1 + A) hGA
  rw [hadd H1 A H2] at h1
  have h2 : T A H2 = 0 := hvanish A hA
  rw [h2, add_zero] at h1
  exact h1

/-- Vanishing joint moments imply vanishing total mass by the zeroth moment. -/
theorem corollary15_crossTermsVanishing
    (F : ℝ → ℝ → ℝ)
    (hmomF : ∀ k l : ℕ,
        ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, x ^ k * y ^ l * F x y = 0) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y = 0) := by
  simpa using hmomF 0 0

end Qatlib.Papers.ProdFormula24.MainResults.MomentLemmas
