/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Basic

/-!
# Composition of size-bounded promise reductions

This module constructs identity and composite `PolyReduction` maps and transfers the model’s
complexity predicates along reductions. It also proves that natural-valued polynomial bounds are
preserved by sums and products. See [AharonovArad2011].

## Main statements

* `PolyReduction.comp`: composes promise-preserving maps and their size bounds.
* `BQPHard.of_reduction`: transfers hardness along a reduction.
* `InBQP.of_reduction`: transfers membership to a problem reducing to the given one.
* `PolyBound.mul`: products retain polynomial bounds.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace PolyReduction

/-- The identity size-bounded reduction from a promise problem to itself. -/
def id (P : PromisedProblem α) : PolyReduction P P where
  map := fun a => a
  degree := 1
  constant := 1
  size_bound := by
    intro a
    simp
  maps_yes := by
    intro a hleg hy
    exact ⟨hleg, hy⟩
  maps_no := by
    intro a hleg hn
    exact ⟨hleg, hn⟩

/-- Compose two size-bounded promise reductions, applying `p` first and then `q`. -/
def comp {P : PromisedProblem α} {Q : PromisedProblem β} {R : PromisedProblem γ}
    (p : PolyReduction P Q) (q : PolyReduction Q R) : PolyReduction P R where
  map := fun a => q.map (p.map a)
  degree := p.degree * q.degree
  constant := q.constant * (p.constant + 1) ^ q.degree
  size_bound := by
    intro a
    have hp := p.size_bound a
    have hq := q.size_bound (p.map a)
    have hone : 1 ≤ (P.size a + 1) ^ p.degree := one_le_pow₀ (by omega)
    have hbase : Q.size (p.map a) + 1 ≤ (p.constant + 1) * (P.size a + 1) ^ p.degree := by
      calc Q.size (p.map a) + 1
          ≤ p.constant * (P.size a + 1) ^ p.degree + 1 := by omega
        _ ≤ p.constant * (P.size a + 1) ^ p.degree + (P.size a + 1) ^ p.degree := by
              omega
        _ = (p.constant + 1) * (P.size a + 1) ^ p.degree := by ring
    have hpow : (Q.size (p.map a) + 1) ^ q.degree ≤
        ((p.constant + 1) * (P.size a + 1) ^ p.degree) ^ q.degree :=
      Nat.pow_le_pow_left hbase q.degree
    calc R.size (q.map (p.map a))
        ≤ q.constant * (Q.size (p.map a) + 1) ^ q.degree := hq
      _ ≤ q.constant * ((p.constant + 1) * (P.size a + 1) ^ p.degree) ^ q.degree :=
            Nat.mul_le_mul_left _ hpow
      _ = q.constant * (p.constant + 1) ^ q.degree * (P.size a + 1) ^ (p.degree * q.degree) := by
            rw [mul_pow, pow_mul]
            ring
  maps_yes := by
    intro a hleg hy
    obtain ⟨hQleg, hQy⟩ := p.maps_yes a hleg hy
    exact q.maps_yes (p.map a) hQleg hQy
  maps_no := by
    intro a hleg hn
    obtain ⟨hQleg, hQn⟩ := p.maps_no a hleg hn
    exact q.maps_no (p.map a) hQleg hQn

end PolyReduction

/-- The model predicate `BQPHard` transfers from `P` to `Q` along a reduction from `P` to `Q`. -/
theorem BQPHard.of_reduction {P : PromisedProblem α} {Q : PromisedProblem β}
    (h : BQPHard P) (r : PolyReduction P Q) : BQPHard Q :=
  h.elim fun s => ⟨s.comp r⟩

/-- If `P` satisfies the model predicate `InBQP`, then so does every problem `Q` reducing to
`P`. -/
theorem InBQP.of_reduction {P : PromisedProblem α} {Q : PromisedProblem β}
    (h : InBQP P) (r : PolyReduction Q P) : InBQP Q :=
  h.elim fun s => ⟨r.comp s⟩

/-- The model predicate `SharpPHard` transfers from `P` to `Q` along a reduction from `P` to
`Q`. -/
theorem SharpPHard.of_reduction {P : PromisedProblem α} {Q : PromisedProblem β}
    (h : SharpPHard P) (r : PolyReduction P Q) : SharpPHard Q :=
  h.elim fun s => ⟨s.comp r⟩

/-- A promise problem satisfying both `BQPHard` and `InBQP` satisfies `BQPComplete`. -/
theorem BQPComplete.of_halves {P : PromisedProblem α} (hHard : BQPHard P)
    (hMem : InBQP P) : BQPComplete P :=
  ⟨hHard, hMem⟩

namespace PolyBound

/-- Every constant natural-valued function has a polynomial bound. -/
theorem const (c : ℕ) : PolyBound (fun _ : ℕ => c) :=
  ⟨c, 0, by intro n; simp⟩

/-- The identity function on natural numbers has a polynomial bound. -/
theorem id : PolyBound (fun n : ℕ => n) :=
  ⟨1, 1, by intro n; simp⟩

/-- The pointwise sum of two polynomially bounded natural-valued functions is polynomially
bounded. -/
theorem add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n + g n) := by
  obtain ⟨Cf, df, hf⟩ := hf
  obtain ⟨Cg, dg, hg⟩ := hg
  refine ⟨Cf + Cg, max df dg, fun n => ?_⟩
  have hf' : f n ≤ Cf * (n + 1) ^ max df dg := by
    calc f n ≤ Cf * (n + 1) ^ df := hf n
      _ ≤ Cf * (n + 1) ^ max df dg :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hg' : g n ≤ Cg * (n + 1) ^ max df dg := by
    calc g n ≤ Cg * (n + 1) ^ dg := hg n
      _ ≤ Cg * (n + 1) ^ max df dg :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  calc f n + g n ≤ Cf * (n + 1) ^ max df dg + Cg * (n + 1) ^ max df dg :=
        Nat.add_le_add hf' hg'
    _ = (Cf + Cg) * (n + 1) ^ max df dg := by ring

/-- The pointwise product of two polynomially bounded natural-valued functions is polynomially
bounded. -/
theorem mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun n => f n * g n) := by
  obtain ⟨Cf, df, hf⟩ := hf
  obtain ⟨Cg, dg, hg⟩ := hg
  refine ⟨Cf * Cg, df + dg, fun n => ?_⟩
  calc f n * g n ≤ (Cf * (n + 1) ^ df) * (Cg * (n + 1) ^ dg) :=
        Nat.mul_le_mul (hf n) (hg n)
    _ = (Cf * Cg) * (n + 1) ^ (df + dg) := by rw [pow_add]; ring

end PolyBound

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
