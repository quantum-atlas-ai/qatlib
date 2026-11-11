/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QSLWEISIS25 / MainResults — source model

Source version fixed for this development: **arXiv:2510.06097v2** (quant-ph,
11 May 2026), *On the Quantum Equivalence between S|LWE⟩ and ISIS*
(Chailloux–Hermouet).  PDF/text used:
`prove/assets/2510.06097.{pdf,txt}`.

This module fixes the notation of the paper once, so that the claim modules can
state the paper's theorems verbatim:

* `dot`, `dotChar` — the coordinate pairing and the additive character
  `v ↦ ω^{x·v}` on `Z_q^k`, built on Mathlib's `ZMod.stdAddChar`;
* `dft`/`fhat` — the Fourier transform with the paper's convention
  `fhat x = q^{-m/2} ∑_e ω^{x·e} f e` (Section 2.1, Definition 6);
* `psi` — the S|LWE⟩ state `|ψ_s⟩ = ∑_e f(e)|Aᵀ s + e⟩` (Definition 12);
* `Wraw`, `wNorm`, `Wvec` — the IC|LWE⟩ states
  `|W_y⟩ = w_y^{-1/2} ∑_s ω^{-y·s} |ψ_s⟩` and their normalization
  (Definition 14);
* the shifted dual lattice `Λ_y^⊥(A) = {x : A x = y mod q}` (Definition 6);
* statistical distance, fidelity, and the randomness-recoverability interface
  (Definition 16).

Only Mathlib's additive-character orthogonality is reused
(`AddChar.sum_eq_ite`, `ZMod.stdAddChar`); no statement of the paper was found
in Dev or in Frozen v2.0.2 (searched for `ISIS`, `S|LWE`, `stdAddChar`,
`randomness recoverable`), so the whole block is built here.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Qatlib.Papers.QSLWEISIS25.MainResults

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {q n m : ℕ}

/-- The ambient space `Z_q^m` (ISIS solutions / S|LWE⟩ error vectors). -/
abbrev Vec (q m : ℕ) := Fin m → ZMod q

/-- The secret space `Z_q^n`. -/
abbrev Secret (q n : ℕ) := Fin n → ZMod q

section Basic

variable [NeZero q]

/-- The coordinate pairing `x · y = ∑ i, x i * y i` over `ZMod q`. -/
def dot {k : ℕ} (x y : Fin k → ZMod q) : ZMod q := ∑ i, x i * y i

/-- The additive character `v ↦ ω^{x·v}` on `Z_q^k`, where `ω = exp(2πi/q)`
is Mathlib's `ZMod.stdAddChar`. -/
noncomputable def dotChar {k : ℕ} (x : Fin k → ZMod q) : AddChar (Fin k → ZMod q) ℂ where
  toFun v := ZMod.stdAddChar (dot x v)
  map_zero_eq_one' := by simp [dot]
  map_add_eq_mul' := by
    intro a b
    have h : dot x (a + b) = dot x a + dot x b := by
      simp [dot, mul_add, Finset.sum_add_distrib]
    rw [h, AddChar.map_add_eq_mul]

/-- Unfold `dotChar x v` to the standard additive character at the inner product. -/
@[simp]
lemma dotChar_apply {k : ℕ} (x : Fin k → ZMod q) (v : Fin k → ZMod q) :
    dotChar x v = ZMod.stdAddChar (dot x v) := rfl

/-- `dotChar` is additive in the frequency: `ω^{(x+y)·v} = ω^{x·v} ω^{y·v}`. -/
lemma dotChar_add {k : ℕ} (x y : Fin k → ZMod q) (v : Fin k → ZMod q) :
    dotChar (x + y) v = dotChar x v * dotChar y v := by
  simp only [dotChar_apply]
  have hdot : dot (x + y) v = dot x v + dot y v := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  rw [hdot, AddChar.map_add_eq_mul]

/-- `dotChar (-x) v = (dotChar x v)⁻¹`. -/
lemma dotChar_neg {k : ℕ} (x : Fin k → ZMod q) (v : Fin k → ZMod q) :
    dotChar (-x) v = (dotChar x v)⁻¹ := by
  simp only [dotChar_apply]
  have hdot : dot (-x) v = -(dot x v) := by
    simp [dot]
  rw [hdot, AddChar.map_neg_eq_inv]

/-- The character `dotChar x` is the constant character `1` only for `x = 0`. -/
lemma dotChar_eq_zero_iff {k : ℕ} (x : Fin k → ZMod q) : dotChar x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have h1 : dotChar x (Pi.single i 1) = (0 : AddChar (Fin k → ZMod q) ℂ) (Pi.single i 1) := by
      rw [h]
    have h2 : dotChar x (Pi.single i 1) = ZMod.stdAddChar (x i) := by
      rw [dotChar_apply]
      have hd : dot x (Pi.single i 1) = x i := by
        rw [dot, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji, mul_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hd]
    have h3 : (0 : AddChar (Fin k → ZMod q) ℂ) (Pi.single i 1) = 1 :=
      AddChar.map_zero_eq_one (0 : AddChar (Fin k → ZMod q) ℂ)
    rw [h2, h3] at h1
    exact ZMod.injective_stdAddChar (h1.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
  · intro h
    subst h
    ext v
    simp [dotChar_apply, dot]

/-- **Orthogonality of characters** on `Z_q^k`:
`∑_v ω^{x·v} = q^k` if `x = 0`, and `0` otherwise. -/
theorem sum_dotChar {k : ℕ} (x : Fin k → ZMod q) :
    (∑ v : Fin k → ZMod q, dotChar x v) = if x = 0 then (q : ℂ) ^ k else 0 := by
  classical
  by_cases hx : x = 0
  · have h : dotChar x = 0 := (dotChar_eq_zero_iff x).mpr hx
    rw [AddChar.sum_eq_ite, if_pos h, if_pos hx]
    have hcard : (Fintype.card (Fin k → ZMod q) : ℂ) = (q : ℂ) ^ k := by
      simp [Fintype.card_fun, ZMod.card]
    exact hcard
  · have h : dotChar x ≠ 0 := fun hh => hx ((dotChar_eq_zero_iff x).mp hh)
    rw [AddChar.sum_eq_ite, if_neg h, if_neg hx]

/-- Reindexing against a translation: `∑_v F (v - c) = ∑_e F e`. -/
lemma sum_sub_shift {k : ℕ} (F : (Fin k → ZMod q) → ℂ) (c : Fin k → ZMod q) :
    (∑ v, F (v - c)) = ∑ e, F e := by
  have hbij : Function.Bijective (fun v : Fin k → ZMod q => v - c) := by
    refine ⟨fun a b h => ?_, fun b => ⟨b + c, ?_⟩⟩
    · have := congrArg (fun z => z + c) h
      simpa using this
    · simp
  simpa using Function.Bijective.sum_comp hbij F

/-- `dot x (Aᵀ s) = (A x) · s`. -/
lemma dot_transpose_mulVec (A : Matrix (Fin n) (Fin m) (ZMod q))
    (x : Vec q m) (s : Secret q n) :
    dot x (A.transpose.mulVec s) = dot (A.mulVec x) s := by
  simp only [dot, Matrix.mulVec, dotProduct]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.transpose_apply]
  ring

/-- `√(q^m)` as a complex scalar (the Fourier normalization). -/
noncomputable def sqrtVol (q m : ℕ) : ℂ := (Real.sqrt ((q : ℝ) ^ m) : ℂ)

/-- The Fourier transform on `Z_q^m` with the paper's convention
`Ψhat x = q^{-m/2} ∑_v ω^{x·v} Ψ v` (Section 2.1). -/
noncomputable def dft {m : ℕ} (Ψ : Vec q m → ℂ) (x : Vec q m) : ℂ :=
  (sqrtVol q m)⁻¹ * ∑ v, dotChar x v * Ψ v

/-- The Fourier transform of an amplitude function `f : Z_q^m → ℂ`
(`fhat x = q^{-m/2} ∑_e ω^{x·e} f e`, Definition 6). -/
noncomputable def fhat {m : ℕ} (f : Vec q m → ℂ) : Vec q m → ℂ := dft f

/-- The S|LWE⟩ state `|ψ_s⟩ = ∑_e f(e)|Aᵀ s + e⟩` (Definition 12), as the
amplitude function `v ↦ f (v - Aᵀ s)`. -/
noncomputable def psi (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (s : Secret q n) : Vec q m → ℂ :=
  fun v => f (v - A.transpose.mulVec s)

/-- Fourier transform of `|ψ_s⟩`. -/
noncomputable def psiHat (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (s : Secret q n) : Vec q m → ℂ := dft (psi A f s)

/-- The unnormalized `W_y` amplitudes: `∑_s ω^{-y·s} |ψ_s⟩`. -/
noncomputable def Wraw (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) : Vec q m → ℂ :=
  fun v => ∑ s, dotChar (-y) s * psi A f s v

/-- The normalizing factor `w_y = ∑_v ‖W_y(v)‖²` (Definition 14). -/
noncomputable def wNorm (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) : ℝ :=
  ∑ v, ‖Wraw A f y v‖ ^ 2

/-- The IC|LWE⟩ state `|W_y⟩ = w_y^{-1/2} ∑_s ω^{-y·s}|ψ_s⟩` (Definition 14). -/
noncomputable def Wvec (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) : Vec q m → ℂ :=
  fun v => ((Real.sqrt (wNorm A f y) : ℂ))⁻¹ * Wraw A f y v

/-- Fourier transform of `|W_y⟩`. -/
noncomputable def WHat (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ)
    (y : Secret q n) : Vec q m → ℂ := dft (Wvec A f y)

/-- The shifted dual lattice `Λ_y^⊥(A) = {x : A x = y mod q}` (Definition 6). -/
def shiftedDual (A : Matrix (Fin n) (Fin m) (ZMod q)) (y : Secret q n) : Set (Vec q m) :=
  {x | A.mulVec x = y}

/-- Squared norm of a (not necessarily normalized) state. -/
noncomputable def stateNormSq {α : Type*} [Fintype α] (Ψ : α → ℂ) : ℝ :=
  ∑ v, ‖Ψ v‖ ^ 2

/-- The mass of the Fourier support on a set `T`: `∑_{x ∈ T} ‖fhat x‖²`. -/
noncomputable def supportMass (f : Vec q m → ℂ) (T : Set (Vec q m)) : ℝ := by
  classical
  exact Finset.sum (Finset.univ.filter (fun x => x ∈ T)) (fun x => ‖fhat f x‖ ^ 2)

/-- Statistical distance between two finitely-supported probability mass
functions (Section 2.1). -/
noncomputable def statDist {α : Type*} [Fintype α] (p r : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |p x - r x|

/-- Fidelity between two finitely-supported probability mass functions
(the Fuchs–van de Graaf quantity `∑_x √(p x r x)`, Section 6). -/
noncomputable def distributionFidelity {α : Type*} [Fintype α] (p r : α → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p x * r x)

/-- A random tape with `ℓ` bits, `{0,1}^ℓ`. -/
abbrev Tape (ℓ : ℕ) := Fin ℓ → Bool

/-- Definition 16: a randomized algorithm `A` (with abort encoded as `none`) is
**perfectly randomness-recoverable** when an extractor `E` recovers the tape
from the input and the output. -/
def PerfectlyRandomnessRecoverable {Y X : Type*} {ℓ : ℕ}
    (A : Y → Tape ℓ → Option X) (E : Y → Option X → Tape ℓ) : Prop :=
  ∀ (r : Tape ℓ) (y : Y), E y (A y r) = r

/-- The output law of a randomized algorithm with uniform random tape. -/
noncomputable def outputLaw {Y X : Type*} [Fintype Y] [Fintype X] {ℓ : ℕ}
    (A : Y → Tape ℓ → Option X) (y : Y) (x : X) : ℝ := by
  classical
  exact ((Fintype.card (Tape ℓ) : ℝ))⁻¹ *
    ((Finset.univ.filter (fun r => A y r = some x)).card : ℝ)

/-- A nonnegative sequence is negligible when it decays faster than every inverse
power of `n`. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ (n : ℝ) ^ (-(k : ℝ))

/-- A randomized classical algorithm for `ISIS(A, T)` with random tape `{0,1}^ℓ`,
uniform in the challenge matrix `A`.  `none` is the abort symbol.  The field
`correct` is the property proved in Proposition 10: every non-aborting output is
an ISIS solution. -/
structure IsisSolver (q n m ℓ : ℕ) [NeZero q] (T : Set (Vec q m)) where
  out : Matrix (Fin n) (Fin m) (ZMod q) → Secret q n → Tape ℓ → Option (Vec q m)
  time : ℝ
  htime : 0 ≤ time
  correct : ∀ A y r x, out A y r = some x → x ∈ T ∧ A.mulVec x = y

/-- A randomness-recoverable classical ISIS algorithm (Definition 16): an ISIS
solver together with an extractor `E` that recovers the random tape from the
challenge matrix and the algorithm's output. -/
structure RecoverableIsisAlg (q n m ℓ : ℕ) [NeZero q] (T : Set (Vec q m))
    extends IsisSolver q n m ℓ T where
  E : Matrix (Fin n) (Fin m) (ZMod q) → Option (Vec q m) → Tape ℓ
  recover : ∀ A y r, E A (out A y r) = r

/-- Success probability of a randomized ISIS solver, over the uniform challenge
`y` and the uniform random tape. -/
noncomputable def successProb {q n m ℓ : ℕ} [NeZero q] {T : Set (Vec q m)}
    (S : IsisSolver q n m ℓ T) (A : Matrix (Fin n) (Fin m) (ZMod q)) : ℝ := by
  classical
  exact ((Fintype.card (Secret q n) : ℝ) * (Fintype.card (Tape ℓ) : ℝ))⁻¹ *
    ∑ y, ((Finset.univ.filter (fun r => (S.out A y r).isSome)).card : ℝ)

/-- The output law of a randomized ISIS solver on a fixed challenge `y`. -/
noncomputable def solverOutputLaw {q n m ℓ : ℕ} [NeZero q] {T : Set (Vec q m)}
    (S : IsisSolver q n m ℓ T) (A : Matrix (Fin n) (Fin m) (ZMod q))
    (y : Secret q n) (x : Vec q m) : ℝ :=
  outputLaw (fun (y : Secret q n) (r : Tape ℓ) => S.out A y r) y x

/-- The uniform distribution on a finite set. -/
noncomputable def uniformOn {α : Type*} [Fintype α] (s : Finset α) (x : α) : ℝ := by
  classical
  exact if x ∈ s then ((s.card : ℝ))⁻¹ else 0

/-- Definition 15: a unitary for `IC|LWE⟩(A, f)`, described by its output states
`W' y` (which are unit vectors). -/
structure ICLWEUnitary {q n m : ℕ} [NeZero q]
    (A : Matrix (Fin n) (Fin m) (ZMod q)) (f : Vec q m → ℂ) where
  time : ℝ
  htime : 0 ≤ time
  W' : Secret q n → Vec q m → ℂ
  unit : ∀ y, stateNormSq (W' y) = 1

/-- The average overlap `E_y |⟨W_y | W'_y⟩|` of Definition 15, i.e. the fidelity
of the IC|LWE⟩ unitary. -/
noncomputable def averageOverlap {q n m : ℕ} [NeZero q]
    {A : Matrix (Fin n) (Fin m) (ZMod q)} {f : Vec q m → ℂ}
    (U : ICLWEUnitary A f) : ℝ :=
  (Fintype.card (Secret q n) : ℝ)⁻¹ *
    ∑ y, ‖∑ v, (star (Wvec A f y v)) * U.W' y v‖

end Basic

end Qatlib.Papers.QSLWEISIS25.MainResults
