/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.Source
public import Qatlib.Papers.HamInversion26.SpinInversion.SpectralTwirl.CyclicShiftTwirl
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The spectral routing word: `K − 1` forward calls invert the spectral family

Fixed arXiv:2607.29382v2.  Theorem 1, page 2 (Eq. (2)), and Theorem S2, pages S4–S7,
Eqs. (S6)–(S8): the *sufficiency* direction of the sumset criterion.  For a diagonal family
`U(t) = Σ_j e^{i λ_j t} Π_j` in a fixed eigenbasis, `K − 1` forward calls suffice to
implement `U(t)†` up to a global phase.

The word is the paper's `R_t = ∏_{r=1}^{K−1} S^r U(t) S^{−r}` with the cyclic shift `S` of
Lemma S1 (`Qatlib.Papers.HamInversion26.SpinInversion.SpectralTwirl.cyclicShiftPow`).  Since
`S` only permutes the basis, `S^r` is a fixed gate for every `r`, and the product is the word

`(S U)^{K−1} S^{−(K−1)}`      (`routeWord` below),

which has `K − 1` forward calls, all other gates equal to `S`, and evaluates to a diagonal
matrix whose `i`-th entry is `e^{i t Σ_{r=1}^{K−1} λ_{i−r}} = e^{i t (c − λ_i)}` with
`c = Σ_j λ_j`.  That is `e^{i c t}` times the `i`-th entry of `U(t)†`, i.e. inversion up to
the global phase `ω(t) = e^{i c t}`: the witness `c = Σ Λ` of
`Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset.kappaWitness_card_sub_one`.

The construction is carried out on the `ZMod K` index set where the shift arithmetic of
Lemma S1 already lives (`spectralUnitaryZ`, `routeWord`, `eval_routeWord_spectral`,
`spectral_route_inverts_Z`), then transported to the paper's `Fin K` eigenbasis along
`ZMod.finEquiv` (`spectral_route_inverts`).

Not covered: the *necessity* direction (no `q < κ(Λ)` forward calls invert the family), hence
the equality "minimum number of calls `= κ(Λ)`" of Theorem 1 is not formalised.  Distinctness
of the eigenvalues plays no role in the sufficiency direction, which matches the paper's
remark that multiplicities do not enter.
-/

open Matrix
open scoped BigOperators Kronecker

namespace Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset

open Qatlib.Papers.HamInversion26.SpinInversion
open Qatlib.Papers.HamInversion26.SpinInversion.Model
open Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset
open Qatlib.Papers.HamInversion26.SpinInversion.SpectralTwirl

set_option autoImplicit false
noncomputable section

variable {K : ℕ} [NeZero K]

/-! ## The routing word on the cyclic-shift index set -/

/-- The spectral family `U(t) = Σ_j e^{i λ_j t} Π_j` on the `ZMod K` index set of Lemma S1
(Eq. (S10), page S4): `Qatlib...SpectralSumset.spectralUnitary` after reindexing. -/
def spectralUnitaryZ (lam : ZMod K → ℝ) (t : ℝ) : Matrix (ZMod K) (ZMod K) ℂ :=
  diagonal fun j => Complex.exp (Complex.I * ((lam j * t : ℝ) : ℂ))

/-- The routing word `(S U)^m S^{last}` of Eqs. (S6)–(S8): `m` forward calls interleaved with
the fixed cyclic shift `S`, followed by the fixed shift `S^{last}`. -/
def routeWord : (m : ℕ) → ZMod K → Word (ZMod K) m
  | 0, last => Word.done (cyclicShiftPow last)
  | m + 1, last => Word.step (cyclicShift (n := K)) (routeWord m last)

/-- The accumulated phase `∏_{r < m} a (i − (r + 1))` after `m` routing steps. -/
def cumProd (a : ZMod K → ℂ) (m : ℕ) (i : ZMod K) : ℂ :=
  ∏ r ∈ Finset.range m, a (i - ((r + 1 : ℕ) : ZMod K))

omit [NeZero K] in

/-- One more routing step multiplies the accumulated phase by `a (i − (m + 1))`. -/
theorem cumProd_succ (a : ZMod K → ℂ) (m : ℕ) (i : ZMod K) :
    cumProd a (m + 1) i = cumProd a m i * a (i - ((m + 1 : ℕ) : ZMod K)) := by
  simp only [cumProd, Finset.prod_range_succ]

/-- A cyclic shift moves past a diagonal matrix by shifting its entries:
`S^r · diag a = diag (a (· − r)) · S^r`. -/
theorem cyclicShiftPow_mul_diagonal (a : ZMod K → ℂ) (r : ZMod K) :
    cyclicShiftPow r * diagonal a =
      diagonal (fun i => a (i - r)) * cyclicShiftPow r := by
  ext i j
  have hlhs : (cyclicShiftPow (n := K) r * diagonal a) i j =
      (if i = j + r then 1 else 0) * a j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [cyclicShiftPow]
    · intro b _ hb
      simp [cyclicShiftPow, hb]
    · intro h
      simp at h
  have hrhs : (diagonal (fun i => a (i - r)) * cyclicShiftPow (n := K) r) i j =
      a (i - r) * (if i = j + r then 1 else 0) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [cyclicShiftPow]
    · intro l _ hl
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
    · intro h
      simp at h
  rw [hlhs, hrhs]
  by_cases h : i = j + r
  · subst h
    rw [add_sub_cancel_right]
    simp
  · simp [h]

/-- The `m`-th power of the routing step is a diagonal phase matrix times the `m`-th cyclic
shift: `(S U)^m = diag (cumProd a m) · S^m`. -/
theorem mul_cyclicShift_diagonal_pow (a : ZMod K → ℂ) (m : ℕ) :
    (cyclicShift * diagonal a) ^ m =
      diagonal (cumProd a m) * cyclicShiftPow (m : ZMod K) := by
  induction m with
  | zero =>
    show (1 : Matrix (ZMod K) (ZMod K) ℂ) =
      diagonal (cumProd a 0) * cyclicShiftPow ((0 : ℕ) : ZMod K)
    have hzero : cumProd a 0 = fun _ => (1 : ℂ) := by
      funext i
      simp [cumProd]
    rw [hzero, Matrix.diagonal_one, Nat.cast_zero, cyclicShiftPow_zero, mul_one]
  | succ m ih =>
    have hS : cyclicShiftPow (n := K) (m : ZMod K) * cyclicShift (n := K) =
        cyclicShiftPow (n := K) ((m + 1 : ℕ) : ZMod K) := by
      rw [cyclicShift, cyclicShiftPow_mul, Nat.cast_add, Nat.cast_one]
    have hstep : cyclicShiftPow (n := K) ((m + 1 : ℕ) : ZMod K) * diagonal a =
        diagonal (fun i => a (i - ((m + 1 : ℕ) : ZMod K))) *
          cyclicShiftPow (n := K) ((m + 1 : ℕ) : ZMod K) :=
      cyclicShiftPow_mul_diagonal a _
    calc (cyclicShift * diagonal a) ^ (m + 1)
        = (cyclicShift * diagonal a) ^ m * (cyclicShift * diagonal a) := pow_succ _ _
      _ = diagonal (cumProd a m) * (cyclicShiftPow (m : ZMod K) *
            (cyclicShift * diagonal a)) := by
            rw [ih]
            simp only [Matrix.mul_assoc]
      _ = diagonal (cumProd a m) * (cyclicShiftPow (m : ZMod K) * cyclicShift (n := K) *
            diagonal a) := by
            rw [← Matrix.mul_assoc (cyclicShiftPow (m : ZMod K)) (cyclicShift (n := K))
              (diagonal a)]
      _ = diagonal (cumProd a m) * (cyclicShiftPow ((m + 1 : ℕ) : ZMod K) * diagonal a) := by
            rw [hS]
      _ = diagonal (cumProd a m) * (diagonal (fun i => a (i - ((m + 1 : ℕ) : ZMod K))) *
            cyclicShiftPow ((m + 1 : ℕ) : ZMod K)) := by
            rw [hstep]
      _ = diagonal (cumProd a m) * diagonal (fun i => a (i - ((m + 1 : ℕ) : ZMod K))) *
            cyclicShiftPow ((m + 1 : ℕ) : ZMod K) := by
            rw [Matrix.mul_assoc]
      _ = diagonal (cumProd a (m + 1)) * cyclicShiftPow ((m + 1 : ℕ) : ZMod K) := by
            have hfun : (fun i => cumProd a m i * a (i - ((m + 1 : ℕ) : ZMod K))) =
                cumProd a (m + 1) := by
              funext i
              exact (cumProd_succ a m i).symm
            rw [Matrix.diagonal_mul_diagonal, hfun]

/-- Evaluation of the routing word at the diagonal family `diag a`: `(S · diag a)^m S^{last}`. -/
theorem eval_routeWord (m : ℕ) (last : ZMod K) (a : ZMod K → ℂ) :
    Word.eval (routeWord (K := K) m last) (diagonal a) =
      (cyclicShift * diagonal a) ^ m * cyclicShiftPow last := by
  induction m with
  | zero =>
    show Word.eval (Word.done (cyclicShiftPow last)) (diagonal a) =
      (cyclicShift * diagonal a) ^ 0 * cyclicShiftPow last
    rw [Word.eval_done, pow_zero, one_mul]
  | succ m ih =>
    simp only [routeWord, Word.eval_step, ih, pow_succ']
    rw [Matrix.mul_assoc (cyclicShift * diagonal a) ((cyclicShift * diagonal a) ^ m)
      (cyclicShiftPow last)]

/-- The conjugate transpose of an exponential of a purely imaginary real phase. -/
theorem star_exp_I_mul (x : ℝ) :
    star (Complex.exp (Complex.I * (x : ℂ))) = Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) := by
  have h1 : star (Complex.exp (Complex.I * (x : ℂ)))
      = Complex.exp (star (Complex.I * (x : ℂ))) := by
    simpa using (Complex.exp_conj (Complex.I * (x : ℂ))).symm
  rw [h1]
  congr 1
  have hI : star (Complex.I) = -Complex.I := Complex.conj_I
  have hx : star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := Complex.conj_ofReal x
  rw [star_mul', hI, hx]
  push_cast
  ring

omit [NeZero K] in

/-- The adjoint of the spectral family is the diagonal with the negated eigenvalues. -/
theorem spectralUnitaryZ_conjTranspose (lam : ZMod K → ℝ) (t : ℝ) :
    (spectralUnitaryZ (K := K) lam t)ᴴ =
      diagonal (fun i => Complex.exp (Complex.I * ((-(lam i) * t : ℝ) : ℂ))) := by
  rw [spectralUnitaryZ, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply]
  simpa [neg_mul] using star_exp_I_mul (lam i * t)

/-! ## The sum of the shifted eigenvalues -/

/-- The residues `1, …, K − 1` exhaust the nonzero elements of `ZMod K`. -/
theorem sum_range_succ_natCast (g : ZMod K → ℝ) :
    (∑ r ∈ Finset.range (K - 1), g ((r + 1 : ℕ) : ZMod K)) =
      ∑ z ∈ (Finset.univ.erase 0), g z := by
  refine Finset.sum_bij (fun r _ => ((r + 1 : ℕ) : ZMod K)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_range] at hr
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hzero
    have hval : (((r + 1 : ℕ) : ZMod K)).val = r + 1 := ZMod.val_natCast_of_lt (by omega)
    rw [hzero] at hval
    simp at hval
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_range] at hr1 hr2
    have h1 : (((r1 + 1 : ℕ) : ZMod K)).val = r1 + 1 := ZMod.val_natCast_of_lt (by omega)
    have h2 : (((r2 + 1 : ℕ) : ZMod K)).val = r2 + 1 := ZMod.val_natCast_of_lt (by omega)
    have hval := congrArg ZMod.val heq
    rw [h1, h2] at hval
    omega
  · intro z hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
    have hne : z.val ≠ 0 := fun h => hz ((ZMod.val_eq_zero z).mp h)
    have hlt : z.val < K := ZMod.val_lt z
    refine ⟨z.val - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · have h1 : z.val - 1 + 1 = z.val := by omega
      rw [h1, ZMod.natCast_zmod_val]
  · intro r _
    rfl

/-- The eigenvalues `λ_{i−r}` over the nonzero shifts sum to the total minus `λ_i`. -/
theorem sum_range_shift_sub (f : ZMod K → ℝ) (i : ZMod K) :
    (∑ r ∈ Finset.range (K - 1), f (i - ((r + 1 : ℕ) : ZMod K))) =
      (∑ z, f (i - z)) - f i := by
  rw [sum_range_succ_natCast (K := K) (g := fun z => f (i - z))]
  refine eq_sub_iff_add_eq.mpr ?_
  have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod K)) (fun z => f (i - z))
    (Finset.mem_univ (0 : ZMod K))
  simp only [sub_zero] at h
  exact h

/-- The total of the negated eigenvalues is the shift-invariant total. -/
theorem sum_sub_shift (f : ZMod K → ℝ) (i : ZMod K) :
    (∑ z : ZMod K, f (i - z)) = ∑ z, f z :=
  Equiv.sum_comp
    { toFun := fun z => i - z
      invFun := fun z => i - z
      left_inv := fun x => by simp
      right_inv := fun x => by simp } f

/-! ## The routed evaluation -/

/-- The routed word evaluates on the spectral family to the global phase `e^{i c t}` times the
adjoint family, `c = Σ_j λ_j`. -/
theorem eval_routeWord_spectral (lam : ZMod K → ℝ) (t : ℝ) :
    Word.eval (routeWord (K := K) (K - 1) (-(((K - 1 : ℕ)) : ZMod K)))
        (spectralUnitaryZ (K := K) lam t) =
      diagonal (fun i => Complex.exp (Complex.I * (((∑ z, lam z) - lam i) * t : ℝ) : ℂ)) := by
  have hmain : Word.eval (routeWord (K := K) (K - 1) (-(((K - 1 : ℕ)) : ZMod K)))
        (spectralUnitaryZ (K := K) lam t) =
      (cyclicShift * diagonal (fun j => Complex.exp (Complex.I * ((lam j * t : ℝ) : ℂ)))) ^
          (K - 1) * cyclicShiftPow (-(((K - 1 : ℕ)) : ZMod K)) := by
    simpa [spectralUnitaryZ] using
      eval_routeWord (K := K) (K - 1) (-(((K - 1 : ℕ)) : ZMod K))
        (fun j => Complex.exp (Complex.I * ((lam j * t : ℝ) : ℂ)))
  rw [hmain, mul_cyclicShift_diagonal_pow]
  have hlast : cyclicShiftPow (n := K) ((K - 1 : ℕ) : ZMod K) *
      cyclicShiftPow (n := K) (-(((K - 1 : ℕ)) : ZMod K)) = 1 := by
    rw [cyclicShiftPow_mul, add_neg_cancel, cyclicShiftPow_zero]
  rw [Matrix.mul_assoc, hlast, Matrix.mul_one]
  congr 1
  funext i
  rw [cumProd, ← Complex.exp_sum]
  congr 1
  have hreal : (∑ r ∈ Finset.range (K - 1),
        lam (i - ((r + 1 : ℕ) : ZMod K)) * t) = ((∑ z, lam z) - lam i) * t := by
    rw [← Finset.sum_mul (Finset.range (K - 1))
      (fun r => lam (i - ((r + 1 : ℕ) : ZMod K))) t,
      sum_range_shift_sub (K := K) (f := lam) (i := i),
      sum_sub_shift (K := K) (f := lam) (i := i)]
  rw [← hreal, Complex.ofReal_sum (Finset.range (K - 1))
    (fun r => lam (i - ((r + 1 : ℕ) : ZMod K)) * t),
    ← Finset.mul_sum (Finset.range (K - 1))
      (fun r => ((lam (i - ((r + 1 : ℕ) : ZMod K)) * t : ℝ) : ℂ)) Complex.I]

/-- **Theorem 1, sufficiency on the cyclic-shift index set**: `K − 1` forward calls invert the
spectral family up to the global phase `e^{i t Σ_j λ_j}`. -/
theorem spectral_route_inverts_Z (lam : ZMod K → ℝ) :
    InvertsIn (H := ZMod K) (K - 1) (spectralUnitaryZ (K := K) lam) := by
  refine ⟨routeWord (K := K) (K - 1) (-(((K - 1 : ℕ)) : ZMod K)),
    fun t => Complex.exp (Complex.I * (((∑ j, lam j) * t : ℝ) : ℂ)), fun t => ?_⟩
  rw [eval_routeWord_spectral, spectralUnitaryZ_conjTranspose]
  ext i j
  rw [Matrix.smul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, smul_zero]

/-! ## Transport to the paper's `Fin K` eigenbasis -/

/-- Reindexing preserves matrix multiplication. -/
theorem reindex_mul' {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
    (e : H ≃ H') (M N : Matrix H H ℂ) :
    Matrix.reindex e e (M * N) = Matrix.reindex e e M * Matrix.reindex e e N :=
  (Matrix.reindexRingEquiv ℂ e).map_mul M N

/-- Reindexing preserves scalar multiplication. -/
theorem reindex_smul' {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
    (e : H ≃ H') (r : ℂ) (M : Matrix H H ℂ) :
    Matrix.reindex e e (r • M) = r • Matrix.reindex e e M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix, Matrix.smul_apply]

/-- Reindexing commutes with the conjugate transpose. -/
theorem reindex_conjTranspose' {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] (e : H ≃ H') (M : Matrix H H ℂ) :
    Matrix.reindex e e Mᴴ = (Matrix.reindex e e M)ᴴ :=
  (Matrix.conjTranspose_reindex e e M).symm

/-- Reindexing a diagonal matrix reindexes its entries. -/
theorem reindex_diagonal' {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] (e : H ≃ H') (a : H → ℂ) :
    Matrix.reindex e e (diagonal a) = diagonal (fun i => a (e.symm i)) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun hh => h (e.symm.injective hh)),
      Matrix.diagonal_apply_ne _ h]

/-- Reindex the fixed gates of a matrix word along an equivalence of registers. -/
def wordReindex {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
    (e : H ≃ H') : {q : ℕ} → Word H q → Word H' q
  | 0, .done g => .done (Matrix.reindex e e g)
  | _, .step g rest => .step (Matrix.reindex e e g) (wordReindex e rest)

/-- Reindexing a matrix word transports its evaluation. -/
theorem eval_wordReindex {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] (e : H ≃ H') (U : Matrix H H ℂ) :
    ∀ {q : ℕ} (W : Word H q),
      Word.eval (wordReindex e W) (Matrix.reindex e e U) =
        Matrix.reindex e e (Word.eval W U) := by
  intro q W
  induction W with
  | done g => rfl
  | step g rest ih =>
    simp only [wordReindex, Word.eval_step, ih]
    rw [reindex_mul', reindex_mul']

/-- **Theorem 1 / Theorem S2, sufficiency** (Eq. (2), page 2; Eqs. (S6)–(S8), pages S4–S7):
for a diagonal family `U(t) = Σ_j e^{i λ_j t} Π_j` on `Fin K`, the routed `K − 1`-query word
implements `U(t)†` up to the global phase `e^{i t Σ_j λ_j}`, so `K − 1` forward calls suffice. -/
theorem spectral_route_inverts {K : ℕ} (hK : 0 < K) (lam : Fin K → ℝ) :
    InvertsIn (H := Fin K) (K - 1) (spectralUnitary lam) := by
  classical
  have : NeZero K := ⟨by omega⟩
  set e : Fin K ≃ ZMod K := (ZMod.finEquiv K).toEquiv
  obtain ⟨W, ω, hW⟩ := spectral_route_inverts_Z (K := K) (fun z => lam (e.symm z))
  refine ⟨wordReindex e.symm W, ω, fun t => ?_⟩
  have hU : Matrix.reindex e.symm e.symm
        (spectralUnitaryZ (K := K) (fun z => lam (e.symm z)) t) = spectralUnitary lam t := by
    rw [spectralUnitaryZ, reindex_diagonal', spectralUnitary]
    congr 1
    funext i
    simp
  have h1 : Word.eval (wordReindex e.symm W) (spectralUnitary lam t) =
      Matrix.reindex e.symm e.symm
        (Word.eval W (spectralUnitaryZ (K := K) (fun z => lam (e.symm z)) t)) := by
    rw [← hU]
    exact eval_wordReindex e.symm _ W
  rw [h1, hW t, reindex_smul', reindex_conjTranspose', hU]

end

end Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset
