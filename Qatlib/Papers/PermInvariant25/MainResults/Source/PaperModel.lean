/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Entropy.VonNeumann
import QuantumInfo.Channels.CPTP
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option backward.isDefEq.respectTransparency false

/-!
# Paper model for *Improving quantum communication rates with permutation-invariant codes*

Bhalerao–Leditzky, fixed arXiv:2508.09978v1.

This file collects the concrete finite-dimensional objects that the paper's
statements refer to:

* the weighted repetition code `φₓⁿ = x |0⟩⟨0|^{⊗n} + (1-x) |1⟩⟨1|^{⊗n}` (equation (5.2));
* the Pauli channel `N_p(ρ) = p₀ρ + p₁XρX + p₂YρY + p₃ZρZ` (equation (5.3)) as a
  `CPTPMap` from the Kraus decomposition, and its `n`-fold tensor power
  (`CPTPMap.piProd`);
* the damping–dephasing channel `F_{p,g}` in the Kraus form (5.42)–(5.44) /
  (D.1)–(D.3);
* the closed-form eigenvalue expressions used in Proposition 5.1
  (equations (5.5)–(5.7)) and Theorem 5.2 (equations (5.45)–(5.46)).

The Hilbert space of `n` qubits is indexed by `Fin n → Fin 2` (a bit string), so that
the `n`-fold tensor power of a one-qubit channel is literally `CPTPMap.piProd`.

Everything is stated over the Physlib `MState`/`CPTPMap`/`coherentInfo` interface;
the paper's symbol `Ic(Λ, ρ)` is `Physlib`'s `coherentInfo ρ Λ`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Qatlib.Papers.PermInvariant25.MainResults.Source

/-! ## Shannon entropy with the `0 log 0 = 0` convention -/

/-- Shannon entropy `H(p) = -∑ i, p i * log (p i)`, with `0 log 0 = 0`
(paper equation (4.12) and throughout). -/
def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-! ## The weighted repetition code (5.2) -/

/-- The all-zero bit string `0ⁿ`. -/
def zeroFun (n : ℕ) : Fin n → Fin 2 := fun _ => 0

/-- The all-one bit string `1ⁿ`. -/
def oneFun (n : ℕ) : Fin n → Fin 2 := fun _ => 1

/-- For `n ≥ 1` the two repetition codewords are distinct. -/
theorem zeroFun_ne_oneFun {n : ℕ} (hn : 1 ≤ n) : zeroFun n ≠ oneFun n := by
  intro h
  have h0 := congrFun h ⟨0, hn⟩
  simp [zeroFun, oneFun] at h0

/-- The probability law of the weighted repetition code: mass `x` on `0ⁿ` and `1 - x`
on `1ⁿ` (equation (5.2)).  It is only a probability law for `n ≥ 1`, where the two
codewords are distinct. -/
def weightedRepetitionDist (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    ProbDistribution (Fin n → Fin 2) :=
  ProbDistribution.mk'
    (fun f => if f = zeroFun n then x else if f = oneFun n then 1 - x else 0)
    (by intro f; split_ifs <;> linarith)
    (by
      have hne : zeroFun n ≠ oneFun n := zeroFun_ne_oneFun hn
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (zeroFun n))]
      have hz : (if zeroFun n = zeroFun n then x else if zeroFun n = oneFun n then 1 - x else 0)
          = x := by simp
      rw [hz]
      have hrest :
          (Finset.univ.erase (zeroFun n)).sum
            (fun f => if f = zeroFun n then x else if f = oneFun n then 1 - x else 0) = 1 - x := by
        rw [Finset.sum_eq_single (oneFun n)]
        · simp [Ne.symm hne]
        · intro b hb hb1
          have hb0 : b ≠ zeroFun n := (Finset.mem_erase.mp hb).1
          simp [hb0, hb1]
        · intro hb
          exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩) hb
      rw [hrest]
      ring)

/-- The weighted repetition code `φₓⁿ = x |0⟩⟨0|^{⊗n} + (1-x) |1⟩⟨1|^{⊗n}`
(equation (5.2)), as a mixed state; it is diagonal in the computational basis. -/
def weightedRepetition (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    MState (Fin n → Fin 2) :=
  MState.ofClassical (weightedRepetitionDist x hx0 hx1 n hn)

/-! ## Pauli matrices and the Pauli channel (5.3) -/

/-- The identity. -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- Pauli `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The four Pauli matrices indexed by `Fin 4` (`I, X, Y, Z`). -/
def pauliMat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![pauliI, pauliX, pauliY, pauliZ]

/-- Each Pauli matrix is an involution: `P² = 1`. -/
theorem pauliMat_sq (k : Fin 4) : pauliMat k * pauliMat k = 1 := by
  fin_cases k <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, pauliI, pauliX, pauliY, pauliZ, Complex.I_mul_I]

/-- Each Pauli matrix is self-adjoint: `P† = P`. -/
theorem pauliMat_conjTranspose (k : Fin 4) :
    Matrix.conjTranspose (pauliMat k) = pauliMat k := by
  fin_cases k <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, pauliI, pauliX, pauliY, pauliZ]

/-- Kraus operators of the Pauli channel (5.3): `√p_k P_k`. -/
def pauliKraus (p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun k => ((Real.sqrt (p k) : ℝ) : ℂ) • pauliMat k

/-- `star (√a) * √a = a` for a nonnegative real, as complex scalars. -/
theorem sqrt_star_mul (a : ℝ) (ha : 0 ≤ a) :
    star ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]

/-- `√a * √a = a` for a nonnegative real, as complex scalars. -/
theorem ofReal_sq_sqrt (a : ℝ) (ha : 0 ≤ a) :
    ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha]

/-- The Kraus operators square-sum to the identity when `∑ p_k = 1`. -/
theorem pauliKraus_sum (p : Fin 4 → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) :
    (∑ k, Matrix.conjTranspose (pauliKraus p k) * pauliKraus p k) = 1 := by
  have hk : ∀ k, Matrix.conjTranspose (pauliKraus p k) * pauliKraus p k
      = ((p k : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro k
    simp only [pauliKraus, Matrix.conjTranspose_smul, pauliMat_conjTranspose]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliMat_sq]
    rw [sqrt_star_mul (p k) (hp k)]
  simp only [hk]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  simp

/-- The Pauli channel `N_p(ρ) = p₀ρ + p₁XρX + p₂YρY + p₃ZρZ` (equation (5.3)) as a
`CPTPMap`, built from the Kraus operators `√p_k P_k`. -/
def pauliChannel (p : Fin 4 → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) :
    CPTPMap (Fin 2) (Fin 2) where
  toLinearMap := MatrixMap.of_kraus (pauliKraus p) (pauliKraus p)
  cp := MatrixMap.of_kraus_isCompletelyPositive (pauliKraus p)
  TP := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _ (pauliKraus_sum p hp hsum)

/-- The `n`-fold tensor power `N_p^{⊗n}` of the Pauli channel. -/
def pauliChannelPow (p : Fin 4 → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (n : ℕ) : CPTPMap (Fin n → Fin 2) (Fin n → Fin 2) :=
  CPTPMap.piProd (fun _ : Fin n => pauliChannel p hp hsum)

/-! ## The damping–dephasing channel (5.42)–(5.44) -/

/-- The dephasing channel `D_p(ρ) = (1-p)ρ + p ZρZ` of §5.4, in Kraus form. -/
def dephasingKraus (p : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![ ((Real.sqrt (1 - p) : ℝ) : ℂ) • pauliI, ((Real.sqrt p : ℝ) : ℂ) • pauliZ ]

/-- The dephasing Kraus operators square-sum to the identity for `p ∈ [0,1]`. -/
theorem dephasingKraus_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ k, Matrix.conjTranspose (dephasingKraus p k) * dephasingKraus p k) = 1 := by
  have hp' : (0 : ℝ) ≤ 1 - p := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dephasingKraus, Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.one_apply, Complex.conj_ofReal, Complex.ofReal_mul,
      pauliI, pauliZ, ofReal_sq_sqrt p hp0, ofReal_sq_sqrt (1 - p) hp', Complex.ofReal_one]

/-- The dephasing channel `D_p` of §5.4 as a `CPTPMap`. -/
def dephasingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : CPTPMap (Fin 2) (Fin 2) where
  toLinearMap := MatrixMap.of_kraus (dephasingKraus p) (dephasingKraus p)
  cp := MatrixMap.of_kraus_isCompletelyPositive (dephasingKraus p)
  TP := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _
    (dephasingKraus_sum p hp0 hp1)

/-- The amplitude-damping Kraus operators `K₁ = |0⟩⟨0| + √(1-g)|1⟩⟨1|`,
`K₂ = √g |0⟩⟨1|` (the `N = 0` case of the generalized amplitude-damping channel). -/
def amplitudeDampingKraus (g : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![ !![1, 0; 0, ((Real.sqrt (1 - g) : ℝ) : ℂ)], !![0, ((Real.sqrt g : ℝ) : ℂ); 0, 0] ]

/-- The amplitude-damping Kraus operators square-sum to the identity for `g ∈ [0,1]`. -/
theorem amplitudeDampingKraus_sum (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    (∑ k, Matrix.conjTranspose (amplitudeDampingKraus g k) * amplitudeDampingKraus g k) = 1 := by
  have hg' : (0 : ℝ) ≤ 1 - g := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amplitudeDampingKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.one_apply, Complex.conj_ofReal, Complex.ofReal_mul, Fin.sum_univ_two,
      ofReal_sq_sqrt (1 - g) hg', ofReal_sq_sqrt g hg0, Complex.ofReal_one]

/-- The amplitude damping channel `A_g = A_{g,0}` of §5.4 as a `CPTPMap`. -/
def amplitudeDampingChannel (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : CPTPMap (Fin 2) (Fin 2) where
  toLinearMap := MatrixMap.of_kraus (amplitudeDampingKraus g) (amplitudeDampingKraus g)
  cp := MatrixMap.of_kraus_isCompletelyPositive (amplitudeDampingKraus g)
  TP := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving _ _
    (amplitudeDampingKraus_sum g hg0 hg1)

/-- The damping–dephasing channel `F_{p,g} = D_p ∘ A_g` of equation (5.41). -/
def dampingDephasingChannel (p g : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : CPTPMap (Fin 2) (Fin 2) :=
  CPTPMap.compose (dephasingChannel p hp0 hp1) (amplitudeDampingChannel g hg0 hg1)

/-- The `n`-fold tensor power `F_{p,g}^{⊗n}`. -/
def dampingDephasingChannelPow (p g : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (n : ℕ) : CPTPMap (Fin n → Fin 2) (Fin n → Fin 2) :=
  CPTPMap.piProd (fun _ : Fin n => dampingDephasingChannel p g hp0 hp1 hg0 hg1)

/-! ## Eigenvalue formulas of Proposition 5.1 (5.5)–(5.7) -/

/-- `y₁(w)` of equation (5.5): the eigenvalues of `N_p^{⊗n}(φₓⁿ)` on the Hamming-weight
`w` sector. -/
def prop51_y1 (x : ℝ) (p : Fin 4 → ℝ) (n w : ℕ) : ℝ :=
  x * (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w
    + (1 - x) * (p 0 + p 3) ^ w * (p 1 + p 2) ^ (n - w)

/-- `Δ(w)` of equation (5.7). -/
def prop51_delta (x : ℝ) (p : Fin 4 → ℝ) (n w : ℕ) : ℝ :=
  ((2 * x - 1) * (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w) ^ 2
    + 4 * x * (1 - x) * ((p 0 - p 3) ^ (n - w) * (p 1 - p 2) ^ w) ^ 2

/-- `y₊(w)` of equation (5.6). -/
def prop51_yPlus (x : ℝ) (p : Fin 4 → ℝ) (n w : ℕ) : ℝ :=
  ((p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w + Real.sqrt (prop51_delta x p n w)) / 2

/-- `y₋(w)` of equation (5.6). -/
def prop51_yMinus (x : ℝ) (p : Fin 4 → ℝ) (n w : ℕ) : ℝ :=
  ((p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w - Real.sqrt (prop51_delta x p n w)) / 2

/-- The discriminant `Δ(w)` of (5.7) is nonnegative for `x ∈ [0,1]`: it is a sum of
squares with a nonnegative coefficient `4x(1-x)`.  Hence the eigenvalues `y±(w)` of
(5.6) are real, as the paper presents them (see also Appendix C, eqs. (C.26)–(C.27)). -/
theorem prop51_delta_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (p : Fin 4 → ℝ) (n w : ℕ) :
    0 ≤ prop51_delta x p n w := by
  have hx1' : (0:ℝ) ≤ 1 - x := by linarith
  have h1 : (0:ℝ) ≤ ((2 * x - 1) * (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w) ^ 2 :=
    sq_nonneg _
  have h4 : (0:ℝ) ≤ 4 := by norm_num
  have hf : (0:ℝ) ≤ 4 * x * (1 - x) :=
    mul_nonneg (mul_nonneg h4 hx0) hx1'
  have h2 : (0:ℝ) ≤ 4 * x * (1 - x) * ((p 0 - p 3) ^ (n - w) * (p 1 - p 2) ^ w) ^ 2 :=
    mul_nonneg hf (sq_nonneg _)
  unfold prop51_delta
  linarith

/-- The eigenvalue pair of (5.6) sums to the sector weight
`(p0+p3)^{n-w} (p1+p2)^w`, the trace of the 2×2 block of `N_p^{⊗n}(φₓⁿ)` on the
Hamming-weight-`w` sector (Appendix C). -/
theorem prop51_yPlus_add_yMinus (x : ℝ) (p : Fin 4 → ℝ) (n w : ℕ) :
    prop51_yPlus x p n w + prop51_yMinus x p n w
      = (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w := by
  unfold prop51_yPlus prop51_yMinus
  ring

/-- Both eigenvalues `y±(w)` of (5.6) are nonnegative on the physical parameter
range `x ∈ [0,1]`, `p_k ≥ 0`: they are eigenvalues of a block of a density matrix,
so the entropy terms of (5.4) are well defined.  The proof uses
`|p0−p3| ≤ p0+p3` and `|p1−p2| ≤ p1+p2` (valid for `p_k ≥ 0`) to compare
`Δ(w)` with the square of the sector weight. -/
theorem prop51_y_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (p : Fin 4 → ℝ) (hp : ∀ k, 0 ≤ p k) (n w : ℕ) :
    0 ≤ prop51_yPlus x p n w ∧ 0 ≤ prop51_yMinus x p n w := by
  have hx1' : (0:ℝ) ≤ 1 - x := by linarith
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have hA : (0:ℝ) ≤ (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w :=
    mul_nonneg (pow_nonneg (add_nonneg h0 h3) _) (pow_nonneg (add_nonneg h1 h2) _)
  have h03 : |p 0 - p 3| ≤ p 0 + p 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have h12 : |p 1 - p 2| ≤ p 1 + p 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hBabs : |(p 0 - p 3) ^ (n - w) * (p 1 - p 2) ^ w|
      ≤ (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w := by
    rw [abs_mul, abs_pow, abs_pow]
    exact mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg _) h03 (n - w))
      (pow_le_pow_left₀ (abs_nonneg _) h12 w)
      (pow_nonneg (abs_nonneg _) w)
      (pow_nonneg (add_nonneg h0 h3) (n - w))
  obtain ⟨hBneg, hBle⟩ := abs_le.mp hBabs
  have hsq : ((p 0 - p 3) ^ (n - w) * (p 1 - p 2) ^ w) ^ 2
      ≤ ((p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w) ^ 2 :=
    sq_le_sq' hBneg hBle
  have hkey : ((p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w) ^ 2 - prop51_delta x p n w
      = 4 * x * (1 - x)
        * (((p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w) ^ 2
          - ((p 0 - p 3) ^ (n - w) * (p 1 - p 2) ^ w) ^ 2) := by
    unfold prop51_delta
    ring
  have h4nn : (0:ℝ) ≤ 4 := by norm_num
  have h4 : (0:ℝ) ≤ 4 * x * (1 - x) :=
    mul_nonneg (mul_nonneg h4nn hx0) hx1'
  have hΔle : prop51_delta x p n w
      ≤ ((p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w) ^ 2 := by
    have hpos := mul_nonneg h4 (sub_nonneg.2 hsq)
    linarith
  have hs : Real.sqrt (prop51_delta x p n w)
      ≤ (p 0 + p 3) ^ (n - w) * (p 1 + p 2) ^ w :=
    (Real.sqrt_le_left hA).mpr hΔle
  refine ⟨?_, ?_⟩
  · unfold prop51_yPlus
    exact div_nonneg (add_nonneg hA (Real.sqrt_nonneg _)) (by norm_num)
  · unfold prop51_yMinus
    exact div_nonneg (sub_nonneg.2 hs) (by norm_num)

/-- The right-hand side of (5.4). -/
def prop51_rhs (x : ℝ) (p : Fin 4 → ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sum (fun w => (n.choose w : ℝ) *
    (Real.negMulLog (prop51_y1 x p n w)
      - Real.negMulLog (prop51_yPlus x p n w)
      - Real.negMulLog (prop51_yMinus x p n w)))

/-! ## Eigenvalue formulas of Theorem 5.2 (5.45)–(5.46) -/

/-- `α = x + (1-x)(1-g)ⁿ = tr(M)` (equation (D.10), `tr M`). -/
def thm52_alpha (x g : ℝ) (n : ℕ) : ℝ :=
  x + (1 - x) * (1 - g) ^ n

/-- `β = x(1-x)[(1-g)ⁿ - ((1-2p)²(1-g))ⁿ] = det(M)` (equation (D.10), `det M`). -/
def thm52_beta (x p g : ℝ) (n : ℕ) : ℝ :=
  x * (1 - x) * ((1 - g) ^ n - ((1 - 2 * p) ^ 2 * (1 - g)) ^ n)

/-- `η₊` of equation (5.46). -/
def thm52_etaPlus (x p g : ℝ) (n : ℕ) : ℝ :=
  (thm52_alpha x g n + Real.sqrt (thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n)) / 2

/-- `η₋` of equation (5.46). -/
def thm52_etaMinus (x p g : ℝ) (n : ℕ) : ℝ :=
  (thm52_alpha x g n - Real.sqrt (thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n)) / 2

/-- Discriminant identity for the 2×2 block `M` of Appendix D: `α² − 4β` equals
`(x − (1−x)(1−g)ⁿ)² + 4x(1−x)·C²` with `C² = ((1−2p)²(1−g))ⁿ`, exactly the
radicand displayed in (D.11). -/
theorem thm52_disc_eq (x p g : ℝ) (n : ℕ) :
    thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n
      = (x - (1 - x) * (1 - g) ^ n) ^ 2
        + 4 * x * (1 - x) * ((1 - 2 * p) ^ 2 * (1 - g)) ^ n := by
  unfold thm52_alpha thm52_beta
  ring

/-- The discriminant `α² − 4β` is nonnegative on the physical parameter range
`x, g ∈ [0,1]` (for any `p`), so the eigenvalues `η±` of (5.46) are real; this is
the content of the square root in (D.11). -/
theorem thm52_disc_nonneg (x p g : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hg1 : g ≤ 1) (n : ℕ) :
    0 ≤ thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n := by
  have hx1' : (0:ℝ) ≤ 1 - x := by linarith
  have hg1' : (0:ℝ) ≤ 1 - g := by linarith
  have hd : (0:ℝ) ≤ ((1 - 2 * p) ^ 2 * (1 - g)) ^ n :=
    pow_nonneg (mul_nonneg (sq_nonneg _) hg1') n
  have h4nn : (0:ℝ) ≤ 4 := by norm_num
  have hf : (0:ℝ) ≤ 4 * x * (1 - x) :=
    mul_nonneg (mul_nonneg h4nn hx0) hx1'
  rw [thm52_disc_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg hf hd)

/-- The eigenvalue pair of (5.46) sums to the block trace `α = tr M` of (D.10). -/
theorem thm52_etaPlus_add_etaMinus (x p g : ℝ) (n : ℕ) :
    thm52_etaPlus x p g n + thm52_etaMinus x p g n = thm52_alpha x g n := by
  unfold thm52_etaPlus thm52_etaMinus
  ring

/-- The eigenvalue pair of (5.46) multiplies to the block determinant
`β = det M` of (D.10). -/
theorem thm52_etaPlus_mul_etaMinus (x p g : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hg1 : g ≤ 1) (n : ℕ) :
    thm52_etaPlus x p g n * thm52_etaMinus x p g n = thm52_beta x p g n := by
  have hd : 0 ≤ thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n :=
    thm52_disc_nonneg x p g hx0 hx1 hg1 n
  unfold thm52_etaPlus thm52_etaMinus
  have h1 : ((thm52_alpha x g n + Real.sqrt (thm52_alpha x g n ^ 2
          - 4 * thm52_beta x p g n)) / 2)
        * ((thm52_alpha x g n - Real.sqrt (thm52_alpha x g n ^ 2
          - 4 * thm52_beta x p g n)) / 2)
      = ((thm52_alpha x g n + Real.sqrt (thm52_alpha x g n ^ 2
            - 4 * thm52_beta x p g n))
          * (thm52_alpha x g n - Real.sqrt (thm52_alpha x g n ^ 2
            - 4 * thm52_beta x p g n))) / 4 := by ring
  rw [h1]
  have h2 : (thm52_alpha x g n + Real.sqrt (thm52_alpha x g n ^ 2
          - 4 * thm52_beta x p g n))
        * (thm52_alpha x g n - Real.sqrt (thm52_alpha x g n ^ 2
          - 4 * thm52_beta x p g n))
      = thm52_alpha x g n ^ 2
        - (Real.sqrt (thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n)) ^ 2 := by ring
  rw [h2, Real.sq_sqrt hd]
  ring

/-- Both eigenvalues `η±` of (5.46) are nonnegative on the physical parameter range
`x, p, g ∈ [0,1]`: `η₊` is manifestly nonnegative, and for `η₋` one uses
`β ≥ 0` (since `((1−2p)²(1−g))ⁿ ≤ (1−g)ⁿ`), which gives `α² − 4β ≤ α²` and hence
`√(α² − 4β) ≤ α`.  As eigenvalues of a block of a density matrix, `η±` must indeed
be nonnegative, so the entropy terms of (5.45) are well defined. -/
theorem thm52_eta_nonneg (x p g : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hg1 : g ≤ 1) (n : ℕ) :
    0 ≤ thm52_etaPlus x p g n ∧ 0 ≤ thm52_etaMinus x p g n := by
  have hx1' : (0:ℝ) ≤ 1 - x := by linarith
  have hg1' : (0:ℝ) ≤ 1 - g := by linarith
  have hα : (0:ℝ) ≤ thm52_alpha x g n := by
    unfold thm52_alpha
    exact add_nonneg hx0 (mul_nonneg hx1' (pow_nonneg hg1' n))
  have hsq : ((1 - 2 * p) ^ 2 * (1 - g)) ^ n ≤ (1 - g) ^ n := by
    have hle : (1 - 2 * p) ^ 2 ≤ 1 := by
      have h1 : (0:ℝ) ≤ (1 - 2 * p) + 1 := by linarith
      have h2 : (1 - 2 * p) - 1 ≤ 0 := by linarith
      have hprod : ((1 - 2 * p) + 1) * ((1 - 2 * p) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h1 h2
      have hEq : (1 - 2 * p) ^ 2 - 1 = ((1 - 2 * p) + 1) * ((1 - 2 * p) - 1) := by ring
      linarith
    have hbase : (1 - 2 * p) ^ 2 * (1 - g) ≤ 1 * (1 - g) :=
      mul_le_mul_of_nonneg_right hle hg1'
    have hd0 : (0:ℝ) ≤ (1 - 2 * p) ^ 2 * (1 - g) :=
      mul_nonneg (sq_nonneg _) hg1'
    simpa using pow_le_pow_left₀ hd0 hbase n
  have hβ : (0:ℝ) ≤ thm52_beta x p g n := by
    unfold thm52_beta
    exact mul_nonneg (mul_nonneg hx0 hx1') (sub_nonneg.2 hsq)
  have hdisc : thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n
      ≤ thm52_alpha x g n ^ 2 := by linarith
  have hsq' : Real.sqrt (thm52_alpha x g n ^ 2 - 4 * thm52_beta x p g n)
      ≤ thm52_alpha x g n :=
    (Real.sqrt_le_left hα).mpr hdisc
  refine ⟨?_, ?_⟩
  · unfold thm52_etaPlus
    exact div_nonneg (add_nonneg hα (Real.sqrt_nonneg _)) (by norm_num)
  · unfold thm52_etaMinus
    exact div_nonneg (sub_nonneg.2 hsq') (by norm_num)

/-- The right-hand side of (5.45). -/
def thm52_rhs (x p g : ℝ) (n : ℕ) : ℝ :=
  Real.negMulLog (x + (1 - x) * g ^ n)
    + Real.negMulLog ((1 - x) * (1 - g) ^ n)
    - Real.negMulLog ((1 - x) * g ^ n)
    - Real.negMulLog (thm52_etaPlus x p g n)
    - Real.negMulLog (thm52_etaMinus x p g n)

end Qatlib.Papers.PermInvariant25.MainResults.Source
