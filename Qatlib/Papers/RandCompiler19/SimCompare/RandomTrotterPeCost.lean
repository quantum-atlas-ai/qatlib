/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Qatlib.Papers.RandCompiler19.PhaseCosts.QdriftPhaseCost

/-!
# Second-order random Trotter phase-estimation cost (source Appendix E.3)

Fixed source: E. Campbell, *A random compiler for fast Hamiltonian simulation*,
arXiv:1811.08017v2 (PDF SHA256 `291fcf6f1c4fb2c487026c6c124a936a03fdc48b85d3ff9738b48a786f891b9f`),
Appendix E.3, Eqs. `(E15)`–`(E21)`.

The source uses the very same phase-estimation chain as Appendix E.2, but pays
every query with the second-order random Trotter count of `(C11)` instead of the
qDRIFT count, and with the renormalised strength `Λ_A = Λ/(2λ)` of `(E16)`:

* `E15`/`E17` — query `j` needs `N(j) = 2·4L²(2Λ_A³t_j³/ε_j)^{1/2}`, and with
  `t_j = π2^j` this is `8L²(2π³Λ_A³8^j/ε_j)^{1/2}`;
* `E18` — the error shares are again proportional to `2^j`, so the very same
  `peShare` allocation of Appendix E.2 applies;
* `E19`/`E20` — summing the shares gives the exact total
  `32L²π^{3/2}Λ_A^{3/2}X^{3/2}/√ε_tot` with `X = 2^m−1`, whence
  `N ≤ 32L²π^{3/2}Λ_A^{3/2}(2^m)^{3/2}/√ε_tot`.

`(E21)`–`(E28)` — substituting `2^m = λ(1+p_f)/(2δ_E p_f)` and minimising over
`p_f` — is formalised below: `trotterYBracket` is the source's exact `Y(p_f)`,
`trotterChainGates_le_Y` bounds the gate count by `√(Y)` for every admissible
`p_f`, `trotterY_sqrt_at_three_quarters` evaluates the optimum at
`p_f = 3P_f/4`, and `trotterGates_E28` yields the `L²Λ^{3/2}/δ_E^{3/2}P_f²`
scaling of `(E28)`.  Note on the source's arithmetic: `E20` prints `2^{m+1}`
where its own `E19` gives `2^{m+2}`, so the printed constant `69` of `(E28)` is a
factor `√2` below the self-consistent chain `97` (see `trotterE20_power_slip`,
`trotterConstant_selfconsistent`, and `trotterConstant_E28`, which recovers the
printed `69 ≈ 64π^{3/2}/(3√3)` exactly).
-/

namespace Qatlib.Papers.RandCompiler19.SimCompare.RandomTrotterPeCost

set_option autoImplicit false

open Finset

open Qatlib.Papers.RandCompiler19.PhaseCosts.QdriftPhaseCost
  (peShare peShare_sum sum_range_pow_two sum_range_pow_two_succ pePowerScale one_lt_pow_two
    two_mul_pow_sub_one_pos)

/-! ## `E15`/`E17`: the per-query count -/

/-- Source `E15`/`E17`: the second-order random Trotter count of
phase-estimation query `j` at error share `eps`, with `t_j = π2^j` already
substituted, so that `N(j) = 8L²(2π³Λ_A³8^j/ε_j)^{1/2}`. -/
noncomputable def trotterQueryGates (L : ℕ) (lamA : ℝ) (j : ℕ) (eps : ℝ) : ℝ :=
  8 * (L : ℝ) ^ 2 * Real.sqrt (2 * lamA ^ 3 * Real.pi ^ 3 * (8 : ℝ) ^ j / eps)

/-- Source `E15` in its stated form `2·4L²(2Λ_A³t_j³/ε_j)^{1/2}` with `t_j = π2^j`;
the leading `2` is again Fig. 3's double rotation. -/
theorem trotterQueryGates_eq_source (L : ℕ) (lamA : ℝ) (j : ℕ) (eps : ℝ) :
    trotterQueryGates L lamA j eps =
      2 * (4 * (L : ℝ) ^ 2 *
        Real.sqrt (2 * lamA ^ 3 * (Real.pi * (2 : ℝ) ^ j) ^ 3 / eps)) := by
  have h8 : (8 : ℝ) ^ j = (2 : ℝ) ^ (3 * j) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_mul]
  have hp : ((2 : ℝ) ^ j) ^ 3 = (2 : ℝ) ^ (3 * j) := by
    rw [← pow_mul, Nat.mul_comm j 3]
  have hcube : (Real.pi * (2 : ℝ) ^ j) ^ 3 = Real.pi ^ 3 * (8 : ℝ) ^ j := by
    rw [mul_pow, hp, h8]
  unfold trotterQueryGates
  rw [hcube]
  ring_nf

/-! ## `E18`: the source's proportional shares applied to a query -/

/-- Source `E18`: at the proportional share `ε_j = ε_tot·2^j/(2(2^m−1))` the
`j`-th query costs `8L²·2^j·√(4Λ_A³π³(2^m−1)/ε_tot)`, the square root being the
same for every query of the chain. -/
theorem trotterQueryGates_at_share {m : ℕ} (hm : 1 ≤ m) {L : ℕ} {lamA E : ℝ}
    (hE : 0 < E) {j : ℕ} (hj : 1 ≤ j) :
    trotterQueryGates L lamA j (peShare m E (j - 1)) =
      8 * (L : ℝ) ^ 2 * (2 : ℝ) ^ j *
        Real.sqrt (4 * lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E) := by
  have hX : (0 : ℝ) < 2 * ((2 : ℝ) ^ m - 1) := two_mul_pow_sub_one_pos hm
  have hε : peShare m E (j - 1) = E * (2 : ℝ) ^ j / (2 * ((2 : ℝ) ^ m - 1)) := by
    unfold peShare
    rw [show j - 1 + 1 = j by omega]
  have h4 : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
    have h1 : (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * j) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
    have h2 : ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (2 * j) := by
      rw [← pow_mul, Nat.mul_comm j 2]
    rw [h1, h2]
  have h8 : (8 : ℝ) ^ j = (2 : ℝ) ^ j * (4 : ℝ) ^ j := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
  have h2j : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hE' : E ≠ 0 := ne_of_gt hE
  have hX' : (2 * ((2 : ℝ) ^ m - 1)) ≠ 0 := ne_of_gt hX
  have hkey : 2 * lamA ^ 3 * Real.pi ^ 3 * (8 : ℝ) ^ j /
        (E * (2 : ℝ) ^ j / (2 * ((2 : ℝ) ^ m - 1)))
      = ((2 : ℝ) ^ j) ^ 2 *
          (4 * lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E) := by
    rw [h8, h4]
    field_simp
    ring
  unfold trotterQueryGates
  rw [hε, hkey, Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ j)),
    Real.sqrt_sq (pow_nonneg (by norm_num) j)]
  ring

/-! ## `E19`/`E20`: the exact total of the chain -/

/-- Source `E19`/`E20`: at the proportional allocation the whole chain costs
`32L²π^{3/2}Λ_A^{3/2}(2^m−1)^{3/2}/√ε_tot`. -/
theorem trotterChainGates_at_share {m : ℕ} (hm : 1 ≤ m) {L : ℕ} {lamA E : ℝ}
    (hlamA : 0 ≤ lamA) (hE : 0 < E) :
    ∑ k ∈ range m, trotterQueryGates L lamA (k + 1) (peShare m E k) =
      32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) *
        ((2 : ℝ) ^ m - 1) * Real.sqrt ((2 : ℝ) ^ m - 1) / Real.sqrt E := by
  have hX : (0 : ℝ) < 2 * ((2 : ℝ) ^ m - 1) := two_mul_pow_sub_one_pos hm
  have hX0 : (0 : ℝ) < (2 : ℝ) ^ m - 1 := by linarith
  have hΛ : Real.sqrt (lamA ^ 3) = lamA * Real.sqrt lamA := by
    rw [show lamA ^ 3 = lamA ^ 2 * lamA by ring, Real.sqrt_mul (sq_nonneg lamA),
      Real.sqrt_sq hlamA]
  have hπ : Real.sqrt (Real.pi ^ 3) = Real.pi * Real.sqrt Real.pi := by
    rw [show Real.pi ^ 3 = Real.pi ^ 2 * Real.pi by ring,
      Real.sqrt_mul (sq_nonneg Real.pi), Real.sqrt_sq Real.pi_pos.le]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt : Real.sqrt (4 * lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E)
      = 2 * (lamA * Real.sqrt lamA) * (Real.pi * Real.sqrt Real.pi) *
          Real.sqrt ((2 : ℝ) ^ m - 1) / Real.sqrt E := by
    rw [show 4 * lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E
          = 4 * (lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E
          = lamA ^ 3 * (Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E) by ring,
      Real.sqrt_mul (pow_nonneg hlamA 3),
      show Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E
          = Real.pi ^ 3 * (((2 : ℝ) ^ m - 1) / E) by ring,
      Real.sqrt_mul (pow_nonneg Real.pi_pos.le 3),
      Real.sqrt_div (by positivity) E,
      h4, hΛ, hπ]
    ring
  have hterm : ∀ k ∈ range m,
      trotterQueryGates L lamA (k + 1) (peShare m E k)
        = (8 * (L : ℝ) ^ 2 *
            Real.sqrt (4 * lamA ^ 3 * Real.pi ^ 3 * ((2 : ℝ) ^ m - 1) / E)) *
            (2 : ℝ) ^ (k + 1) := by
    intro k _
    have h := trotterQueryGates_at_share (L := L) (lamA := lamA) (E := E) hm hE
      (j := k + 1) (by omega)
    rw [show k + 1 - 1 = k by omega] at h
    rw [h]
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_range_pow_two_succ, hsqrt]
  ring

/-! ## `E21`: the pre-substitution bound -/

/-- Source `E19`–`E21`: replacing `2^m−1` by `2^m` (valid because `m ≥ 1`) turns
the exact total into `N ≤ 32L²π^{3/2}Λ_A^{3/2}(2^m)^{3/2}/√ε_tot`. -/
theorem trotterChainGates_le_power {m : ℕ} (hm : 1 ≤ m) {L : ℕ} {lamA E : ℝ}
    (hlamA : 0 ≤ lamA) (hE : 0 < E) :
    ∑ k ∈ range m, trotterQueryGates L lamA (k + 1) (peShare m E k) ≤
      32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) *
        (2 : ℝ) ^ m * Real.sqrt ((2 : ℝ) ^ m) / Real.sqrt E := by
  have hX0 : (0 : ℝ) < (2 : ℝ) ^ m - 1 := by
    have := one_lt_pow_two hm
    linarith
  have hP : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  have hXle : (2 : ℝ) ^ m - 1 ≤ (2 : ℝ) ^ m := by linarith
  have hsqrtle : Real.sqrt ((2 : ℝ) ^ m - 1) ≤ Real.sqrt ((2 : ℝ) ^ m) :=
    Real.sqrt_le_sqrt hXle
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ m - 1 := hX0.le
  have hnn2 : (0 : ℝ) ≤ 32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) *
      (lamA * Real.sqrt lamA) / Real.sqrt E := by
    have h1 : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt lamA := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) < Real.sqrt E := Real.sqrt_pos.2 hE
    positivity
  refine (le_of_eq (trotterChainGates_at_share hm hlamA hE)).trans ?_
  have hstep : ((2 : ℝ) ^ m - 1) * Real.sqrt ((2 : ℝ) ^ m - 1)
      ≤ (2 : ℝ) ^ m * Real.sqrt ((2 : ℝ) ^ m) := by
    refine mul_le_mul hXle hsqrtle (Real.sqrt_nonneg _) hP.le
  calc 32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) *
        ((2 : ℝ) ^ m - 1) * Real.sqrt ((2 : ℝ) ^ m - 1) / Real.sqrt E
      = (32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) /
          Real.sqrt E) * (((2 : ℝ) ^ m - 1) * Real.sqrt ((2 : ℝ) ^ m - 1)) := by
        ring
    _ ≤ (32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) /
          Real.sqrt E) * ((2 : ℝ) ^ m * Real.sqrt ((2 : ℝ) ^ m)) :=
        mul_le_mul_of_nonneg_left hstep hnn2
    _ = 32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) *
          (2 : ℝ) ^ m * Real.sqrt ((2 : ℝ) ^ m) / Real.sqrt E := by ring

/-! ## The arithmetic slip between `E19` and `E20` -/

/-- The source's `E20` carries the factor `(2^{m+1}π³Λ_A³/ε_tot)^{1/2}` where its
own `E19` gives `(2^{m+2}π³Λ_A³/ε_tot)^{1/2}`; the two differ by exactly `√2`, which
is why the printed constant `69` of `(E28)` is `√2` below the self-consistent
chain of `E19`–`E27`. -/
theorem trotterE20_power_slip (m : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (m + 2)) = Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ (m + 1)) := by
  rw [show (2 : ℝ) ^ (m + 2) = 2 * (2 : ℝ) ^ (m + 1) by rw [pow_succ]; ring]
  exact Real.sqrt_mul (by norm_num) _

/-! ## `E21`–`E24`: substituting the depth scale and the bracket `Y` -/

/-- `(a·√a)² = a³` for `a ≥ 0`: the square form of the `3/2` powers of `E21`. -/
theorem sq_mul_sqrt_self {a : ℝ} (ha : 0 ≤ a) : (a * Real.sqrt a) ^ 2 = a ^ 3 := by
  rw [mul_pow, Real.sq_sqrt ha]
  ring

/-- Source `E24`: the bracket `Y = (1+p_f)/(p_f·ε_tot^{1/3})`, with `E4`'s
`ε_tot = (P_f−p_f)/2` already substituted.  The `3/2` power of `E23`/`E25` is
recorded as `Y³` so that only a square root is needed. -/
noncomputable def trotterYBracket (pf Pf : ℝ) : ℝ :=
  2 * (1 + pf) ^ 3 / (pf ^ 3 * (Pf - pf))

/-- The `E24` bracket is positive on `0 < p_f < P_f`. -/
theorem trotterYBracket_pos {pf Pf : ℝ} (hpf : 0 < pf) (hlt : pf < Pf) :
    0 < trotterYBracket pf Pf := by
  unfold trotterYBracket
  have h1 : (0 : ℝ) < 1 + pf := by linarith
  have h2 : (0 : ℝ) < Pf - pf := by linarith
  positivity

/-- Source `E25`: at the source's small-`P_f` fraction `p_f = (3/4)P_f` the
bracket is exactly `Y³ = 512(1+3P_f/4)³/(27P_f⁴)`. -/
theorem trotterYBracket_at_three_quarters {Pf : ℝ} (hPf : 0 < Pf) :
    trotterYBracket (3 * Pf / 4) Pf = 512 * (1 + 3 * Pf / 4) ^ 3 / (27 * Pf ^ 4) := by
  have h1 : (3 * Pf / 4 : ℝ) ≠ 0 := by positivity
  have h2 : (Pf : ℝ) ≠ 0 := ne_of_gt hPf
  have h3 : (Pf - 3 * Pf / 4 : ℝ) ≠ 0 := by
    have : Pf - 3 * Pf / 4 = Pf / 4 := by ring
    rw [this]; positivity
  unfold trotterYBracket
  rw [show Pf - 3 * Pf / 4 = Pf / 4 by ring]
  field_simp
  ring

/-- Source `E25`: the leading coefficient `√(512/27)` of `Y^{3/2}` at
`p_f = (3/4)P_f` is `4.3546…`, the source's `4.35`. -/
theorem trotterY_leading_three_sigfigs :
    (4.35 : ℝ) < Real.sqrt (512 / 27) ∧ Real.sqrt (512 / 27) < 4.36 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

/-- The reduction behind `E23`: after substituting `E10`'s depth scale the
`3/2`-power bookkeeping collapses.  With `X = pePowerScale λ δ_E p_f` and
`ε_tot = (P_f−p_f)/2`, the quantity `4λ_A^{3/2}X^{3/2}/√ε_tot` of `E20` equals
`√2·(λλ_A)^{3/2}Y^{3/2}/δ_E^{3/2}`, which is exactly the statement that
`8√2` is the self-consistent coefficient of `E23`. -/
theorem four_mul_L_Y {lam lamA deltaE Pf pf : ℝ}
    (hlam : 0 < lam) (hlamA : 0 ≤ lamA) (hdelta : 0 < deltaE)
    (hpf : 0 < pf) (hlt : pf < Pf) :
    4 * (lamA * Real.sqrt lamA) * pePowerScale lam deltaE pf *
        Real.sqrt (pePowerScale lam deltaE pf) / Real.sqrt ((Pf - pf) / 2)
      ≤ Real.sqrt 2 * ((lam * lamA) * Real.sqrt (lam * lamA)) /
          (deltaE * Real.sqrt deltaE) * Real.sqrt (trotterYBracket pf Pf) := by
  have hX0 : (0 : ℝ) ≤ pePowerScale lam deltaE pf := by
    unfold pePowerScale
    have : (0 : ℝ) < 1 + pf := by linarith
    positivity
  have hE0 : (0 : ℝ) < (Pf - pf) / 2 := by linarith
  have hY0 : (0 : ℝ) ≤ trotterYBracket pf Pf := (trotterYBracket_pos hpf hlt).le
  have hRHS0 : (0 : ℝ) ≤ Real.sqrt 2 * ((lam * lamA) * Real.sqrt (lam * lamA)) /
      (deltaE * Real.sqrt deltaE) * Real.sqrt (trotterYBracket pf Pf) := by
    have h1 : (0 : ℝ) ≤ lam * lamA := mul_nonneg hlam.le hlamA
    have h2 : (0 : ℝ) ≤ deltaE * Real.sqrt deltaE := by positivity
    have h3 : (0 : ℝ) ≤ (lam * lamA) * Real.sqrt (lam * lamA) :=
      mul_nonneg h1 (Real.sqrt_nonneg _)
    positivity
  have hAsq : (4 * (lamA * Real.sqrt lamA) * pePowerScale lam deltaE pf *
        Real.sqrt (pePowerScale lam deltaE pf) / Real.sqrt ((Pf - pf) / 2)) ^ 2
      = 2 * (lam * lamA) ^ 3 * trotterYBracket pf Pf / deltaE ^ 3 := by
    have h1 : Real.sqrt lamA ^ 2 = lamA := Real.sq_sqrt hlamA
    have h2 : Real.sqrt (pePowerScale lam deltaE pf) ^ 2 = pePowerScale lam deltaE pf :=
      Real.sq_sqrt hX0
    have h3 : Real.sqrt ((Pf - pf) / 2) ^ 2 = (Pf - pf) / 2 := Real.sq_sqrt hE0.le
    rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, h1, h2, h3]
    unfold pePowerScale trotterYBracket
    have hp : pf ≠ 0 := ne_of_gt hpf
    have hd : deltaE ≠ 0 := ne_of_gt hdelta
    have hl : lam ≠ 0 := ne_of_gt hlam
    have hPp : Pf - pf ≠ 0 := by linarith
    field_simp
    ring
  have hle : 4 * (lamA * Real.sqrt lamA) * pePowerScale lam deltaE pf *
        Real.sqrt (pePowerScale lam deltaE pf) / Real.sqrt ((Pf - pf) / 2)
      ≤ Real.sqrt (2 * (lam * lamA) ^ 3 * trotterYBracket pf Pf / deltaE ^ 3) :=
    Real.le_sqrt_of_sq_le (le_of_eq hAsq)
  refine hle.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) hRHS0]
  have h1 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt deltaE ^ 2 = deltaE := Real.sq_sqrt hdelta.le
  have h3 : Real.sqrt (trotterYBracket pf Pf) ^ 2 = trotterYBracket pf Pf :=
    Real.sq_sqrt hY0
  have hll : (0 : ℝ) ≤ lam * lamA := mul_nonneg hlam.le hlamA
  have h4 : Real.sqrt (lam * lamA) ^ 2 = lam * lamA := Real.sq_sqrt hll
  rw [show (Real.sqrt 2 * ((lam * lamA) * Real.sqrt (lam * lamA)) /
        (deltaE * Real.sqrt deltaE) * Real.sqrt (trotterYBracket pf Pf)) ^ 2
      = (Real.sqrt 2) ^ 2 * ((lam * lamA) * Real.sqrt (lam * lamA)) ^ 2 *
        (Real.sqrt (trotterYBracket pf Pf)) ^ 2 / (deltaE * Real.sqrt deltaE) ^ 2 by ring,
    h1, h3,
    show ((lam * lamA) * Real.sqrt (lam * lamA)) ^ 2 = (lam * lamA) ^ 3 from
      sq_mul_sqrt_self hll,
    show (deltaE * Real.sqrt deltaE) ^ 2 = deltaE ^ 3 from sq_mul_sqrt_self hdelta.le]

/-! ## `E23`: the chain total after substituting `E10` -/

/-- Source `E23`: substituting the depth scale `2^m = λ(1+p_f)/(2δ_Ep_f)` of
`E10` and `E4`'s `ε_tot = (P_f−p_f)/2` into the second-order random Trotter
chain of `E20` gives, with the bracket `Y` of `E24`,

`N ≤ 8√2·L²·π^{3/2}·(λλ_A)^{3/2}·Y^{3/2}/δ_E^{3/2}`.

The coefficient `8√2` is self-consistent: the source's `E20` prints `2^{m+1}`
where its own `E19` gives `2^{m+2}`, the `√2` of `trotterE20_power_slip`. -/
theorem trotterChainGates_le_Y {m : ℕ} (hm : 1 ≤ m) {L : ℕ}
    {lam lamA deltaE Pf pf : ℝ}
    (hlam : 0 < lam) (hlamA : 0 ≤ lamA) (hdelta : 0 < deltaE)
    (hpf : 0 < pf) (hlt : pf < Pf)
    (hpow : (2 : ℝ) ^ m = pePowerScale lam deltaE pf) :
    ∑ k ∈ range m, trotterQueryGates L lamA (k + 1) (peShare m ((Pf - pf) / 2) k) ≤
      8 * Real.sqrt 2 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) *
        ((lam * lamA) * Real.sqrt (lam * lamA)) / (deltaE * Real.sqrt deltaE) *
          Real.sqrt (trotterYBracket pf Pf) := by
  have hE : (0 : ℝ) < (Pf - pf) / 2 := by linarith
  have hfac : (0 : ℝ) ≤ 8 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) := by positivity
  refine (trotterChainGates_le_power hm hlamA hE).trans ?_
  rw [hpow]
  calc 32 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) * (lamA * Real.sqrt lamA) *
        pePowerScale lam deltaE pf * Real.sqrt (pePowerScale lam deltaE pf) /
          Real.sqrt ((Pf - pf) / 2)
      = (8 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi)) *
          (4 * (lamA * Real.sqrt lamA) * pePowerScale lam deltaE pf *
            Real.sqrt (pePowerScale lam deltaE pf) / Real.sqrt ((Pf - pf) / 2)) := by ring
    _ ≤ (8 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi)) *
          (Real.sqrt 2 * ((lam * lamA) * Real.sqrt (lam * lamA)) /
            (deltaE * Real.sqrt deltaE) * Real.sqrt (trotterYBracket pf Pf)) :=
        mul_le_mul_of_nonneg_left (four_mul_L_Y hlam hlamA hdelta hpf hlt) hfac
    _ = 8 * Real.sqrt 2 * (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) *
          ((lam * lamA) * Real.sqrt (lam * lamA)) / (deltaE * Real.sqrt deltaE) *
            Real.sqrt (trotterYBracket pf Pf) := by ring

/-! ## `E25`–`E27`: the value at `p_f = (3/4)P_f` -/

/-- Source `E25`: at `p_f = (3/4)P_f` the bracket square root is
`√(512/27)·(1+3P_f/4)^{3/2}/P_f²`, i.e. `Y^{3/2} = √(512/27)(1+3P_f/4)^{3/2}/P_f²`. -/
theorem trotterY_sqrt_at_three_quarters {Pf : ℝ} (hPf : 0 < Pf) :
    Real.sqrt (trotterYBracket (3 * Pf / 4) Pf) =
      Real.sqrt (512 / 27) * ((1 + 3 * Pf / 4) * Real.sqrt (1 + 3 * Pf / 4)) / Pf ^ 2 := by
  have h1 : (0 : ℝ) < 1 + 3 * Pf / 4 := by linarith
  have hB : (0 : ℝ) ≤ trotterYBracket (3 * Pf / 4) Pf :=
    (trotterYBracket_pos (by linarith) (by linarith)).le
  have hRHS0 : (0 : ℝ) ≤ Real.sqrt (512 / 27) *
      ((1 + 3 * Pf / 4) * Real.sqrt (1 + 3 * Pf / 4)) / Pf ^ 2 := by positivity
  rw [Real.sqrt_eq_iff_eq_sq hB hRHS0, trotterYBracket_at_three_quarters hPf]
  have hs : Real.sqrt (512 / 27) ^ 2 = 512 / 27 := Real.sq_sqrt (by norm_num)
  rw [div_pow, mul_pow, mul_pow, hs, Real.sq_sqrt h1.le]
  have hP : (Pf : ℝ) ≠ 0 := ne_of_gt hPf
  field_simp

/-- Source `E25`–`E27`: with `E16`'s `λΛ_A = Λ/2` the chain total of `E23` at
`p_f = (3/4)P_f` is the source's shape

`N ≤ 4√(512/27)·(1+3P_f/4)^{3/2}·L²·π^{3/2}·Λ^{3/2}/(δ_E^{3/2}P_f²)`.

For small `P_f` the constant `4√(512/27)π^{3/2}` is `97.0`, i.e. `√2` times the
source's printed `69`; see `trotterConstant_selfconsistent` and
`trotterConstant_E28`. -/
theorem trotterGates_E28 {m : ℕ} (hm : 1 ≤ m) {L : ℕ} {lam lamA deltaE Lam Pf : ℝ}
    (hlam : 0 < lam) (hlamA : 0 ≤ lamA) (hdelta : 0 < deltaE) (hPf : 0 < Pf)
    (hLA : lam * lamA = Lam / 2) (hLam : 0 ≤ Lam)
    (hpow : (2 : ℝ) ^ m = pePowerScale lam deltaE (3 * Pf / 4)) :
    ∑ k ∈ range m,
        trotterQueryGates L lamA (k + 1) (peShare m ((Pf - 3 * Pf / 4) / 2) k) ≤
      4 * Real.sqrt (512 / 27) * ((1 + 3 * Pf / 4) * Real.sqrt (1 + 3 * Pf / 4)) *
        (L : ℝ) ^ 2 * (Real.pi * Real.sqrt Real.pi) *
          (Lam * Real.sqrt Lam) / (deltaE * Real.sqrt deltaE * Pf ^ 2) := by
  have hpf : (0 : ℝ) < 3 * Pf / 4 := by linarith
  have hlt : 3 * Pf / 4 < Pf := by linarith
  refine (trotterChainGates_le_Y hm hlam hlamA hdelta hpf hlt hpow).trans (le_of_eq ?_)
  have hll : (0 : ℝ) ≤ lam * lamA := mul_nonneg hlam.le hlamA
  have hA : (lam * lamA) * Real.sqrt (lam * lamA) =
      (Lam * Real.sqrt Lam) / (2 * Real.sqrt 2) := by
    rw [hLA]
    have hs : Real.sqrt (Lam / 2) = Real.sqrt Lam / Real.sqrt 2 := Real.sqrt_div hLam 2
    rw [hs]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have h2' : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  have hB : Real.sqrt (trotterYBracket (3 * Pf / 4) Pf) =
      Real.sqrt (512 / 27) * ((1 + 3 * Pf / 4) * Real.sqrt (1 + 3 * Pf / 4)) / Pf ^ 2 :=
    trotterY_sqrt_at_three_quarters hPf
  rw [hA, hB]
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have hP : (Pf : ℝ) ≠ 0 := ne_of_gt hPf
  field_simp
  ring

/-! ## `E28`: the constant `69` and the self-consistent `97` -/

/-- Source `E26`–`E28`: the printed constant of the second-order random Trotter
chain is `8·√(512/27)·π^{3/2}/2^{3/2} = 64·π^{3/2}/(3√3) = 68.58…`, which rounds
to the source's `69`. -/
theorem trotterConstant_E28 :
    68 < 64 * (Real.pi * Real.sqrt Real.pi) / (3 * Real.sqrt 3) ∧
      64 * (Real.pi * Real.sqrt Real.pi) / (3 * Real.sqrt 3) < 69 := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hspi_lo : (1.77245 : ℝ) < Real.sqrt Real.pi := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hspi_hi : Real.sqrt Real.pi < 1.77246 := by
    rw [Real.sqrt_lt Real.pi_pos.le (by norm_num)]
    nlinarith
  have hsq3_lo : (1.7320 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsq3_hi : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hPlo : (5.5682 : ℝ) < Real.pi * Real.sqrt Real.pi := by
    nlinarith [hpi_lo, hspi_lo]
  have hPhi : Real.pi * Real.sqrt Real.pi < 5.5684 := by
    nlinarith [hpi_hi, hspi_hi]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [hPlo, hsq3_hi]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [hPhi, hsq3_lo]

/-- The self-consistent constant of `E23`/`E25`: `4√(512/27)π^{3/2} = 97.0…`,
which is `√2` times the printed `69` of `E28` because the source's `E20` drops a
factor `2` in the exponent (`trotterE20_power_slip`). -/
theorem trotterConstant_selfconsistent :
    96 < 4 * Real.sqrt (512 / 27) * (Real.pi * Real.sqrt Real.pi) ∧
      4 * Real.sqrt (512 / 27) * (Real.pi * Real.sqrt Real.pi) < 98 := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hspi_lo : (1.77245 : ℝ) < Real.sqrt Real.pi := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hspi_hi : Real.sqrt Real.pi < 1.77246 := by
    rw [Real.sqrt_lt Real.pi_pos.le (by norm_num)]
    nlinarith
  have hs_lo : (4.354 : ℝ) < Real.sqrt (512 / 27) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs_hi : Real.sqrt (512 / 27) < 4.356 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hPlo : (5.5682 : ℝ) < Real.pi * Real.sqrt Real.pi := by
    nlinarith [hpi_lo, hspi_lo]
  have hPhi : Real.pi * Real.sqrt Real.pi < 5.5684 := by
    nlinarith [hpi_hi, hspi_hi]
  constructor
  · nlinarith [hPlo, hs_lo]
  · nlinarith [hPhi, hs_hi]

/-- The printed `69` of `E28` is `√2` below the self-consistent constant
`4√(512/27)π^{3/2}` of `E23`, exactly the slip `trotterE20_power_slip` identifies
between `E19`'s `2^{m+2}` and `E20`'s `2^{m+1}`. -/
theorem trotterConstant_ratio :
    4 * Real.sqrt (512 / 27) * (Real.pi * Real.sqrt Real.pi) =
      Real.sqrt 2 * (8 * Real.sqrt (512 / 27) * (Real.pi * Real.sqrt Real.pi) /
        (2 * Real.sqrt 2)) := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

end Qatlib.Papers.RandCompiler19.SimCompare.RandomTrotterPeCost
