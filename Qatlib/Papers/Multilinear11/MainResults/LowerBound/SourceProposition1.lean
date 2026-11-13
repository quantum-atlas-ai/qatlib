/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 of arXiv:1105.3310v3 (Montanaro, 2012)

Paper: Ashley Montanaro, *The quantum query complexity of learning multilinear
polynomials*, arXiv:1105.3310v3 (8 Mar 2012).

Source location: Proposition 1, §1 p.2 (statement), proof p.2.

The proposition says that learning a multilinear degree-`d` polynomial over `𝔽_q` with
bounded error requires `Ω(n^{d-1})` quantum queries.  The proof is entirely
information-theoretic: with `X` the uniformly random target (`M = Σ_{i=0}^d C(n,i)`
coefficients), `Y` the algorithm's output after `r` queries, Holevo gives
`I(X:Y) ≤ 2r(n+1)log₂q` and Fano gives
`Pe ≥ 1 - (I(X:Y) + 1)/(log₂q · M)`; bounding `Pe` by a constant yields `r = Ω(n^{d-1})`.

We formalise the quantitative content of that argument.  The two cited information-theoretic
inequalities are carried as the fields of `LearnerData` (Holevo and Fano); the rest — the
algebraic deduction of the query lower bound, and its `n^{d-1}` form with an explicit
constant — is proved here.  The missing step for the paper's literal statement is
instantiating Holevo/Fano for the `𝔽_q` oracle model, which the library does not contain.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Qatlib.Papers.Multilinear11.MainResults.LowerBound

/-- `M = Σ_{i=0}^{d} C(n,i)`, the number of coefficients of a multilinear polynomial of
degree at most `d` on `n` variables.
Source: arXiv:1105.3310v3, Proposition 1 proof p.2. -/
def numCoefficients (n d : ℕ) : ℕ := ∑ i ∈ Finset.range (d + 1), n.choose i

/-- Data of a bounded-error learner after `r` queries, in the random-target setting of
Proposition 1.  `Pe` is the average error probability and `I` the mutual information between
the uniformly random target `X` and the learner's output `Y`.  The fields `holevo` and `fano`
are the two inequalities the paper quotes (arXiv:1105.3310v3, Proposition 1 proof p.2):

* Holevo: `I(X:Y) ≤ 2 r (n+1) log₂ q`;
* Fano: `Pe ≥ 1 - (I(X:Y) + 1) / (log₂ q · M)` with `M = numCoefficients n d`. -/
structure LearnerData (n d q r : ℕ) where
  /-- Average error probability of the learner. -/
  Pe : ℝ
  /-- Mutual information between the random target and the learner's output. -/
  I : ℝ
  /-- Holevo's theorem, arXiv:1105.3310v3, Proposition 1 proof p.2. -/
  holevo : I ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) * Real.logb 2 (q : ℝ)
  /-- Fano's inequality, arXiv:1105.3310v3, Proposition 1 proof p.2. -/
  fano : Pe ≥ 1 - (I + 1) / (Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ))

/-- **Quantitative core of Proposition 1** (arXiv:1105.3310v3, proof p.2).
If a learner with data `D` errs with probability at most `1/3`, then its query count `r`
satisfies
`((2/3)M - 1/log₂q) / (2(n+1)) ≤ r`
with `M = numCoefficients n d`.  This is exactly the inequality the paper derives from
Holevo + Fano before discarding constants. -/
theorem prop1_query_lower_core
    (n d q r : ℕ) (hq : 2 ≤ q) (D : LearnerData n d q r) (hPe : D.Pe ≤ 1 / 3) :
    ((2 / 3) * (numCoefficients n d : ℝ) - 1 / Real.logb 2 (q : ℝ))
        / (2 * ((n : ℝ) + 1)) ≤ (r : ℝ) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hq1
  have hL : 0 < Real.logb 2 (q : ℝ) := Real.logb_pos (b := 2) (by norm_num) hq1
  -- `M ≥ C(n,0) = 1 > 0`
  have hM1 : 1 ≤ numCoefficients n d := by
    unfold numCoefficients
    have hmem : 0 ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.succ_pos d)
    have h := Finset.single_le_sum (f := fun i => n.choose i)
      (fun i _ => Nat.zero_le _) hmem
    simpa using h
  have hM : 0 < (numCoefficients n d : ℝ) := by
    have : (1 : ℝ) ≤ (numCoefficients n d : ℝ) := by exact_mod_cast hM1
    linarith
  -- Fano + `Pe ≤ 1/3` gives `(2/3) ≤ (I+1)/(log₂q · M)`
  have hratio : (2 / 3 : ℝ) ≤ (D.I + 1) / (Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ)) := by
    have h1 : 1 - (D.I + 1) / (Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ)) ≤ 1 / 3 :=
      le_trans D.fano hPe
    linarith
  have hI : (2 / 3 : ℝ) * Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ) - 1 ≤ D.I := by
    have hle : (2 / 3 : ℝ) * (Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ)) ≤ D.I + 1 := by
      have := (le_div_iff₀ (mul_pos hL hM)).mp hratio
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    linarith
  -- slot the two inequalities together
  have hIpos : (2 / 3 : ℝ) * Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ) - 1
      ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) * Real.logb 2 (q : ℝ) := by
    linarith [hI, D.holevo]
  have hdiv : (2 / 3 : ℝ) * (numCoefficients n d : ℝ) - 1 / Real.logb 2 (q : ℝ)
      ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) := by
    have h := div_le_div_of_nonneg_right hIpos (le_of_lt hL)
    have e1 : ((2 / 3 : ℝ) * Real.logb 2 (q : ℝ) * (numCoefficients n d : ℝ) - 1)
        / Real.logb 2 (q : ℝ)
        = (2 / 3) * (numCoefficients n d : ℝ) - 1 / Real.logb 2 (q : ℝ) := by
      field_simp
    have e2 : (2 * (r : ℝ) * ((n : ℝ) + 1) * Real.logb 2 (q : ℝ)) / Real.logb 2 (q : ℝ)
        = 2 * (r : ℝ) * ((n : ℝ) + 1) := by
      field_simp
    rw [e1, e2] at h
    exact h
  have hden : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hfin := div_le_div_of_nonneg_right hdiv (le_of_lt hden)
  have e3 : (2 * (r : ℝ) * ((n : ℝ) + 1)) / (2 * ((n : ℝ) + 1)) = (r : ℝ) := by
    field_simp
  simpa [e3] using hfin

/-! ## The `n^{d-1}` form

The core inequality, together with the binomial lower bound
`C(n,d) ≥ (n+1-d)^d/d! ≥ n^d/(2^d d!)` for `n ≥ 2d`, yields an explicit `Ω(n^{d-1})`
statement.  We record it as a corollary of the core. -/

/-- **Proposition 1's `Ω(n^{d-1})` conclusion with an explicit constant**
(arXiv:1105.3310v3, Proposition 1 p.2).  For `n ≥ 2d`, `d ≥ 1` and a bounded-error learner
(`Pe ≤ 1/3`) over a field of size `q ≥ 2`,
`n^{d-1} / (3 · 2^{d+2} · d!) ≤ r`; i.e. `r = Ω(n^{d-1})`.

Handoff: the full statement is `r = Ω(n^{d-1})` for every bounded-error quantum query
algorithm; here `LearnerData` supplies the Holevo/Fano inequalities that the paper obtains
from the `𝔽_q` oracle model.  The residual gap is the model instantiation, not the
arithmetic.  The proof below combines `prop1_query_lower_core` with the binomial lower bound
`Nat.pow_le_choose` and `M ≥ C(n,0) + C(n,1) ≥ 3`. -/
theorem proposition1_lower_bound
    (n d q r : ℕ) (hd : 1 ≤ d) (hn : 2 * d ≤ n) (hq : 2 ≤ q)
    (D : LearnerData n d q r) (hPe : D.Pe ≤ 1 / 3) :
    (n : ℝ) ^ (d - 1) ≤ (3 * 2 ^ (d + 2) * (d.factorial : ℝ)) * (r : ℝ) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hLpos : 0 < Real.logb 2 (q : ℝ) := Real.logb_pos (b := 2) (by norm_num) hq1
  have hL1 : 1 ≤ Real.logb 2 (q : ℝ) := by
    have h := (Real.logb_le_logb (b := 2) (x := 2) (y := (q : ℝ)) (by norm_num)
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast (show 0 < q by omega)))
      |>.mpr (by exact_mod_cast hq)
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  -- `M ≥ 1 + n ≥ 3`
  have hmem01 : ({0, 1} : Finset ℕ) ⊆ Finset.range (d + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp
    · simp only [Finset.mem_range]; omega
  have hMn : 1 + n ≤ numCoefficients n d := by
    unfold numCoefficients
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => n.choose i) hmem01
      (by intro i _ _; exact Nat.zero_le _)
    have heq : (∑ i ∈ ({0, 1} : Finset ℕ), n.choose i) = 1 + n := by
      rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
      simp [Nat.add_comm]
    rw [heq] at hpair
    exact hpair
  have hM3 : (3 : ℝ) ≤ (numCoefficients n d : ℝ) := by
    have h3 : 3 ≤ numCoefficients n d := by
      have hn2 : 2 ≤ n := by omega
      omega
    exact_mod_cast h3
  -- binomial lower bound `C(n,d) ≥ n^d / (2^d d!)`
  have hnd : d ≤ n := by omega
  have hhalf : (n : ℝ) / 2 ≤ ((n + 1 - d : ℕ) : ℝ) := by
    have hcast : ((n + 1 - d : ℕ) : ℝ) = (n : ℝ) + 1 - (d : ℝ) := by
      have hd1 : d ≤ n + 1 := by omega
      push_cast [hd1]
      ring
    rw [hcast]
    have h2d : (2 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hchoose : (n : ℝ) ^ d / (2 ^ d * (d.factorial : ℝ)) ≤ (n.choose d : ℝ) := by
    have hpc : ((n + 1 - d : ℕ) : ℝ) ^ d / (d.factorial : ℝ) ≤ (n.choose d : ℝ) :=
      Nat.pow_le_choose (α := ℝ) d n
    have hbase : (n : ℝ) ^ d / 2 ^ d ≤ ((n + 1 - d : ℕ) : ℝ) ^ d := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2) hhalf d
      rwa [div_pow] at h
    calc (n : ℝ) ^ d / (2 ^ d * (d.factorial : ℝ))
        = ((n : ℝ) ^ d / 2 ^ d) / (d.factorial : ℝ) := by ring
      _ ≤ (((n + 1 - d : ℕ) : ℝ) ^ d) / (d.factorial : ℝ) :=
          div_le_div_of_nonneg_right hbase (by positivity)
      _ ≤ (n.choose d : ℝ) := hpc
  have hMchoose : (n.choose d : ℝ) ≤ (numCoefficients n d : ℝ) := by
    have hmem : d ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.lt_succ_self d)
    have h := Finset.single_le_sum (f := fun i => n.choose i)
      (fun i _ => Nat.zero_le _) hmem
    exact_mod_cast h
  have hMlower : (n : ℝ) ^ d / (2 ^ d * (d.factorial : ℝ)) ≤ (numCoefficients n d : ℝ) :=
    hchoose.trans hMchoose
  -- combine with the core inequality
  have hcore := prop1_query_lower_core n d q r hq D hPe
  have hInv : 1 / Real.logb 2 (q : ℝ) ≤ 1 := (div_le_one hLpos).mpr hL1
  have hnum : (1 / 3) * (numCoefficients n d : ℝ)
      ≤ (2 / 3) * (numCoefficients n d : ℝ) - 1 / Real.logb 2 (q : ℝ) := by
    linarith
  -- `(2/3)M - 1/log₂q` is at most `2(n+1)r`, and at least `(1/3)M`
  have hdiv : (2 / 3) * (numCoefficients n d : ℝ) - 1 / Real.logb 2 (q : ℝ)
      ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mp hcore
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h1 : (1 / 3) * (numCoefficients n d : ℝ) ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) :=
    hnum.trans hdiv
  have h2 : (1 / 3) * ((n : ℝ) ^ d / (2 ^ d * (d.factorial : ℝ)))
      ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) := by
    have hM' := mul_le_mul_of_nonneg_left hMlower (by norm_num : (0 : ℝ) ≤ 1 / 3)
    exact hM'.trans h1
  -- multiply up by `3 · 2^d · d!`
  have h3 : (n : ℝ) ^ d ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) * (3 * 2 ^ d * (d.factorial : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 3 * 2 ^ d * (d.factorial : ℝ))
    have e : (1 / 3) * ((n : ℝ) ^ d / (2 ^ d * (d.factorial : ℝ)))
        * (3 * 2 ^ d * (d.factorial : ℝ)) = (n : ℝ) ^ d := by
      field_simp
    rwa [e] at hm
  -- `n^d = n^{d-1} · n`, and `n ≥ (n+1)/2`
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) ^ d = (n : ℝ) ^ (d - 1) * (n : ℝ) := by
    have h1' : d - 1 + 1 = d := by omega
    conv_lhs => rw [← h1']
    rw [pow_succ]
  have hnp1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have h4 : (n : ℝ) ^ (d - 1) * (n : ℝ)
      ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) * (3 * 2 ^ d * (d.factorial : ℝ)) := by
    rwa [← hpow]
  have hnge : ((n : ℝ) + 1) / 2 ≤ (n : ℝ) := by linarith
  have h5 : (n : ℝ) ^ (d - 1) * (((n : ℝ) + 1) / 2) ≤ (n : ℝ) ^ (d - 1) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnge (by positivity)
  have h6 : (n : ℝ) ^ (d - 1) * (((n : ℝ) + 1) / 2)
      ≤ 2 * (r : ℝ) * ((n : ℝ) + 1) * (3 * 2 ^ d * (d.factorial : ℝ)) := h5.trans h4
  have h7 : (n : ℝ) ^ (d - 1)
      ≤ (2 * (r : ℝ) * ((n : ℝ) + 1) * (3 * 2 ^ d * (d.factorial : ℝ)))
          / (((n : ℝ) + 1) / 2) := (le_div_iff₀ (by positivity)).mpr h6
  have h8 : (2 * (r : ℝ) * ((n : ℝ) + 1) * (3 * 2 ^ d * (d.factorial : ℝ)))
        / (((n : ℝ) + 1) / 2)
      = (3 * 2 ^ (d + 2) * (d.factorial : ℝ)) * (r : ℝ) := by
    have hp2 : (2 : ℝ) ^ (d + 2) = 4 * 2 ^ d := by rw [pow_add]; norm_num; ring
    rw [hp2]
    field_simp
    ring
  rwa [h8] at h7

end Qatlib.Papers.Multilinear11.MainResults.LowerBound
