/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AlgGeomCode25.MainResults.HopiInstanceParameters
import Qatlib.Papers.AlgGeomCode25.MainResults.HopiSemicircle

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1: DQI performance for HOPI

Source: `arXiv:2510.06603v1`, Andi Gu and Stephen P. Jordan, "Algebraic Geometry
Codes and Decoded Quantum Interferometry", Section 4 (page 11), Theorem 1, Eq. (8).

The paper's proof route is:

1. HOPI is a `max-LINSAT` instance over `𝔽_{q^2}` with `n = q^3` constraints, constraint
   sets of size `r` and alphabet size `q^2` (Section 4, page 10).
2. The dual of the Hermitian code is again a Hermitian code, so the relevant decoder is
   a decoder of the dual code up to `ℓ = ⌊(d^⊥ - 1)/2⌋` errors, with the Hermitian
   guarantee `d^⊥ ≥ t + 2 - 2g`.
3. The general semicircle law of `arXiv:2408.08292v5`, Eq. (6), then "applies verbatim
   once the code family is fixed", and gives Eq. (8) with `m = n` and `p = q^2`.

Only step 3 is not reproved here: the DQI expectation itself is the imported semicircle
law, made explicit as the predicate `SemicircleLaw`. What this module proves is that
the law instantiates to exactly Eq. (8) with the HOPI parameters, and the consequences
the paper draws from the formula: the expected satisfaction fraction lies between the
random baseline `r/q^2` and `1`, it reaches `1` exactly when `ℓ/n + r/q^2 ≥ 1`, and a
decoder radius justified by the dual-distance guarantee `d^⊥ ≥ t + 2 - 2g` gives at
least the corresponding closed-form value. The HOPI problem, Hermitian codes and their
decoders are not formalized.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AlgGeomCode25.MainResults

/-- `ℓ/n`: the fraction of the `n` constraints addressed by the decoder radius. -/
def decodingFraction (n ℓ : ℕ) : ℝ := (ℓ : ℝ) / (n : ℝ)

/-- `r/q^2`: the fraction of the alphabet `𝔽_{q^2}` taken by a constraint set. -/
def setFraction (q r : ℕ) : ℝ := (r : ℝ) / ((q : ℝ) ^ 2)

/-- The expected satisfaction fraction `⟨s⟩_DQI/n` of Theorem 1, Eq. (8), as a function
of the HOPI instance parameters. -/
def hopiExpectedSatisfactionFraction (n q r ℓ : ℕ) : ℝ :=
  hopiSatisfactionFraction (decodingFraction n ℓ) (setFraction q r)

/-- The general semicircle law of `arXiv:2408.08292v5`, Eq. (6), for a `max-LINSAT`
instance with `m` constraints over an alphabet of size `p`, constraint sets of size `r`
and a decoder of the dual code that corrects `ℓ` errors: the expected satisfaction
fraction is `(√((ℓ/m)(1 - r/p)) + √((r/p)(1 - ℓ/m)))^2` in the regime
`r/p ≤ 1 - ℓ/m` and `1` otherwise.

This is the imported premise of Theorem 1 of `arXiv:2510.06603v1`; the quantum
algorithm and its analysis are not reproved in this repository. -/
def SemicircleLaw (m p r ℓ : ℕ) (f : ℝ) : Prop :=
  f = hopiSatisfactionFraction ((ℓ : ℝ) / (m : ℝ)) ((r : ℝ) / (p : ℝ))

/-- Cast normalization: the alphabet size `q^2` read as a natural number is the square
of `q` read as a real number. -/
theorem cast_alphabetSize (q : ℕ) : ((q ^ 2 : ℕ) : ℝ) = (q : ℝ) ^ 2 := by
  push_cast
  ring

/-- **Theorem 1 (DQI performance for HOPI).** Let `q` be a prime power and consider an
instance of HOPI over the Hermitian curve with `n = q^3` constraints, alphabet `𝔽_{q^2}`
and constraint sets of size `r`. Let the dual Hermitian code have minimum distance
`d^⊥` and let decoding up to `ℓ = ⌊(d^⊥ - 1)/2⌋` errors be efficient. Then Decoded
Quantum Interferometry produces solutions with expected satisfaction fraction
`⟨s⟩_DQI/n = (√((ℓ/n)(1 - r/q^2)) + √((r/q^2)(1 - ℓ/n)))^2` if `r/q^2 ≤ 1 - ℓ/n`, and
`1` otherwise.

The DQI expectation is the semicircle law hypothesis `SemicircleLaw`; the content of
this theorem is that the law, applied with `m = q^3` and `p = q^2`, yields exactly the
closed form of Eq. (8) in the HOPI parameters. -/
theorem hopi_expected_satisfaction_fraction {q r ℓ : ℕ} {f : ℝ}
    (law : SemicircleLaw (blockLength q) (q ^ 2) r ℓ f) :
    f = hopiExpectedSatisfactionFraction (blockLength q) q r ℓ := by
  unfold SemicircleLaw at law
  rw [law]
  unfold hopiExpectedSatisfactionFraction decodingFraction setFraction
  rw [cast_alphabetSize]

/-- The expected satisfaction fraction of Theorem 1 lies between the random-guessing
baseline `r/q^2` and `1`, for constraint sets that fit in the alphabet and a decoding
radius that fits in the block. -/
theorem hopi_expected_satisfaction_range {q r ℓ : ℕ} (hq : 0 < q) (hr : r ≤ q ^ 2)
    (hℓ : ℓ ≤ blockLength q) {f : ℝ}
    (law : SemicircleLaw (blockLength q) (q ^ 2) r ℓ f) :
    setFraction q r ≤ f ∧ f ≤ 1 := by
  have hn : 0 < blockLength q := by
    unfold blockLength
    positivity
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hε0 : 0 ≤ decodingFraction (blockLength q) ℓ := by
    unfold decodingFraction
    positivity
  have hε1 : decodingFraction (blockLength q) ℓ ≤ 1 := by
    unfold decodingFraction
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hℓ
  have hα0 : 0 ≤ setFraction q r := by
    unfold setFraction
    positivity
  have hα1 : setFraction q r ≤ 1 := by
    unfold setFraction
    rw [div_le_one (by positivity : (0:ℝ) < (q:ℝ) ^ 2)]
    rw [← cast_alphabetSize]
    exact_mod_cast hr
  rw [hopi_expected_satisfaction_fraction law]
  unfold hopiExpectedSatisfactionFraction
  exact ⟨hopiSatisfactionFraction_lower_bound hε0 hα0 hα1,
    hopiSatisfactionFraction_le_one hε0 hε1 hα0 hα1⟩

/-- The expected satisfaction fraction of Theorem 1 reaches `1` exactly when
`ℓ/n + r/q^2 ≥ 1`: the curve saturates on `ℓ/n + r/q^2 = 1`, and the paper's second
branch reports full satisfaction beyond it. -/
theorem hopi_expected_satisfaction_eq_one_iff {q r ℓ : ℕ} (hq : 0 < q) (hr : r ≤ q ^ 2)
    (hℓ : ℓ ≤ blockLength q) {f : ℝ}
    (law : SemicircleLaw (blockLength q) (q ^ 2) r ℓ f) :
    f = 1 ↔ 1 ≤ decodingFraction (blockLength q) ℓ + setFraction q r := by
  have hn : 0 < blockLength q := by
    unfold blockLength
    positivity
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hε0 : 0 ≤ decodingFraction (blockLength q) ℓ := by
    unfold decodingFraction
    positivity
  have hε1 : decodingFraction (blockLength q) ℓ ≤ 1 := by
    unfold decodingFraction
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hℓ
  have hα0 : 0 ≤ setFraction q r := by
    unfold setFraction
    positivity
  have hα1 : setFraction q r ≤ 1 := by
    unfold setFraction
    rw [div_le_one (by positivity : (0:ℝ) < (q:ℝ) ^ 2)]
    rw [← cast_alphabetSize]
    exact_mod_cast hr
  rw [hopi_expected_satisfaction_fraction law]
  unfold hopiExpectedSatisfactionFraction
  exact hopiSatisfactionFraction_eq_one_iff hε0 hε1 hα0 hα1

/-- The dual-distance guarantee `d^⊥ ≥ t + 2 - 2g` of a Hermitian code `C_t` supports a
decoder radius `ℓ = ⌊(d^⊥ - 1)/2⌋` of at least `⌊(t + 1 - 2g)/2⌋`, and because the
piecewise fraction is nondecreasing in the decoding fraction, Theorem 1 then guarantees
at least the closed-form value reached at that smaller radius. This is the paper's
"the only nontrivial inputs are the length `n`, the constraint-set size `r`, and the
decoding radius `ℓ`, which in turn comes from the dual distance". -/
theorem hopi_expected_satisfaction_ge_of_dualDistance {q t d r : ℕ} (hq : 0 < q)
    (hr : r ≤ q ^ 2) (hd : t + 2 - 2 * hermitianGenus q ≤ d) (hdn : d ≤ blockLength q)
    {f : ℝ} (law : SemicircleLaw (blockLength q) (q ^ 2) r (decodingRadius d) f) :
    hopiSatisfactionFraction
        (((t + 1 - 2 * hermitianGenus q) / 2 : ℕ) / (blockLength q : ℕ))
        (setFraction q r) ≤ f := by
  have hn : 0 < blockLength q := by
    unfold blockLength
    positivity
  have hnR : (0:ℝ) < (blockLength q : ℝ) := by exact_mod_cast hn
  have hbase : (t + 1 - 2 * hermitianGenus q) / 2 ≤ decodingRadius d :=
    decodingRadius_ge_of_dualDistance hd
  have hε1 : 0 ≤ ((t + 1 - 2 * hermitianGenus q) / 2 : ℕ) / (blockLength q : ℝ) := by
    positivity
  have hε : ((t + 1 - 2 * hermitianGenus q) / 2 : ℕ) / (blockLength q : ℝ)
      ≤ (decodingRadius d : ℝ) / (blockLength q : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hbase) hnR.le
  have hε2 : (decodingRadius d : ℝ) / (blockLength q : ℝ) ≤ 1 := by
    rw [div_le_one hnR]
    have := decodingRadius_le_self d
    exact_mod_cast this.trans hdn
  have hα0 : 0 ≤ setFraction q r := by
    unfold setFraction
    positivity
  have hα1 : setFraction q r ≤ 1 := by
    unfold setFraction
    rw [div_le_one (by positivity : (0:ℝ) < (q:ℝ) ^ 2)]
    rw [← cast_alphabetSize]
    exact_mod_cast hr
  rw [hopi_expected_satisfaction_fraction law]
  unfold hopiExpectedSatisfactionFraction decodingFraction
  exact hopiSatisfactionFraction_mono_left hε1 hε hε2 hα0 hα1

end Qatlib.Papers.AlgGeomCode25.MainResults
