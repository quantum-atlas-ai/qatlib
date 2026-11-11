/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5: support line and totient success probability of the DLP recovery

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 5, p.14, and the
discussion preceding it in Appendix E.  Paper: *Quantum Advantage with
Adaptive Shallow Circuits*.

The recovery step of the DLP-based construction works in `Z_r` (`r` the order
of the base `g`).  Starting from the uniform superposition over
`(a, b) ∈ Z_r × Z_r`, a coherent evaluation of `g^a y^{-b}` and two inverse
quantum Fourier transforms, the outcome `(c, d)` always satisfies the linear
relation

```
d ≡ -x c   (mod r),      x = log_g y,                                  (E1)
```

and the success probability of the reduced output `c` is exactly
`φ(r)/r`, the fraction of residues coprime to `r`.

This file formalizes the two arithmetic facts about the support:

* `lineSupport_card`: for every `(x, c)`, the set of `d ∈ Z_r` with
  `d = -x c` has exactly one element, so the remaining state `|d⟩` is a
  single computational-basis state (the support is a line);
* `successProbability_eq_totient_ratio`: the fraction of `c ∈ Z_r` that are
  units is `φ(r)/r`, using `ZMod.card_units_eq_totient`.

The quantum Fourier analysis itself (that the post-measurement state is
uniform on this line) is the paper's argument in Appendix E and is not a
Lean statement; what is proved here is the exact combinatorial content needed
to read off the success probability.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.DLP

/-- The support line of Lemma 5: the set of `d ∈ Z_r` compatible with the
observed `c` and the secret `x = log_g y`, i.e. `d ≡ -x c (mod r)`.  The
notion "`d ≡ -x c`" is expressed in `ZMod r`, where it is an equality. -/
def lineSupport (r : ℕ) [NeZero r] (x c : ℕ) : Finset (ZMod r) :=
  Finset.univ.filter (fun d : ZMod r => d = -(x * c : ZMod r))

/-- **Eq. (E1), line form.**  The compatible `d` form the singleton
`{-x c}` in `Z_r`. -/
theorem lineSupport_eq_singleton (r : ℕ) [NeZero r] (x c : ℕ) :
    lineSupport r x c = {-(x * c : ZMod r)} := by
  ext d
  simp [lineSupport]

/-- **Lemma 5, support cardinality.**  For every outcome `c`, exactly one
remaining state `|d⟩` satisfies `d ≡ -x c (mod r)`; the post-measurement
state is therefore a single computational-basis state on the second
register. -/
theorem lineSupport_card (r : ℕ) [NeZero r] (x c : ℕ) : (lineSupport r x c).card = 1 := by
  rw [lineSupport_eq_singleton, Finset.card_singleton]

/-- **Lemma 5, membership form.**  Every `d` in the support satisfies the
congruence `d = -x c` in `Z_r`. -/
theorem lineSupport_spec (r : ℕ) [NeZero r] (x c : ℕ) {d : ZMod r} (hd : d ∈ lineSupport r x c) :
    d = -(x * c : ZMod r) := by
  simpa [lineSupport] using hd

/-- Number of residues `c ∈ Z_r` that are units, i.e. coprime to `r`. -/
def invertibleResidueCount (r : ℕ) [NeZero r] : ℕ := Fintype.card (ZMod r)ˣ

/-- The probability that the reduced outcome `c` is coprime to `r`, written
as the unit fraction of `Z_r`. -/
noncomputable def successProbability (r : ℕ) [NeZero r] : ℝ :=
  (invertibleResidueCount r : ℝ) / (r : ℝ)

/-- **Lemma 5, success probability.**  The probability that `gcd(c, r) = 1`
is exactly `φ(r)/r`.  (The count of units of `Z_r` is Euler's totient by
`ZMod.card_units_eq_totient`; units are exactly the residues coprime to `r`
by `ZMod.isUnit_iff_coprime`.) -/
theorem successProbability_eq_totient_ratio (r : ℕ) [NeZero r] :
    successProbability r = (Nat.totient r : ℝ) / (r : ℝ) := by
  unfold successProbability invertibleResidueCount
  rw [ZMod.card_units_eq_totient]

/-- **Lemma 5, unit/coprime dictionary.**  A residue `c ∈ Z_r` is a unit
exactly when `c` is coprime to `r`, which is the step turning the unit count
into the coprime-residue count of the statement. -/
theorem zmod_isUnit_iff_coprime (r c : ℕ) :
    IsUnit (c : ZMod r) ↔ Nat.Coprime c r :=
  ZMod.isUnit_iff_coprime c r

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.DLP
