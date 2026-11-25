/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DihedralHSP04.MainResults.Defs

@[expose] public section

/-!
# Scalar probability of selecting two matching terms

In §3 each accepted label has between two and thirty-two matching masks. Selecting two
terms from its equally weighted components gives the ratio used in the argument. The
bounds below depend only on the matching count.
-/

set_option autoImplicit false

open Qatlib.Papers.DihedralHSP04.MainResults

namespace Qatlib.Papers.DihedralHSP04.MainResults

/-- For the accepted matching count in §3, the paper's two-term projection rate lies in
`[1/16, 1]`. This is the scalar rate bound under its matching-count condition. -/
theorem two_term_projection_rate_bounds {l : ℕ} {y : SampleSpace l} {z : ZMod (2 ^ l)}
    (hs : combinationSucceeds l y z) :
    (1 : ℝ) / 16 ≤ 2 / (matchCount l y z : ℝ) ∧ 2 / (matchCount l y z : ℝ) ≤ 1 := by
  have hlow : (2 : ℝ) ≤ matchCount l y z := by exact_mod_cast hs.1
  have hhigh : (matchCount l y z : ℝ) ≤ 32 := by exact_mod_cast hs.2
  have hpos : (0 : ℝ) < matchCount l y z := by linarith
  constructor
  · rw [le_div_iff₀ hpos]
    linarith
  · exact (div_le_one hpos).2 hlow

end Qatlib.Papers.DihedralHSP04.MainResults
