/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Examples
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Matrix Polynomial
open Qatlib.Papers.ModularFunct00.MainResults.Examples

def GenInfiniteModCenter {d : ℕ} (A B : ↥(unitaryGroup (Fin d) ℂ)) : Prop :=
  Infinite (↥(Subgroup.closure ({A, B} : Set ↥(unitaryGroup (Fin d) ℂ))) ⧸
    Subgroup.center ↥(Subgroup.closure ({A, B} : Set ↥(unitaryGroup (Fin d) ℂ))))

theorem theorem3_1_iii_two_by_two {q : ℂ} (s : ℂ) (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1)
    (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    spectrum ℂ (sig2_21 (q := q) s) = {(-1 : ℂ), q} :=
  spectrum_sig2_21 s hq5 hq1 hs

theorem theorem3_1_iii_five_by_five {q : ℂ} :
    spectrum ℂ (sig1_33 (q := q)) = {(-1 : ℂ), q} :=
  spectrum_sig1_33

theorem theorem3_1_iii_eight_by_eight {q : ℂ} :
    spectrum ℂ (sig1_42 (q := q)) = {(-1 : ℂ), q} :=
  spectrum_sig1_42

theorem theorem3_1_iv_multiplicities {q : ℂ} (hq5 : q ^ 5 = 1) :
    rootMultiplicity (-1) (sig1_42 (q := q)).charpoly = 3 ∧
      rootMultiplicity q (sig1_42 (q := q)).charpoly = 5 :=
  multiplicity_sig1_42 hq5

theorem theorem3_1_iv_charpoly {q : ℂ} :
    (sig1_42 (q := q)).charpoly = (X - C (-1)) ^ 3 * (X - C q) ^ 5 :=
  charpoly_sig1_42

theorem theorem3_1_two_by_two_braid_relation {q : ℂ} (s : ℂ) (hq5 : q ^ 5 = 1)
    (hs : s ^ 2 * q = q ^ 2 + q + 1) :
    sig1_21 (q := q) * sig2_21 (q := q) s * sig1_21 (q := q) =
      sig2_21 (q := q) s * sig1_21 (q := q) * sig2_21 (q := q) s :=
  braid_21 s hq5 hs

end Qatlib.Papers.ModularFunct00.MainResults.Representation
