/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma47
set_option warningAsError false

set_option autoImplicit false

open scoped Classical BigOperators

namespace Qatlib.Papers.QLattice03.MainResults

noncomputable def r3Routine (cm : ℕ) (N : ℕ) [NeZero N] (q : ℕ) (d : ZMod N) : ℕ × ℤ :=
  (q, 0)

def lemma49_R3_estimates_qprime_d
    (cm : ℕ) (hcm : 3 ≤ cm) (N : ℕ) [NeZero N] (q : ℕ) (hq : 0 < q)
    (hqN : q * logPow N cm < N) (d : ZMod N) : Prop :=
  (let r := r3Routine cm N q d
   q ≤ r.1 ∧ r.1 ≤ logPow N cm * q ∧
     ∃ k : ℤ, r.2 - (r.1 : ℤ) * (d.val : ℤ) = k * (N : ℤ) ∧
       |r.2 - (r.1 : ℤ) * (d.val : ℤ)| ≤ (N : ℤ) / (logPow N (cm + 1) : ℤ))

end Qatlib.Papers.QLattice03.MainResults
