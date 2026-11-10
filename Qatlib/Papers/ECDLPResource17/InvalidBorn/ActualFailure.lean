/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.CurveGroups.AffineAdd.CyclicBitRun
import Qatlib.Concepts.FiniteCounts.OffsetWord.MixtureLaw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.InvalidBorn

open Qatlib.Concepts.CurveGroups.AffineAdd

theorem source_actual_bit_failure (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b : ZMod p} (P : (shortCurve a b).Point) (m n : ℕ)
    (k l : Fin (n+1) → Bool)
    (h : letI := cyclicFintype P
      (Finset.univ.erase (0 : AddSubgroup.zmultiples P)).Nonempty) :
    let E := primeFieldEncoding p w hp
    letI := cyclicFintype P
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h).toOuterMeasure
      {a0 | bitError E P m (List.ofFn k) (List.ofFn l) a0}).toReal ≤
      (8*(n+1) : ℕ) / (Fintype.card (AddSubgroup.zmultiples P) - 1 : ℕ) :=
  cyclic_bit_error_le (primeFieldEncoding p w hp) P m n k l h

theorem source_joint_bit_failure (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b : ZMod p} (P : (shortCurve a b).Point) (m n : ℕ)
    (h : letI := cyclicFintype P
      (Finset.univ.erase (0 : AddSubgroup.zmultiples P)).Nonempty) :
    let E := primeFieldEncoding p w hp
    letI := cyclicFintype P
    let law := Qatlib.Concepts.FiniteCounts.OffsetWord.jointLaw
      (PMF.uniformOfFintype' ((Fin (n+1) → Bool) × (Fin (n+1) → Bool)))
      (PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h)
    (law.toOuterMeasure {q | bitError E P m (List.ofFn q.1.1) (List.ofFn q.1.2) q.2}).toReal ≤
      (8*(n+1) : ℕ) / (Fintype.card (AddSubgroup.zmultiples P) - 1 : ℕ) := by
  letI := cyclicFintype P
  apply Qatlib.Concepts.FiniteCounts.OffsetWord.joint_error_le
  intro kl
  exact source_actual_bit_failure p w hp P m n kl.1 kl.2 h

end Qatlib.Papers.ECDLPResource17.InvalidBorn
