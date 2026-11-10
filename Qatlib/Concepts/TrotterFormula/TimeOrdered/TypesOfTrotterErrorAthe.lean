/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.TimeOrdered.TypesOfTrotterErrorStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.TrotterFormula.TimeOrdered

theorem typesOfTrotterError : TypesOfTrotterError := by
  intro I _ _ xs H t
  exact ⟨pf_word_additive_representation xs H t,
    pfWordDefectRight_suffix_sum xs H,
    pf_word_exponentiated_representation xs H t,
    pfWordDefectLeft_prefix_sum xs H,
    pf_word_multiplicative_representation xs H t⟩

end Qatlib.Concepts.TrotterFormula.TimeOrdered
