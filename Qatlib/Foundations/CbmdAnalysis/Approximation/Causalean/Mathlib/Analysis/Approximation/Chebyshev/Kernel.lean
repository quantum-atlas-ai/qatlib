/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.NormNum.Parity
import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.KernelPart1
import Qatlib.Foundations.CbmdAnalysis.Approximation.Causalean.Mathlib.Analysis.Approximation.Chebyshev.KernelPart2

/-!
# Jackson kernel interface

This module imports the raw and normalized Jackson kernel development from `KernelPart1` and
`KernelPart2`. Together these provide the continuous kernel, exact normalization, moment
estimates, and trigonometric degree bounds used by the approximation infrastructure associated
with [WangEtAl2026].

## Main statements

* `jraw_eq_chebyshev`: Represent the raw kernel by a Chebyshev polynomial.
* `jackson_integral_eq_one`: Normalize the kernel on `[-π, π]`.
* `jackson_isTrigPolyLE`: Bound its trigonometric degree.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Approximation

end Qatlib.Foundations.CbmdAnalysis.Approximation
