/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationProofs
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationConsumers

/-!
# Ordered MPS transfer and open-boundary overlaps

This module collects the definitions, transfer-product proofs, and open-boundary consumers for
matrix product states. `MpsExternalAdaptationDefs.word` preserves site order, and
`MpsExternalAdaptationDefs.transferWord` acts on pairs of bond indices.

The imported results connect mixed-transfer products to conjugated Kronecker sums and to
amplitudes with both external bond indices fixed at zero. The matrix product state framework is
described in [PerezGarciaEtAl2007].

## Main statements

* `ordered_mixed_transfer`: Ordered mixed-transfer products expand as sums over physical words.
* `transferWord_inner`: The zero-boundary transfer entry computes the amplitude inner product.
* `open_overlap_and_consumers`: Overlap and norm identities are collected with boundary cases
  and explicit examples.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false
