module

import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Qatlib.Papers.ClassShadows20.ShadowVariance.TensorPauliOperatorNormVariance

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace QatlibTests.ClassShadows20TensorPauliOperatorNorm

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Papers.ClassShadows20.ShadowVariance

/-- The one-qubit Pauli-`X` word as a concrete non-degenerate observable. -/
def xWord : Fin 1 → Option (Fin 3) := fun _ => some 0

/-- The tensor-Pauli snapshot variance of the single-qubit `X` word in the pure state
`|0⟩⟨0|` is bounded by `3 ^ (tensorPauliWeight xWord) * ‖tensorPauliWord 1 xWord‖ ^ 2`,
the Euclidean operator-norm form of the Pauli second-moment bound. -/
example :
    (tensorPauliLaw 1 designProbePure designProbePure_isPure.1).variance
        (tensorPauliValue xWord) ≤
      (3 : ℝ) ^ tensorPauliWeight xWord * ‖tensorPauliWord 1 xWord‖ ^ 2 :=
  tensor_pauli_word_snapshot_variance_le_opNorm_sq 1 (by norm_num) xWord
    designProbePure designProbePure_isPure.1

/-- For the same concrete instance, the median-of-means estimator with block size `12`,
block count `4` and tolerance `1` (budget `4 * 3 ≤ 12 * 1 ^ 2`) misses the true
expectation by more than `1` with probability at most `3 ^ (4 / 2) / 2 ^ 4`. -/
example :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin 4 → Fin 12 → (Fin 1 → Fin 3 × Bool) =>
        (1 : ℝ) < |(tensorPauliLaw 1 designProbePure designProbePure_isPure.1).medianOfMeans
            (tensorPauliValue xWord) ω -
          (Matrix.trace (tensorPauliWord 1 xWord * designProbePure)).re|),
      ∏ k, (tensorPauliLaw 1 designProbePure designProbePure_isPure.1).probOf (ω k))
      ≤ (3 : ℝ) ^ (4 / 2) / 2 ^ 4 := by
  have hw : tensorPauliWeight xWord = 1 := by
    simp [tensorPauliWeight, xWord]
  have hbud : 4 * (3 : ℝ) ^ tensorPauliWeight xWord ≤ (12 : ℝ) * (1 : ℝ) ^ 2 := by
    rw [hw]
    norm_num
  exact tensor_pauli_word_single_median_failure 1 (by norm_num) xWord
    12 4 1 (by norm_num) (by norm_num) (by norm_num) hbud designProbePure designProbePure_isPure.1

end QatlibTests.ClassShadows20TensorPauliOperatorNorm
