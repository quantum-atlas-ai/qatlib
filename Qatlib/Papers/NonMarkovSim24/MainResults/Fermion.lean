/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NonMarkovSim24.MainResults.DQMEModel

@[expose] public section


set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonMarkovSim24.MainResults

open Qatlib.Papers.NonMarkovSim24.MainResults

/-- Fermionic annihilation operator `b̂⁻` on the one-mode Fock space
`H_f = ℂ²`, in the occupation basis `(|0⟩, |1⟩)`: `b̂⁻|1⟩ = |0⟩`, `b̂⁻|0⟩ = 0`. -/
def fAnn : Op 2 := !![0, 1; 0, 0]

/-- Fermionic creation operator `b̂⁺` on `H_f = ℂ²`: `b̂⁺|0⟩ = |1⟩`,
`b̂⁺|1⟩ = 0`. -/
def fCreat : Op 2 := !![0, 0; 1, 0]

/-- **Eq. (15): fermionic anti-commutation.**  The dissipaton creation and
annihilation operators satisfy `{b̂⁻, b̂⁺} = b̂⁻b̂⁺ + b̂⁺b̂⁻ = 1`, the canonical
relation used in Sec. III B to derive Eq. (15) and its equivalence with the
fermionic HEOM. -/
theorem fAnn_anticomm : fAnn * fCreat + fCreat * fAnn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fAnn, fCreat]

/-- The fermionic number operator `N̂ = b̂⁺b̂⁻` (Eq. (15)) is `diag(0,1)` on
`H_f`: it annihilates the vacuum and is the identity on the occupied level. -/
theorem fNum_eq_diag : fCreat * fAnn = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fAnn, fCreat]

/-- **Number-operator eigenrelation.**  On the occupation state `|n⟩`,
`N̂|n⟩ = n|n⟩` for `n ∈ {0,1}`. -/
theorem fNum_mulVec_single (n : Fin 2) :
    (fCreat * fAnn).mulVec (Pi.single n 1) = (n : ℂ) • Pi.single n 1 := by
  fin_cases n <;>
    (ext i; fin_cases i <;>
      simp [fAnn, fCreat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single])

/-- Action of `b̂⁻` on the Fock basis: `b̂⁻|1⟩ = |0⟩`. -/
theorem fAnn_mulVec_one :
    fAnn.mulVec (Pi.single 1 1) = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [fAnn, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single]

/-- Action of `b̂⁻` on the vacuum: `b̂⁻|0⟩ = 0`. -/
theorem fAnn_mulVec_zero : fAnn.mulVec (Pi.single 0 1) = 0 := by
  ext i
  fin_cases i <;> simp [fAnn, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single]

/-- Action of `b̂⁺` on the vacuum: `b̂⁺|0⟩ = |1⟩`. -/
theorem fCreat_mulVec_zero :
    fCreat.mulVec (Pi.single 0 1) = Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [fCreat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single]

/-- Doubled dissipaton configuration `(m,n)` representing `|m n⟩⟩ = |m⟩⟨n|`
(Eq. (23)-(24)). -/
abbrev FConf : Type := Fin 2 × Fin 2

section ComponentLadders

variable {d : ℕ}

/-- Raise the ket occupation `n` (coefficient `ρ_{n+1,m}`, i.e. `ρ_{n+m}` in
Eq. (20)); zero at the truncation boundary `n = 1`. -/
def raiseKet (ρ : FConf → Op d) (p : FConf) : Op d :=
  if (p.2 : ℕ) = 0 then ρ (p.1, 1) else 0

/-- Lower the ket occupation `n` (`ρ_{n−m}` in Eq. (20)). -/
def lowerKet (ρ : FConf → Op d) (p : FConf) : Op d :=
  if (p.2 : ℕ) = 1 then ρ (p.1, 0) else 0

/-- Raise the bra occupation `m` (`ρ_{nm+}` in Eq. (20)). -/
def raiseBra (ρ : FConf → Op d) (p : FConf) : Op d :=
  if (p.1 : ℕ) = 0 then ρ (1, p.2) else 0

/-- Lower the bra occupation `m` (`ρ_{nm−}` in Eq. (20)). -/
def lowerBra (ρ : FConf → Op d) (p : FConf) : Op d :=
  if (p.1 : ℕ) = 1 then ρ (0, p.2) else 0

/-- Number-operator action on the ket factor: at `(m,n)` multiply by `n`. -/
def numKet (ρ : FConf → Op d) (p : FConf) : Op d :=
  if p.2 = 1 then ρ p else 0

/-- Number-operator action on the bra factor: at `(m,n)` multiply by `m`. -/
def numBra (ρ : FConf → Op d) (p : FConf) : Op d :=
  if p.1 = 1 then ρ p else 0

/-- Parity sign `(-1)^e` of Eq. (20). -/
def chi (e : ℤ) : ℂ := (-1 : ℂ) ^ e

/-- Left multiplication by the dissipaton annihilation operator `b̂⁻` (acts on
the bra index `m`): this is exactly `raiseBra`. -/
abbrev leftAnn (ρ : FConf → Op d) (p : FConf) : Op d := raiseBra ρ p

/-- Left multiplication by `b̂⁺` (acts on `m`): `lowerBra`. -/
abbrev leftCre (ρ : FConf → Op d) (p : FConf) : Op d := lowerBra ρ p

/-- Right multiplication by `b̂⁺` (acts on the ket index `n`): `raiseKet`. -/
abbrev rightCre (ρ : FConf → Op d) (p : FConf) : Op d := raiseKet ρ p

/-- Right multiplication by `b̂⁻` (acts on `n`): `lowerKet`. -/
abbrev rightAnn (ρ : FConf → Op d) (p : FConf) : Op d := lowerKet ρ p

end ComponentLadders

/-- **Eq. (15), dissipaton decay term.**  The term
`-Σ_k (γ_k⁻ N̂_k ρ̃ + γ_k⁺ ρ̃ N̂_k)` acts on the doubled coefficient `(m,n)` as
`-(m γ⁻ + n γ⁺) ρ_{mn}`, exactly the `-γ_nm ρ_nm` decay term of the fermionic
HEOM Eq. (20), where `γ_nm ≡ Σ_k(n_k γ_k⁺ + m_k γ_k⁻)`. -/
theorem fermionic_decay_term {d : ℕ} (γm γp : ℂ) (ρ : FConf → Op d) (p : FConf) :
    γm • numBra ρ p + γp • numKet ρ p
      = ((p.1 : ℂ) • γm + (p.2 : ℂ) • γp) • ρ p := by
  rcases p with ⟨m, n⟩
  fin_cases m <;> fin_cases n <;> simp [numBra, numKet, add_smul]

/-- The right-hand side of the single-mode fermionic DQME-SQ Eq. (15),
expanded on the doubled dissipaton basis: the `-i[H_S,·]` term, the dissipaton
decay term, and the four `ζ`/`ξ` coupling groups with the second-quantized
mappings Eq. (14a-d). -/
def fermionicDQMESingle {d : ℕ} (H c cH : Op d) (γm γp ζm ζp ξm ξp : ℂ)
    (ρ : FConf → Op d) (p : FConf) : Op d :=
  (-Complex.I) • (H * ρ p - ρ p * H)
    - (γm • numBra ρ p + γp • numKet ρ p)
    - Complex.I •
        (ζm • (cH * leftAnn ρ p - leftAnn ρ p * cH)
          + ζp • (c * rightCre ρ p - rightCre ρ p * c)
          + ξp • (cH * rightAnn ρ p) - star ξp • (leftCre ρ p * c)
          - ξm • (c * leftCre ρ p) + star ξm • (rightAnn ρ p * cH))

/-- The right-hand side of the single-mode fermionic HEOM Eq. (20), with
`j = (k,σ)`, `M = m`, `N = n`, `θ_k^± = m,n`, and the coefficients
`η_k^σ = ζ_k^σ ξ_k^σ` (`ξ_k^σ = η_k^σ/ζ_k^σ` of Eq. (15)). -/
def fermionicHEOMSingle {d : ℕ} (H c cH : Op d) (γm γp ζm ζp ξm ξp : ℂ)
    (ρ : FConf → Op d) (p : FConf) : Op d :=
  (-Complex.I) • (H * ρ p - ρ p * H)
    - ((p.2 : ℂ) • γp + (p.1 : ℂ) • γm) • ρ p
    - Complex.I •
        (chi ((p.1 : ℤ)) • (c * raiseKet ρ p)
          - chi ((p.2 : ℤ)) • (raiseKet ρ p * c)
          + chi ((p.1 : ℤ) - (p.2 : ℤ)) • (cH * raiseBra ρ p)
          - chi ((p.2 : ℤ) + (p.2 : ℤ)) • (raiseBra ρ p * cH)
          + chi ((p.1 : ℤ)) • ((ζp * ξp) • (cH * lowerKet ρ p))
          - chi ((p.2 : ℤ) - 1) • (star (ζm * ξm) • (lowerKet ρ p * cH))
          + chi ((p.1 : ℤ) - (p.2 : ℤ)) • ((ζm * ξm) • (c * lowerBra ρ p))
          - chi ((p.2 : ℤ) - 1 + (p.2 : ℤ)) • (star (ζp * ξp) • (lowerBra ρ p * c)))

/-- **the fermionic dissipaton algebra underlying Eq. (15).**  The proved
structural content of the claim: anti-commutation, number-operator eigenvalues,
and the matching of the dissipaton decay term between Eq. (15) and Eq. (20). -/
theorem fermionic_dqme_sq_structure {d : ℕ} :
    (fAnn * fCreat + fCreat * fAnn = 1)
      ∧ (∀ n : Fin 2,
          (fCreat * fAnn).mulVec (Pi.single n 1) = (n : ℂ) • Pi.single n 1)
      ∧ (∀ (γm γp : ℂ) (ρ : FConf → Op d) (p : FConf),
          γm • numBra ρ p + γp • numKet ρ p
            = ((p.1 : ℂ) • γm + (p.2 : ℂ) • γp) • ρ p) :=
  ⟨fAnn_anticomm, fNum_mulVec_single, fun γm γp ρ p =>
    fermionic_decay_term γm γp ρ p⟩

/-- Arbitrary independent coupling coefficients do not give equal generators. -/
theorem coupling_contract_false :
    fermionicDQMESingle (0 : Op 1) 1 0 0 0 0 0 0 0 (fun _ => 1) ≠
      fermionicHEOMSingle (0 : Op 1) 1 0 0 0 0 0 0 0 (fun _ => 1) := by
  intro h
  have he := congrFun (congrFun (congrFun h (1, 0)) 0) 0
  norm_num [fermionicDQMESingle, fermionicHEOMSingle, numBra, numKet,
    chi, raiseKet, raiseBra, lowerKet, lowerBra, Matrix.ofNat_apply] at he

end Qatlib.Papers.NonMarkovSim24.MainResults
