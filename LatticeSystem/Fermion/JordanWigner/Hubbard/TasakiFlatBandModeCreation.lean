import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis

/-!
# Tasaki §11.3.1: the single-particle-mode creation map (towards Theorem 11.11 uniqueness)

The flat-band creation operators `â†_{p,σ}` and `b̂†_{u,σ}` are both instances of one
single-particle-mode creation map `Ĉ†_σ(w) = ∑_x w(x) ĉ†_{x,σ}`, linear in the single-particle
coefficient vector `w : Fin (2K+2) → ℂ`.  Since `{α_p} ∪ {β_u}` is a basis of the single-particle
space (`flatBandBasis`, Lemma 11.10), every site creation `ĉ†_{x,σ}` — and hence every
`Ĉ†_σ(w)` — is a linear combination of the `â†` and `b̂†`.  This change of single-particle basis at
the operator level is the foundation of the Fock-space factorisation used for the uniqueness half of
Theorem 11.11 (`flatBandBKernelSubmodule ⊆ flatBandAlphaFockSubmodule`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eqs. (11.3.1)–(11.3.4), Lemma 11.10.

Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **The single-particle-mode creation map** `Ĉ†_σ(w) = ∑_x w(x) ĉ†_{x,σ}` as a `ℂ`-linear map
from single-particle coefficient vectors `Fin (2K+2) → ℂ` to many-body operators.  Both `â†_{p,σ}`
(at `w = α_p`) and `b̂†_{u,σ}` (at `w = β_u`) are values of this map. -/
noncomputable def flatBandModeCreation (K : ℕ) (σ : Fin 2) :
    (Fin (2 * K + 2) → ℂ) →ₗ[ℂ] ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) where
  toFun w := ∑ x : Fin (2 * K + 2), w x •
    fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
  map_add' w₁ w₂ := by
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

/-- `â†_{p,σ}` is the mode creation at the single-particle state `α_p`. -/
theorem flatBandACreation_eq_modeCreation (K : ℕ) (ν : ℝ) (p : Fin (K + 1)) (σ : Fin 2) :
    flatBandACreation K ν p σ = flatBandModeCreation K σ (flatBandAlphaC K ν p) :=
  rfl

/-- `b̂†_{u,σ}` is the mode creation at the single-particle state `β_u`. -/
theorem flatBandBCreation_eq_modeCreation (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) (σ : Fin 2) :
    flatBandBCreation K ν u σ = flatBandModeCreation K σ (flatBandBetaC K ν u) :=
  rfl

/-- The mode creation on a `flatBandBasis` vector is the corresponding `â†` (left summand) or
`b̂†` (right summand). -/
theorem flatBandModeCreation_basis (K : ℕ) (ν : ℝ) (σ : Fin 2)
    (i : Fin (K + 1) ⊕ Fin (K + 1)) :
    flatBandModeCreation K σ (flatBandBasis K ν i)
      = Sum.elim (fun p => flatBandACreation K ν p σ) (fun u => flatBandBCreation K ν u σ) i := by
  have hb : ⇑(flatBandBasis K ν) = Sum.elim (flatBandAlphaC K ν) (flatBandBetaC K ν) := by
    unfold flatBandBasis
    exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  rcases i with p | u
  · rw [Sum.elim_inl, flatBandACreation_eq_modeCreation, hb, Sum.elim_inl]
  · rw [Sum.elim_inr, flatBandBCreation_eq_modeCreation, hb, Sum.elim_inr]

/-- The mode creation at the standard single-particle basis vector `Pi.single x 1` is the site
creation `ĉ†_{x,σ}`: only the `y = x` term of the defining sum survives. -/
theorem flatBandModeCreation_single (K : ℕ) (σ : Fin 2) (x : Fin (2 * K + 2)) :
    flatBandModeCreation K σ (Pi.single x 1)
      = fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) := by
  simp only [flatBandModeCreation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single x]
  · rw [Pi.single_eq_same, one_smul]
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy, zero_smul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- **Operator-level change of single-particle basis.**  Every mode creation `Ĉ†_σ(w)` is the
`flatBandBasis`-expansion combination of the `â†_{p,σ}` and `b̂†_{u,σ}`:
`Ĉ†_σ(w) = ∑_i (repr w) i • Ĉ†_σ(basis i)`.  In particular every site creation `ĉ†_{x,σ}` is a
linear combination of the flat-band creations (no `β`-only or `α`-only restriction yet). -/
theorem flatBandModeCreation_eq_repr_sum (K : ℕ) (ν : ℝ) (σ : Fin 2)
    (w : Fin (2 * K + 2) → ℂ) :
    flatBandModeCreation K σ w
      = ∑ i, (flatBandBasis K ν).repr w i •
          Sum.elim (fun p => flatBandACreation K ν p σ)
            (fun u => flatBandBCreation K ν u σ) i := by
  conv_lhs => rw [← (flatBandBasis K ν).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, flatBandModeCreation_basis]

end LatticeSystem.Fermion
