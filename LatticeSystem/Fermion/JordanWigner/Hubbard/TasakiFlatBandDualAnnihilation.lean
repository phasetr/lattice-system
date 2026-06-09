import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBetaGram
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandCAR
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandGroundState

/-!
# Tasaki §11.3.1: the dual β-annihilators (towards `BKernel ⊆ AlphaFock`)

Using the invertible β-Gram matrix `G` (`flatBandBetaGram`), the *dual annihilators*
`d_{u,σ} = ∑_v (G⁻¹)_{uv} b̂_{v,σ}` satisfy the Kronecker anticommutators
`{d_{u,σ}, b̂†_{w,τ}} = δ_{uw} δ_{στ}`, `{d_{u,σ}, â†_{p,τ}} = 0`, and `d_{u,σ}|vac⟩ = 0`.  They
peel a single `b̂†` factor off a rotated Fock monomial (passing the `â†` factors via the second
relation), the engine of the `flatBandBKernelSubmodule ⊆ flatBandAlphaFockSubmodule` factorisation.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **`{b̂_{u,σ}, b̂†_{w,τ}} = G_{uw} δ_{στ} · 1`** (the β-Gram, from the generic single-particle
CAR). -/
theorem flatBandBAnnihilation_BCreation_anticomm (K : ℕ) (ν : ℝ) (u w : Fin (K + 1)) (σ τ : Fin 2) :
    flatBandBAnnihilation K ν u σ * flatBandBCreation K ν w τ
      + flatBandBCreation K ν w τ * flatBandBAnnihilation K ν u σ
      = (if σ = τ then flatBandBetaGram K ν u w else 0) •
        (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) := by
  rw [flatBandBAnnihilation_eq_modeAnnihilation, flatBandBCreation_eq_modeCreation,
    flatBandMode_annihilation_creation_anticomm]
  simp only [flatBandBetaGram, Matrix.of_apply]

/-- The **dual β-annihilator** `d_{u,σ} = ∑_v (G⁻¹)_{uv} b̂_{v,σ}`. -/
noncomputable def flatBandDualBAnnihilation (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  ∑ v, (flatBandBetaGram K ν)⁻¹ u v • flatBandBAnnihilation K ν v σ

/-- **`{d_{u,σ}, b̂†_{w,τ}} = δ_{uw} δ_{στ} · 1`.**  The β-Gram contracts against its inverse:
`∑_v (G⁻¹)_{uv} G_{vw} = (G⁻¹ G)_{uw} = δ_{uw}`. -/
theorem flatBandDualBAnnihilation_BCreation_anticomm (K : ℕ) (ν : ℝ) (u w : Fin (K + 1))
    (σ τ : Fin 2) :
    flatBandDualBAnnihilation K ν u σ * flatBandBCreation K ν w τ
      + flatBandBCreation K ν w τ * flatBandDualBAnnihilation K ν u σ
      = (if u = w ∧ σ = τ then (1 : ℂ) else 0) •
        (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) := by
  rw [flatBandDualBAnnihilation, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hterm : ∀ v, (flatBandBetaGram K ν)⁻¹ u v • flatBandBAnnihilation K ν v σ *
        flatBandBCreation K ν w τ
      + flatBandBCreation K ν w τ *
        ((flatBandBetaGram K ν)⁻¹ u v • flatBandBAnnihilation K ν v σ)
      = (flatBandBetaGram K ν)⁻¹ u v •
        ((if σ = τ then flatBandBetaGram K ν v w else 0) •
          (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))) := by
    intro v
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, flatBandBAnnihilation_BCreation_anticomm]
  simp_rw [hterm]
  by_cases hστ : σ = τ
  · simp_rw [if_pos hστ, smul_smul, ← Finset.sum_smul]
    rw [show (∑ v, (flatBandBetaGram K ν)⁻¹ u v * flatBandBetaGram K ν v w)
          = ((flatBandBetaGram K ν)⁻¹ * flatBandBetaGram K ν) u w from (Matrix.mul_apply).symm,
      Matrix.nonsing_inv_mul _ (flatBandBetaGram_isUnit_det K ν), Matrix.one_apply]
    by_cases huw : u = w
    · rw [if_pos huw, if_pos ⟨huw, hστ⟩]
    · rw [if_neg huw, if_neg (fun h => huw h.1)]
  · simp_rw [if_neg hστ, zero_smul, smul_zero, Finset.sum_const_zero]
    rw [if_neg (fun h => hστ h.2), zero_smul]

/-- **`{d_{u,σ}, â†_{p,τ}} = 0`** — the dual annihilator passes the `α`-creations, since each `b̂`
anticommutes with every `â†` (`⟨α, β⟩ = 0`). -/
theorem flatBandDualBAnnihilation_ACreation_anticomm (K : ℕ) (ν : ℝ) (u p : Fin (K + 1))
    (σ τ : Fin 2) :
    flatBandDualBAnnihilation K ν u σ * flatBandACreation K ν p τ
      + flatBandACreation K ν p τ * flatBandDualBAnnihilation K ν u σ = 0 := by
  rw [flatBandDualBAnnihilation, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, flatBandBAnnihilation_ACreation_anticomm,
    smul_zero]

/-- **`d_{u,σ}|vac⟩ = 0`** — a combination of the `b̂`, each of which annihilates the vacuum. -/
theorem flatBandDualBAnnihilation_mulVec_vacuum (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) (σ : Fin 2) :
    (flatBandDualBAnnihilation K ν u σ).mulVec (fermionMultiVacuum (2 * (2 * K + 1) + 1)) = 0 := by
  rw [flatBandDualBAnnihilation, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [Matrix.smul_mulVec, flatBandBAnnihilation_mulVec_vacuum, smul_zero]

end LatticeSystem.Fermion
