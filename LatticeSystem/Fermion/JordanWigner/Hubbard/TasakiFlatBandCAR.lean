import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis
import LatticeSystem.Fermion.JordanWigner.CAR.SameSite
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

/-!
# Tasaki §11.3.1: the `a`/`b` anticommutator `{b̂_{u,σ}, â†_{p,τ}} = 0` (eq. 11.3.7)

The key algebraic input to Tasaki's flat-band ferromagnetism: the `b̂` and `â†`
operators anticommute, because the single-particle states `β_u` and `α_p` are
orthogonal.  Expanding the anticommutator of the two linear combinations and
using the canonical anticommutation relations
`{ĉ_{x,σ}, ĉ†_{y,τ}} = δ_{x,y} δ_{σ,τ}` reduces it to the cross-orthogonality
`⟨α_p, β_u⟩ = 0` (proved in `TasakiFlatBandBasis.lean`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eq. (11.3.7).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The spinful canonical anticommutation relation
`{ĉ_{x,σ}, ĉ†_{y,τ}} = [x = y ∧ σ = τ]`. -/
theorem spinful_annihilation_creation_anticomm (K : ℕ) (x y : Fin (2 * K + 2))
    (σ τ : Fin 2) :
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
        fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ)
      + fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ) *
        fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
      = if x = y ∧ σ = τ then 1 else 0 := by
  by_cases h : spinfulIndex (2 * K + 1) x σ = spinfulIndex (2 * K + 1) y τ
  · obtain ⟨rfl, rfl⟩ := (spinfulIndex_eq_iff (2 * K + 1) x y σ τ).mp h
    rw [if_pos ⟨rfl, rfl⟩, fermionMultiAnticomm_self]
  · rw [fermionMultiAnnihilation_creation_anticomm_of_ne h,
      if_neg (fun hxy => h ((spinfulIndex_eq_iff (2 * K + 1) x y σ τ).mpr hxy))]

/-- **Tasaki eq. (11.3.7): `{b̂_{u,σ}, â†_{p,τ}} = 0`.**  The `b̂` and `â†`
operators anticommute, since `⟨α_p, β_u⟩ = 0`. -/
theorem flatBandBAnnihilation_ACreation_anticomm (K : ℕ) (ν : ℝ) (u p : Fin (K + 1))
    (σ τ : Fin 2) :
    flatBandBAnnihilation K ν u σ * flatBandACreation K ν p τ
      + flatBandACreation K ν p τ * flatBandBAnnihilation K ν u σ = 0 := by
  set c : Fin (2 * K + 2) → ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
    fun x => fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
    with hc
  set d : Fin (2 * K + 2) → ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
    fun y => fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ)
    with hd
  -- the anticommutator equals a double sum of scalar-weighted single-mode anticommutators
  have hkey : flatBandBAnnihilation K ν u σ * flatBandACreation K ν p τ
      + flatBandACreation K ν p τ * flatBandBAnnihilation K ν u σ
      = ∑ x, ∑ y, ((flatBandBeta K ν u x : ℂ) * (flatBandAlpha K ν p y : ℂ)) •
          (c x * d y + d y * c x) := by
    unfold flatBandBAnnihilation flatBandACreation
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm _ (flatBandAlpha K ν p y : ℂ),
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (flatBandAlpha K ν p y : ℂ),
      ← smul_add]
  rw [hkey]
  simp_rw [hc, hd, spinful_annihilation_creation_anticomm]
  by_cases hστ : σ = τ
  · subst hστ
    simp_rw [and_true]
    rw [show (∑ x, ∑ y, ((flatBandBeta K ν u x : ℂ) * (flatBandAlpha K ν p y : ℂ)) •
        (if x = y then (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) else 0))
        = ∑ x, ((flatBandBeta K ν u x : ℂ) * (flatBandAlpha K ν p x : ℂ)) • (1 : _) from by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_congr rfl (fun y _ => by rw [smul_ite, smul_zero]),
        Finset.sum_ite_eq Finset.univ x (fun y =>
          ((flatBandBeta K ν u x : ℂ) * (flatBandAlpha K ν p y : ℂ)) • (1 : _)),
        if_pos (Finset.mem_univ x)]]
    rw [← Finset.sum_smul, show (∑ x, (flatBandBeta K ν u x : ℂ) * (flatBandAlpha K ν p x : ℂ))
        = (((∑ x, flatBandAlpha K ν p x * flatBandBeta K ν u x : ℝ)) : ℂ) from by
      push_cast; refine Finset.sum_congr rfl (fun x _ => by ring),
      flatBandAlpha_dot_beta, Complex.ofReal_zero, zero_smul]
  · refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
    rw [if_neg (fun h => hστ h.2), smul_zero]

end LatticeSystem.Fermion
