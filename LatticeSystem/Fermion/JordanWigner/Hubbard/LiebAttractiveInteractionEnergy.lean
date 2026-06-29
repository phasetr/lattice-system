import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffAction

/-!
# The attractive interaction energy as a diagonal `normSq` sum (Tasaki §10.2.1)

Twenty-fourth layer (PR24) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR2 showed that the on-site interaction acts entrywise (Hadamard) on the
spin-reflection coefficient matrix `spinReflectionCoeff`. This file lifts that
diagonal action to the **energy quadratic form**: the expectation of the attractive
interaction in a state `ψ` is a weighted sum of the squared magnitudes of the
coefficient-matrix entries,

  `⟨ψ| Ĥint |ψ⟩ = Σ_{u,h} (Σ_x −U_x · u_x · (1 − h_x)) · |C_{u,h}|²`,  `C = spinReflectionCoeff ψ`.

For attractive `U_x > 0` the weight `Σ_x −U_x · u_x · (1 − h_x) ≤ 0` is non-positive,
the sign that makes the spin-reflection variational argument lower the energy. The
positive-semidefinite / Perron–Frobenius structure lives on `spinReflectionCoeff`
(not the block coefficient matrix used for the kinetic trace), so the interaction
energy is naturally expressed here.

## Main results

* `particleHoleConfig_val_eq_one_sub` — the hole occupation `(P h)_x = 1 − h_x`.
* `dotProduct_eq_sum_spinReflectionCoeff` — the inner product as a sum over the
  spin-reflection coefficient entries.
* `attractiveHubbardInteraction_dotProduct_eq_spinReflectionCoeff_normSq` — the
  interaction energy as a diagonal `normSq` sum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Complex
open scoped BigOperators

variable {N : ℕ}

/-- The hole occupation is the complement of the down occupation:
`(particleHoleConfig h)_x = 1 − h_x` (as reals). -/
theorem particleHoleConfig_val_eq_one_sub (N : ℕ) (h : hubbardSpinConfig N)
    (x : Fin (N + 1)) :
    (((particleHoleConfig N h) x).val : ℝ) = 1 - ((h x).val : ℝ) := by
  change ((flipOccupation (h x)).val : ℝ) = 1 - ((h x).val : ℝ)
  unfold flipOccupation
  by_cases hhx : h x = 0
  · rw [hhx]; simp
  · have h1 : h x = 1 := by omega
    rw [h1]; simp

/-- The inner product `⟪ψ, φ⟫` expanded as a sum over the spin-reflection
coefficient-matrix entries, via the interleaved up/down factorization and the
particle–hole reindexing of the down configuration. -/
theorem dotProduct_eq_sum_spinReflectionCoeff (N : ℕ)
    (ψ φ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star ψ) φ
      = ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
          star (spinReflectionCoeff N ψ u h) * spinReflectionCoeff N φ u h := by
  rw [dotProduct, ← Equiv.sum_comp (hubbardSpinConfigEquiv N).symm
      (fun c => (star ψ) c * φ c), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Equiv.sum_comp (particleHoleConfig_involutive N).toPerm
      (fun d => (star ψ) ((hubbardSpinConfigEquiv N).symm (u, d)) *
        φ ((hubbardSpinConfigEquiv N).symm (u, d)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  simp only [hubbardSpinConfigEquiv, Equiv.coe_fn_symm_mk,
    Function.Involutive.coe_toPerm, Pi.star_apply, spinReflectionCoeff]

/-- **The attractive interaction energy as a diagonal `normSq` sum.** -/
theorem attractiveHubbardInteraction_dotProduct_eq_spinReflectionCoeff_normSq (N : ℕ)
    (U : Fin (N + 1) → ℝ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star ψ) ((attractiveHubbardInteraction N U).mulVec ψ)
      = ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
          ((∑ x : Fin (N + 1), -U x * ((u x).val : ℝ) * (1 - ((h x).val : ℝ)) : ℝ) : ℂ) *
            (Complex.normSq (spinReflectionCoeff N ψ u h) : ℂ) := by
  rw [dotProduct_eq_sum_spinReflectionCoeff]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun h _ => ?_))
  have hact : spinReflectionCoeff N ((attractiveHubbardInteraction N U).mulVec ψ) u h
      = hubbardOnSiteInteractionSiteReflectionCoeffWeight N (fun x => -(U x : ℂ)) u h *
          spinReflectionCoeff N ψ u h := by
    rw [spinReflectionCoeff_attractiveHubbardInteraction]; rfl
  rw [hact]
  have hns : star (spinReflectionCoeff N ψ u h) * spinReflectionCoeff N ψ u h
      = (Complex.normSq (spinReflectionCoeff N ψ u h) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  rw [show star (spinReflectionCoeff N ψ u h) *
        (hubbardOnSiteInteractionSiteReflectionCoeffWeight N (fun x => -(U x : ℂ)) u h *
          spinReflectionCoeff N ψ u h)
      = hubbardOnSiteInteractionSiteReflectionCoeffWeight N (fun x => -(U x : ℂ)) u h *
          (star (spinReflectionCoeff N ψ u h) * spinReflectionCoeff N ψ u h) from by ring,
    hns]
  congr 1
  unfold hubbardOnSiteInteractionSiteReflectionCoeffWeight
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hph : ((particleHoleConfig N h x).val : ℂ) = 1 - ((h x).val : ℂ) := by
    exact_mod_cast particleHoleConfig_val_eq_one_sub N h x
  rw [hph]

end LatticeSystem.Fermion
