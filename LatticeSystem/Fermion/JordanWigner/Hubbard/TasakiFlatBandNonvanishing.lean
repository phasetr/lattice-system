import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandHighestWeight
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis

/-!
# Tasaki §11.3.1: the all-up `α` state is nonzero (`|Φα,all↑⟩ ≠ 0`)

The remaining input to the existence half of Theorem 11.11 is that the candidate
ferromagnetic ground state `|Φα,all↑⟩ = (∏_p â†_{p,↑}) |vac⟩` does not vanish.

The proof avoids any Slater-determinant / Gram machinery by exploiting the
*triangular* structure of the `α` orbitals: on the external sites the orbitals
are exactly the unit vectors, `α_p(deltaExternalSite q) = δ_{pq}`
(`flatBandAlpha_deltaExternalSite`).  Hence the external up-site annihilation
`ĉ_{2q,↑}` is the canonical dual of `â†_{q,↑}`:
`{ĉ_{2q,↑}, â†_{p,↑}} = α_p(2q) = δ_{pq}`
(`flatBandExtUpAnnihilation_ACreation_anticomm`).  Applying the dual annihilations
in order collapses the ordered creation product back to the vacuum (identity
overlap, no determinant): there is an operator `D` with
`D |Φα,all↑⟩ = |vac⟩` (`flatBandAlpha_listProd_exists_collapse`).  Since
`|vac⟩ ≠ 0`, also `|Φα,all↑⟩ ≠ 0` (`flatBandAlphaAllUpState_ne_zero`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11 (existence half).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The external up-site annihilation `ĉ_{2q,↑}`: the annihilation operator at the
JW position of external site `q` with up spin. -/
noncomputable def flatBandExtUpAnnihilation (K : ℕ) (q : Fin (K + 1)) :
    ManyBodyOp (Fin (2 * (2 * K + 1) + 2)) :=
  fermionMultiAnnihilation (2 * (2 * K + 1) + 1)
    (spinfulIndex (2 * K + 1) (deltaExternalSite K q) 0)

/-- **`{ĉ_{2q,↑}, â†_{p,↑}} = δ_{pq}`.**  The external up-site annihilation is the
canonical dual of `â†_{p,↑}`: the anticommutator collapses (via spinful CAR) to
`α_p(deltaExternalSite q) = δ_{pq}`. -/
theorem flatBandExtUpAnnihilation_ACreation_anticomm (K : ℕ) (ν : ℝ)
    (q p : Fin (K + 1)) :
    flatBandExtUpAnnihilation K q * flatBandACreation K ν p 0 +
        flatBandACreation K ν p 0 * flatBandExtUpAnnihilation K q =
      (if q = p then (1 : ℂ) else 0) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) := by
  unfold flatBandExtUpAnnihilation flatBandACreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [show (∑ x : Fin (2 * K + 2),
      (fermionMultiAnnihilation (2 * (2 * K + 1) + 1)
            (spinfulIndex (2 * K + 1) (deltaExternalSite K q) 0) *
          (flatBandAlpha K ν p x : ℂ) •
            fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) +
        (flatBandAlpha K ν p x : ℂ) •
            fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x 0) *
          fermionMultiAnnihilation (2 * (2 * K + 1) + 1)
            (spinfulIndex (2 * K + 1) (deltaExternalSite K q) 0))) =
      ∑ x : Fin (2 * K + 2), (flatBandAlpha K ν p x : ℂ) •
        (if deltaExternalSite K q = x then (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))
          else 0) from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, spinful_annihilation_creation_anticomm]
    congr 1
    simp only [and_true]]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [flatBandAlpha_deltaExternalSite]
  by_cases h : q = p <;> simp [h]

/-- **The dual annihilations collapse the ordered `α` product to the vacuum.**  For
a duplicate-free list `ps`, there is an operator `D` (a product of external
up-site annihilations) with `D · (∏_{p∈ps} â†_{p,↑}) |vac⟩ = |vac⟩`.  Built by
peeling one leading creation at a time with its dual annihilation. -/
theorem flatBandAlpha_listProd_exists_collapse (K : ℕ) (ν : ℝ) :
    ∀ ps : List (Fin (K + 1)), ps.Nodup →
      ∃ D : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)),
        D.mulVec (((ps.map (fun p => flatBandACreation K ν p 0)).prod).mulVec
          (fermionMultiVacuum (2 * (2 * K + 1) + 1))) =
          fermionMultiVacuum (2 * (2 * K + 1) + 1) := by
  intro ps
  induction ps with
  | nil =>
    intro _
    exact ⟨1, by simp⟩
  | cons p ps ih =>
    intro hnodup
    rw [List.nodup_cons] at hnodup
    obtain ⟨D, hD⟩ := ih hnodup.2
    refine ⟨D * flatBandExtUpAnnihilation K p, ?_⟩
    have hpeel : (flatBandExtUpAnnihilation K p *
        (flatBandACreation K ν p 0 *
          (ps.map (fun p => flatBandACreation K ν p 0)).prod)).mulVec
            (fermionMultiVacuum (2 * (2 * K + 1) + 1)) =
        ((ps.map (fun p => flatBandACreation K ν p 0)).prod).mulVec
          (fermionMultiVacuum (2 * (2 * K + 1) + 1)) := by
      refine dualAnnihilation_peel_listProd_mulVec_vacuum _ _ _ ps
        (fermionMultiAnnihilation_mulVec_vacuum _ _) ?_ ?_
      · rw [flatBandExtUpAnnihilation_ACreation_anticomm, if_pos rfl, one_smul]
      · intro q hq
        rw [flatBandExtUpAnnihilation_ACreation_anticomm,
          if_neg (fun (h : p = q) => hnodup.1 (h.symm ▸ hq)), zero_smul]
    rw [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, hpeel, hD]

/-- The vacuum is nonzero (it has value `1` at the all-empty configuration). -/
theorem fermionMultiVacuum_ne_zero (N : ℕ) : fermionMultiVacuum N ≠ 0 := by
  intro h
  have := congrFun h (fun _ : Fin (N + 1) => (0 : Fin 2))
  rw [fermionMultiVacuum, basisVec_self] at this
  exact one_ne_zero this

/-- **`|Φα,all↑⟩ ≠ 0`.**  Some operator `D` maps `|Φα,all↑⟩` to the (nonzero)
vacuum, so `|Φα,all↑⟩` cannot vanish.  This is the last input to the existence
half of Theorem 11.11. -/
theorem flatBandAlphaAllUpState_ne_zero (K : ℕ) (ν : ℝ) :
    flatBandAlphaAllUpState K ν ≠ 0 := by
  obtain ⟨D, hD⟩ := flatBandAlpha_listProd_exists_collapse K ν (List.finRange (K + 1))
    (List.nodup_finRange (K + 1))
  intro h
  rw [flatBandAlphaAllUpState] at h
  rw [h, Matrix.mulVec_zero] at hD
  exact fermionMultiVacuum_ne_zero _ hD.symm

end LatticeSystem.Fermion
