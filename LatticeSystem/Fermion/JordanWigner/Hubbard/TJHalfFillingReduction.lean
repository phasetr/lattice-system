import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingExchange
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingBasis

/-!
# Tasaki 11.5.3: the half-filling reduction on the whole sector (Theorem 11.26 PR3f)

At half-filling `Ne = N + 1` every electron configuration is fully occupied, so the per-basis
half-filling results extend to the whole `N̂ = N+1` hard-core sector by linearity:

* `tJ_kinetic_sandwich_mulVec_eq_zero_of_filling` — `P̂hc K P̂hc v = 0` for any hard-core `N̂ = N+1`
  vector `v`;
* `tJHamiltonian_mulVec_eq_smul_tJExchange_of_filling` — `Ĥ_tJ v = J · tJExchange v` for such `v`.

So on the half-filling sector `Ĥ_tJ` is the ferromagnetic Heisenberg operator `J · tJExchange` — the
bridge to the ground energy `= 0` (`tJExchange ≥ 0`, all-up annihilated).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- A half-filling (`Ne = N+1`) sector configuration is fully occupied (no empty site). -/
theorem tJFillingSector_full (s : TJFillingSector N (N + 1)) (k : Fin (N + 1)) : s.val k ≠ 0 := by
  classical
  have hdisj : Disjoint (Finset.univ.filter (fun k => s.val k = 1))
      (Finset.univ.filter (fun k => s.val k = 2)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    rw [Finset.mem_filter] at h1 h2
    rw [h1.2] at h2; exact absurd h2.2 (by decide)
  have hunion : Finset.univ.filter (fun k => s.val k = 1) ∪
      Finset.univ.filter (fun k => s.val k = 2) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, s.property, Fintype.card_fin]
  intro h0
  have hk : k ∈ Finset.univ.filter (fun k => s.val k = 1) ∪
      Finset.univ.filter (fun k => s.val k = 2) := by rw [hunion]; exact Finset.mem_univ k
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hk
  rcases hk with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h0] at h <;> exact absurd h (by decide)

/-- **Kinetic vanishing on the whole half-filling sector.**  `P̂hc K P̂hc v = 0` for any hard-core
`N̂ = N+1` vector `v` (linear extension of the per-basis vanishing). -/
theorem tJ_kinetic_sandwich_mulVec_eq_zero_of_filling (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hhc : v ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v) :
    (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
        hubbardHardcoreProjection N).mulVec v = 0 := by
  rw [tJ_filling_completeness (N + 1) v hhc hN, tJFillingExpansion, Matrix.mulVec_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Matrix.mulVec_smul,
    tJ_kinetic_sandwich_mulVec_tJConfigOf_eq_zero_of_full N G s.val (tJFillingSector_full s),
    smul_zero]

/-- **Half-filling reduction.**  `Ĥ_tJ v = J · tJExchange v` for any hard-core `N̂ = N+1` vector
`v`: the kinetic term vanishes on the whole sector, leaving the exchange (Heisenberg) part. -/
theorem tJHamiltonian_mulVec_eq_smul_tJExchange_of_filling (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hhc : v ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v) :
    (tJHamiltonian N G τ J).mulVec v = (J : ℂ) • (tJExchange N G).mulVec v := by
  unfold tJHamiltonian
  rw [Matrix.add_mulVec, Matrix.smul_mulVec,
    tJ_kinetic_sandwich_mulVec_eq_zero_of_filling G hhc hN, smul_zero, zero_add, Matrix.smul_mulVec]
  rfl

end LatticeSystem.Fermion
