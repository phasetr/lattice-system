import LatticeSystem.Fermion.JordanWigner.Hubbard.TJEffMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJKineticSector

/-!
# Tasaki 11.5: the hard-core bra drops the projection (Prop 11.24 PR-B7)

Toward the off-diagonal classification of the t-J effective matrix, this file removes the *outer*
hard-core projection of `Ĥ_tJ` when pairing against a hard-core bra `⟨Φ_{s'}|`.  Since the row of
`P̂hc` at a hard-core configuration is the corresponding unit vector (the projection fixes the basis
state, and `P̂hc` is Hermitian), `(P̂hc u)(tJConfigOf s') = u(tJConfigOf s')`.  This returns the
kinetic matrix element to the plain inner-product normal form on which the per-term hop lemmas act.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- **The hard-core projection drops on a sector configuration.**  Evaluating `P̂hc u` at the
hard-core config `tJConfigOf s'` returns `u` there: the row of `P̂hc` at a hard-core configuration
is
the unit vector. -/
theorem tJ_hardcore_proj_apply (N : ℕ) (s' : Fin (N + 1) → Fin 3)
    (u : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (hubbardHardcoreProjection N *ᵥ u) (tJConfigOf N s') = u (tJConfigOf N s') := by
  have hcol : ∀ w, hubbardHardcoreProjection N w (tJConfigOf N s')
      = if w = tJConfigOf N s' then 1 else 0 := by
    intro w
    have h := congrFun
      (hubbardHardcoreProjection_mulVec_eq_self_of_mem N (tJConfigOf_mem_hardcore N s')) w
    have hexp : (hubbardHardcoreProjection N *ᵥ basisVec (tJConfigOf N s')) w
        = hubbardHardcoreProjection N w (tJConfigOf N s') := by
      simp only [Matrix.mulVec, dotProduct]
      exact sum_mul_basisVec (tJConfigOf N s') (fun v => hubbardHardcoreProjection N w v)
    rw [hexp, basisVec_apply] at h
    exact h
  have hrow : ∀ w, hubbardHardcoreProjection N (tJConfigOf N s') w
      = if w = tJConfigOf N s' then 1 else 0 := by
    intro w
    have hH := (hubbardHardcoreProjection_isHermitian N).apply (tJConfigOf N s') w
    rw [hcol w] at hH
    rw [← hH]; split_ifs <;> simp
  simp only [Matrix.mulVec, dotProduct, hrow, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Kinetic matrix element in inner-product normal form.**  Pairing the kinetic sandwich against a
hard-core bra `⟨Φ_{s'}|` drops both projections, leaving `⟨Φ_{s'} | K | Φ_s⟩`. -/
theorem tJKinetic_matrixElement_eq (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (s s' : Fin (N + 1) → Fin 3) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 * hubbardHardcoreProjection
            N).mulVec
            (basisVec (tJConfigOf N s))) w)
      = ∑ w, basisVec (tJConfigOf N s') w *
          ((hubbardKineticOnGraph N G 1).mulVec (basisVec (tJConfigOf N s))) w := by
  rw [tJKinetic_sandwich_mulVec_tJConfigOf]
  rw [basisVec_sum_mul, basisVec_sum_mul, tJ_hardcore_proj_apply]

/-- **The kinetic matrix element expands over the spin/site sums.**  `⟨Φ_{s'} | K | Φ_s⟩` is the
graph-weighted sum over spins `σ` and sites `i, j` of the single-hop matrix elements
`⟨Φ_{s'} | ĉ†_{iσ}ĉ_{jσ} | Φ_s⟩`. -/
theorem tJKinetic_matrixElement_expand (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (s s' : Fin (N + 1) → Fin 3) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((hubbardKineticOnGraph N G 1).mulVec (basisVec (tJConfigOf N s))) w)
      = ∑ σ : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          LatticeSystem.Lattice.couplingOf G (1 : ℂ) i j *
            ∑ w, basisVec (tJConfigOf N s') w *
              ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
                  (basisVec (tJConfigOf N s))) w := by
  unfold hubbardKineticOnGraph hubbardKinetic
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun w _ => by ring

end LatticeSystem.Fermion
