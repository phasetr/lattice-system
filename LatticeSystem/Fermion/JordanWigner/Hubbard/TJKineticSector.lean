import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis

/-!
# Tasaki 11.5: the t-J kinetic term on the hard-core sector basis (Prop 11.24 PR-B3)

The kinetic part of the t-J Hamiltonian is the graph hopping sandwiched by the hard-core projection,
`P̂hc · K · P̂hc`.  On a hard-core sector basis state `|Φ_s⟩ = basisVec (tJConfigOf s)` the *inner*
projection acts as the identity (`tJConfigOf` is hard-core), so the sandwich reduces to the
projected
hopping `P̂hc (K |Φ_s⟩)`, which still lands in the hard-core subspace.  This isolates the hopping
matrix elements (computed sign-free in the hop lemmas) from the projection bookkeeping.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- **Kinetic sandwich reduction on the sector basis.**  Since `tJConfigOf s` is hard-core, the
inner hard-core projection fixes `|Φ_s⟩`, so `P̂hc · K · P̂hc |Φ_s⟩ = P̂hc (K |Φ_s⟩)`. -/
theorem tJKinetic_sandwich_mulVec_tJConfigOf (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (s : Fin (N + 1) → Fin 3) :
    (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 * hubbardHardcoreProjection N).mulVec
        (basisVec (tJConfigOf N s))
      = (hubbardHardcoreProjection N).mulVec
          ((hubbardKineticOnGraph N G 1).mulVec (basisVec (tJConfigOf N s))) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hubbardHardcoreProjection_mulVec_eq_self_of_mem N (tJConfigOf_mem_hardcore N s)]

/-- The projected kinetic action lands in the hard-core subspace (its outer factor is `P̂hc`). -/
theorem tJKinetic_sandwich_mulVec_mem (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (s : Fin (N + 1) → Fin 3) :
    (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 * hubbardHardcoreProjection N).mulVec
        (basisVec (tJConfigOf N s)) ∈ hubbardHardcoreSubspace N := by
  rw [tJKinetic_sandwich_mulVec_tJConfigOf]
  exact hubbardHardcoreProjection_mulVec_mem N _

end LatticeSystem.Fermion
