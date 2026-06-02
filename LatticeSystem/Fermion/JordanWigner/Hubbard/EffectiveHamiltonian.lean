import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreBasis

/-!
# Hubbard effective Hamiltonian on the hard-core sector

This file continues the Tasaki §11.2 Nagaoka-ferromagnetism infrastructure.
It defines the effective Hamiltonian of the infinite-`U` / one-hole Nagaoka
sector as the hard-core compression

  `Ĥ_eff = P̂_hc · H · P̂_hc`

of the full Hubbard Hamiltonian `H = H_hop + H_int`, and establishes its basic
structural properties.

The key reduction is the `U ↑ ∞` projection statement: on a hard-core vector
the on-site interaction `H_int` vanishes and `P̂_hc` acts as the identity, so
the effective Hamiltonian reduces to the projected hopping
`Ĥ_eff ψ = P̂_hc (H_hop ψ)`. The explicit hopping matrix elements
(Tasaki eq. (11.2.5)) — which carry Jordan–Wigner fermion signs — are built in
a follow-up layer on top of this reduction.

Tracked in Issue #4130. References: Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st edition, §11.2, pp. 381-388; this file
formalizes unnumbered effective-Hamiltonian infrastructure used before
Theorems 11.5 and 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## The effective Hamiltonian -/

/-- The Hubbard effective Hamiltonian on the hard-core sector: the
compression `Ĥ_eff = P̂_hc · H · P̂_hc` of the full Hubbard Hamiltonian by the
hard-core projection. -/
noncomputable def hubbardEffectiveHamiltonian (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardHardcoreProjection N * hubbardHamiltonian N t U *
    hubbardHardcoreProjection N

/-- The effective Hamiltonian is Hermitian when the hopping matrix `t` is
Hermitian (`star (t i j) = t j i`) and the coupling `U` is real. It is the
compression of a Hermitian operator by the Hermitian projection `P̂_hc`. -/
theorem hubbardEffectiveHamiltonian_isHermitian
    (N : ℕ) {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    (hubbardEffectiveHamiltonian N t U).IsHermitian := by
  have hP : (hubbardHardcoreProjection N)ᴴ = hubbardHardcoreProjection N :=
    (hubbardHardcoreProjection_isHermitian N).eq
  have h := Matrix.isHermitian_conjTranspose_mul_mul
    (A := hubbardHamiltonian N t U) (hubbardHardcoreProjection N)
    (hubbardHamiltonian_isHermitian N ht hU)
  rwa [hP] at h

/-! ## Reduction to the projected hopping on the hard-core sector -/

/-- The `U ↑ ∞` reduction: on a hard-core vector the effective Hamiltonian
acts as the projected hopping, `Ĥ_eff ψ = P̂_hc (H_hop ψ)`. The on-site
interaction `H_int` annihilates the hard-core vector and the inner `P̂_hc`
fixes it, leaving only the projected kinetic term. -/
theorem hubbardEffectiveHamiltonian_mulVec_eq_projected_kinetic_of_mem
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ hubbardHardcoreSubspace N) :
    (hubbardEffectiveHamiltonian N t U).mulVec ψ =
      (hubbardHardcoreProjection N).mulVec ((hubbardKinetic N t).mulVec ψ) := by
  unfold hubbardEffectiveHamiltonian hubbardHamiltonian
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hubbardHardcoreProjection_mulVec_eq_self_of_mem N hψ, Matrix.add_mulVec,
    hubbardOnSiteInteraction_mulVec_eq_zero_of_mem_hardcore N U hψ, add_zero]

/-- The effective Hamiltonian maps every vector into the hard-core subspace:
its outermost factor is the hard-core projection. -/
theorem hubbardEffectiveHamiltonian_mulVec_mem
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (hubbardEffectiveHamiltonian N t U).mulVec ψ ∈ hubbardHardcoreSubspace N := by
  unfold hubbardEffectiveHamiltonian
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  exact hubbardHardcoreProjection_mulVec_mem N _

/-- The hard-core projection fixes every vector in the range of the effective
Hamiltonian: `P̂_hc (Ĥ_eff ψ) = Ĥ_eff ψ`. -/
theorem hubbardHardcoreProjection_mulVec_effectiveHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (hubbardHardcoreProjection N).mulVec
        ((hubbardEffectiveHamiltonian N t U).mulVec ψ) =
      (hubbardEffectiveHamiltonian N t U).mulVec ψ :=
  hubbardHardcoreProjection_mulVec_eq_self_of_mem N
    (hubbardEffectiveHamiltonian_mulVec_mem N t U ψ)

end LatticeSystem.Fermion
