import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSubspaces

/-!
# Tasaki §11.3.1: the `α`-Fock subspace lies in the `b̂`-kernel

One of the two inclusions of the uniqueness half of Theorem 11.11: every state of
the `α`-Fock subspace is annihilated by every `b̂_{u,σ}`, i.e.
`flatBandAlphaFockSubmodule ⊆ flatBandBKernelSubmodule`.

This is the *easy* direction.  Each `α`-band Slater state `(∏_q â†_q) |vac⟩` is
annihilated by `b̂_{u,σ}` because `b̂_{u,σ}` anticommutes with every `â†_{p,τ}`
(eq. (11.3.7), all spins) and annihilates the vacuum: move `b̂` rightward through
the ordered product to the vacuum.  (The hard reverse inclusion
`flatBandBKernelSubmodule ⊆ flatBandAlphaFockSubmodule` — no `β`-occupation forces
the state into the flat band — needs the Fock-space factorisation of the
non-orthogonal `{α} ∪ {β}` basis and is deferred.)

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, eq. (11.3.7).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`b̂_{u,σ}` annihilates every `α`-Slater state.**  Move `b̂_{u,σ}` rightward
through the ordered `â†` product using the anticommutation (11.3.7) `{b̂, â†} = 0`,
landing on `b̂_{u,σ} |vac⟩ = 0`. -/
theorem flatBandBAnnihilation_mulVec_alphaSlaterState (K : ℕ) (ν : ℝ) (u : Fin (K + 1))
    (σ : Fin 2) (qs : List (Fin (K + 1) × Fin 2)) :
    (flatBandBAnnihilation K ν u σ).mulVec (flatBandAlphaSlaterState K ν qs) = 0 := by
  unfold flatBandAlphaSlaterState
  induction qs with
  | nil =>
    simpa using flatBandBAnnihilation_mulVec_vacuum K ν u σ
  | cons q qs ih =>
    rw [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      eq_neg_of_add_eq_zero_left
        (flatBandBAnnihilation_ACreation_anticomm K ν u q.1 σ q.2),
      Matrix.neg_mul, Matrix.mul_assoc, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_zero, neg_zero]

/-- **`flatBandAlphaFockSubmodule ⊆ flatBandBKernelSubmodule`**: the `α`-Fock
subspace is contained in the common kernel of the `b̂` annihilations (the easy
inclusion of Tasaki's uniqueness argument). -/
theorem flatBandAlphaFockSubmodule_le_BKernelSubmodule (K : ℕ) (ν : ℝ) :
    flatBandAlphaFockSubmodule K ν ≤ flatBandBKernelSubmodule K ν := by
  rw [flatBandAlphaFockSubmodule, Submodule.span_le]
  rintro _ ⟨qs, rfl⟩
  rw [SetLike.mem_coe, mem_flatBandBKernelSubmodule_iff]
  exact fun u σ => flatBandBAnnihilation_mulVec_alphaSlaterState K ν u σ qs

end LatticeSystem.Fermion
