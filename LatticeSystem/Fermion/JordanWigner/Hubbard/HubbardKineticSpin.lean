import LatticeSystem.Fermion.JordanWigner.Hubbard

/-!
# Spin-resolved tight-binding kinetic operator (Tasaki §11.1.1)

The spinful kinetic operator `Ĥ_kin = Σ_σ Σ_{i,j} t_{ij} ĉ†_{iσ}ĉ_{jσ}` is a sum over the two
spin species of independent single-species hopping operators.  This module names that fiber,
`Ĥ^σ = Σ_{i,j} t_{ij} ĉ†_{iσ}ĉ_{jσ}` (`hubbardKineticSpin`), and records the two forms of the
decomposition `Ĥ_kin = Σ_σ Ĥ^σ = Ĥ^↑ + Ĥ^↓`.

The spin-resolved form is what carries the variational argument for the low-density impossibility
theorem: the up and down fibers of a spin-flipped trial state are estimated by different means (an
exact canonical-anticommutation identity for the majority spin, an operator bound `Ĥ^σ ≤ ε_max N̂_σ`
for the minority spin), which the aggregate operator cannot express.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.8)–(11.1.10), p. 376; the underlying argument is
Tasaki, Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, Appendix F, pp. 545–547.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

open scoped BigOperators

/-- The spin-`σ` fiber of the spinful tight-binding kinetic operator:
`Ĥ^σ = Σ_{i,j} t_{ij} ĉ†_{iσ}ĉ_{jσ}`, the single-species hopping of the electrons carrying spin
label `σ`. -/
noncomputable def hubbardKineticSpin (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    t i j • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))

/-- **The kinetic operator is the spin sum of its fibers**: `Ĥ_kin = Σ_σ Ĥ^σ`.  The spin sum is
the outermost layer of `hubbardKinetic`, so this holds definitionally. -/
theorem hubbardKinetic_eq_sum_hubbardKineticSpin (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    hubbardKinetic N t = ∑ σ : Fin 2, hubbardKineticSpin N t σ := rfl

/-- **The kinetic operator splits into its up and down fibers**: `Ĥ_kin = Ĥ^↑ + Ĥ^↓`, the two-term
form of the spin sum. -/
theorem hubbardKinetic_eq_hubbardKineticSpin_add (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    hubbardKinetic N t = hubbardKineticSpin N t 0 + hubbardKineticSpin N t 1 := by
  rw [hubbardKinetic_eq_sum_hubbardKineticSpin, Fin.sum_univ_two]

end LatticeSystem.Fermion
