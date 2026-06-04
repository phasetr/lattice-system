import LatticeSystem.Fermion.JordanWigner.Hubbard

/-!
# Spinful fermion operators built from a single-particle coefficient vector

The recurring construction `Ĉ_σ(φ) = Σ_x φ(x) ĉ_{x,σ}` — the creation/annihilation operator
of a single-particle state `φ` over the physical sites — packaged once.  Tasaki's flat-band
(§11.3.1), nearly-flat-band (§11.4) and the §11.5 decorated models all build their `â`, `b̂`,
`d̂` operators this way; this file gives a generic helper so new models (the §11.5.3/§11.5.4
Tanaka–Tasaki models) need not respell the sum.

For a coefficient vector `φ : Fin (M+1) → ℂ` over the `M+1` physical sites and a spin
`σ : Fin 2`, the operators act on the spinful Jordan–Wigner backbone
`ManyBodyOp (Fin (2M+2))` at the spinful modes `spinfulIndex M x σ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §9.3.3 (the operator `Ĉ_σ(φ)`).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`Ĉ†_σ(φ) = Σ_x φ(x) ĉ†_{x,σ}`** — the creation operator of the single-particle state
`φ` (a coefficient vector over the `M+1` physical sites), at spin `σ`. -/
noncomputable def spinfulCreationFromVector (M : ℕ) (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * M + 2)) :=
  ∑ x : Fin (M + 1), φ x • fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)

/-- **`Ĉ_σ(φ) = Σ_x φ(x) ĉ_{x,σ}`** — the annihilation operator of the single-particle state
`φ`, at spin `σ`. -/
noncomputable def spinfulAnnihilationFromVector (M : ℕ) (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    ManyBodyOp (Fin (2 * M + 2)) :=
  ∑ x : Fin (M + 1), φ x • fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)

end LatticeSystem.Fermion
