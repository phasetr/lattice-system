import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Lieb's theorem for the repulsive Hubbard model at half-filling (Tasaki §10.2.2, Theorem 10.4)

This file formalizes the statement of **Tasaki Theorem 10.4** (Lieb's
theorem for the repulsive Hubbard model at half-filling), from Hal Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 350.

For a **bipartite** real symmetric connected hopping matrix `T`
(`Λ = A ⊔ B`, hopping only across the sublattices) and a repulsive on-site
interaction — either the uniform form `Ĥint = U Σ_x n̂_{x,↑} n̂_{x,↓}`
(`U > 0`, eq. (10.2.5)) or the symmetric form
`Ĥint = Σ_x U_x (n̂_{x,↑} − ½)(n̂_{x,↓} − ½)` (`U_x > 0`, eq. (10.2.6)) — at
half-filling `N = |Λ|`, every ground state has total spin
`S_tot = ||A| − |B||/2`, and the ground states are exactly
`2 S_tot + 1 = |A| − |B| + 1` fold degenerate (the unavoidable SU(2)
multiplet degeneracy).

## Status

Theorem 10.4 is proved by Lieb's spin-space reflection-positivity method
(via the Shiba transformation from the attractive case, Theorem 10.2); per
the project policy this deep result is recorded as a faithful documented
`axiom`, built on concrete repulsive Hubbard Hamiltonians. The model
hypotheses are packaged in `IsLiebRepulsiveModel`, reused by the
correlation theorems (10.5, 10.6) in follow-up files.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The complement sublattice `B = Aᶜ` of a bipartition `Λ = A ⊔ B`. -/
def bipartitionComplement (A : Finset (Fin (N + 1))) : Finset (Fin (N + 1)) :=
  Finset.univ.filter fun x => x ∉ A

/-- The hopping matrix `T` respects the bipartition `A ⊔ Aᶜ`: a nonzero
amplitude `T x y` connects only sites in different sublattices. -/
def HoppingRespectsBipartition (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Prop :=
  ∀ ⦃x y⦄, T x y ≠ 0 → (x ∈ A ↔ y ∉ A)

/-- The sublattice imbalance `||A| − |B||` as a natural number. -/
noncomputable def sublatticeImbalance (A : Finset (Fin (N + 1))) : ℕ :=
  Int.natAbs ((A.card : ℤ) - ((bipartitionComplement A).card : ℤ))

/-- The Casimir eigenvalue `S₀ (S₀ + 1)` of the total-spin operator at
`S₀ = ||A| − |B||/2` (Tasaki's ground-state total spin in Theorem 10.4). -/
noncomputable def liebRepulsiveSpinCasimir (A : Finset (Fin (N + 1))) : ℂ :=
  ((sublatticeImbalance A : ℂ) / 2) * ((sublatticeImbalance A : ℂ) / 2 + 1)

/-- The trivial SU(2)-multiplet ground-state degeneracy
`2 S₀ + 1 = |A| − |B| + 1`. -/
noncomputable def liebRepulsiveGroundMultiplicity (A : Finset (Fin (N + 1))) : ℕ :=
  sublatticeImbalance A + 1

/-- The **uniform repulsive Hubbard Hamiltonian** `Ĥ = Ĥhop + U Σ_x n̂↑n̂↓`
(Tasaki eq. (10.2.5)), with `U > 0`. -/
noncomputable def repulsiveHubbardHamiltonian (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (fun x y => (T x y : ℂ)) +
    hubbardOnSiteInteractionSite N (fun _ => (U : ℂ))

/-- The **symmetric repulsive interaction**
`Σ_x U_x (n̂_{x,↑} − ½)(n̂_{x,↓} − ½)` (Tasaki eq. (10.2.6)). -/
noncomputable def symmetricRepulsiveHubbardInteraction (N : ℕ)
    (U : Fin (N + 1) → ℝ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), (U x : ℂ) •
    ((fermionUpNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))) *
      (fermionDownNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))))

/-- The **symmetric repulsive Hubbard Hamiltonian** `Ĥ = Ĥhop + Ĥint`
with the symmetric interaction (Tasaki eq. (10.2.6)). -/
noncomputable def symmetricRepulsiveHubbardHamiltonian (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (fun x y => (T x y : ℂ)) +
    symmetricRepulsiveHubbardInteraction N U

/-- The fixed-electron-number ground subspace of `H` at energy `E`: the
intersection of the `E`-eigenspace with the `Ne`-electron sector (no
hard-core constraint — double occupancy is allowed). -/
noncomputable def hubbardGroundSubmoduleAtElectronNumber
    (H : ManyBodyOp (Fin (2 * N + 2))) (E : ℂ) (Ne : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace H.mulVecLin E ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ)

/-- `H` is one of the two repulsive Hubbard Hamiltonians of Theorem 10.4:
the uniform form (`U > 0`, eq. (10.2.5)) or the symmetric form
(`U_x > 0`, eq. (10.2.6)). -/
def IsLiebRepulsiveHamiltonian (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2))) : Prop :=
  (∃ U : ℝ, 0 < U ∧ H = repulsiveHubbardHamiltonian N T U) ∨
    (∃ U : Fin (N + 1) → ℝ, (∀ x, 0 < U x) ∧
      H = symmetricRepulsiveHubbardHamiltonian N T U)

/-- The packaged hypotheses of Tasaki's repulsive-Hubbard theorems
(10.4/10.5/10.6): a bipartition `A`, a real symmetric hopping matrix `T`
respecting it whose support graph is connected, and a repulsive
Hamiltonian `H` (uniform or symmetric form). -/
structure IsLiebRepulsiveModel (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2))) : Prop where
  /-- `T` is symmetric. -/
  symm : ∀ x y, T x y = T y x
  /-- `T` respects the bipartition (hops only across sublattices). -/
  bipartite : HoppingRespectsBipartition A T
  /-- The hopping support graph is connected. -/
  connected : (hoppingSupportGraph T).Preconnected
  /-- `H` is a repulsive Hubbard Hamiltonian (uniform or symmetric form). -/
  hamiltonian : IsLiebRepulsiveHamiltonian T H

/-- **Tasaki Theorem 10.4** (Lieb's theorem for the repulsive Hubbard model
at half-filling, 1st ed., Springer 2020, §10.2.2, p. 350, **AXIOM**). For a
bipartite real symmetric connected hopping matrix `T` and a repulsive
Hubbard Hamiltonian `H` (uniform or symmetric form), at half-filling
`N = |Λ|` (electron number `N + 1` on `Fin (N + 1)` sites), there is a
ground energy `E₀` whose `(N+1)`-electron ground subspace `G` is nonzero,
minimal in energy, consists entirely of total-spin `S₀ = ||A| − |B||/2`
states (Casimir eigenvalue `S₀(S₀+1)`), and has dimension exactly
`|A| − |B| + 1` (the unavoidable SU(2) multiplet degeneracy).

Proved by Lieb's spin-space reflection-positivity method (via the Shiba
transformation from the attractive case); recorded as a faithful documented
axiom. -/
axiom theorem_10_4_lieb_repulsive_half_filling
    (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2)))
    (hModel : IsLiebRepulsiveModel A T H) :
    ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A

end LatticeSystem.Fermion
