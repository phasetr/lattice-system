import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHamiltonianHermitian

/-!
# SU(2) invariance of the attractive Hubbard Hamiltonian (Tasaki §10.2)

The attractive Hubbard Hamiltonian
`Ĥ = Ĥhop + (−Σ_x U_x n̂_{x,↑} n̂_{x,↓})` (Tasaki §10.2.1, eqs.
(10.2.1)/(10.2.2)) has the same `SU(2)` spin-rotation invariance as the
canonical Hubbard model of §9.3.3: the total spin operators
`Ŝ⁺_tot`, `Ŝ⁻_tot`, `Ŝ³_tot` and the Casimir `(Ŝ_tot)²` all commute
with `Ĥ`.

The §9.3.3 building blocks are stated for a **generic complex hopping**
and a **per-site** interaction commutator, so they apply verbatim to
`attractiveHubbardHamiltonian`.  The only genuinely new ingredient is the
site-dependent-coefficient interaction commute: `Ŝ` commutes with each
site term `U_x n̂_{x,↑} n̂_{x,↓}` regardless of the scalar `U_x`, so the
scalar-`U` proofs of §9.3.3 clone directly to the
`hubbardOnSiteInteractionSite` sum.

## Main results

* `fermionTotalSpinPlus_commute_hubbardOnSiteInteractionSite`,
  `fermionTotalUpNumber_commute_hubbardOnSiteInteractionSite`,
  `fermionTotalDownNumber_commute_hubbardOnSiteInteractionSite` — the
  site-dependent-`U` interaction commutes with `Ŝ⁺`, `N̂_↑`, `N̂_↓`.
* `fermionTotalSpinPlus_commute_attractiveHubbardHamiltonian`,
  `fermionTotalSpinMinus_commute_attractiveHubbardHamiltonian`,
  `fermionTotalSpinZ_commute_attractiveHubbardHamiltonian` — the three
  `SU(2)` generators commute with `Ĥ`.
* `fermionTotalSpinSquared_commute_attractiveHubbardHamiltonian` —
  `[Ĥ, (Ŝ_tot)²] = 0` (the headline `SU(2)`-invariance statement).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer 2020, §9.3.3, p. 333 (eq. (9.3.35));
§10.2.1, pp. 348–349; §11.1.1, p. 372.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- `[Ŝ⁺_tot, Σ_x U_x n̂_{x,↑} n̂_{x,↓}] = 0`: the site-dependent-`U`
analogue of `fermionTotalSpinPlus_commute_hubbardOnSiteInteraction`
(Tasaki §9.3.3, p. 333).  Each site summand carries the scalar `U x`,
which factors out of the per-site commutator
`fermionSpinPlusTerm_commute_interactionTerm`. -/
theorem fermionTotalSpinPlus_commute_hubbardOnSiteInteractionSite
    (N : ℕ) (U : Fin (N + 1) → ℂ) :
    Commute (fermionTotalSpinPlus N) (hubbardOnSiteInteractionSite N U) := by
  unfold hubbardOnSiteInteractionSite fermionTotalSpinPlus
  apply Commute.sum_right
  intro x _
  apply Commute.smul_right _ (U x)
  exact (Commute.sum_right _ _ _ (fun k _ =>
    (fermionSpinPlusTerm_commute_interactionTerm N k x).symm)).symm

/-- `[N̂_↑, Σ_x U_x n̂_{x,↑} n̂_{x,↓}] = 0`: the site-dependent-`U`
analogue of `fermionTotalUpNumber_commute_hubbardOnSiteInteraction`.
All summands are products of pairwise commuting number operators. -/
theorem fermionTotalUpNumber_commute_hubbardOnSiteInteractionSite
    (N : ℕ) (U : Fin (N + 1) → ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardOnSiteInteractionSite N U) := by
  unfold fermionTotalUpNumber hubbardOnSiteInteractionSite
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ (U i)
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `[N̂_↓, Σ_x U_x n̂_{x,↑} n̂_{x,↓}] = 0`: the site-dependent-`U`
analogue of `fermionTotalDownNumber_commute_hubbardOnSiteInteraction`. -/
theorem fermionTotalDownNumber_commute_hubbardOnSiteInteractionSite
    (N : ℕ) (U : Fin (N + 1) → ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardOnSiteInteractionSite N U) := by
  unfold fermionTotalDownNumber hubbardOnSiteInteractionSite
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ (U i)
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 1)

end LatticeSystem.Fermion
