import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingMaximalSpin
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJProposition1124

/-!
# Tasaki 11.5: the d=1 ferromagnetic t-J ground subspace is the maximal-spin multiplet (all `Ne`)

Combining the metallic case (`proposition_11_24`, `Ne < K+1`) with the half-filling case
(`tJ_halfFilling_isMaximalSpinMultiplet`, `Ne = K+1`) gives the t-J side of Theorem 11.26 for every
admissible electron number:

* `tJ_isMaximalSpinMultiplet_of_le` — for odd `Ne ≤ K+1`, the d=1 ferromagnetic t-J ground subspace
  on `cycleGraph (K+1)` is the maximal-spin `(Ne+1)`-fold multiplet.

This is the t-J input to the discharge of `theorem_11_26` (via the strong-coupling equivalence
`lemma_11_25`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2–11.5.3, Proposition 11.24 + Theorem 11.26 (pp. 443–447).
-/

namespace LatticeSystem.Fermion

open LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-- **The d=1 ferromagnetic t-J ground subspace is the maximal-spin multiplet for all `Ne ≤ K+1`.**
For odd `Ne ≤ K+1` and `τ, J > 0`, the ground subspace of `tJHamiltonian K (cycleGraph (K+1)) τ J` at
filling `Ne` is `IsMaximalSpinMultipletSubmodule K · Ne` — the metallic case `Ne < K+1`
(`proposition_11_24`) and the half-filling case `Ne = K+1` (`tJ_halfFilling_isMaximalSpinMultiplet`)
combined. -/
theorem tJ_isMaximalSpinMultiplet_of_le (K : ℕ) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J)
    (Ne : ℕ) (hNe : Ne ≤ K + 1) (hodd : Odd Ne) :
    IsMaximalSpinMultipletSubmodule K
      (groundSubmoduleAtFilling (tJHamiltonian K (cycleGraph (K + 1)) τ J) Ne) Ne := by
  rcases lt_or_eq_of_le hNe with hlt | heq
  · exact proposition_11_24 K τ J hτ hJ Ne hlt hodd
  · subst heq
    exact tJ_halfFilling_isMaximalSpinMultiplet τ J hJ

end LatticeSystem.Fermion
