import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreProjection
import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.GroundSubspaceAtFilling
import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems

/-!
# Tasaki §11.5.2: the ferromagnetic t-J model (eq. (11.5.4)) and Proposition 11.24

The **ferromagnetic t-J model** (Tasaki §11.5.2, eq. (11.5.4)) is the strong-coupling
effective theory of the nearly-flat-band Hubbard model with electron number `N`
strictly below the number of sites `L = |E|`.  On the no-double-occupancy ("hard-core")
subspace `H_N^hc`, with projection `P̂hc`, it reads
`Ĥ_tJ = −τ P̂hc Σ_{⟨x,y⟩,σ} ĉ†_{x,σ} ĉ_{y,σ} + J Σ_{⟨x,y⟩} (n̂_x n̂_y / 4 − Ŝ_x · Ŝ_y)`,
with hopping amplitude `τ > 0` and ferromagnetic coupling `J > 0`.  Both sums run over
ordered nearest-neighbour pairs `(x, y)` with `|x − y| = 1` (the graph `G`), matching the
ordered-pair convention of `hubbardKineticOnGraph`; the hopping is sandwiched by `P̂hc`
to make it a Hermitian operator whose restriction to `H_N^hc` is Tasaki's `−τ P̂hc Σ ĉ†ĉ`.

**Proposition 11.24** (d = 1 ferromagnetism): for the one-dimensional *periodic* chain
(`SimpleGraph.cycleGraph`), if the electron number `N` is `< L` and **odd**, the ground
states lie in the maximal-spin (ferromagnetic) sector `S_tot = N/2`, non-degenerate apart
from the trivial `2 S_tot + 1 = N + 1`-fold `SU(2)` multiplet.  Tasaki's proof is a
Perron–Frobenius / "spin-charge separation" argument (the oddness of `N` is what makes the
`1 ↔ L` hop sign-free under periodic boundary conditions).  Since it is a complete but
nontrivial argument, it is recorded here as a documented axiom (to be discharged), matching
the policy for the other §11.x ferromagnetism theorems.

The conclusion is phrased on the **ground subspace at fixed electron number `N_e`**
(`groundSubmoduleAtFilling`, from `GroundSubspaceAtFilling`: the `H`-eigenspace at the ground
energy, intersected with the `N_e`-electron sector and the no-double-occupancy subspace
`H_{N_e}^hc` — the t-J Hamiltonian's physical domain).  The full statement — *ground spin
`S_tot = N_e/2`* **and**
*`(N_e + 1)`-fold degeneracy* — is captured at once by the shared
`IsMaximalSpinMultipletSubmodule` predicate (the same one used for Mielke's Theorem 11.13 and
the general flat-band Theorem 11.15).  The electron number must be fixed and the hard-core
constraint imposed because the maximal total spin `S_max = N_e/2` depends on `N_e` (unlike the
filling-agnostic §11.4 `exhibitsFerromagnetism`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, eq. (11.5.4) and Proposition 11.24 (pp. 442–444).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Per-site total number operator** `n̂_x = n̂_{x↑} + n̂_{x↓}` on the spinful
Jordan–Wigner backbone (the summand `ñ_p` of Tasaki eq. (11.5.4)). -/
noncomputable def fermionSiteNumber (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionUpNumber N i + fermionDownNumber N i

/-- **The ferromagnetic t-J Hamiltonian** (Tasaki §11.5.2, eq. (11.5.4)) on the graph `G`:
`Ĥ_tJ = −τ P̂hc (Σ_{⟨x,y⟩,σ} ĉ†_{x,σ} ĉ_{y,σ}) P̂hc + J Σ_{⟨x,y⟩} (n̂_x n̂_y / 4 − Ŝ_x · Ŝ_y)`.
The hopping is `hubbardKineticOnGraph N G 1` sandwiched by the hard-core projection
`hubbardHardcoreProjection N`; the exchange term is the per-bond
`(n̂_x n̂_y)/4 − Ŝ_x · Ŝ_y` summed over the ordered adjacent pairs of `G`.  Both `τ` and `J`
are positive in the physical (ferromagnetic) regime. -/
noncomputable def tJHamiltonian (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) : ManyBodyOp (Fin (2 * N + 2)) :=
  -(τ : ℂ) •
      (hubbardHardcoreProjection N * hubbardKineticOnGraph N G 1 *
        hubbardHardcoreProjection N)
    + (J : ℂ) • ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if G.Adj x y then
            (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
              fermionSpinDot N x y
          else 0)

/-- **Tasaki Proposition 11.24 (ferromagnetism in the d = 1 ferromagnetic t-J model),
AXIOM.**  On the one-dimensional periodic chain (`SimpleGraph.cycleGraph (N + 1)`), if the
electron number `Ne` satisfies `Ne < N + 1 = L` and is **odd**, then the ground states have
total spin `S_tot = Ne/2` and are non-degenerate apart from the trivial
`2 S_tot + 1 = Ne + 1`-fold `SU(2)` multiplet.  Both halves are captured at once by
`IsMaximalSpinMultipletSubmodule`: the `N_e`-electron hard-core ground subspace is the
`(Ne + 1)`-fold multiplet (degeneracy = `Ne + 1`) and every ground state is an `(Ŝ_tot)²`
eigenvector at the maximal eigenvalue `S_max(S_max + 1)`, `S_max = Ne/2`.  Tasaki's proof is
a Perron–Frobenius / spin-charge-separation argument (Theorem A.18); the oddness of `Ne`
makes the wrap-around `1 ↔ L` hop sign-free under periodic boundary conditions.  Recorded as
a documented axiom (to be discharged), matching the §11.x ferromagnetism policy. -/
axiom proposition_11_24 (N : ℕ) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J)
    (Ne : ℕ) (hNe : Ne < N + 1) (hodd : Odd Ne) :
    IsMaximalSpinMultipletSubmodule N
      (groundSubmoduleAtFilling (tJHamiltonian N (SimpleGraph.cycleGraph (N + 1)) τ J) Ne) Ne

end LatticeSystem.Fermion
