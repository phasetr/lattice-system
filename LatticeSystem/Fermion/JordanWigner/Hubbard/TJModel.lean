import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreProjection
import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy

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

Because the maximal total spin at fixed electron number `N` (with no double occupancy) is
`S_max = N/2`, the statement is naturally phrased with the **filling-restricted**
ferromagnetism criterion `exhibitsFerromagnetismAtFilling` introduced here (the electron
number must be fixed — unlike the filling-agnostic `exhibitsFerromagnetism` of §11.4, which
suffices there because the flat-band filling is part of the model's setup).  This predicate
is reusable for the remaining §11.5 results (Theorems 11.26 / 11.27).

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

/-- The **charge-and-spin sector** `(N_e, S = twoS/2)`: unit vectors of `EuclideanSpace ℂ`
over the computational-basis configurations that are simultaneously `(Ŝ_tot)²`-eigenvectors
at `(twoS/2)(twoS/2 + 1)` and `N̂`-eigenvectors at the electron number `N_e`.  Refines
`spinSector` by additionally fixing the electron number, as required for the t-J model. -/
def chargeSpinSector (M Ne twoS : ℕ) :
    Set (EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2)) :=
  {φ | ‖φ‖ = 1 ∧
    (fermionTotalSpinSquared M).mulVec φ.ofLp
        = (((twoS : ℂ) / 2) * ((twoS : ℂ) / 2 + 1)) • φ.ofLp ∧
    (fermionTotalNumber (2 * M + 1)).mulVec φ.ofLp = (Ne : ℂ) • φ.ofLp}

/-- **`E_min(N_e, S)` — the minimum energy in the fixed-electron-number, total-spin-`S`
sector** (the t-J analogue of `sectorMinEnergy`, additionally constraining the electron
number `N_e`): the infimum of `rayleighOnVec H` over the unit vectors of
`chargeSpinSector M Ne twoS`. -/
noncomputable def sectorMinEnergyAtFilling {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne twoS : ℕ) : ℝ :=
  ⨅ φ : chargeSpinSector M Ne twoS, rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp

/-- **Ferromagnetism at fixed filling `N_e`**: at electron number `N_e` the maximal-spin
sector `S_max = twoSmax/2` lies strictly below every other sector,
`E_min(N_e, S_max) < E_min(N_e, S)` for all `S ≠ S_max`.  The filling-fixed counterpart of
`exhibitsFerromagnetism`, needed when (as in the t-J model) the maximal total spin depends
on the electron number. -/
def exhibitsFerromagnetismAtFilling {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne twoSmax : ℕ) : Prop :=
  ∀ twoS : ℕ, twoS < twoSmax →
    sectorMinEnergyAtFilling H Ne twoSmax < sectorMinEnergyAtFilling H Ne twoS

/-- **Tasaki Proposition 11.24 (ferromagnetism in the d = 1 ferromagnetic t-J model),
AXIOM.**  On the one-dimensional periodic chain (`SimpleGraph.cycleGraph (N + 1)`), if the
electron number `Ne` satisfies `Ne < N + 1 = L` and is **odd**, then the ground states have
total spin `S_tot = Ne/2` and are non-degenerate apart from the trivial
`2 S_tot + 1 = Ne + 1`-fold `SU(2)` multiplet — i.e. the model exhibits ferromagnetism at
filling `Ne` with maximal spin `S_max = Ne/2` (`twoSmax = Ne`).  Tasaki's proof is a
Perron–Frobenius / spin-charge-separation argument (Theorem A.18); the oddness of `Ne` makes
the wrap-around `1 ↔ L` hop sign-free under periodic boundary conditions.  Recorded as a
documented axiom (to be discharged), matching the §11.x ferromagnetism policy. -/
axiom proposition_11_24 (N : ℕ) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J)
    (Ne : ℕ) (hNe : Ne < N + 1) (hodd : Odd Ne) :
    exhibitsFerromagnetismAtFilling
      (tJHamiltonian N (SimpleGraph.cycleGraph (N + 1)) τ J) Ne Ne

end LatticeSystem.Fermion
