import LatticeSystem.Fermion.JordanWigner.String
import LatticeSystem.Fermion.JordanWigner.StringBasisVecAction
import LatticeSystem.Fermion.JordanWigner.AnnihilationCreationBasisVec
import LatticeSystem.Fermion.JordanWigner.VacuumCreationBasisVec
import LatticeSystem.Fermion.JordanWigner.HopBasisVec
import LatticeSystem.Fermion.JordanWigner.Operators
import LatticeSystem.Fermion.JordanWigner.CAR
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe
import LatticeSystem.Fermion.JordanWigner.Number
import LatticeSystem.Fermion.JordanWigner.NumberAnticommutators
import LatticeSystem.Fermion.JordanWigner.NumberPow
import LatticeSystem.Fermion.JordanWigner.CDaggerCCommutator
import LatticeSystem.Fermion.JordanWigner.CDaggerCIdentity
import LatticeSystem.Fermion.JordanWigner.CDaggerCProjection
import LatticeSystem.Fermion.JordanWigner.CDaggerCHermitian
import LatticeSystem.Fermion.JordanWigner.ProjectionsOrthogonal
import LatticeSystem.Fermion.JordanWigner.ProjectionsCommute
import LatticeSystem.Fermion.JordanWigner.AnnihilationNumberIdentities
import LatticeSystem.Fermion.JordanWigner.CreationNumberIdentities
import LatticeSystem.Fermion.JordanWigner.PartialIsometry
import LatticeSystem.Fermion.JordanWigner.HoleProjectionsCommute
import LatticeSystem.Fermion.JordanWigner.HoleProjectionCommuteLadder
import LatticeSystem.Fermion.JordanWigner.HoleProjectionCommuteNumber
import LatticeSystem.Fermion.JordanWigner.CDaggerCLadderZero
import LatticeSystem.Fermion.JordanWigner.Hubbard
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges
import LatticeSystem.Fermion.JordanWigner.Hubbard.Graph
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllDownState
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllDownStateTotalNumber
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinTotHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSubspace
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreProjection
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSpan
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopConfig
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopMatrixElement
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonian
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianSpinSymmetry
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaoka
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundState
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaMagnetizationSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaPerronFrobenius
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivityClassification
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandCAR
import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyProjection
import LatticeSystem.Fermion.JordanWigner.Hubbard.DoubleOccupancyCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulNumberHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SitePartitionIdentity
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsIdempotent
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsDoublyEmpty
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsUpDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsEmptySingle
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsSingleDoubly
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsSpinResolved
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsPow
import LatticeSystem.Fermion.JordanWigner.Hubbard.EmptyProjectionCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.SingleProjectionsCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.UpDownProjectionCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.RemainingProjectionCommutes
import LatticeSystem.Fermion.JordanWigner.CPlusCDaggerSq
import LatticeSystem.Fermion.JordanWigner.CMinusCDaggerSq
import LatticeSystem.Fermion.JordanWigner.CPlusMinusCDaggerPauli
import LatticeSystem.Fermion.JordanWigner.OneSubTwoNumberSq
import LatticeSystem.Fermion.JordanWigner.CPlusCDaggerAnticomm
import LatticeSystem.Fermion.JordanWigner.CMinusCDaggerAnticomm
import LatticeSystem.Fermion.JordanWigner.NumberCommutePauliOfNe

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Multi-mode fermion via Jordan–Wigner mapping

**Façade module** re-exporting the full Jordan–Wigner machinery.
Following the refactor plan v4 §3.1 (Phase 2 PR 10–14), this file
is a thin re-import of the sub-files under
`LatticeSystem/Fermion/JordanWigner/` (originally five core
files; further extended with single-mode-mirror and Hubbard
algebra lemmas during the 2026-05-04 autonomous fermion
expansion):

| sub-file | content |
|---|---|
| `String.lean` | JW string fundamentals |
| `Operators.lean` | multi-mode `c_i`, `c_i†`, on-site CAR, hermiticity, number op |
| `CAR.lean` | full canonical anticommutation (same-site + cross-site, factorisations) |
| `CAR/CrossSiteOfNe.lean` | symmetric `_of_ne` cross-site CAR (4 lemmas) |
| `Number.lean` | number commutators, Hubbard skeleton, fermion vacuum |
| `NumberAnticommutators.lean` | same-site `{n_i, c_i}`, `{n_i, c_i†}` anticommutators |
| `NumberPow.lean` | `n_i^(k+1) = n_i` (idempotent projection power) |
| `CDaggerCCommutator.lean` | same-site `[c_i, c_i†] = 1 − 2·n_i` |
| `CDaggerCIdentity.lean` | same-site `c_i · c_i† = 1 − n_i`, `n_i + c_i · c_i† = 1` |
| `CDaggerCProjection.lean` | hole-projection idempotency `(c_i · c_i†)² = c_i · c_i†` + powers |
| `CDaggerCHermitian.lean` | hole projection Hermitian `(c_i · c_i†)ᴴ = c_i · c_i†` |
| `ProjectionsOrthogonal.lean` | `n_i · (c_i · c_i†) = 0`, `(c_i · c_i†) · n_i = 0` |
| `ProjectionsCommute.lean` | `Commute n_i (c_i · c_i†)` (both products zero) |
| `AnnihilationNumberIdentities.lean` | `n_i · c_i = 0`, `c_i · n_i = c_i` |
| `CreationNumberIdentities.lean` | `c_i† · n_i = 0`, `n_i · c_i† = c_i†` |
| `PartialIsometry.lean` | `c_i · c_i† · c_i = c_i`, `c_i† · c_i · c_i† = c_i†` |
| `HoleProjectionsCommute.lean` | `Commute (c_i · c_i†) (c_j · c_j†)` for any `i, j` |
| `HoleProjectionCommuteLadder.lean` | `Commute (c_i · c_i†) c_j` and `…c_j†` for `i ≠ j` |
| `HoleProjectionCommuteNumber.lean` | `Commute (c_i · c_i†) n_j` for any `i, j` |
| `CDaggerCLadderZero.lean` | `c_i · (c_i · c_i†) = 0`, `(c_i · c_i†) · c_i† = 0` |
| `Hubbard.lean` | spinful wrappers, on-graph Hubbard, 1D open / periodic chain Gibbs |
| `Hubbard/Charges.lean` | `N_↑`, `N_↓`, `S^z_tot`, vacuum eigenstates, cross-spin commutes |
| `Hubbard/Graph.lean` | graph-centric wrappers, chain/cycle Hamiltonians + Gibbs families |
| `Hubbard/SpinSymmetry.lean` | U(1)×U(1) charges + S^z_tot commutation with H (Tasaki §9.3.3) |
| `Hubbard/AllUpState.lean` | all-up state: H_kin eigenvalue, no double occupancy |
| `Hubbard/AllDownState.lean` | all-down state: `H_int · |↓..⟩ = 0` (mirror) |
| `Hubbard/AllDownStateTotalNumber.lean` | `N_↓ · |↓..⟩ = (N+1)·|↓..⟩`, `S^z·|↓..⟩ = -(N+1)/2·|↓..⟩` |
| `Hubbard/SpinTotHermitian.lean` | `(Ŝ^-)ᴴ = Ŝ^+`, `(Ŝ^z)`/`(Ŝ²)` Hermitian |
| `Hubbard/SaturatedFerromagnetism.lean` | spin Casimir, Def 11.1, SU(2) algebra |
| `Hubbard/HardcoreSubspace.lean` | hard-core subspace + `H_int` vanishing (Tasaki §11.2) |
| `Hubbard/HardcoreProjection.lean` | hard-core projection `∏ᵢ (1 - n_↑n_↓)` (Tasaki §11.2) |
| `Hubbard/HardcoreBasis.lean` | one-hole hard-core basis states `\|Φ_{x,σ}⟩` (Tasaki §11.2) |
| `Hubbard/HardcoreSpan.lean` | one-hole hard-core sector spanned by the basis states (Tasaki §11.2 fn. 8) |
| `Hubbard/EffectiveHamiltonian.lean` | effective Hamiltonian `Ĥ_eff = P̂_hc H P̂_hc` + `U→∞` reduction (Tasaki §11.2) |
| `Hubbard/TasakiBasis.lean` | Tasaki ordered-creation basis `\|Φ_{x,σ}⟩ = ε • basisVec` + orthonormality (Tasaki §11.2 eq. (11.2.3)) |
| `Hubbard/TasakiHopAction.lean` | uniform-sign hole-filling action `ĉ†_{x,s}ĉ_{z,s}\|Φ_{x,σ}⟩ = -\|Φ_{z,σ_{z→x}}⟩` + sign `ε = (-1)^x` (Tasaki §11.2 eq. (11.2.4)) |
| `Hubbard/EffectiveHamiltonianMatrix.lean` | off-diagonal matrix element `⟨Φ_{y,τ}\|Ĥ_eff\|Φ_{x,σ}⟩ = -t_{x,y}·[τ=σ_{y→x}]` (Tasaki §11.2 eq. (11.2.5)) |
| `Hubbard/WeakNagaoka.lean` | Cauchy–Schwarz energy bound `⟨Φ_↑\|Ĥ_eff\|Φ_↑⟩ ≤ ⟨Φ\|Ĥ_eff\|Φ⟩` (Tasaki §11.2 eq. (11.2.9)) |
| `Hubbard/EffectiveHamiltonianSpinSymmetry.lean` | SU(2) symmetry of the effective Hamiltonian `[Ĥ_eff, Ŝ^±_tot] = 0` (Tasaki §11.2, degeneracy backbone) |
| `Hubbard/WeakNagaokaTheorem.lean` | weak Nagaoka spin multiplet `weakNagaoka_spinMultiplet`: a ferromagnetic GS generates `N+1` degenerate ground states with `S_tot=S_max` via the SU(2) ladder (Tasaki §11.2.1, Theorem 11.5) |
| `Hubbard/WeakNagaokaGroundState.lean` | **Tasaki Theorem 11.5** `weakNagaoka_theorem_11_5`: existence of the ferromagnetic ground multiplet via the all-up block `M_↑ = ` Tasaki matrix of `Ĥ_eff`; operator lift `Ĥ_eff Φ_p = Σ_q ⟨Φ_q\|Ĥ_eff\|Φ_p⟩ Φ_q`, sector completeness, `N+1 = 2S_max+1` linearly independent degenerate eigenvectors with `S_tot=S_max` (Tasaki §11.2.1) |
| `Hubbard/WeakNagaokaGlobalMin.lean` | **Tasaki Theorem 11.5 global form** `weakNagaoka_theorem_11_5_global`: `min(M_↑) = min(M)` via the Schwarz bound (11.2.9) ferromagnetization (real Tasaki matrix + real min eigenvector), so the multiplet sits at the **global** one-hole ground energy — genuine ground states (Tasaki §11.2.1) |
| `Hubbard/NagaokaMagnetizationSector.lean` | **Tasaki §11.2.2 foundations**: the `S_z^{(3)}` magnetization grading (`configMag`/`holeSpinMag`), block-diagonality of `M`, sector matrices (`HoleMagSector`, `tasakiEffReMatrixOnSector`, `nagaokaPFMatrixOnSector`), **Definition 11.6** (`nagaokaConnectivity`), and the per-sector Perron–Frobenius non-degenerate ground state |
| `Hubbard/NagaokaPerronFrobenius.lean` | **Tasaki §11.2.2 upper bound**: sector min `= −μ` (Collatz–Wielandt), `min M ≤ min M_m`, per-sector `finrank ≤ 1` at the global min, and `tasakiEffMatrix_ground_finrank_le_N_add_one` (`≤ N+1`) |
| `Hubbard/NagaokaConnectivity.lean` | **Tasaki Theorem 11.7** `nagaoka_theorem_11_7` / `nagaoka_theorem_11_7_degeneracy`: the capstone — coefficient↔full bridge + SU(2) spin-multiplet lower bound (`≥ N+1`); with the connectivity condition and `t≥0`, the one-hole ground eigenspace is `(N+1)`-dimensional and every ground state has `S_tot=S_max` — Nagaoka's theorem. Sorry-free, axiom-clean (Tasaki §11.2.2) |
| `Hubbard/TasakiFlatBandModel.lean` | **Tasaki §11.3.1 flat-band model setup** (d=1 decorated/Delta chain): external/internal site embeddings `deltaExternalSite`/`deltaInternalSite` into the physical chain `Fin (2K+2)`, single-particle states `flatBandAlpha`/`flatBandBeta` (11.3.1/11.3.2), fermion operators `flatBandA{Annihilation,Creation}`/`flatBandB{…}` (11.3.3/11.3.4) + adjoints, the Hamiltonian `flatBandHamiltonian = t Σ b̂†b̂ + U Σ n↑n↓` (11.3.5/11.3.6) + Hermiticity. First file of §11.3.1 (Issue #4158) |
| `Hubbard/TasakiFlatBandBasis.lean` | **Tasaki §11.3.1 Lemma 11.10**: `{α_p} ∪ {β_u}` is a basis of the single-particle Hilbert space `Fin (2K+2) → ℂ` (`flatBand_linearIndependent`, `flatBandBasis`). Diagonal evaluations, even/odd site-split equiv, cross-orthogonality `⟨α_p,β_u⟩=0`, combined linear independence, and the basis (sorry-free) (Issue #4158) |
| `Hubbard/TasakiFlatBandCAR.lean` | **Tasaki §11.3.1 eq. (11.3.7)** `flatBandBAnnihilation_ACreation_anticomm`: `{b̂_{u,σ}, â†_{p,τ}} = 0` (the `b̂`/`â†` operators anticommute, since `⟨α_p,β_u⟩=0`), via the spinful CAR `{ĉ_{x,σ},ĉ†_{y,τ}}=[x=y∧σ=τ]` and bilinear expansion. Sorry-free (Issue #4158) |
| `Hubbard/NagaokaConnectivityClassification.lean` | **Tasaki Theorem 11.8 + Lemma 11.9 (AXIOMATIZED, deferred)**: bond graph, biconnected / simple-loop / exchange-bond predicates, and the connectivity classification (`nagaoka_theorem_11_8`: connectivity ⟺ biconnected ∧ not a simple loop `>4` sites) + sufficient condition (`nagaoka_lemma_11_9`: exchange-bond-connected ⇒ connectivity). Theorem 11.8's proof is left by Tasaki to external papers (Bobrow–Stubis–Li / Wilson 15-puzzle); Lemma 11.9's faithful proof is a multi-PR effort. Statements formalized as `axiom`s in book order, proofs deferred (Theorem 11.7 does **not** depend on them) (Tasaki §11.2.2) |
| `Hubbard/DoubleOccupancyProjection.lean` | site-`i` `Commute n_↑ n_↓` + idempotent product |
| `Hubbard/DoubleOccupancyCommute.lean` | cross-site `Commute (n_↑(i)·n_↓(i)) (n_↑(j)·n_↓(j))` |
| `Hubbard/SpinfulNumberHermitian.lean` | `n_↑(i)`, `n_↓(i)`, `n_↑(i)·n_↓(i)` Hermitian |
| `Hubbard/SitePartitionIdentity.lean` | per-site `p_∅+p_↑+p_↓+p_⇈ = 1` (4-state partition) |
| `Hubbard/SiteProjectionsIdempotent.lean` | `(p_∅)² = p_∅`, `(p_↑)² = p_↑`, `(p_↓)² = p_↓` |
| `Hubbard/SiteProjectionsDoublyEmpty.lean` | `p_⇈ · p_∅ = 0`, `p_∅ · p_⇈ = 0` |
| `Hubbard/SiteProjectionsHermitian.lean` | `p_∅`, `p_↑`, `p_↓` Hermitian (companions to PR #1007) |
| `Hubbard/SiteProjectionsUpDown.lean` | `p_↑ · p_↓ = 0`, `p_↓ · p_↑ = 0` |
| `Hubbard/SiteProjectionsEmptySingle.lean` | `p_∅ ⊥ p_↑`, `p_∅ ⊥ p_↓` (both orderings) |
| `Hubbard/SiteProjectionsSingleDoubly.lean` | `p_↑ ⊥ p_⇈`, `p_↓ ⊥ p_⇈` (completes 6/6 ortho.) |
| `Hubbard/SiteProjectionsSpinResolved.lean` | `p_↑+p_⇈ = n_↑`, `p_∅+p_↑ = 1−n_↓`, etc. |
| `Hubbard/SiteProjectionsCommute.lean` | same-site `Commute p_α p_β` (all 6 pairs) |
| `Hubbard/SiteProjectionsPow.lean` | per-site `(p_α)^(k+1) = p_α` (all 4 projections) |
| `Hubbard/EmptyProjectionCommute.lean` | cross-site `Commute (p_∅(i)) (p_∅(j))` |
| `Hubbard/SingleProjectionsCommute.lean` | cross-site `Commute (p_↑(i)) (p_↑(j))`, `(p_↓)` |
| `Hubbard/UpDownProjectionCommute.lean` | `Commute (p_↑(i)) (p_↓(j))` for any `i, j` |
| `Hubbard/RemainingProjectionCommutes.lean` | remaining 5 cross-projection commutes (16/16 total) |
| `CPlusCDaggerSq.lean` | `(c_i + c_i†)² = 1` (multi-mode `σ_x`-analog) |
| `CMinusCDaggerSq.lean` | `(c_i − c_i†)² = −1` (multi-mode `iσ_y`-analog) |
| `CPlusMinusCDaggerPauli.lean` | `(c_i ± c_i†)` Pauli-X/iY-analog full structure |
| `OneSubTwoNumberSq.lean` | `(1 − 2·n_i)² = 1` (`σ_z` analog involution) |
| `CPlusCDaggerAnticomm.lean` | cross-site `{c_i+c_i†, c_j+c_j†} = 0` |
| `CMinusCDaggerAnticomm.lean` | cross-site `{c_i−c_i†, c_j−c_j†}=0`, `{+,−}=0` |
| `NumberCommutePauliOfNe.lean` | `Commute n_i (c_j ± c_j†)` for `i ≠ j` |

Old `import LatticeSystem.Fermion.JordanWigner` continues to
work unchanged via this façade. Following the convention from
`docs/refactoring-conventions.md` §2 "Façade module policy".

(Refactor Phase 2 PR 14, plan v4 §3.1. JordanWigner extraction
complete.)
-/

namespace LatticeSystem.Fermion

end LatticeSystem.Fermion
