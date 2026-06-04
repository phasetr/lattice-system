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
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetryAux
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
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandGroundState
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandZeroEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandHighestWeight
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandNonvanishing
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandMultiplet
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandEnergyTower
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPosSemidef
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandFrustrationFree
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandNumberConservation
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSubspaces
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandAlphaFockKernel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandTheorem11_11
import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeHamiltonian
import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeIncidenceMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBand
import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularHubbardModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularLocalStability
import LatticeSystem.Fermion.JordanWigner.Hubbard.WannierExampleModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TranslationOperator
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionicTranslation
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
| `FockProduct.lean` | **(model-agnostic)** generic move-through lemmas for operator products on the JW vacuum: `anticomm_listProd_mulVec_vacuum`, `charge_listProd_mulVec_vacuum`, `dualAnnihilation_peel_listProd_mulVec_vacuum` (reusable across flat-band models) |
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
| `Hubbard/SpinSymmetryAux.lean` | **(split from SpinSymmetry)** U(1)×U(1) auxiliary: Hermiticity/adjoints of `N_↑`/`N_↓`, spin-site injectivity, per-spin number commutators + hopping commute, and `[S^z_tot, H]=0` (Tasaki §9.3.3) |
| `Hubbard/SpinSymmetry.lean` | SU(2) part of the §9.3.3 spin symmetry: `Ŝ^±_tot` definitions + `[Ŝ^±_tot, H]=0` (imports `SpinSymmetryAux`; downstream API unchanged) |
| `Hubbard/SpinChargeCommutation.lean` | **(model-agnostic)** `[Ŝ^-_tot, N̂]=0` + the number-preserving lowering tower `fermionTotalNumber_mulVec_spinMinusPow_eigenvalue` (deduplicated; used by both Nagaoka §11.2 and the flat-band capstone §11.3.1) |
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
| `Hubbard/TasakiFlatBandGroundState.lean` | **Tasaki §11.3.1 eqs. (11.3.8)/(11.3.9)**: the all-up α Slater state `flatBandAlphaAllUpState` = `(∏_p â†_{p,↑})|vac⟩`, the move-through lemma `anticomm_listProd_mulVec_vacuum`, `b̂_{u,σ}|Φα⟩=0` (zero-energy condition), and `Ĥ_hop|Φα⟩=0` (`flatBandHopping_mulVec_alphaAllUpState`) — `|Φα,all↑⟩` is a zero-energy state of the hopping Hamiltonian. Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandZeroEnergy.lean` | **Tasaki §11.3.1 (toward Thm 11.11)**: `Ĥ_int|Φα⟩=0` and `Ĥ|Φα⟩=0` (`flatBandHamiltonian_mulVec_alphaAllUpState`) — the all-up α state is a zero-energy state of the full flat-band Hamiltonian (down annihilation `ĉ_{x↓}|Φα⟩=0` ⇒ no double occupancy). Sorry-free (Issue #4158) |
| `Hubbard/SpinLoweringTowerGeneral.lean` | **Tasaki §11.2.1/§11.3.1 (toward Thm 11.11, existence)**: the SU(2) spin-lowering tower at an *arbitrary* highest weight `m = L/2` (the `N/2`-specialised tower of `WeakNagaokaTheorem.lean` covers only the chain maximum). General `Ŝ^z`/`Ŝ^+Ŝ^-`/highest-weight Casimir formulas + finite-tower nonvanishing/linear independence + the packaged `highestWeight_spinMultiplet_general` (a highest-weight `v` generates an `(L+1)`-dim maximal-spin multiplet). Needed because Tasaki's flat-band ferromagnet has `Ŝ^z=(K+1)/2 < N/2`. Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandHighestWeight.lean` | **Tasaki §11.3.1 (toward Thm 11.11, existence)**: the all-up α state `|Φα,all↑⟩` is the SU(2) highest-weight state of the ferromagnetic multiplet — `Ŝ^+_tot|Φα⟩=0` (`flatBandTotalSpinPlus_mulVec_alphaAllUpState`), `N̂_↑|Φα⟩=(K+1)|Φα⟩` (`flatBandTotalUpNumber_mulVec_alphaAllUpState`, via a charge move-through `charge_listProd_mulVec_vacuum` + the `[N̂_↑,â†_{p,↑}]=â†_{p,↑}` commutator), `N̂_↓|Φα⟩=0`, hence `Ŝ^z_tot|Φα⟩=((K+1)/2)|Φα⟩` (`flatBandTotalSpinZ_mulVec_alphaAllUpState`, eq. (11.3.10)) — the half-filled-band highest weight `m=(K+1)/2=|E|/2`, strictly below the chain max `N/2`. These are exactly the hypotheses of `highestWeight_spinMultiplet_general`. Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandNonvanishing.lean` | **Tasaki §11.3.1 (toward Thm 11.11, existence)**: `|Φα,all↑⟩ ≠ 0` (`flatBandAlphaAllUpState_ne_zero`), the last input to the existence half. No Slater/Gram machinery — the `α` orbitals are unit vectors on the external sites (`α_p(2q)=δ_{pq}`), so the external up annihilation `ĉ_{2q,↑}` is the canonical dual `{ĉ_{2q,↑},â†_{p,↑}}=δ_{pq}` (`flatBandExtUpAnnihilation_ACreation_anticomm`); the ordered dual annihilations collapse the creation product back to `|vac⟩` (`flatBandAlpha_listProd_exists_collapse` via the peel lemma `dualAnnihilation_peel_listProd_mulVec_vacuum`), and `|vac⟩≠0` (`fermionMultiVacuum_ne_zero`). Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandMultiplet.lean` | **Tasaki §11.3.1 Theorem 11.11 (existence half, spin content)**: `flatBand_ferromagnetic_multiplet` — the `K+2 = 2S_max+1` lowered states `(Ŝ^-_tot)^k|Φα,all↑⟩` (`k=0..K+1`) are linearly independent and all carry total spin `S_tot=S_max=(K+1)/2=N_e/2` (eigenstates of `(Ŝ_tot)²` at `S_max(S_max+1)`). Packages the general tower (#4164), highest-weight data (#4165), and nonvanishing (#4166) via `highestWeight_spinMultiplet_general` at `L=K+1`. (That every member is a zero-energy *ground* state needs the energy tower + PSD, in subsequent steps.) Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandEnergyTower.lean` | **Tasaki §11.3.1 (toward Thm 11.11, existence)**: flat-band SU(2) lowering symmetry `[Ŝ^±_tot, Ĥ]=0` (`fermionTotalSpinPlus/Minus_commute_flatBandHamiltonian`) and the **energy tower** `Ĥ(Ŝ^-_tot)^k|Φα,all↑⟩=0` (`flatBandHamiltonian_mulVec_spinMinusPow_alphaAllUpState`) — every member of the ferromagnetic multiplet is a zero-energy state. The kinetic term is SU(2)-invariant: the `b̂` operators form a spin doublet (built from the same spatial `β_u`), so the spin-summed mode number `Σ_σ b̂†_{u,σ}b̂_{u,σ}` commutes with `Ŝ^+` (off-diagonal `b̂†_↑b̂_↓` terms cancel, `commute_two_component_kinetic_of_spinPlus_relations`); the interaction reuses `fermionTotalSpinPlus_commute_hubbardDoubleOccupancy`; `Ŝ^-` follows by adjoint. (That `0` is the *ground* energy needs `Ĥ≥0`, the remaining step.) Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandPosSemidef.lean` | **Tasaki §11.3.1 Theorem 11.11 (existence half, ground states)**: `Ĥ≥0` (`flatBandHamiltonian_posSemidef`, for `t,U≥0`) — a nonnegative combination of PSD terms (`b̂†b̂=(b̂)ᴴb̂`; `n̂↑n̂↓` a Hermitian-idempotent projection `P=PᴴP`); hence the energy `rayleighOnVec Ĥ ψ≥0` everywhere while the tower states attain `0`, so `flatBand_alphaTower_isGroundState`: each `(Ŝ^-_tot)^k|Φα⟩` minimizes the energy (is a ground state). With `flatBand_ferromagnetic_multiplet` (LI + `S_tot=S_max=(K+1)/2`), this is the `(2S_max+1)`-dim maximal-spin degenerate **ground-state** multiplet — the existence half of Theorem 11.11. Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandFrustrationFree.lean` | **Tasaki §11.3.1 (toward Thm 11.11, uniqueness)**: frustration-free conditions on any flat-band ground state `v` (energy `rayleighOnVec Ĥ v=0`, `t,U>0`) — `b̂_{u,σ}v=0` (`flatBand_groundState_BAnnihilation_mulVec_eq_zero`, eq. (11.3.11)) and `n̂_{x↑}n̂_{x↓}v=0` (`flatBand_groundState_doubleOccupancy_mulVec_eq_zero`, no-double-occupancy form of (11.3.12)). Via generic helpers: `Ĥ=ΣPSD` energy decomposition (`flatBandHamiltonian_rayleighOnVec_decompose`) + each PSD term's energy is `≥0` ⇒ each vanishes (`posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero`, `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`), and `(b̂)ᴴb̂ v=0⇒b̂v=0` (`conjTranspose_mul_self_mulVec_eq_zero`). Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandNumberConservation.lean` | **Tasaki §11.3.1 (toward Thm 11.11, uniqueness structure)**: particle-number conservation `[Ĥ, N̂]=0` (`flatBandHamiltonian_commute_fermionTotalNumber`) — each kinetic mode `b̂†_{u,σ}b̂_{u,σ}` is number-conserving (`b̂` lowers, `b̂†` raises `N̂` by one: `flatBandBAnnihilation/BCreation_commutator_fermionTotalNumber`) and the interaction `n̂↑n̂↓` is too; so ground states split into fixed-`N` sectors (Tasaki works in `N_e=K+1`). Plus `flatBand_groundState_mem_hardcoreSubspace`: any ground state lies in the Hubbard hard-core subspace (no double occupancy). Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandSubspaces.lean` | **Tasaki §11.3.1 (toward Thm 11.11, uniqueness framework)**: the two subspaces of the uniqueness argument — `flatBandAlphaFockSubmodule` (span of all α-band Slater states `flatBandAlphaSlaterState`, with `flatBandAlphaAllUpState_mem_alphaFockSubmodule`: `|Φα,all↑⟩` lives in it) and `flatBandBKernelSubmodule = ⨅_{u,σ} ker b̂_{u,σ}` (with `mem_flatBandBKernelSubmodule_iff` and `flatBand_groundState_mem_BKernelSubmodule`: every ground state lies in it, from frustration-free (11.3.11)). Tasaki's uniqueness = the inclusion `BKernel ⊆ αFock` (no β-occupation) + symmetric/maximal-spin classification. Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandAlphaFockKernel.lean` | **Tasaki §11.3.1 (toward Thm 11.11, uniqueness)**: the *easy* inclusion `flatBandAlphaFockSubmodule ≤ flatBandBKernelSubmodule` (`flatBandAlphaFockSubmodule_le_BKernelSubmodule`) — every α-Slater state is annihilated by every `b̂_{u,σ}` (`flatBandBAnnihilation_mulVec_alphaSlaterState`), since `b̂` anticommutes with all `â†` (11.3.7) and kills the vacuum (move-through by direct induction on the ordered product). The hard reverse inclusion `BKernel ⊆ αFock` (no β-occupation ⇒ flat-band) needs the Fock-space factorisation of the non-orthogonal `{α}∪{β}` basis (deferred). Sorry-free (Issue #4158) |
| `Hubbard/TasakiFlatBandTheorem11_11.lean` | **Tasaki Theorem 11.11 (flat-band ferromagnetism, CAPSTONE)**: `flatBand_theorem_11_11_groundSubmodule_eq_multipletSpan` — the half-filled (`N_e=K+1`) zero-energy ground subspace `ker Ĥ ⊓ eigenspace(N̂, K+1)` equals the ferromagnetic multiplet span `flatBandFerromagneticMultipletSubmodule` (the `2S_max+1`-dim maximal-spin multiplet); + maximal-spin corollary `flatBand_theorem_11_11_groundState_maximalSpin` (every ground state has `S_tot=S_max=(K+1)/2`). Wrappers `N̂\|Φα⟩=(K+1)\|Φα⟩`, `[Ŝ^-,N̂]=0`, number-preserving tower. `≥` (existence) fully proven; `≤` (uniqueness) uses a **single documented `axiom`** `flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan` — Tasaki App. A (Lemmas A.10/A.11) classification (no β-occupation + no double occupancy ⇒ symmetric ⇒ maximal spin), deferred like Theorem 11.8/Lemma 11.9 (needs non-orthogonal-basis Fock factorisation + symmetric-tensor classification). Existence half does NOT depend on the axiom (Issue #4158) |
| `Hubbard/MielkeHamiltonian.lean` | **Tasaki §11.3.2 (Mielke's flat-band ferromagnetism, model)**: `mielkeHamiltonian` on a graph `G` (eqs. (11.3.31)/(11.3.6) — uniform hopping `t` + `2t·N̂` shift + on-site `U`, = `hubbardHamiltonianOnGraph + 2t·N̂`); Hermiticity, particle-number conservation `[Ĥ,N̂]=0`, and SU(2) invariance `[Ŝ^±_tot,Ĥ]=0`. Line-graph structure + Theorems 11.12/11.13 in a companion file (Issue #4177) |
| `Hubbard/MielkeTheorems.lean` | **Tasaki §11.3.2 Theorem 11.13 (AXIOMATIZED) + Theorem 11.12 statement data**: `mielkeFlatBandDim` `D(Λ̃,B̃)` (`=\|B̃\|-\|Λ̃\|+1` bipartite else `\|B̃\|-\|Λ̃\|`), `mielkeSingleElectronOp` (the 11.3.32 single-electron operator on the line graph); the line graph is mathlib `SimpleGraph.lineGraph` (realized via `SimpleGraph.Iso G (lineGraph Gbase)`). `axiom mielke_theorem_11_13` (Mielke ferromagnetism: biconnected base, `N=D` ⇒ ground subspace `finrank = N+1` + all maximal spin `S_max=N/2`) — Tasaki states it without proof (Theorem 11.8 policy). **Theorem 11.12 is no longer an axiom**: it is *proved* in `MielkeIncidenceMatrix.lean` (§11.3.3, Issue #4180), which imports this file. The Mielke Hamiltonian model + symmetries are axiom-free (Issue #4177) |
| `Hubbard/MielkeIncidenceMatrix.lean` | **Tasaki §11.3.3 (incidence-matrix `SᴴS` factorisation)**: `mielkeSingleElectronOpOn` (single-electron operator over an arbitrary finite vertex type; `mielkeSingleElectronOp` is now the `Fin (M+1)` wrapper), `mielkeIncidence` (`S = √t·` mathlib `incMatrix`, restricted to genuine edges), and `mielkeIncidence_conjTranspose_mul_self`: `SᴴS = mielkeSingleElectronOpOn (lineGraph G) t` for `t ≥ 0` (eqs. (11.3.36)–(11.3.39)). Presents the line-graph operator as a PSD Gram matrix whose kernel is `ker S`. Carries the §11.3.3 proof through: `mielke_lineGraph_ker_finrank_eq` (rank step `dim ker T = \|B\|−rank S`), `mielke_conjTranspose_ker_finrank` (signless-Laplacian zero-mode count `dim ker(SSᴴ)=Colorable 2 ? 1 : 0` for a connected base, via `ker Sᴴ`/bipartite sign vector), `mielke_lineGraph_ker_finrank_eq_dim` (assembled `D=\|B\|−(\|Λ̃\|−bip)`), and **`mielke_theorem_11_12`** — **now a proved theorem** (formerly an axiom): transports the flat-band dimension to the `Fin (M+1)` realisation along the line-graph `SimpleGraph.Iso` via `Matrix.rank_submatrix` (needs `\|Λ̃\| ≤ \|B\|`, i.e. the base has a cycle). Discharges Issue #4180 |
| `Hubbard/GeneralFlatBand.lean` | **Tasaki §11.3.4 Theorem 11.15 (general flat-band ferromagnetism, AXIOMATIZED)**: for a Hermitian PSD hopping matrix `T` (`Matrix.PosSemidef`) with flat band `h₀=ker T`, `D₀=dim h₀>0`, `U>0`, at filling `N=D₀`. `generalFlatBandProjectionMatrix` `P₀` = orthogonal projection onto `ker T` (`Matrix.toEuclideanLin` → `Submodule.starProjection` → `LinearMap.toMatrixOrthonormal`); `generalFlatBandActiveSites` `Λ₀={x\|(P₀)_{x,x}≠0}`; `generalFlatBandProjectionIrreducible` = `Matrix.IsIrreducible` of the real support matrix `Complex.normSq (P₀)` on `Λ₀` (Tasaki block-decomposability; `P₀` Hermitian ⇒ symmetric support); `generalFlatBandFerromagnetic` = ground subspace `finrank = D₀+1` + all `(Ŝ_tot)²` eigenvectors at `S_max=D₀/2` (mirrors `mielke_theorem_11_13`). **`axiom tasaki_theorem_11_15`**: ferromagnetic ⇔ `P₀\|Λ₀` irreducible. Plus **Lemma 11.16** (`IsGeneralFlatBandSpecialBasis` + `axiom generalFlatBand_lemma_11_16`: `ker T` has a site-localised basis `{μ_z}_{z∈I}`, `\|I\|=D₀`, `μ_z(z)≠0`, `μ_z(z')=0` for `z'≠z`) and **Theorem 11.17** (`generalFlatBandBasisGraph`/`generalFlatBandBasisConnected` + `axiom generalFlatBand_theorem_11_17`: ferromagnetic ⇔ the special basis is connected — Mielke's second nec-&-suf condition). All deep results, deferred (Issue #4186; Theorem 11.8/11.13 policy) |
| `Hubbard/SectorMinEnergy.lean` | **Tasaki §11.4 (sector minimum energy + ferromagnetism criterion, eq. (11.4.26))**: `spinSector twoS` (unit `EuclideanSpace` vectors with `(Ŝ_tot)² Φ = (twoS/2)(twoS/2+1) Φ`, `twoS=2S`), `sectorMinEnergy H twoS` = `E_min(S)` = `⨅` of `rayleighOnVec H` over that sector (L² unit norm via `EuclideanSpace`, matching the project min-eigenvalue convention), and `exhibitsFerromagnetism H twoSmax` = `∀ twoS<twoSmax, E_min(Smax) < E_min(twoS)`. Foundation (definitions only) for the non-singular Hubbard Theorems 11.18–11.20 (Issue #4189) |
| `Hubbard/NonsingularHubbardModel.lean` | **Tasaki §11.4 non-singular Hubbard model (eq. (11.4.23)) + symmetries**: `nonsingularHubbardHamiltonian K ν t ζ tPert U` = `flatBandHamiltonian K ν t U + (ζ:ℂ) • hubbardKinetic (2K+1) tPert` (the flat-band model `t Σ b̂†b̂ + U Σ n̂↑n̂↓` perturbed by `ζ Σ t_xy ĉ†ĉ`; `ζ=0` recovers the flat band). Proven symmetries (by `.add` of the flat-band + kinetic lemmas): Hermiticity (`tPert` Hermitian), `[Ĥ,N̂]=0`, and SU(2) invariance `[Ŝ^±_tot,Ĥ]=0` (spin-minus via the adjoint of spin-plus + Hermiticity). Model setup for Theorems 11.18–11.20 (Issue #4189), axiom-free |
| `Hubbard/NonsingularLocalStability.lean` | **Tasaki §11.4 Theorem 11.18 (local stability, AXIOMATIZED)**: `IsNonsingularHopping K tPert t R` (the (11.4.24) cyclic translation-invariance + (11.4.25) range-`R` summability of the perturbation), and **`axiom nonsingular_theorem_11_18`**: `∃ ν₀,η₀,ξ₀>0` (uniform in system size, dep. on `d=1,R`) s.t. under the parameter bounds `0<ν≤ν₀`, `|ζ|≤ν³η₀`, `U≥ξ₀t|ζ|/ν²` the maximal-spin sector lies below the once-flipped sector, `sectorMinEnergy H (K+1) < sectorMinEnergy H (K−1)` (`S_max=(K+1)/2`) — stability against a single spin flip (eq. (11.4.29)). Deep perturbation-theory result, deferred (Issue #4189; Theorem 11.8/11.13 policy) |
| `Hubbard/WannierExampleModel.lean` | **Tasaki §11.4.1 (Wannier-perturbation example model, eq. (11.4.1))**: §11.4.1 is heuristic/non-rigorous (no numbered theorems); its one formalisable object is the example model — the 1D flat-band model with the internal on-site potential shifted by `γ`. `wannierExamplePerturbation K` (internal-site, odd-index, diagonal indicator); `wannierExampleModel K ν t γ U = nonsingularHubbardHamiltonian K ν t (γ·t) (wannierExamplePerturbation K) U` (the `γ t Σ_{u∈I} n̂_u` shift as a non-singular instance); `wannierExampleModel_isHermitian`; **`wannierExampleModel_gamma_zero`**: `γ=0` ⇒ `= flatBandHamiltonian` (eq. (11.4.1) reduces to (11.3.22)). Explicitly covers §11.4.1 in book order; axiom-free (Issue #4189) |
| `Hubbard/TranslationOperator.lean` | **Tasaki §11.4.2 (lattice translation on the decorated chain, towards Theorem 11.19)**: the combinatorial datum for the fermionic translation operator `τ̂_z` (eq. (11.4.30)). `modeSiteSpinEquiv K` factors the spinful mode space `Fin(2(2K+1)+2) = Fin((2K+2)·2)` as `(physical site) × (spin)` (mode `2p+σ ↔ (p,σ)`); `siteShiftAmount K z = 2z` (one cell = two physical sites); **`siteTranslationPerm K z`** = the `Equiv.Perm` shifting the physical site by `2z` cyclically (via `finCycle`), spin fixed; `siteTranslationPerm_zero` (`z=0 ⇒` identity). Step 1 of Theorem 11.19 (signed `τ̂` operator + `E_SW(k)` + axiom to follow); axiom-free (Issue #4189) |
| `Hubbard/FermionicTranslation.lean` | **Tasaki §11.4.2 fermionic translation operator `τ̂_z` (eq. (11.4.30))** — step 2 of Theorem 11.19. `translationJwSign π σ = (-1)^(occupied inversions of π)` (the Jordan–Wigner sign from reordering shifted creation operators; `translationJwSign_sq`: it is `±1`); **`translationOperator K z`** = the signed permutation operator `Matrix.of (fun τ σ => if τ = σ∘π⁻¹ then translationJwSign π σ else 0)` (`π = siteTranslationPerm K z`); **`translationOperator_mulVec_basisVec`**: the defining action `τ̂_z|σ⟩ = ε(π,σ)·|σ∘π⁻¹⟩` (eq. (11.4.30)); `translationOperator_zero` (`z=0 ⇒ = 1`). Axiom-free; `E_SW(k)` + axiom Theorem 11.19 to follow (Issue #4189) |
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
