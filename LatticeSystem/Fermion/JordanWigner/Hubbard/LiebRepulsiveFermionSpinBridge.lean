import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchange
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeMatrixElement
import LatticeSystem.Quantum.SpinS.HeisenbergCore
import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian

/-!
# Fermion-Spin bridge, sector `Equiv` + Hamiltonian reindexing (Theorem 10.4 arc, PR-9a)

Tenth installment of the Theorem 10.4 discharge arc (issue #5320); first of the two-PR 9a/9b split
of "PR-9: Fermion-Spin bridge". This is a **TDD Red** file: every declaration below is stated with
its exact type and a `sorry` proof body, per the PR-9 design round recorded in the arc's active
record (`.self-local/active/issue-5320.md`, "PR-9 design round" section).

## Central structural fact

`configSector N (liebHalfFillingPred N nUp)` contains doubly-occupied configurations and is
therefore *not* in bijection with `magConfigS`. Single occupancy is available only inside the
narrower **hard-core** sector `liebHardCoreHalfFillingPred`, defined below by conjoining
`liebHalfFillingPred` (`LiebRepulsivePerturbationSetup.lean:300`) with the singly-occupied
condition `hubbardConfigInteractionWeight N (fun _ => 1) c = 0`
(`liebHalfFilling_site_occupation`, `LiebRepulsivePerturbationSetup.lean:388`) unfolded pointwise.
Its `DecidablePred` instance is synthesised automatically from `Nat`/`Fin` decidable equality and
`Fintype.decidableForallFintype` — the same non-`Classical.dec` route already used by
`liebHalfFillingPred` itself, so no bespoke instance is declared.

## The sector `Equiv`

`M = N + 1 − nUp` (the **down**-count, not the up-count `nUp`) — verified against
`magSumS`/`spinSOp3`'s convention (index `0` = up, index `1` = down at `N = 1`) in the design
round. Forward map `liebHardCoreToMagConfigS`: read off the down-orbital occupation. Backward map
`liebHardCoreOfMagConfigS`: `c (spinfulIndex x 0) := 1 − σ x`, `c (spinfulIndex x 1) := σ x`. The
backward direction needs `nUp ≤ N + 1` (truncated-subtraction safety recovering `nUp` from
`N + 1 − (N + 1 − nUp)`), carried as an explicit hypothesis throughout.

## The t-J reuse route

`liebHardCoreSiteState` sends a hard-core configuration to a t-J site-state
`s : Fin (N + 1) → Fin 3` so that `tJConfigOf N s = c` (`TJSectorBasis.lean:31`), letting the
already-proved (sign-free) `TJ*` matrix-element layer (`TJExchangeMatrixElement.lean`) apply without
re-deriving Jordan–Wigner sign combinatorics.

## The capstone

`fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied` is the crux entrywise identity. Composed with
the diagonal number-operator collapse and the PR-8b capstone
(`LiebRepulsiveSuperexchange.lean`), it reindexes the compressed second-order effective Hamiltonian
onto exactly the shape PR-10 needs to apply Theorem 2.3
(`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean:40`): coupling
`(2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))` on
`heisenbergHamiltonianSMatrixOnMagSector … 1 (N + 1 − nUp)`, plus the constant shift
`−|A|(N + 1 − |A|)`.

## Endpoint-graph provenance (arc-wide documented deviation, restated)

As in every file of this arc since PR-4: the endpoint graph is the *complete bipartite* graph on
`(A, Aᶜ)`, not the book's literal bond set `{ {x, y} | t_{x,y} ≠ 0 }` (p. 345); see
`LiebRepulsiveSuperexchange.lean` and `LiebRepulsiveHomotopyContinuity.lean` for the full provenance
note.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1, eq. (10.1.10), p. 345; §2.5, Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped ComplexOrder

variable {N : ℕ}

/-! ## The hard-core half-filling predicate -/

/-- **The hard-core half-filled fixed-`Ŝ³` configuration predicate**: `liebHalfFillingPred` (half
filling, `nUp` up-spins) strengthened by single occupancy at every site. Unlike
`liebHalfFillingPred` alone, `configSector N (liebHardCoreHalfFillingPred N nUp)` *is* in bijection
with a spin-`1/2` magnetization sector (`liebHardCoreHalfFillingSectorEquivS` below), since single
occupancy is exactly what lets each site be read as a single spin-`1/2` degree of freedom. -/
abbrev liebHardCoreHalfFillingPred (N nUp : ℕ) : (Fin (2 * N + 2) → Fin 2) → Prop :=
  fun c => liebHalfFillingPred N nUp c ∧
    ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1

/-! ## The sector `Equiv`: forward direction (down-orbital occupation) -/

/-- The **down-orbital occupation** read off a Fock configuration: at each site `x`, whether the
down orbital is occupied (`1`) or not (`0`). On a hard-core configuration this is the sole
remaining spin-`1/2` degree of freedom once the up orbital's occupation is known to be the
complement. -/
def liebHardCoreDownOccupation {N : ℕ} (c : Fin (2 * N + 2) → Fin 2) : Fin (N + 1) → Fin 2 :=
  fun x => c (spinfulIndex N x 1)

/-- `liebHardCoreDownOccupation` lands in the magnetization sector `M = N + 1 − nUp`: the number of
down-occupied sites is the complement of the up-count `nUp` inside the `N + 1` singly-occupied
sites (design-round convention check: `M` is the **down**-count, not `nUp`). -/
theorem liebHardCoreDownOccupation_magSumS_eq (N nUp : ℕ)
    {c : Fin (2 * N + 2) → Fin 2} (hc : liebHardCoreHalfFillingPred N nUp c) :
    magSumS (liebHardCoreDownOccupation c) = N + 1 - nUp := by
  sorry

/-- The packaged forward map of the PR-9a sector `Equiv`: a hard-core half-filled configuration to
its magnetization-`(N + 1 − nUp)` spin-`1/2` configuration. -/
def liebHardCoreToMagConfigS (N nUp : ℕ) :
    configSector N (liebHardCoreHalfFillingPred N nUp) →
      magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) :=
  fun c => ⟨liebHardCoreDownOccupation c.val,
    liebHardCoreDownOccupation_magSumS_eq N nUp c.property⟩

/-! ## The sector `Equiv`: backward direction -/

/-- The Fock configuration recovered from a spin-`1/2` configuration `σ`: site `x`'s up orbital is
occupied iff `σ x = 0`, and its down orbital iff `σ x = 1` — matching `tJConfigOf`'s indexing
pattern (`k.val % 2 = 0` = up orbital). -/
def liebHardCoreOfMagConfigSFock {N : ℕ} (σ : Fin (N + 1) → Fin 2) : Fin (2 * N + 2) → Fin 2 :=
  fun k =>
    let i : Fin (N + 1) :=
      ⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by have := k.isLt; omega)⟩
    if k.val % 2 = 0 then 1 - σ i else σ i

/-- `liebHardCoreOfMagConfigSFock σ` at the up-orbital `spinfulIndex x 0` is `1 − σ x`. -/
theorem liebHardCoreOfMagConfigSFock_apply_up (N : ℕ) (σ : Fin (N + 1) → Fin 2)
    (x : Fin (N + 1)) :
    liebHardCoreOfMagConfigSFock σ (spinfulIndex N x 0) = 1 - σ x := by
  sorry

/-- `liebHardCoreOfMagConfigSFock σ` at the down-orbital `spinfulIndex x 1` is `σ x`. -/
theorem liebHardCoreOfMagConfigSFock_apply_down (N : ℕ) (σ : Fin (N + 1) → Fin 2)
    (x : Fin (N + 1)) :
    liebHardCoreOfMagConfigSFock σ (spinfulIndex N x 1) = σ x := by
  sorry

/-- `liebHardCoreOfMagConfigSFock σ` lies in `liebHardCoreHalfFillingPred N nUp`, provided
`σ`'s magnetization sum is `N + 1 − nUp` and `nUp ≤ N + 1` (needed to recover `nUp` from the
truncated subtraction `N + 1 − (N + 1 − nUp)`). -/
theorem liebHardCoreOfMagConfigSFock_mem_pred (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    {σ : Fin (N + 1) → Fin 2} (hσ : magSumS σ = N + 1 - nUp) :
    liebHardCoreHalfFillingPred N nUp (liebHardCoreOfMagConfigSFock σ) := by
  sorry

/-- The packaged backward map of the PR-9a sector `Equiv`. -/
def liebHardCoreOfMagConfigS (N nUp : ℕ) (hnUp : nUp ≤ N + 1) :
    magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) →
      configSector N (liebHardCoreHalfFillingPred N nUp) :=
  fun σ => ⟨liebHardCoreOfMagConfigSFock σ.val,
    liebHardCoreOfMagConfigSFock_mem_pred N nUp hnUp σ.property⟩

/-! ## Convention guard and round-trip -/

/-- **Convention guard**: the forward map's up/down convention pinned in a single visible lemma —
`liebHardCoreToMagConfigS`'s down-occupation is `0` at site `x` iff the *up* orbital (not the down
one) is occupied at `x`. Guards against silently flipping the up/down convention elsewhere. -/
theorem liebHardCoreToMagConfigS_apply_eq_zero_iff_up_occupied (N nUp : ℕ)
    (c : configSector N (liebHardCoreHalfFillingPred N nUp)) (x : Fin (N + 1)) :
    (liebHardCoreToMagConfigS N nUp c).val x = 0 ↔ c.val (spinfulIndex N x 0) = 1 := by
  sorry

/-- Round-trip 1: `invFun ∘ toFun = id` on the hard-core sector. -/
theorem liebHardCoreOfMagConfigS_liebHardCoreToMagConfigS (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (c : configSector N (liebHardCoreHalfFillingPred N nUp)) :
    liebHardCoreOfMagConfigS N nUp hnUp (liebHardCoreToMagConfigS N nUp c) = c := by
  sorry

/-- Round-trip 2: `toFun ∘ invFun = id` on the magnetization sector. -/
theorem liebHardCoreToMagConfigS_liebHardCoreOfMagConfigS (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (σ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp)) :
    liebHardCoreToMagConfigS N nUp (liebHardCoreOfMagConfigS N nUp hnUp σ) = σ := by
  sorry

/-- **PR-9a's sector `Equiv`**: the hard-core half-filled fermionic sector is in bijection with the
magnetization-`(N + 1 − nUp)` spin-`1/2` configuration sector. Needs `nUp ≤ N + 1`; the reverse
direction's well-definedness (truncated-subtraction safety), not a further mathematical
restriction, since the fermionic sector is empty whenever `nUp > N + 1` regardless. -/
def liebHardCoreHalfFillingSectorEquivS (N nUp : ℕ) (hnUp : nUp ≤ N + 1) :
    configSector N (liebHardCoreHalfFillingPred N nUp) ≃
      magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) where
  toFun := liebHardCoreToMagConfigS N nUp
  invFun := liebHardCoreOfMagConfigS N nUp hnUp
  left_inv := liebHardCoreOfMagConfigS_liebHardCoreToMagConfigS N nUp hnUp
  right_inv := liebHardCoreToMagConfigS_liebHardCoreOfMagConfigS N nUp hnUp

/-! ## The `t-J` reuse route -/

/-- The t-J site-state read off a hard-core configuration: `↑` (`1`) if the up orbital is occupied,
`↓` (`2`) otherwise (the down orbital must then be occupied, by single occupancy). -/
def liebHardCoreSiteState {N : ℕ} (c : Fin (2 * N + 2) → Fin 2) : Fin (N + 1) → Fin 3 :=
  fun x => if c (spinfulIndex N x 0) = 1 then 1 else 2

/-- `liebHardCoreSiteState c` never takes the "empty" value `0`, since every site is singly
occupied. -/
theorem liebHardCoreSiteState_ne_zero (N nUp : ℕ) {c : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (x : Fin (N + 1)) :
    liebHardCoreSiteState c x ≠ 0 := by
  sorry

/-- **The `tJConfigOf` round-trip**: for a hard-core half-filled configuration, `liebHardCoreSiteState`
recovers exactly `c` under `tJConfigOf` — the bridge letting the already-proved (sign-free) `TJ*`
matrix-element layer (`TJExchangeMatrixElement.lean`) apply verbatim, with no fresh
Jordan–Wigner-sign derivation for this sector. -/
theorem tJConfigOf_liebHardCoreSiteState_eq (N nUp : ℕ) {c : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) :
    tJConfigOf N (liebHardCoreSiteState c) = c := by
  sorry

/-! ## Entrywise operator correspondence -/

/-- **The crux entrywise identity**: on hard-core half-filled bra/ket configurations, the fermionic
two-site spin dot's matrix element equals the spin-`1/2` `spinSDot`'s matrix element at the images
under `liebHardCoreToMagConfigS` (the down-orbital occupation). Both `S^z S^z` diagonal and
`S^+ S^- / S^- S^+` off-diagonal parts of `fermionSpinDot`/`spinSDot` are covered uniformly. -/
theorem fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied (N nUp : ℕ) (x y : Fin (N + 1))
    {c e : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (he : liebHardCoreHalfFillingPred N nUp e) :
    (fermionSpinDot N x y) e c =
      spinSDot x y 1 (liebHardCoreDownOccupation e) (liebHardCoreDownOccupation c) := by
  sorry

/-- **The diagonal number-operator constant**: on a pair of hard-core half-filled bra/ket
configurations, `n̂_x n̂_y` collapses to the Kronecker delta `[e = c]` (every site is singly
occupied, so `n̂_x = n̂_y = 1` identically on both `c` and `e`), giving the exact
`κ = |A| (N + 1 − |A|) / 2` constant shift in the PR-9a capstone below. -/
theorem fermionSiteNumber_mul_apply_eq_ite_of_singlyOccupied (N nUp : ℕ) (x y : Fin (N + 1))
    {c e : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (he : liebHardCoreHalfFillingPred N nUp e) :
    (fermionSiteNumber N x * fermionSiteNumber N y) e c = if e = c then 1 else 0 := by
  sorry

/-! ## The PR-9a capstone: reindexing onto the Heisenberg magnetization sector -/

/-- The inclusion of the hard-core sub-sector into the ambient half-filled sector: the
`.1`-projection of the conjunction defining `liebHardCoreHalfFillingPred`. -/
def liebHardCoreToAmbientSector (N nUp : ℕ) :
    configSector N (liebHardCoreHalfFillingPred N nUp) →
      configSector N (liebHalfFillingPred N nUp) :=
  fun s => ⟨s.val, s.property.1⟩

/-- **PR-9a capstone (raw form)**: the PR-8b superexchange identity
(`kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection`,
`LiebRepulsiveSuperexchange.lean`), restricted to the hard-core sub-sector and reindexed along the
PR-9a `Equiv`, lands in the shape PR-10 needs: `κ • 1` minus twice the antiferromagnetic Heisenberg
matrix with coupling `(2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))` on the
magnetization-`(N + 1 − nUp)` sector, with `κ = |A| (N + 1 − |A|) / 2`. -/
theorem kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection_reindex_eq
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    (LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      ).submatrix (liebHardCoreToAmbientSector N nUp) (liebHardCoreToAmbientSector N nUp)
      = ((((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ)) / 2) • (1 : Matrix _ _ ℂ)
          - (2 : ℂ) • heisenbergHamiltonianSMatrixOnMagSector
              ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))) 1 (N + 1 - nUp)
        ).submatrix (liebHardCoreHalfFillingSectorEquivS N nUp hnUp)
          (liebHardCoreHalfFillingSectorEquivS N nUp hnUp) := by
  sorry

/-- **PR-9a/PR-10-facing corollary**: the same reindexing applied to PR-8b's `Ĥeff` corollary
(`secondOrderEffectiveHamiltonian_liebPerturbation_eq_tJExchange`, `LiebRepulsiveSuperexchange.lean`),
giving the second-order effective Hamiltonian directly as an antiferromagnetic Heisenberg matrix on
the magnetization sector plus the constant shift `−|A| (N + 1 − |A|)` — Tasaki's eq. (10.1.10) at
this arc's `U = 1`, `λ = 1` normalisation, in exactly the shape PR-10 needs to invoke Theorem 2.3
(`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`,
`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean:40`). -/
theorem secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergHamiltonianSMatrixOnMagSector
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    (LatticeSystem.Math.secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)
      ).submatrix (liebHardCoreToAmbientSector N nUp) (liebHardCoreToAmbientSector N nUp)
      = ((2 : ℂ) • heisenbergHamiltonianSMatrixOnMagSector
              ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))) 1 (N + 1 - nUp)
          - (((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ))) • (1 : Matrix _ _ ℂ)
        ).submatrix (liebHardCoreHalfFillingSectorEquivS N nUp hnUp)
          (liebHardCoreHalfFillingSectorEquivS N nUp hnUp) := by
  sorry

end LatticeSystem.Fermion
