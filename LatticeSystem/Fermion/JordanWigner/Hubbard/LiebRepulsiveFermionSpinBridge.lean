import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchange
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingBondAction
import LatticeSystem.Quantum.SpinS.HeisenbergCore
import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian

/-!
# Fermion-Spin bridge, sector `Equiv` + Hamiltonian reindexing (Theorem 10.4 arc, PR-9a)

Tenth installment of the Theorem 10.4 discharge arc (issue #5320); first of the two-PR 9a/9b split
of "PR-9: Fermion-Spin bridge".

## Central structural fact

`configSector N (liebHalfFillingPred N nUp)` contains doubly-occupied configurations and is
therefore *not* in bijection with `magConfigS`. Single occupancy is available only inside the
narrower **hard-core** sector `liebHardCoreHalfFillingPred`, defined below by conjoining
`liebHalfFillingPred` (`LiebRepulsivePerturbationSetup.lean`) with the singly-occupied condition
`hubbardConfigInteractionWeight N (fun _ => 1) c = 0` (`liebHalfFilling_site_occupation`,
`LiebRepulsivePerturbationSetup.lean`) unfolded pointwise. Its `DecidablePred` instance is
synthesised automatically from `Nat`/`Fin` decidable equality and `Fintype.decidableForallFintype` —
the same non-`Classical.dec` route already used by `liebHalfFillingPred` itself, so no bespoke
instance is declared.

## The sector `Equiv`

`M = N + 1 − nUp` (the **down**-count, not the up-count `nUp`), matching `magSumS`/`spinSOp3`'s
convention (index `0` = up, index `1` = down at `N = 1`). Forward map
`liebHardCoreToMagConfigS`: read off the down-orbital occupation. Backward map
`liebHardCoreOfMagConfigS`: `c (spinfulIndex x 0) := 1 − σ x`, `c (spinfulIndex x 1) := σ x`. The
backward direction needs `nUp ≤ N + 1` (truncated-subtraction safety recovering `nUp` from
`N + 1 − (N + 1 − nUp)`), carried as an explicit hypothesis throughout.

## The t-J reuse route

`liebHardCoreSiteState` sends a hard-core configuration to a t-J site-state
`s : Fin (N + 1) → Fin 3` so that `tJConfigOf N s = c` (`TJSectorBasis.lean`), letting the
already-proved (sign-free) `TJ*`
bond-action layer (`tJExchangeBond_mulVec_tJConfigOf_full`, `TJHalfFillingBondAction.lean`) apply
without re-deriving Jordan–Wigner sign combinatorics.

## The capstone

`fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied` is the crux entrywise identity. Composed with
the diagonal number-operator collapse and the PR-8b capstone (`LiebRepulsiveSuperexchange.lean`), it
reindexes the compressed second-order effective Hamiltonian onto exactly the shape PR-10 needs to
apply Theorem 2.3 (`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean`): the Heisenberg matrix with
coupling `(2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))` on
`heisenbergHamiltonianSMatrixOnMagSector … 1 (N + 1 − nUp)`, minus the constant `|A|(N + 1 − |A|)`.

The two-site crux and both capstones carry `x ≠ y` / an irreflexive endpoint graph: `tJExchange`
sums only over `SimpleGraph` adjacencies and `bipartiteCoupling` vanishes on the diagonal, so the
same-site entry `fermionSpinDot N x x` never reaches the capstone and is deliberately not treated.

## Debt

Two declarations are at reference 0. The `Ĥeff` corollary
`secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergOnMagSector` is staged for
PR-10 (endpoint Heisenberg Casimir) per the fixed PR order (issue #5320); the raw capstone it is
derived from is consumed inside this file by that corollary.
The convention guard `liebHardCoreToMagConfigS_apply_eq_zero_iff_up_occupied` is deliberate: it pins
the up/down reading of the sector `Equiv` in a single visible statement so that a silent flip of
the convention (which selects the mirror sector `M = nUp` and would break PR-10) fails loudly here
rather than downstream.

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

variable {N : ℕ}

/-! ## `Fin 2` occupation arithmetic -/

/-- The two occupation values of a singly occupied site are complementary. -/
private theorem fin2_one_sub_add_val (a : Fin 2) : (1 - a).val + a.val = 1 := by
  revert a; decide

/-- A singly occupied site's up occupation is the complement of its down occupation. -/
private theorem fin2_fst_eq_one_sub (a b : Fin 2) (h : a.val + b.val = 1) : a = 1 - b := by
  revert a b; decide

/-- A singly occupied site's down occupation is the complement of its up occupation. -/
private theorem fin2_snd_eq_one_sub (a b : Fin 2) (h : a.val + b.val = 1) : b = 1 - a := by
  revert a b; decide

/-! ## The hard-core half-filling predicate -/

/-- **The hard-core half-filled fixed-`Ŝ³` configuration predicate**: `liebHalfFillingPred` (half
filling, `nUp` up-spins) strengthened by single occupancy at every site. Unlike
`liebHalfFillingPred` alone, `configSector N (liebHardCoreHalfFillingPred N nUp)` *is* in bijection
with a spin-`1/2` magnetization sector (`liebHardCoreHalfFillingSectorEquivS` below), since single
occupancy is exactly what lets each site be read as a single spin-`1/2` degree of freedom. -/
abbrev liebHardCoreHalfFillingPred (N nUp : ℕ) : (Fin (2 * N + 2) → Fin 2) → Prop :=
  fun c => liebHalfFillingPred N nUp c ∧
    ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1

/-- A hard-core configuration carries no doubly occupied site, so it lies in `ker Ĥ₀`: the
interaction weight of `Ĥ₀` vanishes on it. This is the converse of
`liebHalfFilling_site_occupation` and is what lets the hard-core projection `P̂₀` act as the
identity on the sub-sector. -/
private theorem hubbardConfigInteractionWeight_one_eq_zero_of_singlyOccupied {N : ℕ}
    {c : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1) :
    hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 := by
  rw [hubbardConfigInteractionWeight]
  refine Finset.sum_eq_zero fun z _ => ?_
  rcases (show (c (spinfulIndex N z 0)).val = 0 ∨ (c (spinfulIndex N z 1)).val = 0 by
    have := hc z; omega) with h | h <;> rw [h] <;> simp

/-! ## The sector `Equiv`: forward direction (down-orbital occupation) -/

/-- The **down-orbital occupation** read off a Fock configuration: at each site `x`, whether the
down orbital is occupied (`1`) or not (`0`). On a hard-core configuration this is the sole
remaining spin-`1/2` degree of freedom once the up orbital's occupation is known to be the
complement. -/
def liebHardCoreDownOccupation {N : ℕ} (c : Fin (2 * N + 2) → Fin 2) : Fin (N + 1) → Fin 2 :=
  fun x => c (spinfulIndex N x 1)

/-- `liebHardCoreDownOccupation` lands in the magnetization sector `M = N + 1 − nUp`: the number of
down-occupied sites is the complement of the up-count `nUp` inside the `N + 1` singly-occupied
sites (`M` is the **down**-count, not `nUp`). -/
theorem liebHardCoreDownOccupation_magSumS_eq (N nUp : ℕ)
    {c : Fin (2 * N + 2) → Fin 2} (hc : liebHardCoreHalfFillingPred N nUp c) :
    magSumS (liebHardCoreDownOccupation c) = N + 1 - nUp := by
  have hsum : ∑ x : Fin (N + 1),
      ((c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val) = N + 1 := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hc.2 x]
    simp
  rw [Finset.sum_add_distrib, hc.1.2] at hsum
  have hdown : magSumS (liebHardCoreDownOccupation c)
      = ∑ x : Fin (N + 1), (c (spinfulIndex N x 1)).val := rfl
  omega

/-- The packaged forward map of the PR-9a sector `Equiv`: a hard-core half-filled configuration to
its magnetization-`(N + 1 − nUp)` spin-`1/2` configuration. -/
def liebHardCoreToMagConfigS (N nUp : ℕ) :
    configSector N (liebHardCoreHalfFillingPred N nUp) →
      magConfigS (Fin (N + 1)) 1 (N + 1 - nUp) :=
  fun c => ⟨liebHardCoreDownOccupation c.val,
    liebHardCoreDownOccupation_magSumS_eq N nUp c.property⟩

/-! ## The sector `Equiv`: backward direction -/

/-- The Fock configuration recovered from a spin-`1/2` configuration `σ`: site `x`'s up orbital is
occupied iff `σ x = 0`, and its down orbital iff `σ x = 1`. It is the `tJConfigOf` basis
configuration (`TJSectorBasis.lean`) of the t-J site-state reading `σ x = 0` as `↑` and `σ x = 1`
as `↓`, so the orbital-indexing arithmetic is reused rather than redone. -/
def liebHardCoreOfMagConfigSFock {N : ℕ} (σ : Fin (N + 1) → Fin 2) : Fin (2 * N + 2) → Fin 2 :=
  tJConfigOf N fun x => if σ x = 0 then 1 else 2

/-- `liebHardCoreOfMagConfigSFock σ` at the up-orbital `spinfulIndex x 0` is `1 − σ x`. -/
theorem liebHardCoreOfMagConfigSFock_apply_up (N : ℕ) (σ : Fin (N + 1) → Fin 2)
    (x : Fin (N + 1)) :
    liebHardCoreOfMagConfigSFock σ (spinfulIndex N x 0) = 1 - σ x := by
  simp only [liebHardCoreOfMagConfigSFock, tJConfigOf_apply_up]
  rcases fin2_eq_zero_or_one (σ x) with h | h <;> rw [h] <;> decide

/-- `liebHardCoreOfMagConfigSFock σ` at the down-orbital `spinfulIndex x 1` is `σ x`. -/
theorem liebHardCoreOfMagConfigSFock_apply_down (N : ℕ) (σ : Fin (N + 1) → Fin 2)
    (x : Fin (N + 1)) :
    liebHardCoreOfMagConfigSFock σ (spinfulIndex N x 1) = σ x := by
  simp only [liebHardCoreOfMagConfigSFock, tJConfigOf_apply_down]
  rcases fin2_eq_zero_or_one (σ x) with h | h <;> rw [h] <;> decide

/-- `liebHardCoreOfMagConfigSFock σ` lies in `liebHardCoreHalfFillingPred N nUp`, provided
`σ`'s magnetization sum is `N + 1 − nUp` and `nUp ≤ N + 1` (needed to recover `nUp` from the
truncated subtraction `N + 1 − (N + 1 − nUp)`). -/
theorem liebHardCoreOfMagConfigSFock_mem_pred (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    {σ : Fin (N + 1) → Fin 2} (hσ : magSumS σ = N + 1 - nUp) :
    liebHardCoreHalfFillingPred N nUp (liebHardCoreOfMagConfigSFock σ) := by
  have hsingle : ∀ z : Fin (N + 1),
      ((liebHardCoreOfMagConfigSFock σ) (spinfulIndex N z 0)).val
        + ((liebHardCoreOfMagConfigSFock σ) (spinfulIndex N z 1)).val = 1 := by
    intro z
    rw [liebHardCoreOfMagConfigSFock_apply_up, liebHardCoreOfMagConfigSFock_apply_down]
    exact fin2_one_sub_add_val (σ z)
  have hmag : ∑ x : Fin (N + 1), (σ x).val = N + 1 - nUp := hσ
  have hup : ∑ x : Fin (N + 1),
      ((liebHardCoreOfMagConfigSFock σ) (spinfulIndex N x 0)).val = nUp := by
    have hsum : ∑ x : Fin (N + 1),
        (((liebHardCoreOfMagConfigSFock σ) (spinfulIndex N x 0)).val + (σ x).val) = N + 1 := by
      have h1 : ∀ x : Fin (N + 1),
          ((liebHardCoreOfMagConfigSFock σ) (spinfulIndex N x 0)).val + (σ x).val = 1 := by
        intro x
        rw [liebHardCoreOfMagConfigSFock_apply_up]
        exact fin2_one_sub_add_val (σ x)
      rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => h1 x]
      simp
    rw [Finset.sum_add_distrib] at hsum
    omega
  refine ⟨⟨?_, hup⟩, hsingle⟩
  rw [sum_spinful_split N fun j => ((liebHardCoreOfMagConfigSFock σ) j).val,
    Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) => hsingle z]
  simp

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
  have hx : (c.val (spinfulIndex N x 0)).val + (c.val (spinfulIndex N x 1)).val = 1 :=
    c.property.2 x
  have hval : (liebHardCoreToMagConfigS N nUp c).val x = c.val (spinfulIndex N x 1) := rfl
  rw [hval]
  revert hx
  generalize c.val (spinfulIndex N x 0) = a
  generalize c.val (spinfulIndex N x 1) = b
  revert a b
  decide

/-- On a singly occupied configuration the backward map inverts the down-orbital read-off. -/
private theorem liebHardCoreOfMagConfigSFock_downOccupation {N : ℕ}
    {c : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1) :
    liebHardCoreOfMagConfigSFock (liebHardCoreDownOccupation c) = c := by
  funext k
  obtain ⟨t, r, rfl⟩ := exists_spinfulIndex N k
  rcases fin2_eq_zero_or_one r with rfl | rfl
  · rw [liebHardCoreOfMagConfigSFock_apply_up]
    exact (fin2_fst_eq_one_sub _ _ (hc t)).symm
  · rw [liebHardCoreOfMagConfigSFock_apply_down]
    rfl

/-- Two singly occupied configurations are equal iff their down-orbital occupations agree: the up
orbital is the complement, so the down occupation already determines the whole configuration. -/
theorem singlyOccupied_eq_iff_downOccupation {N : ℕ} {c e : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1)
    (he : ∀ z : Fin (N + 1), (e (spinfulIndex N z 0)).val + (e (spinfulIndex N z 1)).val = 1) :
    e = c ↔ liebHardCoreDownOccupation e = liebHardCoreDownOccupation c := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  rw [← liebHardCoreOfMagConfigSFock_downOccupation he,
    ← liebHardCoreOfMagConfigSFock_downOccupation hc, h]

/-- Round-trip 1: `invFun ∘ toFun = id` on the hard-core sector. -/
theorem liebHardCoreOfMagConfigS_liebHardCoreToMagConfigS (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (c : configSector N (liebHardCoreHalfFillingPred N nUp)) :
    liebHardCoreOfMagConfigS N nUp hnUp (liebHardCoreToMagConfigS N nUp c) = c :=
  Subtype.ext (liebHardCoreOfMagConfigSFock_downOccupation c.property.2)

/-- Round-trip 2: `toFun ∘ invFun = id` on the magnetization sector. -/
theorem liebHardCoreToMagConfigS_liebHardCoreOfMagConfigS (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (σ : magConfigS (Fin (N + 1)) 1 (N + 1 - nUp)) :
    liebHardCoreToMagConfigS N nUp (liebHardCoreOfMagConfigS N nUp hnUp σ) = σ :=
  Subtype.ext (funext fun x => liebHardCoreOfMagConfigSFock_apply_down N σ.val x)

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

/-- The sector `Equiv` reads off the down-orbital occupation (definitional unfolding, used to keep
the capstone's entrywise computation free of `Equiv` plumbing). -/
private theorem liebHardCoreHalfFillingSectorEquivS_val (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (s : configSector N (liebHardCoreHalfFillingPred N nUp)) :
    (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val = liebHardCoreDownOccupation s.val :=
  rfl

/-- The sector `Equiv` is injective, phrased on the underlying Fock configurations. -/
private theorem liebHardCoreHalfFillingSectorEquivS_eq_iff (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (s s' : configSector N (liebHardCoreHalfFillingPred N nUp)) :
    liebHardCoreHalfFillingSectorEquivS N nUp hnUp s
        = liebHardCoreHalfFillingSectorEquivS N nUp hnUp s' ↔ s.val = s'.val := by
  rw [Equiv.apply_eq_iff_eq]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-! ## The `t-J` reuse route -/

/-- The t-J site-state read off a hard-core configuration: `↑` (`1`) if the up orbital is occupied,
`↓` (`2`) otherwise (the down orbital must then be occupied, by single occupancy). -/
def liebHardCoreSiteState {N : ℕ} (c : Fin (2 * N + 2) → Fin 2) : Fin (N + 1) → Fin 3 :=
  fun x => if c (spinfulIndex N x 0) = 1 then 1 else 2

/-- `liebHardCoreSiteState c` never takes the "empty" value `0`: it reads every site as `↑` or `↓`
by construction, so no half-filling hypothesis is needed. -/
theorem liebHardCoreSiteState_ne_zero (N : ℕ) {c : Fin (2 * N + 2) → Fin 2} (x : Fin (N + 1)) :
    liebHardCoreSiteState c x ≠ 0 := by
  simp only [liebHardCoreSiteState]
  split_ifs <;> decide

/-- **The `tJConfigOf` round-trip**: for a hard-core half-filled configuration,
`liebHardCoreSiteState` recovers exactly `c` under `tJConfigOf` — the bridge letting the
already-proved (sign-free) `TJ*`
bond-action layer (`TJHalfFillingBondAction.lean`) apply verbatim, with no fresh
Jordan–Wigner-sign derivation for this sector. -/
theorem tJConfigOf_liebHardCoreSiteState_eq (N nUp : ℕ) {c : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) :
    tJConfigOf N (liebHardCoreSiteState c) = c := by
  funext k
  obtain ⟨t, r, rfl⟩ := exists_spinfulIndex N k
  have hsingle := hc.2 t
  rcases fin2_eq_zero_or_one r with rfl | rfl
  · rw [tJConfigOf_apply_up]
    by_cases hup : c (spinfulIndex N t 0) = 1
    · rw [show liebHardCoreSiteState c t = 1 from if_pos hup, if_pos rfl, hup]
    · rw [show liebHardCoreSiteState c t = 2 from if_neg hup,
        if_neg (by decide : ¬ ((2 : Fin 3) = 1)), fin2_eq_zero_of_ne_one hup]
  · rw [tJConfigOf_apply_down, fin2_snd_eq_one_sub _ _ hsingle]
    by_cases hup : c (spinfulIndex N t 0) = 1
    · rw [show liebHardCoreSiteState c t = 1 from if_pos hup,
        if_neg (by decide : ¬ ((1 : Fin 3) = 2)), hup]
      decide
    · rw [show liebHardCoreSiteState c t = 2 from if_neg hup, if_pos rfl,
        fin2_eq_zero_of_ne_one hup]
      decide

/-- On a hard-core configuration, `liebHardCoreSiteState`'s down-state marker is exactly the
down-orbital occupation, so the t-J site-state and the spin-`1/2` configuration carry the same
information. -/
private theorem liebHardCoreSiteState_eq_two_iff (N nUp : ℕ) {c : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (x : Fin (N + 1)) :
    liebHardCoreSiteState c x = 2 ↔ liebHardCoreDownOccupation c x = 1 := by
  have hsingle := hc.2 x
  simp only [liebHardCoreSiteState, liebHardCoreDownOccupation]
  by_cases hup : c (spinfulIndex N x 0) = 1
  · rw [if_pos hup]
    refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
    rw [hup] at hsingle
    rw [h] at hsingle
    exact absurd hsingle (by decide)
  · rw [if_neg hup]
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    rw [fin2_eq_zero_of_ne_one hup] at hsingle
    exact (fin2_snd_eq_one_sub _ _ hsingle).trans (by decide)

/-! ## The spin-`1/2` two-site dot in swap form -/

/-- The spin-`1/2` raising operator's matrix entries: `Ŝ⁺` is the single unit entry `(0, 1)`. -/
private theorem spinSOpPlus_one_apply (a b : Fin 2) :
    spinSOpPlus 1 a b = if a = 0 ∧ b = 1 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [spinSOpPlus]

/-- The spin-`1/2` lowering operator's matrix entries: `Ŝ⁻` is the single unit entry `(1, 0)`. -/
private theorem spinSOpMinus_one_apply (a b : Fin 2) :
    spinSOpMinus 1 a b = if a = 1 ∧ b = 0 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [spinSOpMinus]

/-- The spin-`1/2` `Ŝ³` matrix entries: `diag(½, −½)`. -/
private theorem spinSOp3_one_apply (a b : Fin 2) :
    spinSOp3 1 a b = if a = b then (if a = 0 then (1 / 2 : ℂ) else -(1 / 2)) else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [spinSOp3, Matrix.diagonal_apply]

/-- The two-site spin-`1/2` dot's matrix element factorised into per-site entries, for
configurations agreeing off `{x, y}` (`x ≠ y`): the ladder pairing plus the `Ŝ³ Ŝ³` diagonal. -/
private theorem spinSDot_one_apply_of_agree {N : ℕ} {x y : Fin (N + 1)} (hxy : x ≠ y)
    {σ' σ : Fin (N + 1) → Fin 2} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    spinSDot x y 1 σ' σ
      = (1 / 2 : ℂ) * (spinSOpPlus 1 (σ' x) (σ x) * spinSOpMinus 1 (σ' y) (σ y)
          + spinSOpMinus 1 (σ' x) (σ x) * spinSOpPlus 1 (σ' y) (σ y))
        + spinSOp3 1 (σ' x) (σ x) * spinSOp3 1 (σ' y) (σ y) := by
  rw [spinSDot_apply_eq_pm_3, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy h,
    onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree hxy h,
    onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- **The spin-`1/2` two-site dot in swap form** (`x ≠ y`): `Ŝ_x·Ŝ_y = −¼ + ½ P_{xy}`, where
`P_{xy}` is the transposition of the two sites' spins. Both the `Ŝ³Ŝ³` diagonal part and the
`Ŝ⁺Ŝ⁻ / Ŝ⁻Ŝ⁺` ladder part are packaged into this single two-term form, which is exactly the shape
the fermionic bond (`tJExchangeBond_mulVec_tJConfigOf_full`) produces on the singly-occupied
sector. Private: it exists only to feed
`fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied`. -/
private theorem spinSDot_one_apply_eq_of_ne {N : ℕ} {x y : Fin (N + 1)} (hxy : x ≠ y)
    (σ' σ : Fin (N + 1) → Fin 2) :
    spinSDot x y 1 σ' σ
      = -(1 / 4 : ℂ) * (if σ' = σ then 1 else 0)
        + (1 / 2 : ℂ) * (if σ' = fun k => σ (Equiv.swap x y k) then 1 else 0) := by
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · have heq1 : (σ' = σ) ↔ (σ' x = σ x ∧ σ' y = σ y) := by
      refine ⟨fun h => ⟨by rw [h], by rw [h]⟩, fun ⟨hx, hy⟩ => funext fun k => ?_⟩
      by_cases hkx : k = x
      · rw [hkx]; exact hx
      · by_cases hky : k = y
        · rw [hky]; exact hy
        · exact hagree k hkx hky
    have heq2 : (σ' = fun k => σ (Equiv.swap x y k)) ↔ (σ' x = σ y ∧ σ' y = σ x) := by
      constructor
      · intro h
        exact ⟨by rw [h]; simp, by rw [h]; simp⟩
      · rintro ⟨hx, hy⟩
        refine funext fun k => ?_
        by_cases hkx : k = x
        · rw [hkx, Equiv.swap_apply_left]; exact hx
        · by_cases hky : k = y
          · rw [hky, Equiv.swap_apply_right]; exact hy
          · rw [Equiv.swap_apply_of_ne_of_ne hkx hky]; exact hagree k hkx hky
    rw [spinSDot_one_apply_of_agree hxy hagree]
    simp only [heq1, heq2]
    rcases fin2_eq_zero_or_one (σ' x) with h1 | h1 <;>
      rcases fin2_eq_zero_or_one (σ x) with h2 | h2 <;>
        rcases fin2_eq_zero_or_one (σ' y) with h3 | h3 <;>
          rcases fin2_eq_zero_or_one (σ y) with h4 | h4 <;>
            rw [h1, h2, h3, h4] <;>
              norm_num [spinSOpPlus_one_apply, spinSOpMinus_one_apply, spinSOp3_one_apply]
  · rw [spinSDot_apply_eq_zero_of_off_two_site_diff hxy 1 hagree]
    have hne1 : σ' ≠ σ := fun h => hagree fun k _ _ => by rw [h]
    have hne2 : σ' ≠ fun k => σ (Equiv.swap x y k) := by
      intro h
      exact hagree fun k hkx hky => by
        simp only [h, Equiv.swap_apply_of_ne_of_ne hkx hky]
    rw [if_neg hne1, if_neg hne2]
    ring

/-! ## Entrywise operator correspondence -/

/-- **The diagonal number-operator constant**: on a hard-core half-filled ket configuration `c`,
`n̂_x n̂_y` collapses to the Kronecker delta `[e = c]` (every site of `c` is singly occupied, so
`n̂_x = n̂_y = 1` there; the bra `e` is arbitrary). Summed over the endpoint graph's
`2 |A| (N + 1 − |A|)` ordered adjacent pairs, this is what produces the exact
`|A| (N + 1 − |A|)` constant shift in the PR-9a capstones below. -/
theorem fermionSiteNumber_mul_apply_eq_ite_of_singlyOccupied (N nUp : ℕ) (x y : Fin (N + 1))
    {c e : Fin (2 * N + 2) → Fin 2} (hc : liebHardCoreHalfFillingPred N nUp c) :
    (fermionSiteNumber N x * fermionSiteNumber N y) e c = if e = c then 1 else 0 := by
  have hx : ((c (spinfulIndex N x 0)).val : ℂ) + ((c (spinfulIndex N x 1)).val : ℂ) = 1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (hc.2 x)
  have hy : ((c (spinfulIndex N y 0)).val : ℂ) + ((c (spinfulIndex N y 1)).val : ℂ) = 1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (hc.2 y)
  rw [← mulVec_basisVec_apply (fermionSiteNumber N x * fermionSiteNumber N y) e c,
    ← Matrix.mulVec_mulVec, fermionSiteNumber_mulVec_basisVec, Matrix.mulVec_smul,
    fermionSiteNumber_mulVec_basisVec, smul_smul, hx, hy, one_mul]
  simp only [Pi.smul_apply, smul_eq_mul, one_mul, basisVec_apply]

/-- **The crux entrywise identity**: on hard-core half-filled bra/ket configurations at distinct
sites, the fermionic two-site spin dot's matrix element equals the spin-`1/2` `spinSDot`'s matrix
element at the images under `liebHardCoreToMagConfigS` (the down-orbital occupation). Both the
`Ŝ³Ŝ³` diagonal and the `Ŝ⁺Ŝ⁻ / Ŝ⁻Ŝ⁺` off-diagonal parts of `fermionSpinDot`/`spinSDot` are covered
uniformly, through the common `−¼ + ½ P_{xy}` swap form: the fermionic side is
`tJExchangeBond_mulVec_tJConfigOf_full` and the spin side is `spinSDot_one_apply_eq_of_ne`.

`x ≠ y` is required and is not a restriction for the capstones: `tJExchange` sums only over
`SimpleGraph` adjacencies and `bipartiteCoupling` vanishes on the diagonal, so the same-site entry
never enters. -/
theorem fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied (N nUp : ℕ) {x y : Fin (N + 1)}
    (hxy : x ≠ y) {c e : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (he : liebHardCoreHalfFillingPred N nUp e) :
    (fermionSpinDot N x y) e c =
      spinSDot x y 1 (liebHardCoreDownOccupation e) (liebHardCoreDownOccupation c) := by
  have hcfg : tJConfigOf N (liebHardCoreSiteState c) = c :=
    tJConfigOf_liebHardCoreSiteState_eq N nUp hc
  have hswapVal : ∀ k : Fin (N + 1),
      tJSpinSwap (liebHardCoreSiteState c) x y k = liebHardCoreSiteState c (Equiv.swap x y k) :=
    congrFun (tJSpinSwap_eq_comp_swap (liebHardCoreSiteState c) x y)
  -- the swapped ket configuration is again singly occupied
  have hswapSingle : ∀ z : Fin (N + 1),
      ((tJConfigOf N (tJSpinSwap (liebHardCoreSiteState c) x y)) (spinfulIndex N z 0)).val
        + ((tJConfigOf N (tJSpinSwap (liebHardCoreSiteState c) x y))
            (spinfulIndex N z 1)).val = 1 := by
    intro z
    rw [tJConfigOf_apply_up, tJConfigOf_apply_down, hswapVal]
    rcases fin3_eq_zero_or_one_or_two (liebHardCoreSiteState c (Equiv.swap x y z)) with h | h | h
    · exact absurd h (liebHardCoreSiteState_ne_zero N _)
    · rw [h]; decide
    · rw [h]; decide
  -- and its down-orbital occupation is the site-swapped spin configuration
  have hswapDown : liebHardCoreDownOccupation (tJConfigOf N (tJSpinSwap
        (liebHardCoreSiteState c) x y))
      = fun k => liebHardCoreDownOccupation c (Equiv.swap x y k) := by
    funext k
    have hk : liebHardCoreDownOccupation (tJConfigOf N (tJSpinSwap
          (liebHardCoreSiteState c) x y)) k
        = if tJSpinSwap (liebHardCoreSiteState c) x y k = 2 then 1 else 0 :=
      tJConfigOf_apply_down N (tJSpinSwap (liebHardCoreSiteState c) x y) k
    rw [hk, hswapVal]
    by_cases hval : liebHardCoreSiteState c (Equiv.swap x y k) = 2
    · rw [if_pos hval]
      exact ((liebHardCoreSiteState_eq_two_iff N nUp hc _).mp hval).symm
    · rw [if_neg hval]
      refine (fin2_eq_zero_of_ne_one fun hcontra => hval ?_).symm
      exact (liebHardCoreSiteState_eq_two_iff N nUp hc _).mpr hcontra
  -- the fermionic bond action, read entrywise against the bra `e`
  have hbond := congrFun (tJExchangeBond_mulVec_tJConfigOf_full N (liebHardCoreSiteState c) x y hxy
    (liebHardCoreSiteState_ne_zero N x) (liebHardCoreSiteState_ne_zero N y)) e
  rw [hcfg] at hbond
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mulVec_basisVec_apply, Matrix.sub_apply,
    Matrix.smul_apply, basisVec_apply] at hbond
  rw [fermionSiteNumber_mul_apply_eq_ite_of_singlyOccupied N nUp x y hc] at hbond
  -- the spin side, in the same swap form
  rw [spinSDot_one_apply_eq_of_ne hxy]
  have hdelta : (if e = c then (1 : ℂ) else 0)
      = if liebHardCoreDownOccupation e = liebHardCoreDownOccupation c then 1 else 0 := by
    simp only [singlyOccupied_eq_iff_downOccupation hc.2 he.2]
  have hswapDelta :
      (if e = tJConfigOf N (tJSpinSwap (liebHardCoreSiteState c) x y) then (1 : ℂ) else 0)
      = if liebHardCoreDownOccupation e
          = fun k => liebHardCoreDownOccupation c (Equiv.swap x y k) then 1 else 0 := by
    simp only [singlyOccupied_eq_iff_downOccupation hswapSingle he.2, hswapDown]
  rw [← hdelta, ← hswapDelta]
  linear_combination -hbond

/-! ## The PR-9a capstone: reindexing onto the Heisenberg magnetization sector -/

/-- The inclusion of the hard-core sub-sector into the ambient half-filled sector: the
`.1`-projection of the conjunction defining `liebHardCoreHalfFillingPred`. -/
def liebHardCoreToAmbientSector (N nUp : ℕ) :
    configSector N (liebHardCoreHalfFillingPred N nUp) →
      configSector N (liebHalfFillingPred N nUp) :=
  fun s => ⟨s.val, s.property.1⟩

/-- The sub-sector inclusion keeps the underlying Fock configuration (definitional unfolding, used
to keep the capstone's entrywise computation free of subtype plumbing). -/
private theorem liebHardCoreToAmbientSector_val (N nUp : ℕ)
    (s : configSector N (liebHardCoreHalfFillingPred N nUp)) :
    (liebHardCoreToAmbientSector N nUp s).val = s.val := rfl

/-- The endpoint graph's adjacency indicator *is* the bipartite coupling at the sublattice
indicator of `A`; entry for entry, with no factor of `2`. -/
private theorem bipartiteCoupling_eq_liebEndpointGraph_indicator (N : ℕ)
    (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) :
    bipartiteCoupling (fun z => decide (z ∈ A)) x y
      = if (liebEndpointGraph A).Adj x y then (1 : ℂ) else 0 := by
  simp only [bipartiteCoupling, liebEndpointGraph_adj, ne_eq, decide_eq_decide]
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx, hy]

/-- The number of ordered adjacent pairs of the complete bipartite endpoint graph is
`2 |A| (N + 1 − |A|)`: the adjacency indicator *is* the bipartite coupling at `A`'s sublattice
indicator, so this is `bipartiteCoupling_sum` (`Quantum/MarshallLiebMattis/ToyHamiltonian.lean`)
with the two sublattice filters read back as `A` and `Aᶜ`. -/
private theorem sum_liebEndpointGraph_adj_eq (N : ℕ) (A : Finset (Fin (N + 1))) :
    ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (if (liebEndpointGraph A).Adj x y then (1 : ℂ) else 0)
      = 2 * (A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ) := by
  have hA : (Finset.univ.filter fun x : Fin (N + 1) => decide (x ∈ A) = true) = A := by
    ext z; simp
  have hAc : (Finset.univ.filter fun x : Fin (N + 1) => (!decide (x ∈ A)) = true) = Aᶜ := by
    ext z; simp
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) =>
        (bipartiteCoupling_eq_liebEndpointGraph_indicator N A x y).symm,
    bipartiteCoupling_sum, hA, hAc, Finset.card_compl, Fintype.card_fin]

/-- **PR-9a capstone (raw form)**: the PR-8b superexchange identity
(`kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection`,
`LiebRepulsiveSuperexchange.lean`), restricted to the hard-core sub-sector and reindexed along the
PR-9a `Equiv`, lands in the shape PR-10 needs: the constant `|A| (N + 1 − |A|)` minus the
antiferromagnetic Heisenberg matrix with coupling
`(2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))` on the magnetization-`(N + 1 − nUp)`
sector.

The constant is `2 κ` with `κ = ¼ · #{(x, y) : Adj} = |A| (N + 1 − |A|) / 2` the `tJExchange`-level
shift: the PR-8b capstone carries the extra factor `2` in
`P̂₀ V̂ V̂ P̂₀ = 2 • (P̂₀ · tJExchange · P̂₀)`,
which is the same factor that turns the bond coupling `bipartiteCoupling` into
`(2 : ℂ) • bipartiteCoupling`. -/
theorem kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection_reindex_eq
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    (LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      ).submatrix (liebHardCoreToAmbientSector N nUp) (liebHardCoreToAmbientSector N nUp)
      = (((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ)) • (1 : Matrix _ _ ℂ)
          - heisenbergHamiltonianSMatrixOnMagSector
              ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))) 1 (N + 1 - nUp)
        ).submatrix (liebHardCoreHalfFillingSectorEquivS N nUp hnUp)
          (liebHardCoreHalfFillingSectorEquivS N nUp hnUp) := by
  ext s s'
  have hs0 : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ))
      (liebHardCoreToAmbientSector N nUp s).val = 0 :=
    hubbardConfigInteractionWeight_one_eq_zero_of_singlyOccupied s.property.2
  have hs0' : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ))
      (liebHardCoreToAmbientSector N nUp s').val = 0 :=
    hubbardConfigInteractionWeight_one_eq_zero_of_singlyOccupied s'.property.2
  -- left-hand side: PR-8b, then `P̂₀ = 1` on the hard-core sub-sector, then the entrywise crux
  rw [Matrix.submatrix_apply,
    kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection N nUp hbip hT,
    kernelProjectionMatrix_liebPerturbationH0Compressed_eq_diagonal]
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  rw [if_pos hs0, if_pos hs0', one_mul, mul_one, configSectorCompress_apply,
    liebHardCoreToAmbientSector_val, liebHardCoreToAmbientSector_val]
  -- expand `tJExchange` entrywise through the crux identity
  have hexp : (tJExchange N (liebEndpointGraph A)) s.val s'.val
      = (1 / 4 : ℂ) * (if s.val = s'.val then 1 else 0)
            * ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
                (if (liebEndpointGraph A).Adj x y then (1 : ℂ) else 0)
          - ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
              (if (liebEndpointGraph A).Adj x y then
                  spinSDot x y 1 (liebHardCoreDownOccupation s.val)
                    (liebHardCoreDownOccupation s'.val)
                else 0) := by
    rw [tJExchange]
    simp only [Matrix.sum_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hadj : (liebEndpointGraph A).Adj x y
    · rw [if_pos hadj, if_pos hadj, if_pos hadj, mul_one, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul,
        fermionSiteNumber_mul_apply_eq_ite_of_singlyOccupied N nUp x y s'.property,
        fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied N nUp hadj.ne s'.property s.property]
    · rw [if_neg hadj, if_neg hadj, if_neg hadj, Matrix.zero_apply]
      ring
  rw [hexp, sum_liebEndpointGraph_adj_eq]
  -- right-hand side: unfold the sector matrix into the same double sum
  rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    heisenbergHamiltonianSMatrixOnMagSector_apply, heisenbergHamiltonianS_apply,
    liebHardCoreHalfFillingSectorEquivS_val, liebHardCoreHalfFillingSectorEquivS_val]
  have hone : (if liebHardCoreHalfFillingSectorEquivS N nUp hnUp s
        = liebHardCoreHalfFillingSectorEquivS N nUp hnUp s' then (1 : ℂ) else 0)
      = if s.val = s'.val then 1 else 0 := by
    simp only [liebHardCoreHalfFillingSectorEquivS_eq_iff]
  have hcoup : ∀ x y : Fin (N + 1),
      ((2 : ℂ) • bipartiteCoupling fun z => decide (z ∈ A)) x y
          * spinSDot x y 1 (liebHardCoreDownOccupation s.val)
              (liebHardCoreDownOccupation s'.val)
        = 2 * (if (liebEndpointGraph A).Adj x y then
            spinSDot x y 1 (liebHardCoreDownOccupation s.val)
              (liebHardCoreDownOccupation s'.val)
          else 0) := by
    intro x y
    have hsmul : ((2 : ℂ) • bipartiteCoupling fun z => decide (z ∈ A)) x y
        = 2 * bipartiteCoupling (fun z => decide (z ∈ A)) x y := rfl
    rw [hsmul, bipartiteCoupling_eq_liebEndpointGraph_indicator]
    by_cases hadj : (liebEndpointGraph A).Adj x y
    · rw [if_pos hadj, if_pos hadj]; ring
    · rw [if_neg hadj, if_neg hadj]; ring
  rw [hone, Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hcoup x y]
  simp only [← Finset.mul_sum]
  ring

/-- **PR-9a/PR-10-facing corollary**: the same reindexing applied to PR-8b's `Ĥeff` corollary
(`secondOrderEffectiveHamiltonian_liebPerturbation_eq_tJExchange`,
`LiebRepulsiveSuperexchange.lean`),
giving the second-order effective Hamiltonian directly as an antiferromagnetic Heisenberg matrix on
the magnetization sector plus the constant shift `−|A| (N + 1 − |A|)` — Tasaki's eq. (10.1.10) at
this arc's `U = 1`, `λ = 1` normalisation, in exactly the shape PR-10 needs to invoke Theorem 2.3
(`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`,
`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean`). -/
theorem secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergOnMagSector
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    (LatticeSystem.Math.secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)
      ).submatrix (liebHardCoreToAmbientSector N nUp) (liebHardCoreToAmbientSector N nUp)
      = (heisenbergHamiltonianSMatrixOnMagSector
              ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))) 1 (N + 1 - nUp)
          - (((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ))) • (1 : Matrix _ _ ℂ)
        ).submatrix (liebHardCoreHalfFillingSectorEquivS N nUp hnUp)
          (liebHardCoreHalfFillingSectorEquivS N nUp hnUp) := by
  have hneg : LatticeSystem.Math.secondOrderEffectiveHamiltonian
        (liebPerturbationH0Compressed N nUp) (liebPerturbationVCompressed N nUp A T)
        (liebPerturbationH0InvCompressed N nUp)
      = -(LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
          * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
          * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)) := by
    rw [secondOrderEffectiveHamiltonian_liebPerturbation_eq_tJExchange N nUp hbip hT,
      kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection N nUp hbip hT]
  ext s s'
  have hkey : (LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
          * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
          * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        ).submatrix (liebHardCoreToAmbientSector N nUp) (liebHardCoreToAmbientSector N nUp) s s'
      = (((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ)) • (1 : Matrix _ _ ℂ)
            - heisenbergHamiltonianSMatrixOnMagSector
                ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ A))) 1 (N + 1 - nUp)
          ).submatrix (liebHardCoreHalfFillingSectorEquivS N nUp hnUp)
            (liebHardCoreHalfFillingSectorEquivS N nUp hnUp) s s' := by
    rw [kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection_reindex_eq
      N nUp hnUp hbip hT]
  rw [Matrix.submatrix_apply] at hkey ⊢
  rw [hneg, Matrix.neg_apply, hkey]
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end LatticeSystem.Fermion
