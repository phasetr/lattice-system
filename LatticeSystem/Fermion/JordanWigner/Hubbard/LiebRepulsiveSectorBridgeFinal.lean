import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCasimirSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsivePerturbationSetup
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaSector
import LatticeSystem.Math.MatrixAnalysis.SubmatrixGroundState

/-!
# The three-way sector bridge for Theorem 10.4 (Tasaki §10.2.2, PR-11c)

Fourteenth installment of the Theorem 10.4 discharge arc (issue #5320). Three distinct
descriptions of the half-filled fixed-`Ŝ³` sector are in play across the arc, and until this file
no lemma connects them:

* `numberSpinZSectorEuclidean N L m₀` (`LiebRepulsiveCasimirSector.lean`, PR-3) — the joint
  eigenspace intersection `{N̂ = L} ⊓ {Ŝ³ = m₀}`, the sector PR-3's Casimir machinery
  (`exists_unique_casimir_sector_strict_min`) is stated on.
* `spinZSectorEuclidean N m₀` (`LiebRepulsiveBalancedGround.lean`, PR-1) — the spin-`z`-only
  eigenspace `{Ŝ³ = m₀}`, the sector PR-1's `repulsiveSpinZSector_ground_unique` is stated on.
* `configSector N (liebHalfFillingPred N nUp)` (`LiebRepulsivePerturbationSetup.lean`, PR-5) — the
  configuration-basis subtype `{c // liebHalfFillingPred N nUp c}` that the homotopy/perturbation
  machinery (PR-5 through PR-11b) compresses onto.

Since `N̂` and `Ŝ³` are both diagonal in the computational configuration basis
(`fermionTotalNumber_eq_diagonal`, `fermionTotalSpinZ_eq_diagonal`,
`LiebRepulsiveShibaSector.lean`), all three coincide as subspaces of
`EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)` at the matching
parameters `L = N + 1`, `m₀ = (2 nUp − (N + 1))/2`. This file supplies that missing bridge, plus
the downward restriction of PR-1's `repulsiveSpinZSector_ground_unique` from `spinZSectorEuclidean`
to `numberSpinZSectorEuclidean` — a debt open since PR-3, whose Casimir machinery consumes ground
state uniqueness on the joint sector but could only take it as an abstract hypothesis — and a
capstone that pins down exactly what remains before `theorem_10_4_lieb_repulsive_half_filling`
(`LiebRepulsive.lean:134`) can be discharged.

## Contents

* `liebHalfFillingSpinZVal` — the `nUp`-parameterized spin-`z` eigenvalue `m₀ = (2 nUp − (N+1))/2`,
  pinned as its own named quantity so that the bridge is stated with `nUp` as the primitive.
* `numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred` — the diagonal-charge bridge
  `numberSpinZSectorEuclidean N (N+1) m₀ = coordinateSpan (liebHalfFillingPred N nUp)`.
* `numberSpinZSectorEuclidean_le_spinZSectorEuclidean` — the definitional inclusion
  `numberSpinZSectorEuclidean N (N+1) m₀ ≤ spinZSectorEuclidean N m₀`.
* `repulsiveSpinZSector_ground_unique_on_numberSpinZSector` — PR-1's uniqueness result, restricted
  downward to the joint sector `numberSpinZSectorEuclidean` (discharges the PR-3 debt).
* `liebRepulsive_exists_unique_casimir_sector` — capstone: combines the restriction above with
  PR-3's `exists_unique_casimir_sector_strict_min`, explicitly exposing the SU(2) commute
  adapters (`Commute` with `N̂`, `Ŝ³`, `Ŝ²`) and Hermiticity of the symmetric repulsive Hamiltonian
  as hypotheses. Those adapters are available for `hubbardHamiltonian`
  (`SaturatedFerromagnetism.lean`) and for `attractiveHubbardHamiltonian`
  (`LiebAttractiveSU2Invariance.lean`), but not yet for `repulsiveHubbardHamiltonian` /
  `symmetricRepulsiveHubbardHamiltonian`; supplying them is scheduled PR-12 work. This pins down
  the exact remaining obligations of the arc before Theorem 10.4 itself can be discharged: (1) the
  SU(2) commute/Hermiticity adapters below, (2) identifying the occupied Casimir eigenvalue with
  `liebRepulsiveSpinCasimir A` via the homotopy continuity of PR-4 and PR-11b's Lemma 10.1
  application, (3) the site-dependent `U_x → U` reduction (or, in its place, a homotopy run along
  the site-dependent path `U_x(s) = (1 − s) U_x + s`), and (4) the finrank/degeneracy count
  assembly (PR-13/PR-14).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

/-! ## The `nUp`-parameterized spin-`z` sector arithmetic -/

/-- **The spin-`z` eigenvalue of the half-filled sector, parameterized by `nUp`.**
`m₀ = (2 nUp − (N+1))/2`, matching `liebHalfFillingPred N nUp`'s convention (`∑ c(x,↑) = nUp`) and
`repulsiveSpinZSector_ground_unique`'s convention (`m = (Ne − (N+1))/2` at `Ne = 2 nUp`). Stated as
its own named quantity so that `nUp` stays the primitive of the bridge, avoiding the cast-inversion
trap of recovering the natural number `nUp` from a complex `m₀`. -/
noncomputable def liebHalfFillingSpinZVal (N nUp : ℕ) : ℂ :=
  ((2 * nUp : ℂ) - ((N : ℂ) + 1)) / 2

/-! ## The three-way sector bridge -/

/-- **The diagonal-charge bridge.** The joint number/spin-`z` sector `K = {N̂ = N+1} ⊓ {Ŝ³ = m₀}`
(`numberSpinZSectorEuclidean`, PR-3) equals the coordinate span of the configuration-basis
predicate `liebHalfFillingPred N nUp` (PR-5), at the matching parameter `m₀ =
liebHalfFillingSpinZVal N nUp`. Both `N̂` and `Ŝ³` are diagonal in the computational configuration
basis (`fermionTotalNumber_eq_diagonal`, `fermionTotalSpinZ_eq_diagonal`), so this is the
generic eigenspace-intersection identity `eigenspace_diagonal_eq_coordinateSpan` applied twice,
composed via `coordinateSpan_inf_coordinateSpan`. The `Ŝ³` factor alone constrains only the
*difference* `n_↑ − n_↓`; it is the number condition `n_↑ + n_↓ = N + 1` that turns the pair into
the up-count condition `n_↑ = nUp` of `liebHalfFillingPred`. -/
theorem numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred (N nUp : ℕ) :
    numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp)
      = coordinateSpan (liebHalfFillingPred N nUp) := by
  -- The `N̂` condition, in the configuration basis: `∑_j c j = N + 1`.
  have hN : Module.End.eigenspace
        (Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1))) ((N : ℂ) + 1)
      = coordinateSpan (fun c : Fin (2 * N + 2) → Fin 2 =>
          (∑ j : Fin (2 * N + 2), (c j).val) = N + 1) := by
    rw [fermionTotalNumber_eq_diagonal]
    refine eigenspace_diagonal_eq_coordinateSpan _ _ _ fun c => ?_
    rw [← Nat.cast_sum, show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Nat.cast_inj]
  -- The `Ŝ³` condition, cleared of the ambient subtraction: `n_↑ + (N+1) = 2 nUp + n_↓`.
  have hS3 : Module.End.eigenspace
        (Matrix.toEuclideanLin (fermionTotalSpinZ N)) (liebHalfFillingSpinZVal N nUp)
      = coordinateSpan (fun c : Fin (2 * N + 2) → Fin 2 =>
          (∑ x : Fin (N + 1), (c (spinfulIndex N x 0)).val) + (N + 1)
            = 2 * nUp + ∑ x : Fin (N + 1), (c (spinfulIndex N x 1)).val) := by
    rw [fermionTotalSpinZ_eq_diagonal]
    refine eigenspace_diagonal_eq_coordinateSpan _ _ _ fun c => ?_
    rw [← Nat.cast_sum, ← Nat.cast_sum, liebHalfFillingSpinZVal]
    constructor
    · intro h
      have h' : ((∑ x : Fin (N + 1), (c (spinfulIndex N x 0)).val : ℕ) : ℂ) + ((N : ℂ) + 1)
          = 2 * (nUp : ℂ) + ((∑ x : Fin (N + 1), (c (spinfulIndex N x 1)).val : ℕ) : ℂ) := by
        linear_combination 2 * h
      exact_mod_cast h'
    · intro h
      have h' : ((∑ x : Fin (N + 1), (c (spinfulIndex N x 0)).val : ℕ) : ℂ) + ((N : ℂ) + 1)
          = 2 * (nUp : ℂ) + ((∑ x : Fin (N + 1), (c (spinfulIndex N x 1)).val : ℕ) : ℂ) := by
        exact_mod_cast h
      linear_combination h' / 2
  rw [numberSpinZSectorEuclidean, spinZSectorEuclidean, hN, hS3]
  refine coordinateSpan_inf_coordinateSpan _ _ _ fun c => ?_
  have hsplit : (∑ j : Fin (2 * N + 2), (c j).val)
      = (∑ x : Fin (N + 1), (c (spinfulIndex N x 0)).val)
        + ∑ x : Fin (N + 1), (c (spinfulIndex N x 1)).val := by
    rw [sum_spinful_split N fun j => (c j).val, Finset.sum_add_distrib]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩

/-- **The definitional inclusion** `numberSpinZSectorEuclidean N (N+1) m₀ ≤ spinZSectorEuclidean N
m₀`: the joint sector `K` (fixing both `N̂` and `Ŝ³`) is contained in the spin-`z`-only sector
(fixing `Ŝ³` alone), since `K` unfolds to an infimum with `spinZSectorEuclidean` as its right
factor (`numberSpinZSectorEuclidean`, `LiebRepulsiveCasimirSector.lean:55-58`). -/
theorem numberSpinZSectorEuclidean_le_spinZSectorEuclidean (N : ℕ) (m₀ : ℂ) :
    numberSpinZSectorEuclidean N ((N : ℂ) + 1) m₀ ≤ spinZSectorEuclidean N m₀ := by
  rw [numberSpinZSectorEuclidean]
  exact inf_le_right

/-! ## Downward restriction of PR-1's uniqueness (discharges the PR-3 debt) -/

/-- **PR-1's uniqueness, restricted to the joint number/spin-`z` sector.** This supplies the
`IsUniqueGroundStateOn`-on-`K` hypothesis that PR-3's `exists_unique_casimir_sector_strict_min`
(`LiebRepulsiveCasimirSector.lean`) consumes, which PR-3 itself could only state abstractly.
Restricts `repulsiveSpinZSector_ground_unique`'s conclusion from `spinZSectorEuclidean N m` down to
`numberSpinZSectorEuclidean N (N+1) m` via `IsUniqueGroundStateOn.mono`, using the same PR-1
witness `φ`, whose membership in the smaller sector follows from the number-operator eigenvalue
conjunct `N̂ φ = (N+1) • φ` already exported by `repulsiveSpinZSector_ground_unique`. -/
theorem repulsiveSpinZSector_ground_unique_on_numberSpinZSector (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn
          (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
          (symmetricRepulsiveHubbardHamiltonian N T U) E φ := by
  obtain ⟨E, φ, -, hGS, -, -, hnum⟩ :=
    repulsiveSpinZSector_ground_unique N Ne hNe_even hNe_pos hNe_lt T hT_symm hbip hT_conn U hU_pos
  refine ⟨E, φ, IsUniqueGroundStateOn.mono
    (numberSpinZSectorEuclidean_le_spinZSectorEuclidean N _) ?_ hGS⟩
  rw [numberSpinZSectorEuclidean, Submodule.mem_inf]
  exact ⟨Module.End.mem_eigenspace_iff.mpr hnum, hGS.1⟩

/-! ## Capstone: remaining obligations before Theorem 10.4's discharge -/

/-- **Capstone (PR-11c).** Assuming the SU(2) commute/Hermiticity adapters for the symmetric
repulsive Hubbard Hamiltonian — `Commute` with `N̂`, `Ŝ³`, `Ŝ²`, and `IsHermitian` — the
repulsive model's unique ground state on the joint number/spin-`z` sector occupies a unique,
strictly-minimal occupied Casimir sector (PR-3's `exists_unique_casimir_sector_strict_min`, fed by
this file's restriction bridge `repulsiveSpinZSector_ground_unique_on_numberSpinZSector`). PR-12a
(`LiebRepulsiveSU2Invariance.lean`) has since supplied these adapters and packages the
unconditional corollary `liebRepulsive_exists_unique_casimir_sector_unconditional`; this theorem
keeps them as explicit hypotheses so the adapter-discharge step stays separable from the sector
bridge.

This capstone pins down **exactly** what remains before `theorem_10_4_lieb_repulsive_half_filling`
(`LiebRepulsive.lean:134`) can be discharged, beyond what this arc has already proved:

1. The SU(2) commute/Hermiticity adapters taken as hypotheses here — supplied by PR-12a
   (`LiebRepulsiveSU2Invariance.lean`).
2. Identifying the occupied Casimir eigenvalue `c` with `liebRepulsiveSpinCasimir A` — via the
   homotopy continuity of PR-4 (`casimirSelector_eq_const_of_locally_unique_strict_min`) and
   PR-11b's Lemma 10.1 application (`tasaki_lemma_10_1_liebRepulsive_apply`) transported along
   this file's sector bridge (PR-12/PR-13).
3. The site-dependent `U_x → U` reduction for the general symmetric form (PR-12b). Expanding the
   symmetric form at a genuine `U : Λ → ℝ` produces the term `−(1/2) ∑_x U_x (n̂_{x,↑} + n̂_{x,↓})`,
   a site-dependent one-body potential rather than a multiple of `N̂`, so no constant energy shift
   reduces it to the uniform form. The alternative is to run the homotopy along the site-dependent
   path `U_x(s) = (1 − s) U_x + s`, whose endpoint `U_x = 1` differs from the uniform form by
   `−(1/2) N̂ + ((N+1)/4) • 1`, which *is* constant on the fixed `N̂ = N + 1` sector.
4. The finrank/degeneracy count assembly, `dim G = |A| − |B| + 1` (PR-13/PR-14), and the direct
   `A = ∅` / `A = univ` endpoint cases (PR-14). -/
theorem liebRepulsive_exists_unique_casimir_sector (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    (hH : (symmetricRepulsiveHubbardHamiltonian N T U).IsHermitian)
    (hHN : Commute (symmetricRepulsiveHubbardHamiltonian N T U)
      (fermionTotalNumber (2 * N + 1)))
    (hHS3 : Commute (symmetricRepulsiveHubbardHamiltonian N T U) (fermionTotalSpinZ N))
    (hHS2 : Commute (symmetricRepulsiveHubbardHamiltonian N T U)
      (fermionTotalSpinSquared N)) :
    ∃ c : ℂ,
      numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
          (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c ≠ ⊥ ∧
        ∀ c' : ℂ, c' ≠ c →
          numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
              (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c' ≠ ⊥ →
            minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c)
                (symmetricRepulsiveHubbardHamiltonian N T U) <
              minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c')
                (symmetricRepulsiveHubbardHamiltonian N T U) := by
  obtain ⟨E, φ, hGS⟩ := repulsiveSpinZSector_ground_unique_on_numberSpinZSector N Ne hNe_even
    hNe_pos hNe_lt T hT_symm hbip hT_conn U hU_pos
  obtain ⟨c, hKcne, hKcmin, hstrict⟩ :=
    exists_unique_casimir_sector_strict_min hH hHN hHS3 hHS2 hGS
  refine ⟨c, hKcne, fun c' hcc' hc'ne => ?_⟩
  rw [hKcmin]
  exact hstrict c' hcc' hc'ne

end LatticeSystem.Fermion
