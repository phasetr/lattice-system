import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCasimirPinning
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSU2Invariance
import LatticeSystem.Math.AngularMomentum.Multiplet
import LatticeSystem.Math.InvariantSubmoduleEigenvector
import LatticeSystem.Math.CommutingHermitianEigenvector
import LatticeSystem.Math.MatrixAnalysis.PiEuclideanEigenBridge

/-!
# SU(2) weight transport and the sector energy ladder (Tasaki §10.2.2, PR-14a)

Nineteenth installment of the Theorem 10.4 discharge arc (issue #5320). This file assembles the
first half (PR-14a) of the arc's final assembly step, per the "PR-10 through PR-14 design round"
(`.self-local/active/issue-5320.md`, PR-14 design round): for every admissible `Ŝ³` sector of the
physical symmetric repulsive Hamiltonian, the sector's unique ground state is a
`liebRepulsiveSpinCasimir A`-eigenvector of `Ŝ²`, all admissible sectors share the same ground
energy `E₀`, and `E₀` is minimal over the whole `(N+1)`-electron sector. The complementary weight
confinement + `finrank` count (PR-14b) and the axiom discharge itself (PR-15) are **not** in this
file's scope.

## Route

Reuses `ham_su2_multiplet_companion` (`Math/AngularMomentum/Multiplet.lean:56`) rather than the
highest-weight tower `highestWeight_spinMultiplet_general`, per the arc's main-agent decision
(the companion lemma manufactures the top state internally and carries the `Ĥ`/`N̂` eigenvalues
along, so no separate highest-weight certificate is needed). See the design round's "Route note"
for the full argument against the tower route.

## Contents (this file, PR-14a scope)

* `liebRepulsive_su2_weight_transport` — specializes `ham_su2_multiplet_companion` to the physical
  symmetric repulsive Hamiltonian: from a joint `(Ĥ, N̂, Ŝ³, Ŝ²)`-eigenvector, produces a nonzero
  companion at any admissible weight with the same `Ĥ` and `N̂` eigenvalues (steps 2/3 of the
  design round's closing argument).
* `liebRepulsive_admissibleSector_groundState_casimir_eigenvector` — per-admissible-sector step
  (step 1): the unique ground state on `numberSpinZSectorEuclidean` at an admissible `Ŝ³` value is
  an `Ŝ²`-eigenvector at `liebRepulsiveSpinCasimir A`, via `exists_unique_casimir_sector_strict_min`
  + `casimirSelector_strict_min_unique` + PR-13b's `s = 0` selector pinning.
* `liebRepulsive_multipletCompanion_capstone` — the PR-14a capstone: a single ground energy `E₀`
  such that every admissible `Ŝ³` sector has a unique ground state at `E₀` carrying the Casimir
  eigenvalue `liebRepulsiveSpinCasimir A`, and `E₀` is minimal over the whole `(N+1)`-electron
  sector (conjunct (ii) of `theorem_10_4_lieb_repulsive_half_filling`,
  `LiebRepulsive.lean:134`, restricted to the symmetric disjunct).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## Step 2/3: SU(2) weight transport for the physical Hamiltonian -/

/-- **SU(2) weight transport, specialized to the physical symmetric repulsive Hamiltonian.** From
a nonzero joint eigenvector `Φ` of `(Ĥ, N̂, Ŝ³, Ŝ²)` at real weight `m₀` and Casimir `J(J+1)`, for
every `k ≤ 2J` there is a nonzero companion `Ψ` at weight `m₀ − k` with the same `Ĥ`- and
`N̂`-eigenvalues (energy `E` and electron number `Ne`). Built from `ham_su2_multiplet_companion`
(`Multiplet.lean:56`), applied twice via its transport clause: once to `A = symmetricRepulsive...`,
once to `A = fermionTotalNumber`, using `symmetricRepulsiveHubbardHamiltonian_mul_tJTotalSpinOne`/
`Two` (`LiebRepulsiveSU2Invariance.lean`) and the analogous commutators for `fermionTotalNumber`
with `tJTotalSpinOne`/`Two`. -/
theorem liebRepulsive_su2_weight_transport
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    {Φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)} {Jr m₀ : ℝ} {E : ℂ} {Ne : ℂ}
    (hΦ : Φ ≠ 0) (hJ : 0 ≤ Jr)
    (hsq : Matrix.toEuclideanLin (fermionTotalSpinSquared N) Φ
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : Matrix.toEuclideanLin (fermionTotalSpinZ N) Φ = (m₀ : ℂ) • Φ)
    (hH : Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U) Φ = E • Φ)
    (hNe : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) Φ = Ne • Φ) :
    ∀ k : ℕ, (k : ℝ) ≤ 2 * Jr →
      ∃ Ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2), Ψ ≠ 0 ∧
        Matrix.toEuclideanLin (fermionTotalSpinSquared N) Ψ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Ψ ∧
        Matrix.toEuclideanLin (fermionTotalSpinZ N) Ψ = ((m₀ - k : ℝ) : ℂ) • Ψ ∧
        Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U) Ψ = E • Ψ ∧
        Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) Ψ = Ne • Ψ := by
  sorry

/-! ## Step 1: per-admissible-sector ground state is a Casimir eigenvector -/

/-- **Per-admissible-sector step (step 1 of the design round's closing argument).** For an
admissible `Ŝ³` value (indexed by `nUp`, `1 ≤ |A|`, `1 ≤ |B|`), the unique ground state `φ` of the
physical symmetric repulsive Hamiltonian on `numberSpinZSectorEuclidean N (N+1) m₀` is an
`Ŝ²`-eigenvector at `liebRepulsiveSpinCasimir A`. Combines
`repulsiveSpinZSector_ground_unique_on_numberSpinZSector`
(`LiebRepulsiveSectorBridgeFinal.lean:148`) with `exists_unique_casimir_sector_strict_min`
(`LiebRepulsiveCasimirSector.lean:116`), `casimirSelector_strict_min_unique`
(`LiebRepulsiveCasimirPinning.lean:63`), and the `s = 0` selector pinning
`symmetricHomotopy_casimirSelector_zero_eq_liebRepulsiveSpinCasimir`
(`LiebRepulsiveCasimirPinning.lean:339`). -/
theorem liebRepulsive_admissibleSector_groundState_casimir_eigenvector
    (N Ne : ℕ) (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    (nUp : ℕ) (hnUp : nUp ≤ N + 1) (hNe2 : Ne = 2 * nUp)
    {A : Finset (Fin (N + 1))} (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (E : ℝ) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      IsUniqueGroundStateOn
          (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
          (symmetricRepulsiveHubbardHamiltonian N T U) E φ ∧
        Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = liebRepulsiveSpinCasimir A • φ := by
  sorry

/-! ## PR-14a capstone -/

/-- **The PR-14a capstone.** For the physical symmetric repulsive Hubbard model at half-filling
(`1 ≤ |A|`, `1 ≤ |B|`), there is a single ground energy `E₀` such that every admissible `Ŝ³`
sector (indexed by `nUp` with `(N+1-nUp) ∈ tasaki23GroundStateSectors …`) has a unique ground state
at that energy, carrying the Casimir eigenvalue `liebRepulsiveSpinCasimir A`; moreover `E₀` is
minimal over the whole `(N+1)`-electron sector (conjunct (ii) of
`theorem_10_4_lieb_repulsive_half_filling`, `LiebRepulsive.lean:134`, symmetric disjunct only).
The energy-ladder equality across admissible sectors (step 3) is via
`liebRepulsive_su2_weight_transport`; global minimality (step 4) is via
`exists_eigenvector_in_invariant_submodule`
(`Math/InvariantSubmoduleEigenvector.lean:29`, applied twice) and
`isHermitian_mulVec_eigenvalue_eq_ofReal` (`Math/CommutingHermitianEigenvector.lean:130`).

PR-14b's weight confinement and `finrank` count (the remaining two conjuncts of Theorem 10.4) are
**not** part of this capstone. -/
theorem liebRepulsive_multipletCompanion_capstone
    (N : ℕ) {A : Finset (Fin (N + 1))} (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (hbip : HoppingRespectsBipartition A T) (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) {lam : ℝ} (hlam : 0 < lam) :
    ∃ E₀ : ℝ,
      (∀ nUp : ℕ, nUp ≤ N + 1 →
        (N + 1 - nUp) ∈ tasaki23GroundStateSectors
            (fun x => decide (x ∈ liebOrientedSublattice A)) 1 →
        ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
          IsUniqueGroundStateOn
              (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp))
              (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
            Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ
              = liebRepulsiveSpinCasimir A • φ) ∧
      ∀ E : ℂ,
        hubbardGroundSubmoduleAtElectronNumber
            (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
        E₀ ≤ E.re := by
  sorry

end LatticeSystem.Fermion
