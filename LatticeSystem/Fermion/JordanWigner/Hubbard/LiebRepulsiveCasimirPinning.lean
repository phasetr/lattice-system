import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveEndpointIdentification
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveUniquenessAssembly
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveTheorem23Instance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSectorBridgeFinal

/-!
# Casimir pinning `c 0 = liebRepulsiveSpinCasimir A` (Tasaki §10.2.2, PR-13b)

Eighteenth installment of the Theorem 10.4 discharge arc (issue #5320). **Red scaffolding only**:
every declaration in this file is a type signature closed by `sorry`, following the PR-13 design
round (`.self-local/active/issue-5320.md`, "PR-13 design round" / "The Casimir pinning argument
(task (c))"). `dev-implement` supplies the proofs.

## Main results (statements only, all `sorry`)

* `casimirSelector_strict_min_unique` — **selector uniqueness**: two occupied Casimir eigenvalues
  each satisfying the strict-minimality property of
  `exists_unique_casimir_sector_strict_min` (`LiebRepulsiveCasimirSector.lean:114`) for the *same*
  Hamiltonian must coincide. The ~15-line lemma the design round calls "new, needed anyway".
* `symmetricHomotopyHamiltonian_one_isUniqueGroundStateOn` — the PR-13a-scoped λ-family transport
  capstone left undelivered by PR-13a: for every `λ ∈ (0, λ₀)`,
  `IsUniqueGroundStateOn K (symmetricHomotopyHamiltonian N A T U lam 1) E_λ φ_λ` on the joint
  number/spin-`z` sector `K = numberSpinZSectorEuclidean N (N+1) m₀`, obtained by transporting
  `tasaki_lemma_10_1_liebRepulsive_apply`'s (extended) compressed uniqueness up along
  `coordinateExtend` and the generalized `isUniqueGroundStateOn_coordinateSpan_iff_submatrix`
  (`Math/MatrixAnalysis/BlockTransport.lean:229`).
* `symmetricHomotopy_casimirSelector_zero_eq_liebRepulsiveSpinCasimir` — the arc's Casimir-pinning
  capstone: extends PR-12b's `symmetricHomotopy_casimirSelector_eq_const`
  (`LiebRepulsiveSymmetricHomotopy.lean:165`, `c 0 = c 1`) conclusion with
  `c 0 = liebRepulsiveSpinCasimir A`, via the `λ → 0` limit of the occupied Casimir eigenvalue along
  the λ-family above, selector uniqueness against PR-10b's
  `liebRepulsive_groundState_casimir_eq_predicted`
  (`LiebRepulsiveTheorem23Instance.lean:310`), and the endpoint identification of
  `LiebRepulsiveEndpointIdentification.lean`. No finite-spectrum argument is used (design round:
  "no finiteness argument needed").

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators Topology

variable {N : ℕ}

/-! ## Selector uniqueness -/

/-- **Selector uniqueness.** If `c₁` and `c₂` are both occupied Casimir eigenvalues of the same
Hamiltonian `H` satisfying the strict-minimality property of `exists_unique_casimir_sector_strict_min`
(each sector's minimum energy is `E₁`/`E₂` respectively, and every *other* occupied sector's minimum
energy is strictly higher), then `c₁ = c₂`: applying `c₁`'s strict inequality at the comparison
sector `c₂` (occupied, since `h₂.1`) forces `E₁ < minEnergyOn K_{c₂} H = E₂` unless `c₁ = c₂`, and
symmetrically `E₂ < E₁` unless `c₂ = c₁`; both cannot hold simultaneously. -/
theorem casimirSelector_strict_min_unique {L m₀ : ℂ} {H : ManyBodyOp (Fin (2 * N + 2))}
    {c₁ c₂ : ℂ} {E₁ E₂ : ℝ}
    (h₁ : numberSpinZCasimirSectorEuclidean N L m₀ c₁ ≠ ⊥ ∧
      minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c₁) H = E₁ ∧
      ∀ c' : ℂ, c' ≠ c₁ → numberSpinZCasimirSectorEuclidean N L m₀ c' ≠ ⊥ →
        E₁ < minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c') H)
    (h₂ : numberSpinZCasimirSectorEuclidean N L m₀ c₂ ≠ ⊥ ∧
      minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c₂) H = E₂ ∧
      ∀ c' : ℂ, c' ≠ c₂ → numberSpinZCasimirSectorEuclidean N L m₀ c' ≠ ⊥ →
        E₂ < minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c') H) :
    c₁ = c₂ := by
  sorry

/-! ## PR-13a-scoped λ-family transport (moved from PR-13a, delivered here) -/

/-- **The λ-family transport capstone left undelivered by PR-13a.** For a nondegenerate bipartition
and an admissible magnetization sector, the `s = 1` endpoint of the symmetric-form homotopy has,
for every sufficiently small `λ > 0`, a unique ground state on the joint number/spin-`z` sector
`K = numberSpinZSectorEuclidean N (N+1) (liebHalfFillingSpinZVal N nUp)`. Route: transport
`tasaki_lemma_10_1_liebRepulsive_apply`'s compressed λ-family uniqueness
(`LiebRepulsiveUniquenessAssembly.lean:153`) up along `coordinateExtend` and the generalized
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix`, then along
`configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul`
(`LiebRepulsiveEndpointIdentification.lean:105`) and `isUniqueGroundStateOn_sub_smul_one_iff`
(`Math/MatrixAnalysis/SubmatrixGroundState.lean`) to remove the constant shift, and finally along
`numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred`
(`LiebRepulsiveSectorBridgeFinal.lean:87`) to land on `numberSpinZSectorEuclidean`. -/
theorem symmetricHomotopyHamiltonian_one_isUniqueGroundStateOn
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (A : Finset (Fin (N + 1))) (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1)
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ) :
    ∃ lam0 : ℝ, 0 < lam0 ∧
      ∃ Elam : ℝ → ℝ,
      ∃ philam : ℝ → EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        ∀ lam : ℝ, 0 < lam → lam < lam0 →
          IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp))
            (symmetricHomotopyHamiltonian N A T U lam 1) (Elam lam) (philam lam) := by
  sorry

/-! ## The Casimir pinning capstone -/

/-- **The arc's Casimir-pinning capstone.** Extends PR-12b's
`symmetricHomotopy_casimirSelector_eq_const` (`LiebRepulsiveSymmetricHomotopy.lean:165`) with the
identification `c 0 = liebRepulsiveSpinCasimir A`. Route (design round, "no finiteness argument
needed"): for `λ ∈ (0, λ₀)`, the λ-family transport above supplies a unique ground state `φ_λ` on
`K`; `exists_unique_casimir_sector_strict_min` (extended with its membership conjunct) gives an
occupied Casimir eigenvalue `c_λ` with `Ŝ² φ_λ = c_λ • φ_λ` and the strict-min property; selector
uniqueness (`casimirSelector_strict_min_unique` above) forces `c_λ = c 1 = c 0` (PR-12b); as
`λ → 0⁺`, `φ_λ → φeff := coordinateExtend _ Φeff` (`Φeff` from the extended
`tasaki_lemma_10_1_liebRepulsive_apply`) and `c_λ = ⟪φ_λ, Ŝ² φ_λ⟫ → ⟪φeff, Ŝ² φeff⟫`; since
`c_λ` is eventually constant at `c 0`, uniqueness of limits gives `c 0 = ⟪φeff, Ŝ² φeff⟫` exactly;
finally `Ŝ² φeff = liebRepulsiveSpinCasimir A • φeff` by mutual ground-energy minimality and
proportionality against PR-10b's `liebRepulsive_groundState_casimir_eq_predicted`
(`LiebRepulsiveTheorem23Instance.lean:310`). -/
theorem symmetricHomotopy_casimirSelector_zero_eq_liebRepulsiveSpinCasimir (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    (nUp : ℕ) (hnUp : nUp ≤ N + 1) (hNe2 : Ne = 2 * nUp)
    {A : Finset (Fin (N + 1))} (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℝ → ℂ,
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
            (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) (c s) ≠ ⊥ ∧
          ∀ c' : ℂ, c' ≠ c s →
            numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c' ≠ ⊥ →
              minEnergyOn
                  (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                    (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c')
                  (symmetricHomotopyHamiltonian N A T U lam s) >
                minEnergyOn
                  (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                    (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) (c s))
                  (symmetricHomotopyHamiltonian N A T U lam s)) ∧
      c 0 = c 1 ∧
      c 0 = liebRepulsiveSpinCasimir A := by
  sorry

end LatticeSystem.Fermion
