import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismGroundTower

/-!
# §10.2.3 Theorem 10.6 — ground-multiplet tower basis (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356.)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismGroundTower.lean` (PR-5 of the
Theorem 10.6 discharge arc, issue #5347). The `example`s pin down the exact signatures of the
seven declarations `L0`–`L7` of the confirmed design
(`.self-local/docs/theorem-10-6-pr5-design.md`, 2026-08-24): the general weight-band bound `L0`,
the `Ŝ³`-weight band `L1`, the top-weight existence `L2`, tower-membership `L3`, tower
nonvanishing `L4`, tower linear independence `L5`, the ground-submodule span identity `L6`, and the
weight-orthogonal cross-term vanishing `L7`. This is **RED**: none of these declarations exist yet
(the module they live in, `LiebFerrimagnetismGroundTower.lean`, is not written), so this file does
not compile — that is the intended failing state before implementation. Mirrors the specification
style of `Tests/LiebFerrimagnetismLadderRatio.lean` / `Tests/LiebFerrimagnetismSU2Invariance.lean`.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismGroundTower

open Matrix LatticeSystem.Fermion LatticeSystem.Quantum

/-! ## `L0` — general `Ŝ³`-weight band from an arbitrary Casimir eigenvalue -/

/-- **`L0`: general weight-band bound.** A nonzero joint eigenvector of `(Ŝ_tot)²` (eigenvalue
`Jr(Jr+1)`, `Jr ≥ 0`) and `Ŝ³_tot` (eigenvalue `m`) has `|m| ≤ Jr`. Factored out of the two inline
copies at `LiebAttractiveFullSectorUnique.lean:275-283` and
`LiebRepulsiveMultipletCompanion.lean:388-397` (design §2 `L0`). -/
example (N : ℕ) {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw : w ≠ 0)
    {Jr m : ℝ} (hJ : 0 ≤ Jr)
    (hcas : (fermionTotalSpinSquared N).mulVec w = ((Jr * (Jr + 1) : ℝ) : ℂ) • w)
    (h3 : (fermionTotalSpinZ N).mulVec w = (m : ℂ) • w) :
    |m| ≤ Jr :=
  fermionTotalSpin_abs_weight_le N (hw := hw) (hJ := hJ) (hcas := hcas) (h3 := h3)

/-! ## `L1` — the `Ŝ³`-weight band on the repulsive ground submodule -/

/-- **`L1`: ground-submodule weight band.** Any nonzero `Ŝ³_tot`-eigenvector `w` (eigenvalue `m`)
in the `(N+1)`-electron ground submodule `G` of `symmetricRepulsiveHubbardHamiltonian N T U` at
`E₀` satisfies `|m| ≤ ||A| − |B||/2`, the `L0` band instantiated at `Jr := sublatticeImbalance A / 2`
using the Theorem 10.4 Casimir conclusion `hcas`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hw0 : w ≠ 0) {m : ℝ}
    (h3 : (fermionTotalSpinZ N).mulVec w = (m : ℂ) • w) :
    |m| ≤ (sublatticeImbalance A : ℝ) / 2 :=
  liebRepulsive_ground_spinZ_abs_le N A T U E₀ (hcas := hcas) (hwG := hwG) (hw0 := hw0)
    (h3 := h3)

/-! ## `L2` — existence of a top-weight vector in the ground submodule -/

/-- **`L2`: top-weight existence.** If the `(N+1)`-electron ground submodule `G` is nonzero, it
contains a nonzero highest-weight vector: `Ŝ⁺_tot w = 0` and `Ŝ³_tot w = (||A|−|B||/2) w`. The only
nontrivial proof of the PR (design §2 `L2`), assembled from
`exists_eigenvector_in_invariant_submodule`, the raising-tower termination via `Nat.find`, and the
`L1` band excluding the spurious Casimir root. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥) :
    ∃ w : (Fin (2 * N + 2) → Fin 2) → ℂ, w ≠ 0 ∧
      w ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ∧
      (fermionTotalSpinPlus N).mulVec w = 0 ∧
      (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w :=
  liebRepulsive_ground_exists_topWeight N A T U E₀ (hcas := hcas) (hne := hne)

/-! ## `L3` — the lowering tower stays inside the ground submodule -/

/-- **`L3`: tower membership.** Every lowered iterate `(Ŝ⁻_tot)^k w` of a top-weight ground vector
`w` stays in the ground submodule `G`, by the same one-line invariant-submodule comap argument as
`L2` step 2 (precedent: `generalFlatBandGround_finrank_ge`, `GeneralFlatBandMultiplet.lean:270`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1)) :
    ∀ k : ℕ, ((fermionTotalSpinMinus N) ^ k).mulVec w ∈
      hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) :=
  liebRepulsive_ground_spinMinusPow_mem N A T U E₀ (hcas := hcas) (hwG := hwG)

/-! ## `L4` — the tower iterates up to `L` are nonzero -/

/-- **`L4`: tower nonvanishing.** For a nonzero top-weight ground vector `w`
(`Ŝ⁺_tot w = 0`, `Ŝ³_tot w = (L/2) w` with `L := sublatticeImbalance A`), every lowered iterate
`(Ŝ⁻_tot)^k w` with `k ≤ L` is nonzero, by `spinMinusPow_ne_zero_general`
(`SpinLoweringTowerGeneral.lean:105`) fed by `L2` + `hcas`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (htop : (fermionTotalSpinPlus N).mulVec w = 0)
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A → ((fermionTotalSpinMinus N) ^ k).mulVec w ≠ 0 :=
  liebRepulsive_ground_tower_ne_zero N A T U E₀ (hcas := hcas) (hw0 := hw0) (hwG := hwG)
    (htop := htop) (hz := hz)

/-! ## `L5` — linear independence of the tower iterates -/

/-- **`L5`: tower linear independence.** The `L + 1` lowered iterates `(Ŝ⁻_tot)^k w`
(`k = 0, …, L`, `L := sublatticeImbalance A`) of a nonzero top-weight ground vector `w` are
linearly independent, by `spinMinusPow_linearIndependent_general`
(`SpinLoweringTowerGeneral.lean:145`) / `highestWeight_spinMultiplet_general` (`:170`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (htop : (fermionTotalSpinPlus N).mulVec w = 0)
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    LinearIndependent ℂ (fun k : Fin (sublatticeImbalance A + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w) :=
  liebRepulsive_ground_tower_linearIndependent N A T U E₀ (hcas := hcas) (hw0 := hw0)
    (hwG := hwG) (htop := htop) (hz := hz)

/-! ## `L6` — the ground submodule equals the tower span -/

/-- **`L6`: ground submodule = tower span.** The `(N+1)`-electron ground submodule `G` equals the
span of the `L + 1` lowered iterates of a nonzero top-weight ground vector `w`
(`L := sublatticeImbalance A`), by `span ≤ G` (`L3`), `finrank span = L + 1` (`L5` +
`finrank_span_eq_card`), `finrank G = L + 1` (Theorem 10.4's `hrank`), and
`Submodule.eq_of_le_of_finrank_eq`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    (hrank : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
      = liebRepulsiveGroundMultiplicity A)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (htop : (fermionTotalSpinPlus N).mulVec w = 0)
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) =
      Submodule.span ℂ (Set.range fun k : Fin (sublatticeImbalance A + 1) =>
        ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w) :=
  liebRepulsive_ground_eq_span_tower N A T U E₀ (hcas := hcas) (hrank := hrank) (hw0 := hw0)
    (hwG := hwG) (htop := htop) (hz := hz)

/-! ## `L7` — vanishing of cross terms between distinct tower weights -/

/-- **`L7`: tower cross-term vanishing.** For any `Ŝ³_tot`-commuting operator `O` and distinct
indices `j ≠ k` (both `≤ L := sublatticeImbalance A`), the cross term
`⟨(Ŝ⁻_tot)^j w, O (Ŝ⁻_tot)^k w⟩` vanishes, by `Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne`
(`Quantum/SpinS/SaturatedFullLadderOrthogonality.lean:43`, moved to `Math/MatrixAnalysis/` in this
PR) at the two distinct real `Ŝ³_tot` weights `L/2 − j ≠ L/2 − k`. Instantiated by PR-8 at `O = 1`
(orthonormality) and `O = fermionStaggeredCasimirOp N A` (PR-3's `Ô²`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (htop : (fermionTotalSpinPlus N).mulVec w = 0)
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (O : ManyBodyOp (Fin (2 * N + 2))) (hO : Commute O (fermionTotalSpinZ N))
    {j k : ℕ} (hjk : j ≠ k) (hj : j ≤ sublatticeImbalance A) (hk : k ≤ sublatticeImbalance A) :
    star (((fermionTotalSpinMinus N) ^ j).mulVec w) ⬝ᵥ
        (O.mulVec (((fermionTotalSpinMinus N) ^ k).mulVec w)) = 0 :=
  liebRepulsive_tower_crossTerm_eq_zero N A T U E₀ (hcas := hcas) (hw0 := hw0) (hwG := hwG)
    (htop := htop) (hz := hz) (O := O) (hO := hO) (hjk := hjk) (hj := hj) (hk := hk)

end LatticeSystem.Tests.LiebFerrimagnetismGroundTower
