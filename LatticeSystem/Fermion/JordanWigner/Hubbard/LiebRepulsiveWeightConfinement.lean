import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveMultipletCompanion
import LatticeSystem.Math.AngularMomentum.Ladder

/-!
# Weight confinement and the `finrank` count (Tasaki §10.2.2, PR-14b)

Twentieth installment of the Theorem 10.4 discharge arc (issue #5320). This file supplies the
weight confinement of the `(N+1)`-electron ground submodule to admissible `Ŝ³` sectors and the
matching `finrank` count, completing (together with PR-14a's
`liebRepulsive_multipletCompanion_capstone`) the symmetric disjunct of
`theorem_10_4_lieb_repulsive_half_filling` (`LiebRepulsive.lean:134`) as a conditional theorem
(the axiom itself is untouched; discharge is PR-15).

## Route

Since `Ŝ³` preserves `G = hubbardGroundSubmoduleAtElectronNumber H E₀ (N+1)` (it commutes with `H`
and `N̂`), `G` decomposes as the supremum of its weight blocks `G ⊓ eigenspace Ŝ³ μ`
(`Submodule.eq_iSup_inf_genEigenspace`, the repulsive analogue of
`attractiveHubbardFullSectorGround_eq_iSup_inf_eigenspace`,
`LiebAttractiveFullSectorUnique.lean:190`). Weight confinement shows every *occupied* block sits at
an admissible weight `μ = liebHalfFillingSpinZVal N q`, `cB ≤ q ≤ cA`, by running PR-14b's joint
eigenvector seed extraction (`liebRepulsive_exists_jointEigenvector_of_ne_bot`,
`LiebRepulsiveMultipletCompanion.lean`) on the block itself, transporting the resulting spin label
to the top admissible sector, and comparing the transported Casimir eigenvalue against
`liebRepulsiveSpinCasimir A` via PR-14a's per-sector uniqueness. The `finrank` bounds are then a
sum over the (confined) admissible blocks: the upper bound via `finrank_span_finset_le_card` +
`Submodule.finrank_mono` (each block spanned by its unique ground state), the lower bound via
`Module.End.eigenvectors_linearIndependent'` + `LinearIndependent.fintype_card_le_finrank`
(distinct-weight eigenvectors of `Ŝ³` are linearly independent).

## Contents

* `liebRepulsive_mem_groundSubmodule_inf_spinZ_iff` — the Pi/Euclidean packaging step relating a
  weight block of `G` (Pi carrier) to `numberSpinZSectorEuclidean` (Euclidean carrier) plus the
  `Ĥ`-eigenvector condition.
* `liebRepulsive_groundSubmodule_spinZ_weight_admissible` — **weight confinement**: an occupied
  weight block sits at an admissible weight.
* `liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace` — `G` decomposes into its `Ŝ³` weight
  blocks.
* `liebRepulsive_groundSubmodule_inf_spinZ_le_span` — each admissible weight block is at most
  one-dimensional (spanned by its unique ground state).
* `liebRepulsive_finrank_groundSubmodule_le` / `_ge` — the two-sided `finrank` bound
  `cA − cB + 1 ≤ finrank G ≤ cA − cB + 1`.
* `liebRepulsive_groundSubmodule_le_spinSquared_eigenspace` — conjunct (iii): every vector of `G` is
  a `Ŝ²`-eigenvector at `liebRepulsiveSpinCasimir A`.
* `liebRepulsive_groundSubmodule_ne_bot` — conjunct (i): `G ≠ ⊥`.
* `liebRepulsive_symmetric_halfFilling_conditional` — the capstone:
  `theorem_10_4_lieb_repulsive_half_filling`'s conclusion verbatim, for
  `symmetricRepulsiveHubbardHamiltonian N T U`, as a conditional theorem (the axiom itself is not
  discharged by this file).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-! ## The Pi/Euclidean packaging step -/

/-- **The Pi/Euclidean packaging step.** A vector of the `EuclideanSpace` carrier lies (via
`WithLp.ofLp`) in the weight block `G_E ⊓ eigenspace Ŝ³ μ` of the Pi-carrier ground submodule iff
it lies in the joint number/spin-`z` sector `numberSpinZSectorEuclidean N (N+1) μ` and is a
`Ĥ`-eigenvector at `E` on the `EuclideanSpace` carrier. Built from
`mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul`
(`Math/MatrixAnalysis/PiEuclideanEigenBridge.lean`); nothing else crosses the two carriers in this
file. -/
theorem liebRepulsive_mem_groundSubmodule_inf_spinZ_iff (N : ℕ)
    (H : ManyBodyOp (Fin (2 * N + 2))) (E μ : ℂ)
    (ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    WithLp.ofLp ψ ∈ hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ ↔
      ψ ∈ numberSpinZSectorEuclidean N ((N : ℂ) + 1) μ ∧
        Matrix.toEuclideanLin H ψ = E • ψ := by
  sorry

/-! ## The `Ŝ³` weight decomposition of `G` -/

/-- **`G` decomposes into its `Ŝ³` weight blocks.** The repulsive analogue of
`attractiveHubbardFullSectorGround_eq_iSup_inf_eigenspace`
(`LiebAttractiveFullSectorUnique.lean:190`): `Ŝ³` commutes with the symmetric repulsive Hamiltonian
and `N̂`, hence preserves `G`, and its eigenspaces span `⊤`
(`fermionTotalSpinZ_iSup_eigenspace_eq_top`), so
`Submodule.eq_iSup_inf_genEigenspace` gives the decomposition. -/
theorem liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ) (E : ℂ) :
    hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) =
      ⨆ μ : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ := by
  sorry

/-! ## Weight confinement -/

/-- **Weight confinement.** If the weight block `G_{E₀} ⊓ eigenspace Ŝ³ μ` is occupied, then `μ` is
an admissible weight `liebHalfFillingSpinZVal N q`, `cB ≤ q ≤ cA`: running
`liebRepulsive_exists_jointEigenvector_of_ne_bot` on the block itself gives a joint eigenvector
whose spin label `Jr` and weight `mur = μ` satisfy `|mur| ≤ Jr` (`angMom_abs_le_J`); transporting to
the top admissible sector and comparing Casimir eigenvalues against
`liebRepulsiveSpinCasimir A` via the per-admissible-sector family `hfam` pins `Jr` to
`S₀ = (cA − cB)/2`, from which `cB ≤ q ≤ cA` follows. -/
theorem liebRepulsive_groundSubmodule_spinZ_weight_admissible (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ)
    {μ : ℂ}
    (hne : hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ ≠ ⊥) :
    ∃ q : ℕ, cB ≤ q ∧ q ≤ cA ∧ μ = liebHalfFillingSpinZVal N q := by
  sorry

/-! ## Each admissible block is at most one-dimensional -/

/-- **Each admissible weight block is spanned by its unique ground state.** For `cB ≤ q ≤ cA`, the
weight block `G_{E₀} ⊓ eigenspace Ŝ³ (liebHalfFillingSpinZVal N q)` is contained in the span of
(the Pi-carrier image of) the sector's unique ground state `φ`, via the uniqueness clause of
`IsUniqueGroundStateOn` transported across `liebRepulsive_mem_groundSubmodule_inf_spinZ_iff`. -/
theorem liebRepulsive_groundSubmodule_inf_spinZ_le_span (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ)
    {q : ℕ} (hq1 : cB ≤ q) (hq2 : q ≤ cA) :
    ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (liebHalfFillingSpinZVal N q) ≤
        Submodule.span ℂ {WithLp.ofLp φ} := by
  sorry

/-! ## The `finrank` bounds -/

/-- **Upper `finrank` bound.** `finrank G ≤ cA − cB + 1`: `G` is contained in the span of the
(at most `cA − cB + 1`-element) family of admissible-sector ground states, via weight confinement
(only admissible blocks are occupied) and `liebRepulsive_groundSubmodule_inf_spinZ_le_span` (each
occupied block is one-dimensional); `finrank_span_finset_le_card` +
`Submodule.finrank_mono` conclude. No `finrank_iSup_le_sum`-style generic sum lemma is needed
(PR-14a's `FinrankIndexedSup.lean` deletion is not recreated). -/
theorem liebRepulsive_finrank_groundSubmodule_le (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1)) ≤ cA - cB + 1 := by
  sorry

/-- **Lower `finrank` bound.** `cA − cB + 1 ≤ finrank G`: the family of admissible-sector ground
states (`q ∈ Finset.Icc cB cA`) lies in `G` and consists of `Ŝ³`-eigenvectors at pairwise distinct
eigenvalues (`liebHalfFillingSpinZVal` is injective in `q`), so
`Module.End.eigenvectors_linearIndependent'` + `LinearIndependent.fintype_card_le_finrank`
(applied inside `↥G`) give the bound; `Nat.card_Icc` supplies
`card (Finset.Icc cB cA) = cA − cB + 1`. -/
theorem liebRepulsive_finrank_groundSubmodule_ge (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    cA - cB + 1 ≤ Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1)) := by
  sorry

/-! ## Conjuncts (i) and (iii) -/

/-- **Conjunct (iii).** Every vector of `G` is a `Ŝ²`-eigenvector at `liebRepulsiveSpinCasimir A`:
`G = ⨆ μ, G ⊓ eigenspace Ŝ³ μ` (`liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace`), and on each
summand either the block is trivial or (weight confinement) it is admissible, where
`liebRepulsive_groundSubmodule_inf_spinZ_le_span` pins it inside the span of a Casimir-`c₀`
eigenvector. -/
theorem liebRepulsive_groundSubmodule_le_spinSquared_eigenspace (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ≤
      Module.End.eigenspace (fermionTotalSpinSquared N).mulVecLin c₀ := by
  sorry

/-- **Conjunct (i).** `G ≠ ⊥`: the top admissible sector `q = cA` supplies a nonzero ground state
(`hfam cA horient le_rfl`), whose Pi-carrier image is nonzero and lies in `G`. -/
theorem liebRepulsive_groundSubmodule_ne_bot (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ≠ ⊥ := by
  sorry

/-! ## The PR-14b capstone -/

/-- **The arc's PR-14b capstone.** For the physical symmetric repulsive Hubbard model at
half-filling (`1 ≤ |A|`, `1 ≤ |B|`), `theorem_10_4_lieb_repulsive_half_filling`'s conclusion holds
verbatim for `H = symmetricRepulsiveHubbardHamiltonian N T U`, as a **conditional theorem** built
from PR-14a's `liebRepulsive_multipletCompanion_capstone` (ground energy `E₀`, conjunct (ii), and
the per-sector Casimir family) together with this file's weight confinement and `finrank` count
(conjuncts (i), (iii), (iv)). The axiom `theorem_10_4_lieb_repulsive_half_filling` is not touched by
this capstone; discharging it (replacing the axiom with this theorem, plus the uniform disjunct and
the degenerate `A = ∅`/`A = univ` cases) is PR-15's responsibility. -/
theorem liebRepulsive_symmetric_halfFilling_conditional (N : ℕ) {A : Finset (Fin (N + 1))}
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (hbip : HoppingRespectsBipartition A T) (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A := by
  sorry

end LatticeSystem.Fermion
