import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismGroundTower

/-!
# §10.2.3 Theorem 10.6 — ground-multiplet tower basis (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356.)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismGroundTower.lean` (PR-5 of the
Theorem 10.6 discharge arc, issue #5347). The `example`s pin down the exact signatures of the
eight declarations `L0`–`L7` of the confirmed design
(`.self-local/docs/theorem-10-6-pr5-design.md`, 2026-08-24): the general weight-band bound `L0`,
the `Ŝ³`-weight band `L1`, the top-weight existence `L2`, tower-membership `L3`, tower
nonvanishing `L4`, tower linear independence `L5`, the ground-submodule span identity `L6`, and the
weight-orthogonal cross-term vanishing `L7`. Mirrors the specification style of
`Tests/LiebFerrimagnetismLadderRatio.lean` / `Tests/LiebFerrimagnetismSU2Invariance.lean`.

Each pin records the hypothesis set the corresponding declaration actually takes, so that a later
edit cannot silently widen it. What the pins fix in particular: `L3`/`L6` need the hopping symmetry
`hT` (it is what makes `Ŝ⁻_tot` commute with the Hamiltonian), while `L4`, `L5` and `L7` do not
need the highest-weight equation `Ŝ⁺_tot w = 0`, and `L7` needs neither the ground-submodule data
nor a range restriction on the tower indices. `L1`, `L4` and `L5` still take Theorem 10.4's Casimir
conclusion in the submodule-wide form `hcas : ∀ v ∈ G, …` even though each proof uses it at the
single vector `w` alone; that is the shape Theorem 10.4 exports, not the pointwise-weakest
hypothesis.

The closing section instantiates the design's degenerate cases: the balanced bipartition
`L = sublatticeImbalance A = 0` (single-member tower) and the one-site model `N = 0`, `A = univ`
(`L = 1`, a spin-`1/2` doublet), which fix the `Fin (L + 1)` indexing and the `finrank` arithmetic
against `liebRepulsiveGroundMultiplicity`.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismGroundTower

open Matrix Module LatticeSystem.Fermion LatticeSystem.Quantum

/-! ## `L0` — general `Ŝ³`-weight band from an arbitrary Casimir eigenvalue -/

/-- **`L0`: general weight-band bound.** A nonzero joint eigenvector of `(Ŝ_tot)²` (eigenvalue
`Jr(Jr+1)`, `Jr ≥ 0`) and `Ŝ³_tot` (eigenvalue `m`) has `|m| ≤ Jr`. Factored out of the two inline
copies in `LiebAttractiveFullSectorUnique.lean` and `LiebRepulsiveMultipletCompanion.lean`
(design §2 `L0`). -/
example (N : ℕ) {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw : w ≠ 0)
    {Jr m : ℝ} (hJ : 0 ≤ Jr)
    (hcas : (fermionTotalSpinSquared N).mulVec w = ((Jr * (Jr + 1) : ℝ) : ℂ) • w)
    (h3 : (fermionTotalSpinZ N).mulVec w = (m : ℂ) • w) :
    |m| ≤ Jr :=
  fermionTotalSpin_abs_weight_le N (hw := hw) (hJ := hJ) (hcas := hcas) (h3 := h3)

/-! ## `L1` — the `Ŝ³`-weight band on the repulsive ground submodule -/

/-- **`L1`: ground-submodule weight band.** Any nonzero `Ŝ³_tot`-eigenvector `w` (eigenvalue `m`)
in the `(N+1)`-electron ground submodule `G` of `symmetricRepulsiveHubbardHamiltonian N T U` at
`E₀` satisfies `|m| ≤ ||A| − |B||/2`, the `L0` band instantiated at
`Jr := sublatticeImbalance A / 2` using the Theorem 10.4 Casimir conclusion `hcas`. -/
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

/-- **`L3`: tower membership.** Every lowered iterate `(Ŝ⁻_tot)^k w` of a ground vector `w` stays
in the ground submodule `G`, by the same one-line invariant-submodule comap argument as `L2`
step 2 (precedent: `generalFlatBandGround_finrank_ge`, `GeneralFlatBandMultiplet.lean:270`). The
hopping symmetry `hT` is what makes `Ŝ⁻_tot` commute with the Hamiltonian
(`fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian`); no Casimir input is
needed, so `A`/`hcas` do not occur. -/
example (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1)) :
    ∀ k : ℕ, ((fermionTotalSpinMinus N) ^ k).mulVec w ∈
      hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) :=
  liebRepulsive_ground_spinMinusPow_mem N T hT U E₀ (hwG := hwG)

/-! ## `L4` — the tower iterates up to `L` are nonzero -/

/-- **`L4`: tower nonvanishing.** For a nonzero ground vector `w` of top weight
`Ŝ³_tot w = (L/2) w` (`L := sublatticeImbalance A`), every lowered iterate `(Ŝ⁻_tot)^k w` with
`k ≤ L` is nonzero, by `spinMinusPow_ne_zero_general` (`SpinLoweringTowerGeneral.lean:105`) fed by
`hz` + `hcas`. The highest-weight condition `Ŝ⁺_tot w = 0` is not an input: on `G` the Casimir
value already comes from `hcas`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A → ((fermionTotalSpinMinus N) ^ k).mulVec w ≠ 0 :=
  liebRepulsive_ground_tower_ne_zero N A T U E₀ (hcas := hcas) (hw0 := hw0) (hwG := hwG)
    (hz := hz)

/-! ## `L5` — linear independence of the tower iterates -/

/-- **`L5`: tower linear independence.** The `L + 1` lowered iterates `(Ŝ⁻_tot)^k w`
(`k = 0, …, L`, `L := sublatticeImbalance A`) of a nonzero top-weight ground vector `w` are
linearly independent, by `spinMinusPow_linearIndependent_general`
(`SpinLoweringTowerGeneral.lean:145`), whose Casimir input is `hcas`; as in `L4` the highest-weight
condition `Ŝ⁺_tot w = 0` is therefore not an input. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    LinearIndependent ℂ (fun k : Fin (sublatticeImbalance A + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w) :=
  liebRepulsive_ground_tower_linearIndependent N A T U E₀ (hcas := hcas) (hw0 := hw0)
    (hwG := hwG) (hz := hz)

/-! ## `L6` — the ground submodule equals the tower span -/

/-- **`L6`: ground submodule = tower span.** The `(N+1)`-electron ground submodule `G` equals the
span of the `L + 1` lowered iterates of a nonzero top-weight ground vector `w`
(`L := sublatticeImbalance A`), by `span ≤ G` (`L3`, whence the hopping symmetry `hT`),
`finrank span = L + 1` (`L5` + `finrank_span_eq_card`), `finrank G = L + 1` (Theorem 10.4's
`hrank`), and `Submodule.eq_of_le_of_finrank_eq`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    (hrank : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
      = liebRepulsiveGroundMultiplicity A)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) =
      Submodule.span ℂ (Set.range fun k : Fin (sublatticeImbalance A + 1) =>
        ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w) :=
  liebRepulsive_ground_eq_span_tower N A T hT U E₀ (hcas := hcas) (hrank := hrank) (hw0 := hw0)
    (hwG := hwG) (hz := hz)

/-! ## `L7` — vanishing of cross terms between distinct tower weights -/

/-- **`L7`: tower cross-term vanishing.** For any `Ŝ³_tot`-commuting operator `O` and distinct
indices `j ≠ k`, the cross term `⟨(Ŝ⁻_tot)^j w, O (Ŝ⁻_tot)^k w⟩` vanishes, by
`Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne`
(`Quantum/SpinS/SaturatedFullLadderOrthogonality.lean`, already in scope through the ground-tower
module's import chain) at the two distinct real `Ŝ³_tot`
weights `L/2 − j ≠ L/2 − k`, `L := sublatticeImbalance A`. The weights are already distinct as
complex numbers, so no range restriction `j, k ≤ L` and no ground-submodule membership enter;
only the top weight `hz` does. Instantiated by PR-8 at `O = 1` (orthonormality) and
`O = fermionStaggeredCasimirOp N A` (PR-3's `Ô²`). -/
example (N : ℕ) (A : Finset (Fin (N + 1)))
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (O : ManyBodyOp (Fin (2 * N + 2))) (hO : Commute O (fermionTotalSpinZ N))
    {j k : ℕ} (hjk : j ≠ k) :
    star (((fermionTotalSpinMinus N) ^ j).mulVec w) ⬝ᵥ
        (O.mulVec (((fermionTotalSpinMinus N) ^ k).mulVec w)) = 0 :=
  liebRepulsive_tower_crossTerm_eq_zero N A (hz := hz) (O := O) (hO := hO) (hjk := hjk)

/-! ## Degenerate instantiations: the `L = 0` tower and the one-site `N = 0` doublet -/

/-- **`L = 0` arithmetic.** The balanced bipartition `A = {0}` of `Fin 2` (`|A| = |B| = 1`) has
`sublatticeImbalance A = 0` and `liebRepulsiveGroundMultiplicity A = 1`, so the tower index type
`Fin (L + 1)` is `Fin 1` and the top weight `L/2` is `0`. -/
example : sublatticeImbalance ({0} : Finset (Fin (1 + 1))) = 0 ∧
    liebRepulsiveGroundMultiplicity ({0} : Finset (Fin (1 + 1))) = 1 := by
  have hcard := bipartitionComplement_card_add 1 ({0} : Finset (Fin (1 + 1)))
  have hA : ({0} : Finset (Fin (1 + 1))).card = 1 := by simp
  refine ⟨?_, ?_⟩
  · rw [sublatticeImbalance]
    omega
  · rw [liebRepulsiveGroundMultiplicity, sublatticeImbalance]
    omega

/-- **`L4`/`L6` at `L = 0`.** On the balanced bipartition the top-weight equation reads
`Ŝ³_tot w = 0`, the nonvanishing range `k ≤ L` collapses to `k = 0` (so `(Ŝ⁻_tot)^0 = 1` must be
the tower's first member), and the span identity collapses to `G = ℂ ∙ w`: the ground multiplet is
the single vector `w`. -/
example (T : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (1 + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian 1 T U) E₀ (1 + 1),
      (fermionTotalSpinSquared 1).mulVec v =
        liebRepulsiveSpinCasimir ({0} : Finset (Fin (1 + 1))) • v)
    (hrank : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian 1 T U) E₀ (1 + 1))
      = liebRepulsiveGroundMultiplicity ({0} : Finset (Fin (1 + 1))))
    {w : (Fin (2 * 1 + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 1 T U) E₀ (1 + 1))
    (hz : (fermionTotalSpinZ 1).mulVec w = 0) :
    (∀ k : ℕ, k ≤ 0 → ((fermionTotalSpinMinus 1) ^ k).mulVec w ≠ 0) ∧
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian 1 T U) E₀ (1 + 1)
        = Submodule.span ℂ {w} := by
  have hcard := bipartitionComplement_card_add 1 ({0} : Finset (Fin (1 + 1)))
  have hA : ({0} : Finset (Fin (1 + 1))).card = 1 := by simp
  have himb : sublatticeImbalance ({0} : Finset (Fin (1 + 1))) = 0 := by
    rw [sublatticeImbalance]
    omega
  have hz' : (fermionTotalSpinZ 1).mulVec w
      = ((sublatticeImbalance ({0} : Finset (Fin (1 + 1))) : ℂ) / 2) • w := by
    rw [himb]
    simpa using hz
  refine ⟨fun k hk => liebRepulsive_ground_tower_ne_zero 1 _ T U E₀ hcas hw0 hwG hz' k (by omega),
    ?_⟩
  rw [liebRepulsive_ground_eq_span_tower 1 _ T hT U E₀ hcas hrank hw0 hwG hz']
  congr 1
  rw [himb]
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, by simp⟩

/-- **`L7` at `L = 0`.** With the top weight `0` the two lowest tower slots `j = 0`, `k = 1` carry
the distinct weights `0` and `−1`, so the cross term `⟨w, O (Ŝ⁻_tot w)⟩` of any `Ŝ³_tot`-commuting
observable vanishes — the `(Ŝ⁻_tot)^0 = 1` slot of `L7` in concrete form. -/
example (O : ManyBodyOp (Fin (2 * 1 + 2))) (hO : Commute O (fermionTotalSpinZ 1))
    {w : (Fin (2 * 1 + 2) → Fin 2) → ℂ}
    (hz : (fermionTotalSpinZ 1).mulVec w = 0) :
    star w ⬝ᵥ O.mulVec ((fermionTotalSpinMinus 1).mulVec w) = 0 := by
  have hcard := bipartitionComplement_card_add 1 ({0} : Finset (Fin (1 + 1)))
  have hA : ({0} : Finset (Fin (1 + 1))).card = 1 := by simp
  have himb : sublatticeImbalance ({0} : Finset (Fin (1 + 1))) = 0 := by
    rw [sublatticeImbalance]
    omega
  have hz' : (fermionTotalSpinZ 1).mulVec w
      = ((sublatticeImbalance ({0} : Finset (Fin (1 + 1))) : ℂ) / 2) • w := by
    rw [himb]
    simpa using hz
  simpa using
    liebRepulsive_tower_crossTerm_eq_zero 1 ({0} : Finset (Fin (1 + 1))) (hz := hz') (O := O)
      (hO := hO) (j := 0) (k := 1) (hjk := by omega)

/-- **`N = 0`, `A = univ` arithmetic.** The one-site model (`|A| = 1`, `|B| = 0`) has
`sublatticeImbalance A = 1` and `liebRepulsiveGroundMultiplicity A = 2`: the spin-`1/2` doublet. -/
example : sublatticeImbalance (Finset.univ : Finset (Fin (0 + 1))) = 1 ∧
    liebRepulsiveGroundMultiplicity (Finset.univ : Finset (Fin (0 + 1))) = 2 := by
  have hcard := bipartitionComplement_card_add 0 (Finset.univ : Finset (Fin (0 + 1)))
  have hA : (Finset.univ : Finset (Fin (0 + 1))).card = 1 := by simp
  refine ⟨?_, ?_⟩
  · rw [sublatticeImbalance]
    omega
  · rw [liebRepulsiveGroundMultiplicity, sublatticeImbalance]
    omega

/-- **`L5`/`L6` `finrank` arithmetic at `N = 0`, `A = univ`.** The two-member tower of the
top-weight vector `w` (weight `1/2`) spans the ground submodule, so Theorem 10.4's count
`finrank G = liebRepulsiveGroundMultiplicity A` evaluates to the concrete `finrank G = 2` — the
`Fin (L + 1)` cardinality and `liebRepulsiveGroundMultiplicity` agree at `L = 1`. -/
example (T : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (0 + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian 0 T U) E₀ (0 + 1),
      (fermionTotalSpinSquared 0).mulVec v =
        liebRepulsiveSpinCasimir (Finset.univ : Finset (Fin (0 + 1))) • v)
    (hrank : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian 0 T U) E₀ (0 + 1))
      = liebRepulsiveGroundMultiplicity (Finset.univ : Finset (Fin (0 + 1))))
    {w : (Fin (2 * 0 + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) E₀ (0 + 1))
    (hz : (fermionTotalSpinZ 0).mulVec w = ((1 : ℂ) / 2) • w) :
    Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) E₀ (0 + 1)) = 2 := by
  have hcard := bipartitionComplement_card_add 0 (Finset.univ : Finset (Fin (0 + 1)))
  have hA : (Finset.univ : Finset (Fin (0 + 1))).card = 1 := by simp
  have himb : sublatticeImbalance (Finset.univ : Finset (Fin (0 + 1))) = 1 := by
    rw [sublatticeImbalance]
    omega
  have hz' : (fermionTotalSpinZ 0).mulVec w
      = ((sublatticeImbalance (Finset.univ : Finset (Fin (0 + 1))) : ℂ) / 2) • w := by
    rw [himb]
    simpa using hz
  rw [liebRepulsive_ground_eq_span_tower 0 _ T hT U E₀ hcas hrank hw0 hwG hz',
    finrank_span_eq_card
      (liebRepulsive_ground_tower_linearIndependent 0 _ T U E₀ hcas hw0 hwG hz'),
    Fintype.card_fin, himb]

/-! ## `A0a` (PR-8) — de-privatized Casimir realification -/

/-- **`A0a` (PR-8 design §2 layer A): `liebRepulsiveSpinCasimir_eq_ofReal` must be public.**
Theorem 10.4's Casimir eigenvalue rewritten as the real cast `J (J + 1)` at `J = L/2`; PR-8's
`N = 0` branch (`E1`, `liebFerrimagnetism_N_zero`) needs it from outside this module, so it must be
de-privatized in place (no restatement). This pin fails to compile while the declaration stays
`private` in `LiebFerrimagnetismGroundTower.lean`. -/
example {N : ℕ} (A : Finset (Fin (N + 1))) :
    liebRepulsiveSpinCasimir A =
      ((((sublatticeImbalance A : ℝ) / 2) * ((sublatticeImbalance A : ℝ) / 2 + 1) : ℝ) : ℂ) :=
  liebRepulsiveSpinCasimir_eq_ofReal A

end LatticeSystem.Tests.LiebFerrimagnetismGroundTower
