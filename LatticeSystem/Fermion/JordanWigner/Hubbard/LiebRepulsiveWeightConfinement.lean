import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveMultipletCompanion

/-!
# Weight confinement and the `finrank` count (Tasaki §10.2.2, PR-14b)

Twentieth installment of the Theorem 10.4 discharge arc (issue #5320). This file supplies the
weight confinement of the `(N+1)`-electron ground submodule to admissible `Ŝ³` sectors and the
matching `finrank` count, completing (together with PR-14a's
`liebRepulsive_multipletCompanion_capstone`) the symmetric disjunct of
`theorem_10_4_lieb_repulsive_half_filling` (`LiebRepulsiveHalfFillingDischarge.lean`) as a
conditional theorem (the full unconditional discharge is PR-15).

## Route

Since `Ŝ³` preserves `G = hubbardGroundSubmoduleAtElectronNumber H E₀ (N+1)` (it commutes with `H`
and `N̂`), `G` decomposes as the supremum of its weight blocks `G ⊓ eigenspace Ŝ³ μ`
(`Submodule.eq_iSup_inf_genEigenspace`, the repulsive analogue of
`attractiveHubbardFullSectorGround_eq_iSup_inf_eigenspace`,
`LiebAttractiveFullSectorUnique.lean:190`). Weight confinement shows every *occupied* block sits at
an admissible weight `μ = liebHalfFillingSpinZVal N q`, `cB ≤ q ≤ cA`, by running PR-14b's joint
eigenvector seed extraction (`liebRepulsive_exists_jointEigenvector_of_ne_bot`,
`LiebRepulsiveMultipletCompanion.lean`) on the block itself, transporting the resulting spin label
to an admissible sector, and comparing the transported Casimir eigenvalue against
`S₀(S₀+1)` via PR-14a's per-sector uniqueness. The `finrank` bounds are then a
sum over the (confined) admissible blocks: the upper bound via `finrank_span_finset_le_card` +
`Submodule.finrank_mono` (each block spanned by its unique ground state), the lower bound via
`Module.End.eigenvectors_linearIndependent'` + `LinearIndependent.fintype_card_le_finrank`
(distinct-weight eigenvectors of `Ŝ³` are linearly independent).

## Contents

* `liebRepulsive_mem_groundSubmodule_inf_spinZ_iff` — the Pi/Euclidean packaging step relating a
  weight block of `G` (Pi carrier) to `numberSpinZSectorEuclidean` (Euclidean carrier) plus the
  `Ĥ`-eigenvector condition.
* `liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace` — `G` decomposes into its `Ŝ³` weight
  blocks.
* `liebRepulsive_groundSubmodule_spinZ_weight_admissible` — **weight confinement**: an occupied
  weight block sits at an admissible weight.
* `liebRepulsive_groundSubmodule_inf_spinZ_le_span` — each admissible weight block is at most
  one-dimensional (spanned by its unique ground state).
* `liebRepulsive_finrank_groundSubmodule_le` / `_ge` — the two-sided `finrank` bound
  `cA − cB + 1 ≤ finrank G ≤ cA − cB + 1`.
* `liebRepulsive_groundSubmodule_le_spinSquared_eigenspace` — conjunct (iii): every vector of `G` is
  a `Ŝ²`-eigenvector at the Casimir value `c₀`.
* `liebRepulsive_groundSubmodule_ne_bot` — conjunct (i): `G ≠ ⊥`.
* `liebRepulsive_symmetric_halfFilling_conditional` — the capstone:
  `theorem_10_4_lieb_repulsive_half_filling`'s conclusion verbatim, for
  `symmetricRepulsiveHubbardHamiltonian N T U`, as a conditional theorem (the `1 ≤ |A|`/`1 ≤ |B|`
  restriction is lifted, and the uniform disjunct is added, in
  `LiebRepulsiveHalfFillingDischarge.lean`).

The per-sector Casimir value `c₀` is carried as a parameter pinned by
`hc₀ : c₀ = S₀ (S₀ + 1)`, `S₀ = (cA − cB)/2`. That hypothesis is not bookkeeping: confinement
concludes `|m| ≤ S₀` from `|m| ≤ J` and `J(J+1) = c₀`, so the *numerical value* of `c₀` is what
turns the spin label into the two-sided weight bound.

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
  have key : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (a : ℂ),
      WithLp.ofLp ψ ∈ Module.End.eigenspace M.mulVecLin a ↔
        Matrix.toEuclideanLin M ψ = a • ψ := by
    intro M a
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul M (WithLp.ofLp ψ) a
  have hcast : ((N + 1 : ℕ) : ℂ) = (N : ℂ) + 1 := by push_cast; ring
  rw [Submodule.mem_inf, hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf, hcast,
    key, key, key, numberSpinZSectorEuclidean, Submodule.mem_inf, spinZSectorEuclidean,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  tauto

/-! ## The `Ŝ³` weight decomposition of `G` -/

/-- **`G` decomposes into its `Ŝ³` weight blocks.** The repulsive analogue of
`attractiveHubbardFullSectorGround_eq_iSup_inf_eigenspace`
(`LiebAttractiveFullSectorUnique.lean:190`): `Ŝ³` commutes with the symmetric repulsive Hamiltonian
and `N̂`, hence preserves `G`, and its eigenspaces span `⊤`
(`fermionTotalSpinZ_iSup_eigenspace_eq_top`), so
`Submodule.eq_iSup_inf_genEigenspace` gives the decomposition. -/
theorem liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E : ℂ) :
    hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) =
      ⨆ μ : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ := by
  have hinv : ∀ x ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1),
      (fermionTotalSpinZ N).mulVecLin x ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) := fun x hx =>
    liebRepulsive_groundSubmodule_le_comap_of_commute N T U E (fermionTotalSpinZ N)
      (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U)
      (fermionTotalSpinZ_commute_fermionTotalNumber N) hx
  have htop : ⨆ μ : ℂ, Module.End.genEigenspace (fermionTotalSpinZ N).mulVecLin μ 1 = ⊤ := by
    simpa only [Module.End.genEigenspace_one] using fermionTotalSpinZ_iSup_eigenspace_eq_top N
  simpa only [Module.End.genEigenspace_one] using
    Submodule.eq_iSup_inf_genEigenspace
      (p := hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1))
      (f := (fermionTotalSpinZ N).mulVecLin) 1 hinv htop

/-! ## Weight confinement -/

/-- **Weight confinement.** If the weight block `G_{E₀} ⊓ eigenspace Ŝ³ μ` is occupied, then `μ` is
an admissible weight `liebHalfFillingSpinZVal N q`, `cB ≤ q ≤ cA`: running
`liebRepulsive_exists_jointEigenvector_of_ne_bot` on the block itself gives a joint eigenvector
whose spin label `Jr` and weight `mur = μ` satisfy `|mur| ≤ Jr` (`angMom_abs_le_J`); transporting to
the admissible sector `min p cA` and comparing Casimir eigenvalues against `c₀ = S₀(S₀+1)` via the
per-admissible-sector family `hfam` pins `Jr` to `S₀ = (cA − cB)/2`, from which `cB ≤ q ≤ cA`
follows. -/
theorem liebRepulsive_groundSubmodule_spinZ_weight_admissible (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hc₀ : c₀ = (((((cA : ℝ) - (cB : ℝ)) / 2) * ((((cA : ℝ) - (cB : ℝ)) / 2) + 1) : ℝ) : ℂ))
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
  classical
  -- the weight block is invariant under `Ŝ³` and `Ŝ²`
  have hB3 : (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ) ≤
      (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ).comap
        (fermionTotalSpinZ N).mulVecLin := by
    intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_comap, Submodule.mem_inf]
    refine ⟨liebRepulsive_groundSubmodule_le_comap_of_commute N T U _ (fermionTotalSpinZ N)
        (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U)
        (fermionTotalSpinZ_commute_fermionTotalNumber N) hx.1, ?_⟩
    rw [Matrix.mulVecLin_apply]
    exact mulVec_mem_eigenspace_of_commute (Commute.refl _) hx.2
  have hB2 : (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ) ≤
      (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ).comap
        (fermionTotalSpinSquared N).mulVecLin := by
    intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.mem_comap, Submodule.mem_inf]
    refine ⟨liebRepulsive_groundSubmodule_le_comap_of_commute N T U _ (fermionTotalSpinSquared N)
        (fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian N T hT_symm U)
        (fermionTotalSpinSquared_commute_fermionTotalNumber N) hx.1, ?_⟩
    rw [Matrix.mulVecLin_apply]
    exact mulVec_mem_eigenspace_of_commute (fermionTotalSpinSquared_commute_fermionTotalSpinZ N)
      hx.2
  obtain ⟨Jr, mur, Er, p, nUp, v, hvne, hvB, -, hJr0, hJrp, hmurval, -, hmurabs,
      hsqE, h3E, hHE, hNE⟩ :=
    liebRepulsive_exists_jointEigenvector_of_ne_bot N T hT_symm U
      (B := hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ)
      inf_le_left hB3 hB2 hne
  -- the block pins the weight: `μ = mur`
  have h3μ : Matrix.toEuclideanLin (fermionTotalSpinZ N) v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hvB).2
    rw [Matrix.mulVecLin_apply] at h
    exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp h
  have hμeq : μ = (mur : ℂ) := by
    have hsub : (μ - (mur : ℂ)) • v = 0 := by rw [sub_smul, ← h3μ, ← h3E, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hvne)
  -- transport into the admissible sector `q = min p cA`
  have hNp : N + 1 ≤ 2 * p := by
    have h0 := hJr0
    rw [hJrp] at h0
    have h : ((N + 1 : ℕ) : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h
  have hpcB : cB ≤ p := by omega
  set q : ℕ := min p cA with hqdef
  have hq1 : cB ≤ q := le_min hpcB horient
  have hq2 : q ≤ cA := min_le_right p cA
  have hqp : q ≤ p := min_le_left p cA
  have hpq : N + 1 ≤ p + q := by
    rcases min_cases p cA with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [hqdef, he] <;> omega
  have hqcast : ((p - q : ℕ) : ℝ) = (p : ℝ) - (q : ℝ) := Nat.cast_sub hqp
  have hpq' : ((N : ℝ) + 1) ≤ (p : ℝ) + (q : ℝ) := by
    have h : ((N + 1 : ℕ) : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpq
    push_cast at h
    linarith
  obtain ⟨Ψ, hΨne, hΨmem, hΨH, hΨsq⟩ :=
    liebRepulsive_transport_to_sector N q (p - q) T hT_symm U hvne hJr0 hsqE h3E hHE hNE
      (by rw [hqcast, hJrp]; linarith) (by rw [hqcast, hJrp]; ring)
  -- the transported state is the sector's unique ground state, so its Casimir eigenvalue is `c₀`
  obtain ⟨φ, hGS, hcas⟩ := hfam q hq1 hq2
  obtain ⟨c, hc⟩ := hGS.2.2.2.2 Ψ hΨmem hΨH
  have hsqΨ2 : Matrix.toEuclideanLin (fermionTotalSpinSquared N) Ψ = c₀ • Ψ := by
    rw [hc, map_smul, hcas, smul_comm]
  have hval : ((Jr * (Jr + 1) : ℝ) : ℂ) = c₀ := by
    have hsub : (((Jr * (Jr + 1) : ℝ) : ℂ) - c₀) • Ψ = 0 := by
      rw [sub_smul, ← hΨsq, ← hsqΨ2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hΨne)
  -- `J (J + 1) = S₀ (S₀ + 1)` with both `≥ 0` forces `J = S₀`
  have hS0 : (0 : ℝ) ≤ ((cA : ℝ) - (cB : ℝ)) / 2 := by
    have : (cB : ℝ) ≤ (cA : ℝ) := by exact_mod_cast horient
    linarith
  have hJrS : Jr * (Jr + 1) = (((cA : ℝ) - (cB : ℝ)) / 2) * ((((cA : ℝ) - (cB : ℝ)) / 2) + 1) := by
    rw [hc₀] at hval
    exact_mod_cast hval
  have hJreq : Jr = ((cA : ℝ) - (cB : ℝ)) / 2 := by
    have hfac : (Jr - ((cA : ℝ) - (cB : ℝ)) / 2) * (Jr + ((cA : ℝ) - (cB : ℝ)) / 2 + 1) = 0 := by
      linear_combination hJrS
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith
  -- `|m| ≤ S₀` is the two-sided admissibility bound on the up-count
  obtain ⟨hlow, hhigh⟩ := abs_le.mp hmurabs
  have hcard' : (cA : ℝ) + (cB : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hcard
  rw [hJreq] at hlow hhigh
  rw [hmurval] at hlow hhigh
  refine ⟨nUp, ?_, ?_, ?_⟩
  · have h : (cB : ℝ) ≤ (nUp : ℝ) := by linarith
    exact_mod_cast h
  · have h : (nUp : ℝ) ≤ (cA : ℝ) := by linarith
    exact_mod_cast h
  · rw [hμeq, hmurval, liebHalfFillingSpinZVal]
    push_cast
    ring

/-! ## Each admissible block is at most one-dimensional -/

/-- **Each admissible weight block is spanned by its unique ground state.** For `cB ≤ q ≤ cA`, the
weight block `G_{E₀} ⊓ eigenspace Ŝ³ (liebHalfFillingSpinZVal N q)` is contained in the span of
(the Pi-carrier image of) the sector's unique ground state `φ`, via the uniqueness clause of
`IsUniqueGroundStateOn` transported across `liebRepulsive_mem_groundSubmodule_inf_spinZ_iff`. The
`Ŝ²`-eigenvector clause of `φ` is carried along because conjunct (iii) reads the Casimir eigenvalue
of the whole block off this span. -/
theorem liebRepulsive_groundSubmodule_inf_spinZ_le_span (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ)
    {q : ℕ} (hq1 : cB ≤ q) (hq2 : q ≤ cA) :
    ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ ∧
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (liebHalfFillingSpinZVal N q) ≤
        Submodule.span ℂ {WithLp.ofLp φ} := by
  obtain ⟨φ, hGS, hcas⟩ := hfam q hq1 hq2
  refine ⟨φ, hcas, ?_⟩
  intro x hx
  obtain ⟨ψ, rfl⟩ : ∃ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2), x = WithLp.ofLp ψ :=
    ⟨WithLp.toLp 2 x, rfl⟩
  obtain ⟨hmem, hH⟩ :=
    (liebRepulsive_mem_groundSubmodule_inf_spinZ_iff N
      (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) _ ψ).mp hx
  obtain ⟨c, hc⟩ := hGS.2.2.2.2 ψ hmem hH
  rw [hc, WithLp.ofLp_smul]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-! ## The `finrank` bounds -/

/-- **The admissible weights are pairwise distinct.** `q ↦ liebHalfFillingSpinZVal N q` is
injective: it is an affine function of `q` with nonzero slope. -/
private theorem liebHalfFillingSpinZVal_injective (N : ℕ) :
    Function.Injective (liebHalfFillingSpinZVal N) := by
  intro q₁ q₂ h
  rw [liebHalfFillingSpinZVal, liebHalfFillingSpinZVal] at h
  have h2 : (q₁ : ℂ) = (q₂ : ℂ) := by linear_combination h
  exact_mod_cast h2

/-- **Upper `finrank` bound.** `finrank G ≤ cA − cB + 1`: `G` is contained in the span of the
(at most `cA − cB + 1`-element) family of admissible-sector ground states, via weight confinement
(only admissible blocks are occupied) and `liebRepulsive_groundSubmodule_inf_spinZ_le_span` (each
occupied block is one-dimensional); `finrank_span_finset_le_card` +
`Submodule.finrank_mono` conclude. No `finrank_iSup_le_sum`-style generic sum lemma is needed. -/
theorem liebRepulsive_finrank_groundSubmodule_le (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hc₀ : c₀ = (((((cA : ℝ) - (cB : ℝ)) / 2) * ((((cA : ℝ) - (cB : ℝ)) / 2) + 1) : ℝ) : ℂ))
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1)) ≤ cA - cB + 1 := by
  classical
  -- pick, for every admissible `q`, the vector spanning the block at weight `μ_q`
  have hchoice : ∀ q : ℕ, ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      cB ≤ q → q ≤ cA →
        hubbardGroundSubmoduleAtElectronNumber
            (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
          Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (liebHalfFillingSpinZVal N q) ≤
          Submodule.span ℂ {WithLp.ofLp φ} := by
    intro q
    by_cases h : cB ≤ q ∧ q ≤ cA
    · obtain ⟨φ, -, hle⟩ :=
        liebRepulsive_groundSubmodule_inf_spinZ_le_span N cA cB T U hfam h.1 h.2
      exact ⟨φ, fun _ _ => hle⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose f hf using hchoice
  set S : Finset ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
    (Finset.Icc cB cA).image (fun q => WithLp.ofLp (f q)) with hSdef
  have hGle : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ≤
      Submodule.span ℂ (S : Set ((Fin (2 * N + 2) → Fin 2) → ℂ)) := by
    refine le_trans
      (le_of_eq (liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace N T U (E₀ : ℂ)))
      (iSup_le fun μ => ?_)
    by_cases hbot : hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊥
    · rw [hbot]
      exact bot_le
    · obtain ⟨q, hq1, hq2, hqμ⟩ :=
        liebRepulsive_groundSubmodule_spinZ_weight_admissible N cA cB T hT_symm U hcard horient
          hc₀ hfam hbot
      subst hqμ
      refine le_trans (hf q hq1 hq2) ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine Submodule.subset_span ?_
      rw [hSdef, Finset.coe_image]
      exact ⟨q, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hq1, hq2⟩), rfl⟩
  calc Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1))
      ≤ Module.finrank ℂ (Submodule.span ℂ (S : Set ((Fin (2 * N + 2) → Fin 2) → ℂ))) :=
        Submodule.finrank_mono hGle
    _ ≤ S.card := finrank_span_finset_le_card S
    _ ≤ (Finset.Icc cB cA).card := by rw [hSdef]; exact Finset.card_image_le
    _ = cA - cB + 1 := by rw [Nat.card_Icc]; omega

/-- **Lower `finrank` bound.** `cA − cB + 1 ≤ finrank G`: the family of admissible-sector ground
states, indexed by `i : Fin (cA − cB + 1)` through the up-count `cB + i`, lies in `G` and consists
of `Ŝ³`-eigenvectors at pairwise distinct eigenvalues (`liebHalfFillingSpinZVal` is injective), so
`Module.End.eigenvectors_linearIndependent'` + `LinearIndependent.fintype_card_le_finrank`
(applied inside `↥G`) give the bound. -/
theorem liebRepulsive_finrank_groundSubmodule_ge (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    cA - cB + 1 ≤ Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1)) := by
  classical
  -- the admissible up-counts, indexed by `Fin (cA − cB + 1)` via `i ↦ cB + i`
  have hstate : ∀ i : Fin (cA - cB + 1),
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        WithLp.ofLp φ ∈ hubbardGroundSubmoduleAtElectronNumber
            (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ∧
          WithLp.ofLp φ ≠ 0 ∧
          WithLp.ofLp φ ∈ Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin
            (liebHalfFillingSpinZVal N (cB + i.val)) := by
    intro i
    have hilt := i.isLt
    obtain ⟨φ, hGS, -⟩ := hfam (cB + i.val) (Nat.le_add_right _ _) (by omega)
    have hφne : φ ≠ 0 := by
      intro h
      have hn := hGS.2.1
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    have hmem := (liebRepulsive_mem_groundSubmodule_inf_spinZ_iff N
      (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ)
      (liebHalfFillingSpinZVal N (cB + i.val)) φ).mpr ⟨hGS.1, hGS.2.2.1⟩
    rw [Submodule.mem_inf] at hmem
    exact ⟨φ, hmem.1, by simpa using hφne, hmem.2⟩
  choose f hfG hfne hfeig using hstate
  have hinj : Function.Injective
      (fun i : Fin (cA - cB + 1) => liebHalfFillingSpinZVal N (cB + i.val)) := by
    intro i₁ i₂ h
    have h1 := liebHalfFillingSpinZVal_injective N h
    exact Fin.ext (by omega)
  -- distinct weights give a linearly independent family inside `G`
  have hli : LinearIndependent ℂ (fun i : Fin (cA - cB + 1) => WithLp.ofLp (f i)) :=
    Module.End.eigenvectors_linearIndependent' _ _ hinj _ fun i => ⟨hfeig i, hfne i⟩
  have hliG : LinearIndependent ℂ (fun i : Fin (cA - cB + 1) =>
      (⟨WithLp.ofLp (f i), hfG i⟩ : ↥(hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1)))) :=
    LinearIndependent.of_comp (Submodule.subtype _) hli
  simpa using hliG.fintype_card_le_finrank

/-! ## Conjuncts (i) and (iii) -/

/-- **Conjunct (iii).** Every vector of `G` is a `Ŝ²`-eigenvector at the Casimir value `c₀`:
`G = ⨆ μ, G ⊓ eigenspace Ŝ³ μ` (`liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace`), and on each
summand either the block is trivial or (weight confinement) it is admissible, where
`liebRepulsive_groundSubmodule_inf_spinZ_le_span` pins it inside the span of a Casimir-`c₀`
eigenvector. -/
theorem liebRepulsive_groundSubmodule_le_spinSquared_eigenspace (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ)
    (hcard : cA + cB = N + 1) (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hc₀ : c₀ = (((((cA : ℝ) - (cB : ℝ)) / 2) * ((((cA : ℝ) - (cB : ℝ)) / 2) + 1) : ℝ) : ℂ))
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ≤
      Module.End.eigenspace (fermionTotalSpinSquared N).mulVecLin c₀ := by
  refine le_trans
    (le_of_eq (liebRepulsive_groundSubmodule_eq_iSup_inf_eigenspace N T U (E₀ : ℂ)))
    (iSup_le fun μ => ?_)
  by_cases hbot : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊥
  · rw [hbot]
    exact bot_le
  · obtain ⟨q, hq1, hq2, hqμ⟩ :=
      liebRepulsive_groundSubmodule_spinZ_weight_admissible N cA cB T hT_symm U hcard horient
        hc₀ hfam hbot
    subst hqμ
    obtain ⟨φ, hcas, hle⟩ :=
      liebRepulsive_groundSubmodule_inf_spinZ_le_span N cA cB T U hfam hq1 hq2
    refine le_trans hle ?_
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact (mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mpr hcas

/-- **Conjunct (i).** `G ≠ ⊥`: the top admissible sector `q = cA` supplies a nonzero ground state
(`hfam cA horient le_rfl`), whose Pi-carrier image is nonzero and lies in `G`. -/
theorem liebRepulsive_groundSubmodule_ne_bot (N cA cB : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (horient : cB ≤ cA)
    {E₀ : ℝ} {c₀ : ℂ}
    (hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = c₀ • φ) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ) (N + 1) ≠ ⊥ := by
  obtain ⟨φ, hGS, -⟩ := hfam cA horient le_rfl
  have hφne : φ ≠ 0 := by
    intro h
    have hn := hGS.2.1
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hmem := (liebRepulsive_mem_groundSubmodule_inf_spinZ_iff N
    (symmetricRepulsiveHubbardHamiltonian N T U) (E₀ : ℂ)
    (liebHalfFillingSpinZVal N cA) φ).mpr ⟨hGS.1, hGS.2.2.1⟩
  rw [Submodule.mem_inf] at hmem
  exact (Submodule.ne_bot_iff _).mpr ⟨WithLp.ofLp φ, hmem.1, by simpa using hφne⟩

/-! ## The PR-14b capstone -/

/-- **The arc's PR-14b capstone.** For the physical symmetric repulsive Hubbard model at
half-filling (`1 ≤ |A|`, `1 ≤ |B|`), `theorem_10_4_lieb_repulsive_half_filling`'s conclusion holds
verbatim for `H = symmetricRepulsiveHubbardHamiltonian N T U`, as a **conditional theorem** built
from PR-14a's `liebRepulsive_multipletCompanion_capstone` (ground energy `E₀`, conjunct (ii), and
the per-sector Casimir family) together with this file's weight confinement and `finrank` count
(conjuncts (i), (iii), (iv)). Completing the unconditional
`theorem_10_4_lieb_repulsive_half_filling` from this capstone (lifting the `1 ≤ |A|`/`1 ≤ |B|`
restriction via the degenerate `A = ∅`/`A = univ` cases, and adding the uniform disjunct) is
PR-15's responsibility. -/
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
  classical
  obtain ⟨E₀, hsector, hmin⟩ :=
    liebRepulsive_multipletCompanion_capstone N hA hB T hT_symm hbip hT_conn U hU_pos
  set cA : ℕ := (liebOrientedSublattice A).card with hcAdef
  set cB : ℕ := (bipartitionComplement (liebOrientedSublattice A)).card with hcBdef
  have hcard : cA + cB = N + 1 := bipartitionComplement_card_add N (liebOrientedSublattice A)
  have horient : cB ≤ cA := liebOrientedSublattice_horient A
  have himb : sublatticeImbalance A = cA - cB := by
    rw [← liebOrientedSublattice_sublatticeImbalance_eq A, sublatticeImbalance]
    omega
  have hLcast : ((sublatticeImbalance A : ℕ) : ℝ) = (cA : ℝ) - (cB : ℝ) := by
    rw [himb, Nat.cast_sub horient]
  have hc₀ : liebRepulsiveSpinCasimir A
      = (((((cA : ℝ) - (cB : ℝ)) / 2) * ((((cA : ℝ) - (cB : ℝ)) / 2) + 1) : ℝ) : ℂ) := by
    have h1 : ((sublatticeImbalance A : ℕ) : ℂ) = ((((cA : ℝ) - (cB : ℝ) : ℝ)) : ℂ) := by
      rw [← hLcast]
      push_cast
      ring
    rw [liebRepulsiveSpinCasimir, h1]
    push_cast
    ring
  have hfam : ∀ q : ℕ, cB ≤ q → q ≤ cA →
      ∃ φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
        IsUniqueGroundStateOn
            (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N q))
            (symmetricRepulsiveHubbardHamiltonian N T U) E₀ φ ∧
          Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ
            = liebRepulsiveSpinCasimir A • φ := by
    intro q h1 h2
    exact hsector q (by omega)
      ((liebRepulsive_mem_tasaki23GroundStateSectors_iff N A (by omega)).mpr ⟨h1, h2⟩)
  refine ⟨(E₀ : ℂ), liebRepulsive_groundSubmodule_ne_bot N cA cB T U horient hfam, ?_, ?_, ?_⟩
  · intro E hE
    rw [Complex.ofReal_re]
    exact hmin E hE
  · intro v hv
    have h := liebRepulsive_groundSubmodule_le_spinSquared_eigenspace N cA cB T hT_symm U hcard
      horient hc₀ hfam hv
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
    exact h
  · have hle := liebRepulsive_finrank_groundSubmodule_le N cA cB T hT_symm U hcard horient hc₀ hfam
    have hge := liebRepulsive_finrank_groundSubmodule_ge N cA cB T U horient hfam
    rw [liebRepulsiveGroundMultiplicity, himb]
    exact le_antisymm hle hge

end LatticeSystem.Fermion
