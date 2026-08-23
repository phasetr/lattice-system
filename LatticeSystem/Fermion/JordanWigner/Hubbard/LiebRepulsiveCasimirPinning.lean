import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveEndpointIdentification
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveUniquenessAssembly
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveTheorem23Instance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSectorBridgeFinal

/-!
# Casimir pinning `c 0 = liebRepulsiveSpinCasimir A` (Tasaki §10.2.2, PR-13b)

Eighteenth installment of the Theorem 10.4 discharge arc (issue #5320).

## Main results

* `casimirSelector_strict_min_unique` — **selector uniqueness**: two occupied Casimir eigenvalues
  each satisfying the strict-minimality property of
  `exists_unique_casimir_sector_strict_min` (`LiebRepulsiveCasimirSector.lean`) for the *same*
  Hamiltonian must coincide.
* `symmetricHomotopyHamiltonian_one_isUniqueGroundStateOn` — the PR-13a-scoped λ-family transport
  capstone: for every `λ ∈ (0, λ₀)`,
  `IsUniqueGroundStateOn K (symmetricHomotopyHamiltonian N A T U lam 1) E_λ φ_λ` on the joint
  number/spin-`z` sector `K = numberSpinZSectorEuclidean N (N+1) m₀`, obtained by transporting
  `tasaki_lemma_10_1_liebRepulsive_apply`'s compressed uniqueness up along `coordinateExtend` and
  the generalized `isUniqueGroundStateOn_coordinateSpan_iff_submatrix`
  (`Math/MatrixAnalysis/BlockTransport.lean`).
* `symmetricHomotopy_casimirSelector_zero_eq_liebRepulsiveSpinCasimir` — the arc's Casimir-pinning
  capstone: extends PR-12b's `symmetricHomotopy_casimirSelector_eq_const`
  (`LiebRepulsiveSymmetricHomotopy.lean`, `c 0 = c 1`) with `c 0 = liebRepulsiveSpinCasimir A`.

## The pinning argument

For every `λ ∈ (0, λ₀)` the transported unique ground state `φ_λ` of the `s = 1` endpoint occupies,
by the (membership-extended) `exists_unique_casimir_sector_strict_min`, an occupied Casimir sector
`c_λ` with the strict-minimality property; selector uniqueness identifies `c_λ` with the PR-12b
selector value at `s = 1` for the coupling `λ`, hence — through `c 0 = c 1` and the
`λ`-independence of the `s = 0` endpoint (`symmetricHomotopyHamiltonian_zero`) — with `c 0` for the
*given* coupling. Restricting the resulting Casimir eigen-equation back to the half-filled
coordinate block makes it an identity between compressed vectors, so `λ → 0⁺` (Lemma 10.1's
convergence `Philam λ → Φeff`) transports it to `Φeff` by uniqueness of limits; no finite-spectrum
argument is used. Finally `Φeff` is proportional to the Marshall-positive Theorem 2.3 eigenvector of
`liebRepulsive_groundState_casimir_eq_predicted` (`LiebRepulsiveTheorem23Instance.lean`) — the two
ground energies agree by mutual minimality, and the uniqueness clause supplies the proportionality —
which carries `liebRepulsiveSpinCasimir A`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators Topology

variable {N : ℕ}

/-! ## Selector uniqueness -/

/-- **Selector uniqueness.** If `c₁` and `c₂` are both occupied Casimir eigenvalues of the same
Hamiltonian `H` satisfying the strict-minimality property of
`exists_unique_casimir_sector_strict_min`
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
  by_contra hne
  have h12 : E₁ < E₂ := by
    have := h₁.2.2 c₂ (fun h => hne h.symm) h₂.1
    rwa [h₂.2.1] at this
  have h21 : E₂ < E₁ := by
    have := h₂.2.2 c₁ hne h₁.1
    rwa [h₁.2.1] at this
  exact absurd h12 (not_lt.mpr h21.le)

/-! ## `SU(2)` adapters and block invariance along the symmetric-form homotopy -/

/-- **The `SU(2)` adapters of the symmetric-form homotopy**, at every interpolation parameter `s`:
`H_s` is Hermitian and commutes with `N̂`, `Ŝ³` and `Ŝ²`. These are PR-12a's adapters for
`symmetricRepulsiveHubbardHamiltonian` (`LiebRepulsiveSU2Invariance.lean`) read at the homotoped
hopping matrix, whose symmetry is `homotopyHopping_symm`. Bundled as a single conjunction because
`exists_unique_casimir_sector_strict_min` consumes all four together. -/
private theorem symmetricHomotopyHamiltonian_su2_adapters (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ x y, T x y = T y x)
    (U : Fin (N + 1) → ℝ) (lam s : ℝ) :
    (symmetricHomotopyHamiltonian N A T U lam s).IsHermitian ∧
      Commute (symmetricHomotopyHamiltonian N A T U lam s) (fermionTotalNumber (2 * N + 1)) ∧
      Commute (symmetricHomotopyHamiltonian N A T U lam s) (fermionTotalSpinZ N) ∧
      Commute (symmetricHomotopyHamiltonian N A T U lam s) (fermionTotalSpinSquared N) := by
  have hTs : ∀ x y, homotopyHopping T (liebEndpointHopping A T lam) s x y
      = homotopyHopping T (liebEndpointHopping A T lam) s y x := homotopyHopping_symm A T hT lam s
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [symmetricHomotopyHamiltonian]
  · exact symmetricRepulsiveHubbardHamiltonian_isHermitian N _ hTs _
  · exact (fermionTotalNumber_commute_symmetricRepulsiveHubbardHamiltonian N _ _).symm
  · exact (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N _ _).symm
  · exact (fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian N _ hTs _).symm

/-- **The symmetric-form homotopy has no matrix element leaving the half-filled fixed-`Ŝ³` block.**
Because `H_s` commutes with `N̂` and `Ŝ³` it preserves the joint sector `K`, which is the coordinate
span of `liebHalfFillingPred N nUp`
(`numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred`);
reading that invariance off on standard basis vectors
(`apply_eq_zero_of_mapsTo_coordinateSpan`) gives the entrywise hypothesis
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix` consumes. -/
private theorem symmetricHomotopyHamiltonian_apply_eq_zero_of_liebHalfFillingPred (N nUp : ℕ)
    (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (lam s : ℝ) {i j : Fin (2 * N + 2) → Fin 2}
    (hj : liebHalfFillingPred N nUp j) (hi : ¬ liebHalfFillingPred N nUp i) :
    symmetricHomotopyHamiltonian N A T U lam s i j = 0 := by
  have hHN : Commute (symmetricHomotopyHamiltonian N A T U lam s)
      (fermionTotalNumber (2 * N + 1)) := by
    rw [symmetricHomotopyHamiltonian]
    exact (fermionTotalNumber_commute_symmetricRepulsiveHubbardHamiltonian N _ _).symm
  have hHS3 : Commute (symmetricHomotopyHamiltonian N A T U lam s) (fermionTotalSpinZ N) := by
    rw [symmetricHomotopyHamiltonian]
    exact (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N _ _).symm
  refine apply_eq_zero_of_mapsTo_coordinateSpan (fun v hv => ?_) hj hi
  rw [← numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred N nUp] at hv ⊢
  exact numberSpinZSectorEuclidean_mem_of_commute hHN hHS3 hv

/-! ## Compressed-to-full transport of the `s = 1` unique ground state -/

/-- **Transport of a compressed unique ground state to the joint number/spin-`z` sector.** A unique
ground state of the compressed `λ`-family `Ĥ₀|_K + λ V̂|_K` on the whole compressed sector extends
by zero to a unique ground state of the symmetric-form homotopy's `s = 1` endpoint on
`K = numberSpinZSectorEuclidean N (N+1) (liebHalfFillingSpinZVal N nUp)`, with the ground energy
shifted by the explicit real constant `(N+1)/4`. Chains the sector bridge
(`numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred`), the block transport
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix`, the identification of the block submatrix
with `configSectorCompress` (`configSectorCompress_apply`), the compressed endpoint identity
`configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul`, and the
constant-shift transport `isUniqueGroundStateOn_sub_smul_one_iff`. -/
private theorem isUniqueGroundStateOn_symmetricHomotopyHamiltonian_one_of_compressed (N nUp : ℕ)
    (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (lam E : ℝ)
    (Φ : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp)))
    (hGS : IsUniqueGroundStateOn
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp))))
      (perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) lam) E Φ) :
    IsUniqueGroundStateOn
      (numberSpinZSectorEuclidean N ((N : ℂ) + 1) (liebHalfFillingSpinZVal N nUp))
      (symmetricHomotopyHamiltonian N A T U lam 1) (E - ((N : ℝ) + 1) / 4)
      (coordinateExtend (liebHalfFillingPred N nUp) Φ) := by
  have hsub : (symmetricHomotopyHamiltonian N A T U lam 1).submatrix Subtype.val Subtype.val
      = configSectorCompress N (liebHalfFillingPred N nUp)
          (symmetricHomotopyHamiltonian N A T U lam 1) := by
    ext s s'
    rw [configSectorCompress_apply]
    rfl
  have hiff := isUniqueGroundStateOn_coordinateSpan_iff_submatrix
    (H := symmetricHomotopyHamiltonian N A T U lam 1) (P := liebHalfFillingPred N nUp)
    (fun _ _ hj hi =>
      symmetricHomotopyHamiltonian_apply_eq_zero_of_liebHalfFillingPred N nUp A T U lam 1 hj hi)
    (E := E - ((N : ℝ) + 1) / 4)
    (coordinateExtend_mem_coordinateSpan (P := liebHalfFillingPred N nUp) Φ)
  rw [numberSpinZSectorEuclidean_eq_coordinateSpan_liebHalfFillingPred N nUp]
  refine hiff.mpr ?_
  rw [coordinateRestrict_coordinateExtend, hsub,
    configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul]
  exact (isUniqueGroundStateOn_sub_smul_one_iff _ _ (((N : ℝ) + 1) / 4) E Φ).mp hGS

/-- **The λ-family transport capstone.** For a nondegenerate bipartition and an admissible
magnetization sector, the `s = 1` endpoint of the symmetric-form homotopy has, for every
sufficiently small `λ > 0`, a unique ground state on the joint number/spin-`z` sector
`K = numberSpinZSectorEuclidean N (N+1) (liebHalfFillingSpinZVal N nUp)`: PR-11b's compressed
`λ`-family uniqueness (`tasaki_lemma_10_1_liebRepulsive_apply`,
`LiebRepulsiveUniquenessAssembly.lean`) transported by
`isUniqueGroundStateOn_symmetricHomotopyHamiltonian_one_of_compressed`. -/
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
  obtain ⟨lam0, hlam0, Elam, Philam, -, -, hUnique, -, -⟩ :=
    tasaki_lemma_10_1_liebRepulsive_apply A hA hB nUp hnUp hM hbip hT
  exact ⟨lam0, hlam0, fun lam => Elam lam - ((N : ℝ) + 1) / 4,
    fun lam => coordinateExtend (liebHalfFillingPred N nUp) (Philam lam),
    fun lam hlam hlt => isUniqueGroundStateOn_symmetricHomotopyHamiltonian_one_of_compressed
      N nUp A T U lam (Elam lam) (Philam lam) (hUnique lam hlam hlt)⟩

/-! ## The Casimir eigenvalue of the effective ground state -/

/-- **The effective ground state carries the predicted Casimir.** If the second-order effective
Hamiltonian's unique ground state `Φeff` on `ker (Ĥ₀|_K)` happens to be a `Ŝ²`-eigenvector at `c0`,
then `c0 = liebRepulsiveSpinCasimir A`. PR-11a's assembly `iff`
(`isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`) turns `Φeff` into the
unique ground state of the shifted superexchange Heisenberg matrix, reindexed onto the hard-core
sector; PR-10b's `liebRepulsive_groundState_casimir_eq_predicted` supplies a nonzero, energy-minimal
eigenvector of exactly that matrix carrying `liebRepulsiveSpinCasimir A`; the two ground energies
agree by mutual minimality, so the uniqueness clause makes the two vectors proportional and the
`Ŝ²`-eigenvalues coincide. -/
private theorem casimirValue_eq_liebRepulsiveSpinCasimir_of_effectiveGroundState (N nUp : ℕ)
    (hnUp : nUp ≤ N + 1) (A : Finset (Fin (N + 1))) (hA : 1 ≤ A.card)
    (hB : 1 ≤ (bipartitionComplement A).card)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1)
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x)
    {Eeff : ℝ} {Φeff : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp))}
    (hEffGS : IsUniqueGroundStateOn (matrixKernel (liebPerturbationH0Compressed N nUp))
      (secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp))
      Eeff Φeff)
    {c0 : ℂ}
    (hcas : Matrix.toEuclideanLin
        ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val) Φeff = c0 • Φeff) :
    c0 = liebRepulsiveSpinCasimir A := by
  classical
  set eS := liebHardCoreHalfFillingSectorEquivS N nUp hnUp
  set eA := liebHardCoreAmbientSubtypeEquiv N nUp
  set Heis := heisenbergHamiltonianSMatrixOnMagSector
    ((2 : ℂ) • bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A))) 1 (N + 1 - nUp)
  set sh : ℝ := ((A.card * (N + 1 - A.card) : ℕ) : ℝ) with hsh
  set ρ := coordinateRestrict (liebHalfFillingHardcorePred N nUp) Φeff
  -- the vector-level bridge between `toEuclideanLin` eigen-equations and `mulVec` ones
  have hbridge : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
      (v : EuclideanSpace ℂ ι) (z : ℂ),
      Matrix.toEuclideanLin M v = z • v ↔ M.mulVec (WithLp.ofLp v) = z • WithLp.ofLp v := by
    intro ι _ _ M v z
    exact ⟨fun h => congrArg WithLp.ofLp h, fun h => WithLp.ofLp_injective 2 h⟩
  -- PR-11a's assembly `iff` moves `Φeff` onto the Heisenberg side of the bridge
  have hshift : ((A.card : ℂ) * ((N + 1 - A.card : ℕ) : ℂ)) = ((sh : ℝ) : ℂ) := by
    rw [hsh]; push_cast; ring
  have hΨ := (isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg
    N nUp hnUp hbip hT Eeff Φeff hEffGS.1).mp hEffGS
  rw [hshift] at hΨ
  -- reindexing onto the hard-core fermionic sector is what PR-10b's statement is indexed by
  have hsubmat : (Heis - ((sh : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)).submatrix eS eS
      = Heis.submatrix eS eS - ((sh : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
    ext u u'
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, EmbeddingLike.apply_eq_iff_eq]
  have hΨhc := (isUniqueGroundStateOn_reindex_iff (Heis - ((sh : ℝ) : ℂ) • (1 : Matrix _ _ ℂ))
    eS Eeff _).mp hΨ
  rw [hsubmat] at hΨhc
  set Ψhc : EuclideanSpace ℂ (configSector N (liebHardCoreHalfFillingPred N nUp)) :=
    WithLp.toLp 2 fun u => (WithLp.ofLp ρ) (eA u) with hΨhcdef
  have hΨhceq : (WithLp.toLp 2 fun u =>
      (WithLp.ofLp (WithLp.toLp 2 fun j => (WithLp.ofLp ρ) ((eS.symm.trans eA) j))) (eS u))
      = Ψhc := by
    refine PiLp.ext fun u => ?_
    simp [hΨhcdef]
  rw [hΨhceq] at hΨhc
  -- undo the constant shift, so both sides speak about the unshifted Heisenberg matrix
  have hΨhc' : IsUniqueGroundStateOn
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (configSector N (liebHardCoreHalfFillingPred N nUp))))
      (Heis.submatrix eS eS) (Eeff + sh) Ψhc := by
    refine (isUniqueGroundStateOn_sub_smul_one_iff _ (Heis.submatrix eS eS) sh (Eeff + sh)
      Ψhc).mpr ?_
    simpa using hΨhc
  have hΨne : Ψhc ≠ 0 := by
    intro h
    have := hΨhc'.2.1
    rw [h, norm_zero] at this
    exact zero_ne_one this
  -- the Casimir eigen-equation, restricted to the hard-core block and reindexed the same way
  have hmemρ : Φeff ∈ coordinateSpan (liebHalfFillingHardcorePred N nUp) := by
    rw [← matrixKernel_liebPerturbationH0Compressed_eq_coordinateSpan]
    exact hEffGS.1
  have hres := coordinateRestrict_toEuclideanLin
    (H := (fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val)
    (P := liebHalfFillingHardcorePred N nUp) hmemρ
  rw [hcas, coordinateRestrict_smul] at hres
  have hS2hc : ((((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val).submatrix
        Subtype.val Subtype.val).submatrix eA eA)
      = (fermionTotalSpinSquared N).submatrix
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val) := rfl
  have hcashc : Matrix.toEuclideanLin
      ((fermionTotalSpinSquared N).submatrix
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)) Ψhc
      = c0 • Ψhc := by
    rw [← hS2hc, hΨhcdef, toEuclideanLin_submatrix_equiv_apply, ← hres]
    exact PiLp.ext fun u => rfl
  -- PR-10b's Marshall-positive Casimir eigenvector of exactly that Heisenberg matrix
  obtain ⟨μ, w, hw0, -, hweig, hwmin, hwcas⟩ :=
    liebRepulsive_groundState_casimir_eq_predicted A hA hB nUp hnUp hM
  set w' : EuclideanSpace ℂ (configSector N (liebHardCoreHalfFillingPred N nUp)) :=
    WithLp.toLp 2 w
  have hw'ne : w' ≠ 0 := by
    intro h
    exact hw0 (congrArg WithLp.ofLp h)
  have hw'eig : Matrix.toEuclideanLin (Heis.submatrix eS eS) w' = ((μ : ℝ) : ℂ) • w' :=
    (hbridge _ w' _).mpr hweig
  -- mutual minimality pins the two ground energies to each other
  have hle₁ : Eeff + sh ≤ μ := hΨhc'.2.2.2.1.2 μ ⟨w', Submodule.mem_top, hw'ne, hw'eig⟩
  have hle₂ : μ ≤ Eeff + sh :=
    hwmin (Eeff + sh) (WithLp.ofLp Ψhc) (fun h => hΨne (WithLp.ofLp_injective 2 h))
      ((hbridge _ Ψhc _).mp hΨhc'.2.2.1)
  have hEμ : ((μ : ℝ) : ℂ) = ((Eeff + sh : ℝ) : ℂ) := by
    rw [le_antisymm hle₂ hle₁]
  -- equal ground energies make the uniqueness clause applicable, hence the vectors proportional
  obtain ⟨a, ha⟩ := hΨhc'.2.2.2.2 w' Submodule.mem_top (by rw [hw'eig, hEμ])
  have hcasw : Matrix.toEuclideanLin
      ((fermionTotalSpinSquared N).submatrix
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)) w'
      = c0 • w' := by
    rw [ha, map_smul, hcashc, smul_comm]
  have hcasw' : Matrix.toEuclideanLin
      ((fermionTotalSpinSquared N).submatrix
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)) w'
      = liebRepulsiveSpinCasimir A • w' := (hbridge _ w' _).mpr hwcas
  have hzero : (c0 - liebRepulsiveSpinCasimir A) • w' = 0 := by
    rw [sub_smul, ← hcasw, ← hcasw', sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hw'ne

/-! ## The Casimir pinning capstone -/

/-- **The arc's Casimir-pinning capstone.** For the physical symmetric repulsive model at half
filling and an admissible `Ŝ³` sector, the occupied Casimir sector is `liebRepulsiveSpinCasimir A`:
PR-12b's `symmetricHomotopy_casimirSelector_eq_const` (`LiebRepulsiveSymmetricHomotopy.lean`) is
extended from `c 0 = c 1` to `c 0 = liebRepulsiveSpinCasimir A`. The selector value at `s = 0` is
independent of the coupling `λ` (`symmetricHomotopyHamiltonian_zero` plus
`casimirSelector_strict_min_unique`), so it can be evaluated along the `λ → 0⁺` family of
`tasaki_lemma_10_1_liebRepulsive_apply`; see the module docstring for the full argument. -/
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
  classical
  obtain ⟨c, hsel, hc01⟩ := symmetricHomotopy_casimirSelector_eq_const N Ne hNe_even hNe_pos
    hNe_lt T hT_symm hbip hT_conn U hU_pos hlam
  refine ⟨c, hsel, hc01, ?_⟩
  obtain ⟨lam0, hlam0, Elam, Philam, Eeff, Φeff, hUnique, hEffGS, hTend⟩ :=
    tasaki_lemma_10_1_liebRepulsive_apply A hA hB nUp hnUp hM hbip hT_symm
  have hm₀ : liebHalfFillingSpinZVal N nUp = ((Ne : ℂ) - ((N : ℂ) + 1)) / 2 :=
    liebHalfFillingSpinZVal_eq_of_two_mul N nUp Ne hNe2
  -- for every small coupling the compressed ground state carries the Casimir eigenvalue `c 0`
  have hkey : ∀ mu : ℝ, 0 < mu → mu < lam0 →
      Matrix.toEuclideanLin ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val)
        (Philam mu) = c 0 • Philam mu := by
    intro mu hmu hmulam
    have hGS := isUniqueGroundStateOn_symmetricHomotopyHamiltonian_one_of_compressed N nUp A T U
      mu (Elam mu) (Philam mu) (hUnique mu hmu hmulam)
    rw [hm₀] at hGS
    obtain ⟨hH, hHN, hHS3, hHS2⟩ :=
      symmetricHomotopyHamiltonian_su2_adapters N A T hT_symm U mu 1
    obtain ⟨cc, hccne, hccmem, hccmin, hccstrict⟩ :=
      exists_unique_casimir_sector_strict_min hH hHN hHS3 hHS2 hGS
    obtain ⟨cmu, hselmu, hcmu01⟩ := symmetricHomotopy_casimirSelector_eq_const N Ne hNe_even
      hNe_pos hNe_lt T hT_symm hbip hT_conn U hU_pos hmu
    -- the transported ground state occupies the `s = 1` selector sector of the coupling `mu`
    have hone : cc = cmu 1 :=
      casimirSelector_strict_min_unique ⟨hccne, hccmin, hccstrict⟩
        ⟨(hselmu 1 (by norm_num)).1, rfl,
          fun c' hne hK => (hselmu 1 (by norm_num)).2 c' hne hK⟩
    -- the `s = 0` endpoint does not depend on the coupling, so its selector value does not either
    have hzero : c 0 = cmu 0 := by
      have hH0 : symmetricHomotopyHamiltonian N A T U lam 0
          = symmetricRepulsiveHubbardHamiltonian N T U :=
        symmetricHomotopyHamiltonian_zero A T U lam
      have hH0' : symmetricHomotopyHamiltonian N A T U mu 0
          = symmetricRepulsiveHubbardHamiltonian N T U :=
        symmetricHomotopyHamiltonian_zero A T U mu
      have h1 := hsel 0 (by norm_num)
      have h2 := hselmu 0 (by norm_num)
      rw [hH0] at h1
      rw [hH0'] at h2
      exact casimirSelector_strict_min_unique
        ⟨h1.1, rfl, fun c' hne hK => h1.2 c' hne hK⟩
        ⟨h2.1, rfl, fun c' hne hK => h2.2 c' hne hK⟩
    have hcc : cc = c 0 := by rw [hone, ← hcmu01, ← hzero]
    -- read the Casimir eigen-equation off the sector membership and restrict it to the block
    have hcasfull : Matrix.toEuclideanLin (fermionTotalSpinSquared N)
        (coordinateExtend (liebHalfFillingPred N nUp) (Philam mu))
        = c 0 • coordinateExtend (liebHalfFillingPred N nUp) (Philam mu) := by
      rw [numberSpinZCasimirSectorEuclidean, Submodule.mem_inf] at hccmem
      rw [← hcc]
      exact Module.End.mem_eigenspace_iff.mp hccmem.2
    have hres := coordinateRestrict_toEuclideanLin (H := fermionTotalSpinSquared N)
      (P := liebHalfFillingPred N nUp)
      (coordinateExtend_mem_coordinateSpan (P := liebHalfFillingPred N nUp) (Philam mu))
    rw [hcasfull, coordinateRestrict_smul, coordinateRestrict_coordinateExtend] at hres
    exact hres.symm
  -- pass to the limit `λ → 0⁺`
  have hcont : Continuous fun v : EuclideanSpace ℂ (configSector N (liebHalfFillingPred N nUp)) =>
      Matrix.toEuclideanLin ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val) v :=
    LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanLin ((fermionTotalSpinSquared N).submatrix
        (Subtype.val : configSector N (liebHalfFillingPred N nUp) → Fin (2 * N + 2) → Fin 2)
        Subtype.val))
  have hT1 : Filter.Tendsto (fun mu : ℝ =>
      Matrix.toEuclideanLin ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val)
        (Philam mu)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Matrix.toEuclideanLin
        ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val) Φeff)) :=
    (hcont.tendsto _).comp hTend
  have hT2 : Filter.Tendsto (fun mu : ℝ => c 0 • Philam mu) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (c 0 • Φeff)) := hTend.const_smul (c 0)
  have heq : (fun mu : ℝ =>
      Matrix.toEuclideanLin ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val)
        (Philam mu)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] fun mu : ℝ => c 0 • Philam mu := by
    filter_upwards [Ioo_mem_nhdsGT hlam0] with mu hmu
    exact hkey mu hmu.1 hmu.2
  have hcasΦ : Matrix.toEuclideanLin
      ((fermionTotalSpinSquared N).submatrix Subtype.val Subtype.val) Φeff = c 0 • Φeff :=
    tendsto_nhds_unique (hT1.congr' heq) hT2
  exact casimirValue_eq_liebRepulsiveSpinCasimir_of_effectiveGroundState N nUp hnUp A hA hB hM
    hbip hT_symm hEffGS hcasΦ

end LatticeSystem.Fermion
