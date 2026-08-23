import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSymmetricHomotopy
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchangeReducedInverse

/-!
# Symmetric endpoint identification (Tasaki §10.2.2)

Seventeenth installment of the Theorem 10.4 discharge arc (issue #5320): the `s = 1` endpoint of
the symmetric-form homotopy is identified with the `λ`-family of the perturbative step, first as an
operator identity on Fock space and then in compressed form on the half-filled fixed-`Ŝ³` sector.

## Main results

* `sum_fermionSiteNumber_eq_fermionTotalNumber` — the site occupation numbers sum to the total
  particle number, `Σ_x n̂_x = N̂`.
* `configSectorCompress_fermionTotalNumber_eq_smul_one` — on the half-filled sector `N̂` compresses
  to the scalar `(N + 1) • 1`, since every configuration of the sector carries `N + 1` electrons.
* `symmetricHomotopyHamiltonian_one_eq_uniform` — the `s = 1` endpoint of the symmetric-form
  homotopy is the uniform-`U = 1` symmetric repulsive Hubbard Hamiltonian on the endpoint hopping
  matrix `liebEndpointHopping A T lam`, since `homotopyHopping … 1 = liebEndpointHopping A T lam`
  and `homotopyOnSiteFn U 1 ≡ 1`.
* `configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul` — the
  compressed form of that endpoint on the half-filled fixed-`Ŝ³` sector: the site-dependent
  expansion `symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber`
  (`LiebRepulsiveSU2Invariance.lean`) at `U ≡ 1` writes the endpoint interaction as
  `liebPerturbationH0 N − (1/2) • N̂ + ((N+1)/4) • 1`, and compression turns the two offsets into
  genuine scalar multiples of `1`; combined with
  `homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian`
  (`LiebRepulsiveSuperexchangeReducedInverse.lean`) the compressed endpoint is the compressed
  perturbed Hamiltonian shifted by `((N+1)/4 : ℝ)`.

The shift is a real constant multiple of `1`, which is exactly the shape consumed by
`isUniqueGroundStateOn_sub_smul_one_iff` (`Math/MatrixAnalysis/SubmatrixGroundState.lean`); no
sector-restricted shift lemma is required.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-! ## The total particle number as a sum of site occupations -/

/-- **The site occupation numbers sum to the total particle number**, `Σ_x n̂_x = N̂`: splitting
the sum over the `2N + 2` spinful modes into up/down pairs (`sum_spinful_split`) turns `N̂` into
`Σ_x (n̂_{x↑} + n̂_{x↓})`, which is `Σ_x n̂_x` by definition of `fermionSiteNumber`. -/
theorem sum_fermionSiteNumber_eq_fermionTotalNumber (N : ℕ) :
    ∑ x : Fin (N + 1), fermionSiteNumber N x = fermionTotalNumber (2 * N + 1) := by
  rw [fermionTotalNumber, sum_spinful_split N fun j => fermionMultiNumber (2 * N + 1) j]
  rfl

/-! ## Compression of `N̂` on the half-filled fixed-`Ŝ³` sector -/

/-- **`N̂` compresses to the scalar `(N + 1) • 1` on the half-filled sector.** `N̂` is diagonal in
the occupation basis with entry the electron count of the configuration
(`fermionTotalNumber_eq_diagonal`), and every configuration of
`configSector N (liebHalfFillingPred N nUp)` carries exactly `N + 1` electrons, so the compressed
matrix is that constant times the identity. -/
theorem configSectorCompress_fermionTotalNumber_eq_smul_one (N nUp : ℕ) :
    configSectorCompress N (liebHalfFillingPred N nUp) (fermionTotalNumber (2 * N + 1))
      = ((N : ℂ) + 1) • (1 : Matrix (configSector N (liebHalfFillingPred N nUp))
          (configSector N (liebHalfFillingPred N nUp)) ℂ) := by
  ext s s'
  rw [configSectorCompress_apply, fermionTotalNumber_eq_diagonal, Matrix.diagonal_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : s = s'
  · rw [if_pos (congrArg Subtype.val h), if_pos h, mul_one, ← Nat.cast_sum, s.property.1,
      Nat.cast_add, Nat.cast_one]
  · rw [if_neg fun hv => h (Subtype.ext hv), if_neg h, mul_zero]

/-! ## The `s = 1` endpoint of the symmetric-form homotopy -/

/-- **The symmetric-form homotopy's `s = 1` endpoint is the uniform-`U = 1` symmetric repulsive
Hubbard Hamiltonian on the endpoint hopping matrix.** `homotopyHopping T (liebEndpointHopping A T
lam) 1 = liebEndpointHopping A T lam` and `homotopyOnSiteFn U 1 ≡ 1` (`homotopyOnSite _ 1 = 1`),
so `symmetricHomotopyHamiltonian N A T U lam 1` reduces to `symmetricRepulsiveHubbardHamiltonian N
(liebEndpointHopping A T lam) (fun _ => 1)`. -/
theorem symmetricHomotopyHamiltonian_one_eq_uniform (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (lam : ℝ) :
    symmetricHomotopyHamiltonian N A T U lam 1
      = symmetricRepulsiveHubbardHamiltonian N (liebEndpointHopping A T lam) (fun _ => 1) := by
  have hhop : homotopyHopping T (liebEndpointHopping A T lam) 1
      = liebEndpointHopping A T lam := by
    simp [homotopyHopping]
  have hons : homotopyOnSiteFn U 1 = fun _ => (1 : ℝ) := by
    funext x
    simp [homotopyOnSiteFn, homotopyOnSite]
  rw [symmetricHomotopyHamiltonian, hhop, hons]

/-! ## Compression to the half-filled fixed-`Ŝ³` sector -/

/-- **The compressed `s = 1` endpoint is the compressed perturbed Hamiltonian up to a genuine
scalar shift.** On `configSector N (liebHalfFillingPred N nUp)`,
`symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber` (at `U ≡ 1`) expands the endpoint
interaction as `liebPerturbationH0 N − (1/2) • N̂ + ((N+1)/4) • 1`; since `N̂` compresses to
`(N+1) • 1` on this sector, the whole offset from `perturbedHamiltonian (liebPerturbationH0
Compressed N nUp) (liebPerturbationVCompressed N nUp A T) lam` collapses to the explicit real
scalar `((N+1)/4 : ℝ)`. This is the shape `isUniqueGroundStateOn_sub_smul_one_iff`
(`Math/MatrixAnalysis/SubmatrixGroundState.lean`) consumes directly; no sector-restricted shift
lemma is needed. -/
theorem configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul
    (N nUp : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (lam : ℝ) :
    configSectorCompress N (liebHalfFillingPred N nUp)
        (symmetricHomotopyHamiltonian N A T U lam 1)
      = LatticeSystem.Math.perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
          (liebPerturbationVCompressed N nUp A T) lam
        - ((((N : ℝ) + 1) / 4 : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
  have hsumsite : (∑ x : Fin (N + 1), ((1 : ℂ) / 2) • fermionSiteNumber N x)
      = (1 / 2 : ℂ) • fermionTotalNumber (2 * N + 1) := by
    rw [← sum_fermionSiteNumber_eq_fermionTotalNumber, Finset.smul_sum]
  have hcard : (∑ _x : Fin (N + 1), (1 : ℂ)) = (N : ℂ) + 1 := by simp
  have hkin : homotopyHamiltonian N A T (1 : ℝ) lam 1
      = hubbardKinetic N (fun x y => ((liebEndpointHopping A T lam x y : ℝ) : ℂ))
        + hubbardOnSiteInteractionSite N fun _ => (1 : ℂ) := by
    have hhop : homotopyHopping T (liebEndpointHopping A T lam) 1
        = liebEndpointHopping A T lam := by
      simp [homotopyHopping]
    have hons : homotopyOnSite (1 : ℝ) 1 = 1 := by simp [homotopyOnSite]
    rw [homotopyHamiltonian, hhop, hons, repulsiveHubbardHamiltonian]
    simp only [Complex.ofReal_one]
  have hsym : symmetricHomotopyHamiltonian N A T U lam 1
      = homotopyHamiltonian N A T (1 : ℝ) lam 1
        - (1 / 2 : ℂ) • fermionTotalNumber (2 * N + 1)
        + (((N : ℂ) + 1) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
    rw [symmetricHomotopyHamiltonian_one_eq_uniform, symmetricRepulsiveHubbardHamiltonian,
      symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber, hkin]
    simp only [Complex.ofReal_one]
    rw [hsumsite, hcard]
    abel
  have hcompressone : configSectorCompress N (liebHalfFillingPred N nUp)
      (1 : ManyBodyOp (Fin (2 * N + 2)))
      = (1 : Matrix (configSector N (liebHalfFillingPred N nUp))
          (configSector N (liebHalfFillingPred N nUp)) ℂ) := by
    ext s s'
    rw [configSectorCompress_apply]
    simp only [Matrix.one_apply]
    by_cases h : s = s'
    · rw [if_pos (congrArg Subtype.val h), if_pos h]
    · rw [if_neg fun hv => h (Subtype.ext hv), if_neg h]
  rw [hsym, configSectorCompress_add, configSectorCompress_sub, configSectorCompress_smul,
    configSectorCompress_smul, homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian,
    configSectorCompress_fermionTotalNumber_eq_smul_one, hcompressone,
    show ((((N : ℝ) + 1) / 4 : ℝ) : ℂ) = ((N : ℂ) + 1) / 4 by push_cast; ring]
  module

end LatticeSystem.Fermion
