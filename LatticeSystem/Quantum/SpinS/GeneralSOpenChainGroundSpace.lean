import LatticeSystem.Quantum.SpinS.GeneralSCasimirSpectrum
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Math.FrustrationFree

/-!
# Tasaki §8.3.1: the ground space of the general-`S` open AKLT chain is the joint bond kernel

The general-`S` open-chain Hamiltonian `Ĥ = Σ_{x ∈ openBonds L} ĥ_x` (`openAKLTHamiltonianGeneralS`)
is a sum of positive-semidefinite bond terms (`bondCasimirPenaltyS_posSemidef`), hence itself
positive semidefinite, and its zero-energy space is *frustration-free*: a state has zero energy
iff it is annihilated by every bond term separately (Tasaki Appendix Lemmas A.9/A.10,
`Math/FrustrationFree`).  Composed with the prime-power bond divisibility of
`GeneralSOpenChainBondTerm` and the boundary shape of `AKLTOpenChainWeylFactorization`, this pins
the Weyl image of every ground state to the `(S+1)²` boundary multidegrees of §8.3.1, p. 252
(`weylMap_groundSpaceGeneralS_eq_boundary_mul_prod`); the dimension count itself is future work.

The Hamiltonian is already normalised to ground energy `0` (unlike the `S = 1` open chain
`openProjHamiltonianS`, which needs an affine shift), so the frustration-free argument here carries
every local energy `0` with no shift, mirroring `openGroundSpace_isVBSGroundForm`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.3, eq. (7.2.46), p. 205; §8.3.1, p. 252; Appendix A.2.3, Lemmas A.9–A.10, pp. 469–470.
-/

open Matrix
open scoped ComplexOrder

namespace LatticeSystem.Quantum

open LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness MvPolynomial

/-- The **zero-energy space of the general-`S` open chain**: the eigenspace of the Hamiltonian's
linear map at eigenvalue `0`.  This is the zero-energy eigenspace of a positive-semidefinite
Hamiltonian (`openAKLTHamiltonianGeneralS_posSemidef`); attainment (that `0` is actually the
ground energy, i.e. this space is nonzero) needs an explicit VBS zero mode and is not claimed
here. -/
noncomputable def openAKLTGroundSpaceGeneralS (L S : ℕ) :
    Submodule ℂ ((Fin L → Fin (2 * S + 1)) → ℂ) :=
  Module.End.eigenspace (Matrix.mulVecLin (openAKLTHamiltonianGeneralS L S)) 0

/-- **The zero-energy space is the kernel of the Hamiltonian.** -/
theorem openAKLTGroundSpaceGeneralS_eq_ker (L S : ℕ) :
    openAKLTGroundSpaceGeneralS L S
      = LinearMap.ker (Matrix.mulVecLin (openAKLTHamiltonianGeneralS L S)) := by
  ext Φ
  rw [openAKLTGroundSpaceGeneralS, Module.End.mem_eigenspace_iff, zero_smul, LinearMap.mem_ker]

/-- **`Ĥ ≥ 0`**, so `0` lower-bounds the energy: each bond term is positive semidefinite
(`bondCasimirPenaltyS_posSemidef`), and a sum of positive-semidefinite matrices is
positive semidefinite. -/
theorem openAKLTHamiltonianGeneralS_posSemidef {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    (openAKLTHamiltonianGeneralS L S).PosSemidef := by
  rw [openAKLTHamiltonianGeneralS]
  exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero
    fun x _ => bondCasimirPenaltyS_posSemidef (ne_ringSucc (by omega) x) hS

/-- **Headline: the zero-energy space is the joint bond kernel** (frustration-freeness).  A state
has zero energy iff it is annihilated by every open-bond Casimir penalty term separately. -/
theorem mem_openAKLTGroundSpaceGeneralS_iff {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0)
    (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS L S
      ↔ ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 := by
  have hlb : ∀ x ∈ openBonds L,
      (bondCasimirPenaltyS x (ringSucc x) S
        - ((0 : ℝ) : ℂ) • (1 : ManyBodyOpS (Fin L) (2 * S))).PosSemidef := fun x _ => by
    simpa using bondCasimirPenaltyS_posSemidef (ne_ringSucc (by omega) x) hS
  rw [openAKLTGroundSpaceGeneralS_eq_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    openAKLTHamiltonianGeneralS]
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · have hgs : (∑ x ∈ openBonds L, bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ
        = ((∑ _x ∈ openBonds L, (0 : ℝ) : ℝ) : ℂ) • Φ := by simpa using h
    simpa using frustration_free_local_eigen (openBonds L)
      (fun x : Fin L => bondCasimirPenaltyS x (ringSucc x) S) (fun _ => (0 : ℝ)) Φ hlb hgs x hx
  · rw [Matrix.sum_mulVec]
    exact Finset.sum_eq_zero h

/-- **Boundary shape of the general-`S` open-chain ground states** (Tasaki §8.3.1, p. 252).  The
Weyl image of any zero-energy state factors as the product `∏_x f_x^S` of the `S`-th powers of the
open bond factors times a boundary form: a linear combination of the `(S+1)²` monomials
`X^{boundaryDeg m S ab}`, which involve only the two end sites and record Tasaki's two free
effective spin-`S/2` edge spins.

Proof: frustration-freeness (`mem_openAKLTGroundSpaceGeneralS_iff`) turns membership into
annihilation by every bond term, which yields the prime-power divisibility
`prod_fBond_pow_dvd_weylMap_of_annihilated`; the per-site degree input is the weighted homogeneity
of the Weyl image, and `exists_boundary_factorization` supplies the shape. -/
theorem weylMap_groundSpaceGeneralS_eq_boundary_mul_prod {m S : ℕ} (hS : S ≠ 0)
    {Φ : (Fin (m + 2) → Fin (2 * S + 1)) → ℂ}
    (hΦ : Φ ∈ openAKLTGroundSpaceGeneralS (m + 2) S) :
    ∃ c : Fin (S + 1) × Fin (S + 1) → ℂ,
      weylMap Φ
        = (∑ ab : Fin (S + 1) × Fin (S + 1), monomial (boundaryDeg m S ab) (c ab))
            * ∏ x ∈ openBonds (m + 2), fBond x ^ S :=
  exists_boundary_factorization (weylMap_isWeightedHomogeneous Φ)
    (prod_fBond_pow_dvd_weylMap_of_annihilated (by omega) S Φ
      ((mem_openAKLTGroundSpaceGeneralS_iff (by omega) hS Φ).mp hΦ))

end LatticeSystem.Quantum
