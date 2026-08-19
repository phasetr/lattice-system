import LatticeSystem.Quantum.SpinS.GeneralSCasimirSpectrum
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Math.FrustrationFree

/-!
# Tasaki §8.3.1: the ground space of the general-`S` open AKLT chain is the joint bond kernel

The general-`S` open-chain Hamiltonian `Ĥ = Σ_{x ∈ openBonds L} ĥ_x` (`openAKLTHamiltonianGeneralS`)
is a sum of positive-semidefinite bond terms (`bondCasimirPenaltyS_posSemidef`), hence itself
positive semidefinite, and its zero-energy space is *frustration-free*: a state has zero energy
iff it is annihilated by every bond term separately (Tasaki Appendix Lemmas A.9/A.10,
`Math/FrustrationFree`).  This is the polynomial input of the `(S+1)²` ground-state count asserted
at §8.3.1, p. 252 — the count itself (needing the `(S+1)²` boundary multidegree bijection) is
future work.

The Hamiltonian is already normalised to ground energy `0` (unlike the `S = 1` open chain
`openProjHamiltonianS`, which needs an affine shift), so the frustration-free argument here carries
every local energy `0` with no shift, mirroring `AKLTOpenChainCompleteness.lean:44–56`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.3, eq. (7.2.46), p. 205; §8.3.1, p. 252; Appendix A.2.3, Lemmas A.9–A.10, pp. 469–470.
-/

open Matrix
open scoped ComplexOrder

namespace LatticeSystem.Quantum

open LatticeSystem.Math

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
  sorry -- dev-implement: `Module.End.eigenspace` at eigenvalue `0` unfolds to `ker`
        -- (`Module.End.mem_eigenspace_iff` + `zero_smul`).

/-- **`Ĥ ≥ 0`**, so `0` lower-bounds the energy: each bond term is positive semidefinite
(`bondCasimirPenaltyS_posSemidef`), and a sum of positive-semidefinite matrices is
positive semidefinite. -/
theorem openAKLTHamiltonianGeneralS_posSemidef {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    (openAKLTHamiltonianGeneralS L S).PosSemidef := by
  sorry -- dev-implement: `openAKLTHamiltonianGeneralS` unfolded as `Finset.sum` +
        -- `bondCasimirPenaltyS_posSemidef (ne_ringSucc hL x) hS` for each `x ∈ openBonds L` +
        -- `Matrix.PosSemidef.add`/`.zero` (`Finset.sum_induction`).

/-- **Headline: the zero-energy space is the joint bond kernel** (frustration-freeness).  A state
has zero energy iff it is annihilated by every open-bond Casimir penalty term separately. -/
theorem mem_openAKLTGroundSpaceGeneralS_iff {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0)
    (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS L S
      ↔ ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 := by
  sorry -- dev-implement: `openAKLTGroundSpaceGeneralS_eq_ker` + `LinearMap.mem_ker` +
        -- `Matrix.mulVecLin_apply`; `→` via `frustration_free_local_eigen` with
        -- `bondCasimirPenaltyS_posSemidef` as the local lower bound (all local energies `0`);
        -- `←` via `Finset.sum_mulVec` + `Finset.sum_eq_zero`.

end LatticeSystem.Quantum
