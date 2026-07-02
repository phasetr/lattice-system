import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionTotalSpinCasimirCharges
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSU2Invariance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedUniqueness
import LatticeSystem.Math.CommutingHermitianEigenvector
import LatticeSystem.Math.SubmoduleFinrankLeOne

/-!
# The balanced ground state is a `(Ŝ_tot)²`-eigenstate (Tasaki §10.2)

Toward Lieb's theorem for the attractive Hubbard model (Tasaki §10.2.1 Theorem 10.2), this file
proves the *eigenstate* step: the (unique-up-to-scalar) balanced ground state is an eigenstate of
the total-spin Casimir `(Ŝ_tot)²`.

The balanced ground eigenspace `balancedGroundEigenspace` (the vectors that are simultaneously
`Ĥ`-eigenvectors at the balanced minimum energy and per-spin number eigenvectors `N̂_↑ = N̂_↓ = k`)
is at most one-dimensional (`balanced_ground_eigenspace_finrank_le_one`, uniqueness half of Theorem
10.2).  Because `(Ŝ_tot)²` commutes with `Ĥ` (SU(2) invariance,
`fermionTotalSpinSquared_commute_attractiveHubbardHamiltonian`), with `N̂_↑`
(`fermionTotalSpinSquared_commute_fermionTotalUpNumber`), and with `N̂_↓`
(`fermionTotalSpinSquared_commute_fermionTotalDownNumber`), it maps this eigenspace into itself.  A
linear operator mapping a nonzero vector into a `finrank ≤ 1` subspace containing it acts on it as a
scalar (`exists_smul_of_mem_of_finrank_le_one`), and the scalar is real because `(Ŝ_tot)²` is
Hermitian (`isHermitian_mulVec_eigenvalue_eq_ofReal`).

The identification of the eigenvalue as `S(S+1)` (in particular `μ ≥ 0` and `S = 0` for the
attractive balanced ground state) is deferred to the singlet step that consumes this result.

## Main result

* `balancedGround_totalSpinSquared_eigenvector` — any nonzero balanced ground state `ψ` satisfies
  `(Ŝ_tot)² ψ = μ • ψ` for some real `μ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2), pp. 348–349; §9.3.3, p. 332; E. H. Lieb, *Phys. Rev. Lett.* **62**
(1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math

variable {N : ℕ}

/-- **The balanced ground state is a `(Ŝ_tot)²`-eigenstate (Tasaki §10.2, eigenstate step).** For an
attractive Hubbard model with symmetric real hopping `T` whose support graph is connected and
strictly attractive on-site interaction `U > 0`, any nonzero balanced ground state `ψ` (a vector in
`balancedGroundEigenspace`) is an eigenvector of the total-spin Casimir `(Ŝ_tot)²` with a real
eigenvalue `μ`.

Proof: `(Ŝ_tot)²` commutes with `Ĥ`, `N̂_↑`, `N̂_↓`, so it maps `balancedGroundEigenspace` into
itself; the eigenspace is at most one-dimensional
(`balanced_ground_eigenspace_finrank_le_one`), so `(Ŝ_tot)² ψ` — which lies in it — is a scalar
multiple of `ψ` (`exists_smul_of_mem_of_finrank_le_one`); the scalar is real because `(Ŝ_tot)²` is
Hermitian (`isHermitian_mulVec_eigenvalue_eq_ofReal`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2), pp. 348–349. -/
theorem balancedGround_totalSpinSquared_eigenvector (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ balancedGroundEigenspace k T U hT_symm) (hψ0 : ψ ≠ 0) :
    ∃ μ : ℝ, (fermionTotalSpinSquared N).mulVec ψ = (μ : ℂ) • ψ := by
  obtain ⟨hH, hUp, hDn⟩ := (mem_balancedGroundEigenspace_iff k T U hT_symm ψ).mp hψ
  -- `(Ŝ_tot)²` preserves the balanced ground eigenspace (it commutes with `Ĥ`, `N̂_↑`, `N̂_↓`).
  have hmem : (fermionTotalSpinSquared N).mulVec ψ ∈ balancedGroundEigenspace k T U hT_symm := by
    refine (mem_balancedGroundEigenspace_iff k T U hT_symm _).mpr ⟨?_, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec,
        ← (fermionTotalSpinSquared_commute_attractiveHubbardHamiltonian N T U hT_symm).eq,
        ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
    · rw [Matrix.mulVec_mulVec,
        ← (fermionTotalSpinSquared_commute_fermionTotalUpNumber N).eq,
        ← Matrix.mulVec_mulVec, hUp, Matrix.mulVec_smul]
    · rw [Matrix.mulVec_mulVec,
        ← (fermionTotalSpinSquared_commute_fermionTotalDownNumber N).eq,
        ← Matrix.mulVec_mulVec, hDn, Matrix.mulVec_smul]
  -- The eigenspace is at most one-dimensional, so `(Ŝ_tot)² ψ` is a scalar multiple of `ψ`.
  have hle := balanced_ground_eigenspace_finrank_le_one k T U hT_symm hU_pos hT_conn
  obtain ⟨c, hc⟩ := exists_smul_of_mem_of_finrank_le_one hle hψ hmem hψ0
  -- The scalar is real because `(Ŝ_tot)²` is Hermitian.
  obtain ⟨μ, hμ⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (fermionTotalSpinSquared_isHermitian N) hψ0 hc.symm
  exact ⟨μ, by rw [← hc, hμ]⟩

end LatticeSystem.Fermion
