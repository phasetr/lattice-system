import LatticeSystem.Quantum.SpinS.FerromagneticSectorPF
import LatticeSystem.Quantum.SpinS.EigenspaceFinrankLeOneTransfer
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum

/-!
# Tasaki §2.4, p. 34: the sector ground state is the ladder state, up to a scalar

Turns the Perron-Frobenius dimension bound of `FerromagneticSectorPF` into the identification the
solution of Problem 2.4.a (p. 496) states: in each magnetization sector `H_M` the ground state of
the ferromagnetic spin-`S` Heisenberg model on a connected graph is unique up to a scalar, and is
the ladder state `Φ_M = (Ŝ⁻_tot)^k Φ↑` of eq. (2.4.9), p. 33.

The bound is transferred from the sector matrix to the full Hilbert space intersected with the
magnetization subspace, where the ladder state is a non-zero member; a one-dimensional subspace
containing a non-zero vector is that vector's span.  Summing this identification over the
magnetization sectors is what yields eq. (2.4.10), p. 34.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; eq. (2.4.9), p. 33; solution of Problem 2.4.a, p. 496;
Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Per-sector uniqueness of the ferromagnetic ground state** (Tasaki §2.4 Theorem 2.1, p. 34;
solution of Problem 2.4.a, p. 496).

For a connected graph and a real, symmetric, edge-supported, strictly ferromagnetic coupling, the
ground-state eigenspace of `Ĥ` intersected with the magnetization subspace of `Ŝ³_tot`-eigenvalue
`m_max - k` is exactly the line spanned by the ladder state `Φ_M = (Ŝ⁻_tot)^k Φ↑`.

Perron-Frobenius (Theorem A.18, p. 475) bounds that intersection by one dimension and the ladder
state is a non-zero member of it. -/
theorem heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_eq_span_ladderIterateUp
    [Nonempty V] {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) (k : Fin (Fintype.card V * N + 1)) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      ⊓ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) =
    Submodule.span ℂ {ladderIterateUp V N k} := by
  have hmem : ladderIterateUp V N k ∈
      Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
          (saturatedFerromagnetEigenvalueS (V := V) J N)
        ⊓ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) := by
    refine Submodule.mem_inf.mpr ⟨ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k, ?_⟩
    unfold ladderIterateUp
    exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS k.val
  have hne : ladderIterateUp V N k ≠ 0 := by
    unfold ladderIterateUp
    exact totalSpinSOpMinus_pow_allAlignedStateS_zero_ne_zero (Nat.lt_succ_iff.mp k.isLt)
  have hspan_finrank : Module.finrank ℂ
      (Submodule.span ℂ {ladderIterateUp V N k} : Submodule ℂ ((V → Fin (N + 1)) → ℂ)) = 1 :=
    finrank_span_singleton hne
  have hle_one := heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
    (Λ := V) (N := N) J k.val (saturatedFerromagnetEigenvalueS (V := V) J N)
    (heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_connected_ferro
      hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN k)
  rw [Matrix.toLin'_apply'] at hle_one
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmem
  · rw [hspan_finrank]
    exact hle_one

end LatticeSystem.Quantum
