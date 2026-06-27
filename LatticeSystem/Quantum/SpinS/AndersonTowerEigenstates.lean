/-
Tasaki §4.2.2 Corollary 4.7 (the tower of low-lying energy eigenstates).

Building on Theorem 4.6 (`tower_lowLying_energy_bound`, proved in `AndersonTowerTheorem46`): for each
nonzero magnetization `M` the lowest energy eigenstate in the `Ŝ_tot^{(3)}` sector `μ₀+M` is low-lying.
This file develops the magnetization-sector tools for the torus tower; the first piece is the
magnetization eigenvalue shift of the tower trial state.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector

namespace LatticeSystem.Quantum

open Matrix

variable {d L N : ℕ}

/-- **Magnetization shift of an order-density power.**  If `Ŝ_tot^{(3)} v = λ v` then
`Ŝ_tot^{(3)} ((ô^b)^m v) = (λ + m·ε_b) (ô^b)^m v` (`ε_true = +1`, `ε_false = −1`): each order
density `ô^b` shifts the total magnetization by `ε_b`, so `m` of them shift by `m·ε_b`.  This
places the tower trial state `(ô^±)^M Φ` in the magnetization sector `μ₀ ± M`. -/
theorem totalSpinSOp3_mulVec_orderDensityPow_eigenvec [NeZero L] (b : Bool) (m : ℕ)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = lam • v) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((staggeredOrderDensityOpS d L N b ^ m).mulVec v)
      = (lam + (m : ℂ) * (if b then (1 : ℂ) else (-1 : ℂ)))
          • (staggeredOrderDensityOpS d L N b ^ m).mulVec v := by
  induction m with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec,
      totalSpinSOp3_mulVec_orderDensity_eigenvec d L N b ih, Matrix.mulVec_mulVec, ← pow_succ']
    congr 1
    push_cast
    ring

/-- **The tower state lies in the magnetization sector `μ₀ + M`.**  If `Ŝ_tot^{(3)} Φ = μ₀ Φ` then
`Ŝ_tot^{(3)} (towerState M Φ) = (μ₀ + M) (towerState M Φ)`: the raising/lowering tower shifts the
total magnetization by `M` (the scalar `V^{|M|}` in `towerState` does not change the eigenvalue). -/
theorem totalSpinSOp3_mulVec_towerState_eigenvec [NeZero L] (M : ℤ)
    {Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {μ₀ : ℂ}
    (hΦ : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = μ₀ • Φ) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        (towerState (torusParitySublattice d L) N M Φ)
      = (μ₀ + (M : ℂ)) • towerState (torusParitySublattice d L) N M Φ := by
  rcases lt_or_ge M 0 with hM | hM
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = -(m : ℤ) := ⟨M.natAbs, by omega⟩
    have hmpos : 1 ≤ m := by omega
    rw [towerState_neg_eq_smul d L N m hmpos, Matrix.mulVec_smul,
      totalSpinSOp3_mulVec_orderDensityPow_eigenvec false m hΦ, smul_smul, smul_smul]
    congr 1
    rw [if_neg (by decide)]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = (m : ℤ) := ⟨M.natAbs, by omega⟩
    rw [towerState_pos_eq_smul, Matrix.mulVec_smul,
      totalSpinSOp3_mulVec_orderDensityPow_eigenvec true m hΦ, smul_smul, smul_smul]
    congr 1
    rw [if_pos rfl]
    push_cast
    ring

/-- **Magnetization-sector minimum energy eigenvector.**  For real coupling `J` and a nonempty
magnetization sector `K`, the Heisenberg Hamiltonian has a nonzero eigenstate `ψ` whose energy is
the minimum eigenvalue of the sector-restricted (Hermitian) matrix and which lies in the
`Ŝ_tot^{(3)}` eigenspace of eigenvalue `|V|·N/2 − K`.  Built by lifting the restricted matrix's min
eigenvector (`exists_nonzero_eigenvector_hermitianMinEigenvalue`) via
`heisenbergHamiltonianS_mulVec_magSectorEmbedding`. -/
theorem heisenbergHamiltonianS_magSector_min_eigenvector {V : Type*} [Fintype V] [DecidableEq V]
    {J : V → V → ℂ} (hJ : ∀ x y, star (J x y) = J x y) (N K : ℕ)
    [Nonempty (magConfigS V N K)] :
    ∃ ψ : (V → Fin (N + 1)) → ℂ, ψ ≠ 0 ∧
      (heisenbergHamiltonianS J N).mulVec ψ
        = ((hermitianMinEigenvalue
            (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K hJ) : ℝ) : ℂ) • ψ ∧
      (totalSpinSOp3 V N).mulVec ψ
        = (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ)) • ψ := by
  obtain ⟨v, hv0, hveig⟩ :=
    exists_nonzero_eigenvector_hermitianMinEigenvalue
      (heisenbergHamiltonianSMatrixOnMagSector_isHermitian N K hJ)
  refine ⟨magSectorEmbedding v, ?_, heisenbergHamiltonianS_mulVec_magSectorEmbedding J v hveig, ?_⟩
  · intro hψ0
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hv0
    apply hτ
    have hval : magSectorEmbedding v τ.1 = v τ := magSectorEmbedding_apply_of_mem v τ.2
    rw [Pi.zero_apply, ← hval, hψ0, Pi.zero_apply]
  · rw [← mem_magSubspaceS_iff]
    exact magSectorEmbedding_mem_magSubspaceS v

end LatticeSystem.Quantum
