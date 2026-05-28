import LatticeSystem.Quantum.SpinS.BlockDiagSubmatrixBridge
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank
import LatticeSystem.Quantum.SpinS.DressedAxisSwapDegeneracyBound

/-!
# Dressed `Ĥ'` full eigenspace ⊓ ker(P) `finrank ℂ ≤ 1` at the PF eigenvalue

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(g.2): lifts the parity-submatrix per-block PF simplicity (#3831) to the **full**
dressed `Ĥ'_dressed` eigenspace via the block-diag bridge (#3832), under the dressed
parity-block-diagonality (#3833 step 1).

This is the per-block input consumed by the `dressed eig ≤ 2` assembly (next).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Per-parity-block full-eigenspace `finrank ℂ ≤ 1`** for the Marshall-dressed
axis-swapped Hamiltonian, at the PF eigenvalue of the parity-block submatrix.

Combines:
- `complex_dressed_parity_block_submatrix_eigenspace_finrank_le_one` (#3831): gives `ν : ℝ`
  with `finrank ℂ (eig dressed.submatrix ν) ≤ 1`.
- `parity_block_full_eigenspace_inter_finrank_le_submatrix` (#3832): bounds
  `finrank ℂ (eig dressed ν ⊓ ker(P=(-1)^p))` by the submatrix finrank.
- `dressedAxisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne` (#3833 step 1):
  dressed Ĥ' is parity-block-diagonal (required hypothesis of #3832). -/
theorem dressed_full_eigenspace_inter_parity_finrank_le_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (h_intermediate : ∀ τ : Λ → Fin (N + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {p : ℕ} (hp : p < 2)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ,
      Module.finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) (ν : ℂ) ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) ≤ 1 := by
  obtain ⟨ν, hsub⟩ :=
    complex_dressed_parity_block_submatrix_eigenspace_finrank_le_one
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨ν, ?_⟩
  have hblock : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 →
      dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ τ = 0 := by
    intro σ τ hne_par
    have hne : σ ≠ τ := fun h => hne_par (by rw [h])
    have hodd : Odd (magSumS σ + magSumS τ) := by
      rw [Nat.odd_iff]
      have h1 : magSumS σ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : magSumS τ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    exact dressedAxisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne
      A hJself lam D hne hodd
  have hbridge :=
    parity_block_full_eigenspace_inter_finrank_le_submatrix hblock hp (ν : ℂ)
  exact le_trans hbridge hsub

end LatticeSystem.Quantum
