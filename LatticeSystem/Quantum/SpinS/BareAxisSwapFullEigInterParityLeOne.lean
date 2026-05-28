import LatticeSystem.Quantum.SpinS.DressedFullEigInterParityLeOne
import LatticeSystem.Quantum.SpinS.GaugeIntersectionEigenspaceFinrank

/-!
# Bare `Ĥ'` per-parity-block full-eigenspace `finrank ℂ ≤ 1` at the PF ν

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(g.4): transfers the dressed `Ĥ'_dressed` per-block PF bound (#3834) to the bare
axis-swapped `Ĥ'`, via the Marshall similarity (#3776 family) lifted to intersected
eigenspaces (#3835).

The key observation: the Marshall sign diagonal `Θ_A` commutes with the magnetization
parity diagonal `P = magParityDiagS` (two diagonal matrices), so the intersected
eigenspace finrank `eig Ĥ' μ ⊓ ker(P=c)` is preserved by Marshall similarity from
dressed to bare.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Marshall diagonal commutes with `magParityDiagS`**: two diagonal matrices commute. -/
theorem marshallDiagonal_commute_magParityDiagS (A : Λ → Bool) (N : ℕ) :
    magParityDiagS Λ N * (Matrix.diagonal (marshallSignS A) : ManyBodyOpS Λ N) =
      (Matrix.diagonal (marshallSignS A) : ManyBodyOpS Λ N) * magParityDiagS Λ N := by
  rw [magParityDiagS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext σ
  ring

/-- **Bare `Ĥ'` per-block full-eigenspace `finrank ℂ ≤ 1`** at the PF ν, via the Marshall
similarity transfer from #3834. -/
theorem bare_axisSwapped_full_eigenspace_inter_parity_finrank_le_one
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
          (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) (ν : ℂ) ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) ≤ 1 := by
  obtain ⟨ν, hdressed⟩ :=
    dressed_full_eigenspace_inter_parity_finrank_le_one
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate hp
  refine ⟨ν, ?_⟩
  have htransfer :=
    matrix_similar_eigenspace_inter_finrank_eq
      (U := Matrix.diagonal (marshallSignS A))
      (Uinv := Matrix.diagonal (marshallSignS A))
      (H := axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)
      (H' := dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)
      (Q := magParityDiagS Λ N)
      (marshallDiagonal_mul_self A) (marshallDiagonal_mul_self A)
      (dressedAxisSwappedAnisotropicHeisenbergS_eq_diag_conj A J lam D N)
      (marshallDiagonal_commute_magParityDiagS A N) (ν : ℂ) ((-1 : ℂ) ^ p)
  rw [htransfer] at hdressed
  exact hdressed

end LatticeSystem.Quantum
