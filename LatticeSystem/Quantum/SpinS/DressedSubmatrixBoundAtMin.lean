import LatticeSystem.Quantum.SpinS.DressedSubmatrixPFAtMin
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank

/-!
# Per-block bound `finrank ≤ 1` at `hermitianMinEigenvalue` (conditional)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.5): given a hypothesis `hPF_eq_min : ν_PF = hermitianMinEigenvalue submatrix_Herm`
(the missing identification deferred to a future Collatz-Wielandt step), the per-block
PF bound from #3831 transfers to a bound at `(hermitianMinEigenvalue : ℂ)`.

This is the **consumer-friendly form** for (i.7) #3854's `h0`/`h1` hypotheses — once the
PF = min identification is proven, this theorem (when paired) directly closes (i.7)'s
hypotheses unconditionally.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Per-block PF bound at `hermitianMinEigenvalue` (conditional)**: under the assumption
`ν_PF = hermitianMinEigenvalue submatrix_Herm`, the bound `finrank ≤ 1` at `(ν_PF : ℂ)`
from #3831 transfers to a bound at `(hermitianMinEigenvalue : ℂ)`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_min_conditional
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
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)]
    (hPF_eq_min : ∀ ν : ℝ,
      (finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1) →
      ν = hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p) : ℂ))) ≤ 1 := by
  obtain ⟨ν, hν_bound⟩ :=
    complex_dressed_parity_block_submatrix_eigenspace_finrank_le_one
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  have hν_eq := hPF_eq_min ν hν_bound
  rw [← hν_eq]
  exact hν_bound

end LatticeSystem.Quantum
