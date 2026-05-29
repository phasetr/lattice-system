import LatticeSystem.Quantum.SpinS.MarshallSubmatrixMinEq
import LatticeSystem.Quantum.SpinS.DressedSubmatrixPFAtMin

/-!
# Bare submatrix `hermitianMinEigenvalue ≤ ν_PF` via Marshall transfer

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.9): combines (j.4) #3860 (dressed: `hermitianMinEigenvalue dressed.submatrix ≤ ν_PF`)
with (j.8) #3865 (`hermitianMinEigenvalue bare.submatrix = hermitianMinEigenvalue
dressed.submatrix` via Marshall similarity) to give the bare-side bound:

```
hermitianMinEigenvalue bare.submatrix ≤ ν_PF (the PF eigenvalue).
```

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bare submatrix `hermitianMinEigenvalue ≤ PF ν`** via the Marshall similarity transfer
from the dressed side (j.4) #3860 + (j.8) #3865. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_min_le_pf_eigenvalue
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
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ,
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hlam hDim p) ≤ ν ∧
      ∃ w : parityConfigS Λ N p → ℂ, w ≠ 0 ∧
        Matrix.mulVec
          ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
            (fun σ : parityConfigS Λ N p => σ.1)
            (fun σ : parityConfigS Λ N p => σ.1)) w = (ν : ℂ) • w := by
  obtain ⟨ν, hν_min_le, hν_witness⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergS_submatrix_min_le_pf_eigenvalue
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨ν, ?_, hν_witness⟩
  -- Bridge: bare min = dressed min via (j.8); then bare min ≤ ν follows.
  rw [bare_dressed_submatrix_hermitianMinEigenvalue_eq A hJim hlam hDim p]
  exact hν_min_le

end LatticeSystem.Quantum
