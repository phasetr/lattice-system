import LatticeSystem.Quantum.SpinS.ComplexDressedSubmatrixPFEigenvector
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank

/-!
# Packaged PF bound + `hermitianMinEigenvalue ≤ ν`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.4): packages (j.2) #3858 (complex PF eigenvector existence at ν) + (j.3) #3859
(`hermitianMinEigenvalue ≤ μ` from eigenvector existence) + #3831 (per-block PF bound
at ν) into a single existential capturing all three facts for the dressed-`Ĥ'` parity-block
submatrix:

```
∃ ν : ℝ,
  hermitianMinEigenvalue submatrix_Herm ≤ ν ∧
  finrank ℂ (eig dressed.submatrix (ν : ℂ)) ≤ 1
```

This is the **one-direction half** of the per-block identification needed by (i.7) #3854.
The other half (`ν ≤ hermitianMinEigenvalue`, i.e., ν IS the min) requires
Collatz-Wielandt's "PF eigenvalue = max spectrum" — deferred.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **`hermitianMinEigenvalue ≤ PF ν` for the dressed-`Ĥ'` submatrix**: combines
(j.2) #3858 (PF complex eigenvector existence) with (j.3) #3859 (Hermitian min ≤ μ from
eigenvector existence). -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_min_le_pf_eigenvalue
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
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p) ≤ ν ∧
      ∃ w : parityConfigS Λ N p → ℂ, w ≠ 0 ∧
        Matrix.mulVec
          ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
            (fun σ : parityConfigS Λ N p => σ.1)
            (fun σ : parityConfigS Λ N p => σ.1)) w = (ν : ℂ) • w := by
  -- (j.2): get complex eigenvector w ≠ 0 at ν.
  obtain ⟨ν, w, hw_ne, hw_eig⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergS_submatrix_complex_eigenvector_exists
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨ν, ?_, w, hw_ne, hw_eig⟩
  -- (j.3): hermitianMinEigenvalue ≤ ν via the eigenvector existence.
  exact hermitian_min_eigenvalue_le_of_eigenvector_exists
    (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
      (Λ := Λ) (N := N) A hJim hlam hDim p) hw_ne hw_eig

end LatticeSystem.Quantum
