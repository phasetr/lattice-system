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

/-- **Per-block PF bound at `hermitianMinEigenvalue` (conditional)**: given a specific
`ν : ℝ` that (i) satisfies the PF bound `finrank ≤ 1` and (ii) equals `hermitianMinEigenvalue`,
the bound transfers to `(hermitianMinEigenvalue : ℂ)`.

The hypothesis `hν_eq_min : ν = hermitianMinEigenvalue` is the substantive part — it
captures the missing Collatz-Wielandt identification. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_finrank_le_one_at_min_conditional
    (A : Λ → Bool) {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hDim : D.im = 0)
    (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (ν : ℝ)
    (hν_bound : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1)
    (hν_eq_min : ν = hermitianMinEigenvalue
      (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) A hJim hlam hDim p)) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1)))
      ((hermitianMinEigenvalue
        (dressedAxisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) A hJim hlam hDim p) : ℂ))) ≤ 1 := by
  rw [← hν_eq_min]
  exact hν_bound

end LatticeSystem.Quantum
