import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergContinuity

/-!
# Matrix-level continuity of `Ĥ(λ, D)` (full Hamiltonian) for real `(λ, D)`

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

The full anisotropic Hamiltonian `Ĥ(λ, D) ∈ Matrix _ _ ℂ` is continuous as a
function of the real parameters `(λ, D) ∈ ℝ × ℝ` (via the real-to-complex
coercion). Specialises PR #3939's `continuous_anisotropicHeisenbergS`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The matrix-valued function `(λ, D) ↦ Ĥ(λ, D)` is continuous on `ℝ × ℝ`. -/
theorem continuous_anisotropicHeisenbergS_real (J : Λ → Λ → ℂ) (N : ℕ) :
    Continuous (fun p : ℝ × ℝ => anisotropicHeisenbergS (Λ := Λ) J ((p.1 : ℂ)) ((p.2 : ℂ)) N) := by
  refine continuous_matrix (fun σ τ => ?_)
  -- entry-wise continuity reduces to continuity of complex polynomials in (λ, D).
  unfold anisotropicHeisenbergS
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Continuous.add ?_ ?_
  · -- ∑ x y, J x y * spinSDotXXZ x y lam N σ τ — polynomial in lam
    refine continuous_finset_sum _ (fun x _ => continuous_finset_sum _ (fun y _ => ?_))
    refine Continuous.mul continuous_const ?_
    -- spinSDotXXZ x y lam N σ τ is polynomial in lam (= a + lam * b for constants a, b)
    unfold spinSDotXXZ
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine Continuous.add (Continuous.add continuous_const continuous_const) ?_
    refine Continuous.mul ?_ continuous_const
    exact Complex.continuous_ofReal.comp continuous_fst
  · -- singleIonAnisotropyS D N σ τ = D * (∑ x, ...) σ τ
    unfold singleIonAnisotropyS
    simp only [Matrix.smul_apply, smul_eq_mul]
    refine Continuous.mul ?_ continuous_const
    exact Complex.continuous_ofReal.comp continuous_snd

end LatticeSystem.Quantum
