import LatticeSystem.Quantum.SpinS.ManyBodyReversalS
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg

/-!
# Reflection invariance of the anisotropic Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The anisotropic XXZ + single-ion Hamiltonian is invariant under the `M ↔ −M` magnetization
reflection `Θ` (the many-body π-rotation about axis 1): `Θ Ĥ Θ = Ĥ`.  Indeed the single-site
reversal fixes `Ŝ¹` and `(Ŝ³)²` and flips `Ŝ² ↦ −Ŝ²`, `Ŝ³ ↦ −Ŝ³`, so every bilinear bond
term `Ŝ^α Ŝ^α` and the single-ion `(Ŝ³)²` term is preserved.  Together with
`Θ Ŝ³_tot Θ = −Ŝ³_tot` (#3744) this is the reflection symmetry of the Mattis–Nishimori
argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Conjugation by `Θ` distributes over a product (inserting `Θ² = 1`). -/
theorem manyBodyReversalS_conj_mul (A B : ManyBodyOpS Λ N) :
    manyBodyReversalS Λ N * (A * B) * manyBodyReversalS Λ N =
      (manyBodyReversalS Λ N * A * manyBodyReversalS Λ N) *
        (manyBodyReversalS Λ N * B * manyBodyReversalS Λ N) := by
  rw [show (manyBodyReversalS Λ N * A * manyBodyReversalS Λ N) *
        (manyBodyReversalS Λ N * B * manyBodyReversalS Λ N)
      = manyBodyReversalS Λ N * A * (manyBodyReversalS Λ N * manyBodyReversalS Λ N) *
          (B * manyBodyReversalS Λ N) by simp only [mul_assoc],
    manyBodyReversalS_mul_self]
  simp only [mul_one, mul_assoc]

/-- Conjugation of the two-site XXZ term by `Θ` fixes it. -/
theorem manyBodyReversalS_conj_spinSDotXXZ (x y : Λ) (lam : ℂ) :
    manyBodyReversalS Λ N * spinSDotXXZ x y lam N * manyBodyReversalS Λ N =
      spinSDotXXZ x y lam N := by
  rw [spinSDotXXZ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    manyBodyReversalS_conj_mul, manyBodyReversalS_conj_onSiteS,
    spinReversalS_conj_spinSOp1, spinReversalS_conj_spinSOp2, spinReversalS_conj_spinSOp3,
    onSiteS_neg, neg_mul_neg]

/-- Conjugation of the single-ion term by `Θ` fixes it. -/
theorem manyBodyReversalS_conj_singleIonAnisotropyS (D : ℂ) :
    manyBodyReversalS Λ N * singleIonAnisotropyS D N * manyBodyReversalS Λ N =
      singleIonAnisotropyS (Λ := Λ) D N := by
  rw [singleIonAnisotropyS, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [manyBodyReversalS_conj_mul, manyBodyReversalS_conj_onSiteS, spinReversalS_conj_spinSOp3,
    onSiteS_neg, neg_mul_neg]

/-- **Reflection invariance** of the anisotropic Hamiltonian: `Θ Ĥ Θ = Ĥ`. -/
theorem manyBodyReversalS_conj_anisotropicHeisenbergS (J : Λ → Λ → ℂ) (lam D : ℂ) :
    manyBodyReversalS Λ N * anisotropicHeisenbergS J lam D N * manyBodyReversalS Λ N =
      anisotropicHeisenbergS (Λ := Λ) J lam D N := by
  rw [anisotropicHeisenbergS, Matrix.mul_add, Matrix.add_mul,
    manyBodyReversalS_conj_singleIonAnisotropyS]
  congr 1
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, manyBodyReversalS_conj_spinSDotXXZ]

end LatticeSystem.Quantum
