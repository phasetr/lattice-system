import Mathlib.Analysis.Matrix.Order

/-!
# Tasaki Appendix A.2.3: positive-semidefinite operator basics (Lemmas A.4, A.5, A.6)

Elementary facts about nonnegative (positive-semidefinite) self-adjoint operators from
Tasaki's Mathematical Appendix, here for finite complex matrices `Matrix n n ℂ` (the operator
algebra of a finite-volume quantum system).  Unlike the Lie product formula (Theorem A.1),
these are available in mathlib, so they are **proved** (not axiomatized):

* **Lemma A.4**: a Hermitian operator is positive-semidefinite iff all its eigenvalues are
  nonnegative.
* **Lemma A.5**: the sum of two positive-semidefinite operators is positive-semidefinite.
* **Lemma A.6**: `B̂†B̂ ≥ 0` for any `B̂`, and conversely every `Â ≥ 0` is the square `Ĉ²` of a
  positive-semidefinite operator `Ĉ = √Â` (its square root, here `cfc Real.sqrt`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Lemmas A.4–A.6, pp. 467–468.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder MatrixOrder

/-- **Tasaki Lemma A.4.**  A Hermitian matrix `A` is positive-semidefinite iff every
eigenvalue is nonnegative. -/
theorem posSemidef_iff_eigenvalues_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ i, 0 ≤ hA.eigenvalues i :=
  hA.posSemidef_iff_eigenvalues_nonneg

/-- **Tasaki Lemma A.5.**  The sum of two positive-semidefinite matrices is
positive-semidefinite (`⟨Φ|(Â+B̂)|Φ⟩ = ⟨Φ|Â|Φ⟩ + ⟨Φ|B̂|Φ⟩ ≥ 0`). -/
theorem PosSemidef.add {n : Type*} {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  hA.add hB

/-- **Tasaki Lemma A.6 (first part).**  For an arbitrary matrix `B`, the operator `Bᴴ B` is
positive-semidefinite (`⟨Φ|BᴴB|Φ⟩ = ‖B Φ‖² ≥ 0`). -/
theorem posSemidef_conjTranspose_mul_self {n : Type*} [Fintype n] (B : Matrix n n ℂ) :
    (Bᴴ * B).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self B

/-- **Tasaki Lemma A.6 (second part).**  Every positive-semidefinite matrix `A` is the square
`A = C * C` of a positive-semidefinite matrix `C` — its square root `Ĉ = √Â` (`cfc Real.sqrt`,
the Hermitian continuous functional calculus applied to the real square root). -/
theorem exists_posSemidef_sq_eq_of_posSemidef {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ C : Matrix n n ℂ, C.PosSemidef ∧ A = C * C := by
  classical
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hspec : ∀ x ∈ spectrum ℝ A, 0 ≤ x :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A hsa).mp hA.nonneg
  refine ⟨cfc Real.sqrt A, ?_, ?_⟩
  · rw [← nonneg_iff_posSemidef]
    exact cfc_nonneg fun x _ => Real.sqrt_nonneg x
  · calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A).symm
      _ = cfc (fun x => Real.sqrt x * Real.sqrt x) A := by
            refine cfc_congr fun x hx => ?_
            simp only [id_eq]
            exact (Real.mul_self_sqrt (hspec x hx)).symm
      _ = cfc Real.sqrt A * cfc Real.sqrt A := by
            rw [cfc_mul Real.sqrt Real.sqrt A (by fun_prop) (by fun_prop)]

end LatticeSystem.Math
