import LatticeSystem.Quantum.SpinS.Problem25cSingleSiteSquared
import LatticeSystem.Quantum.SpinS.RayleighUnitarySimilarity

/-!
# Tasaki Problem 2.5.c: unitary symmetry input for equal axes

This module packages the next symmetry input for Tasaki Problem 2.5.c after the
algebraic equal-axis bridge in `Problem25cSingleSiteSquared.lean`.  If a
many-body unitary conjugates one single-site spin component to another and the
state is invariant under the inverse unitary, then the corresponding squared
single-site expectations are equal.

The axis-2/axis-3 specialization is phrased using the conjugation identity as
an explicit hypothesis.  The existing `AxisSwapUnitaryS.tensor_conj_onSiteS`
API supplies this hypothesis for the lifted tensor axis-swap; the remaining
state-invariance input is intentionally left explicit.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the SU(2)-symmetry context around
Theorem 2.4, pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Generic unitary-invariance bridge -/

/-- Moving a many-body unitary from the ket side to the bra side inside the
matrix inner product. -/
theorem dotProduct_star_mulVec_eq_dotProduct_star_conjTranspose_mulVec
    (T : ManyBodyOpS V N) (Φ Ψ : (V → Fin (N + 1)) → ℂ) :
    dotProduct (star Φ) (T.mulVec Ψ) =
      dotProduct (star (T.conjTranspose.mulVec Φ)) Ψ := by
  rw [Matrix.dotProduct_mulVec, star_vecMul]

/-- If `T` conjugates the single-site operator `A` to `B` and `Φ` is fixed by
`T⁻¹ = T†`, then the squared single-site expectations of `A` and `B` in `Φ`
are equal. -/
theorem singleSiteSpinSquareExpectationS_eq_of_conj_invariant
    (x : V) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (T Tinv : ManyBodyOpS V N) (Φ : (V → Fin (N + 1)) → ℂ)
    (hTadj : T.conjTranspose = Tinv)
    (hTinvT : Tinv * T = 1)
    (hΦ : Tinv.mulVec Φ = Φ)
    (hconj : T * onSiteS x A * Tinv = onSiteS x B) :
    singleSiteSpinSquareExpectationS x B Φ =
      singleSiteSpinSquareExpectationS x A Φ := by
  let OA : ManyBodyOpS V N := onSiteS x A
  let OB : ManyBodyOpS V N := onSiteS x B
  have hOB : OB = T * OA * Tinv := by
    simpa [OA, OB] using hconj.symm
  have hsq : OB * OB = T * (OA * OA) * Tinv := by
    calc
      OB * OB = (T * OA * Tinv) * (T * OA * Tinv) := by rw [hOB]
      _ = T * (OA * OA) * Tinv := by
        rw [show (T * OA * Tinv) * (T * OA * Tinv) =
            T * OA * (Tinv * T) * OA * Tinv by simp only [mul_assoc]]
        rw [hTinvT]
        simp only [mul_one, mul_assoc]
  unfold singleSiteSpinSquareExpectationS
  calc
    dotProduct (star Φ) ((OB * OB).mulVec Φ) =
        dotProduct (star Φ) ((T * (OA * OA) * Tinv).mulVec Φ) := by rw [hsq]
    _ = dotProduct (star Φ) (T.mulVec ((OA * OA).mulVec Φ)) := by
      rw [show (T * (OA * OA) * Tinv).mulVec Φ =
          T.mulVec ((OA * OA).mulVec (Tinv.mulVec Φ)) from by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
      rw [hΦ]
    _ = dotProduct (star (T.conjTranspose.mulVec Φ)) ((OA * OA).mulVec Φ) := by
      rw [dotProduct_star_mulVec_eq_dotProduct_star_conjTranspose_mulVec]
    _ = dotProduct (star Φ) ((OA * OA).mulVec Φ) := by
      rw [hTadj, hΦ]

end LatticeSystem.Quantum
