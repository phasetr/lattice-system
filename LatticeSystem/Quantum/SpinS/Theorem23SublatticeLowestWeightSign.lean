import LatticeSystem.Quantum.SpinS.Theorem23SublatticeCasimirSzBound
import LatticeSystem.Quantum.SpinS.SublatticeLowestWeight

/-!
# A sublattice lowest weight has non-positive magnetization

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 1 (see `.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

A sublattice lowest-weight vector (`Ŝ_A^- v = 0`, `Ŝ_A^(3) v = q v`, `v ≠ 0`) has
`q.re ≤ 0`: the lowest-weight Casimir relation `(Ŝ_A)² = q(q−1)`
(`sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpMinus_eq_zero`) combined with the
magnitude bound `(Ŝ_A)² ≥ q(q+1)` (Route 5 brick 0) forces `q(q−1) ≥ q(q+1)`, i.e.
`q.re ≤ 0`.  This pins the unique admissible lowest-weight magnetization (`q = −b` on
the `(Ŝ_A)² = b(b+1)` eigenspace, excluding the spurious root `q = b+1`) at the
recurrence boundary of the coupled total-spin lower bound.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **A sublattice lowest weight has non-positive magnetization**: if `v ≠ 0`,
`Ŝ_A^(3) v = q v` and `Ŝ_A^- v = 0`, then `q.re ≤ 0`. -/
theorem sublatticeSpinSOpMinus_eq_zero_sublatticeSpinSOp3_re_nonpos (A : V → Bool)
    {q : ℂ} {v : (V → Fin (N + 1)) → ℂ} (hv_ne : v ≠ 0)
    (hz : (sublatticeSpinSOp3 N A).mulVec v = q • v)
    (hker : (sublatticeSpinSOpMinus N A).mulVec v = 0) :
    q.re ≤ 0 := by
  -- Lowest-weight Casimir relation: (Ŝ_A)² v = q(q−1) v.
  have hcas : (sublatticeSpinSquaredS N A).mulVec v = (q * (q - 1)) • v :=
    sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpMinus_eq_zero A hz hker
  -- Magnitude bound at this Casimir value: q(q+1) ≤ q(q−1) (real parts).
  have hbound : (q * (q + 1)).re ≤ (q * (q - 1)).re :=
    sublatticeSpinSquaredS_re_ge_sublatticeSpinSOp3_mul_succ A hv_ne hcas hz
  -- Expand both real parts and conclude q.re ≤ 0.
  have he1 : (q * (q + 1)).re = q.re * q.re - q.im * q.im + q.re := by
    simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.one_im, Complex.add_im]
    ring
  have he2 : (q * (q - 1)).re = q.re * q.re - q.im * q.im - q.re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.one_im, Complex.sub_im]
    ring
  rw [he1, he2] at hbound
  linarith

end LatticeSystem.Quantum
