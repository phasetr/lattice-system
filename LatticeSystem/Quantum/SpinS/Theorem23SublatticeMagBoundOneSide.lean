import LatticeSystem.Quantum.SpinS.Theorem23SublatticeBottomComponent
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeLowestWeightSign

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# One-sided total-magnetization bound for a total lowest weight

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 3a (see `.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

For a total lowest weight `w` in the joint sublattice-Casimir eigenspace with
sublattice spins `a, b` (`(Ŝ_A)² = a(a+1)`, `(Ŝ_¬A)² = b(b+1)`), the total
magnetization `m` satisfies `m.re ≤ b − a`.  Combining this with the `A ↔ ¬A` mirror
(applied to `¬A`) gives `|m| ≥ |a − b|` — the Clebsch–Gordan triangle inequality.

Proof: the bottom-`A`-magnetization component `v` (brick 2b) is `Ŝ_A^-`-killed at
`A`-weight `p`, so `p ≤ 0` (brick 1) and `p(p−1) = a(a+1)` (lowest-weight Casimir),
forcing `p ≤ −a`; its `Ŝ_¬A^(3)`-weight is `m − p`, and the magnitude bound on `¬A`
(brick 0) gives `m − p ≤ b`, whence `m.re ≤ b + p.re ≤ b − a`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **One-sided total-magnetization bound**: a total lowest weight `w` in the joint
sublattice-Casimir eigenspace with spins `a, b` has `m.re ≤ b − a`. -/
theorem totalLowestWeight_re_le_complement_sub (A : Λ → Bool) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {m : ℂ} {w : (Λ → Fin (N + 1)) → ℂ} (hw_ne : w ≠ 0)
    (hztot : (totalSpinSOp3 Λ N).mulVec w = m • w)
    (hker : (totalSpinSOpMinus Λ N).mulVec w = 0)
    (hcasA : (sublatticeSpinSquaredS N A).mulVec w = ((a * (a + 1) : ℝ) : ℂ) • w)
    (hcasB : (sublatticeSpinSquaredS N (fun x => !A x)).mulVec w =
      ((b * (b + 1) : ℝ) : ℂ) • w) :
    m.re ≤ b - a := by
  obtain ⟨p, v, hv_ne, hp, hq, hkerA, hcA, hcB⟩ :=
    exists_sublattice_A_lowestWeight_component A hw_ne hztot hker hcasA hcasB
  -- p is real (Hermitian eigenvalue).
  have hp_im : p.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq (sublatticeSpinSOp3_isHermitian (N := N) A) hp hv_ne)
  -- p ≤ 0 (sublattice lowest weight, brick 1).
  have hp_nonpos : p.re ≤ 0 :=
    sublatticeSpinSOpMinus_eq_zero_sublatticeSpinSOp3_re_nonpos A hv_ne hp hkerA
  -- Lowest-weight Casimir: (Ŝ_A)² v = p(p−1) v, so p(p−1) = a(a+1).
  have hlwc : (sublatticeSpinSquaredS N A).mulVec v = (p * (p - 1)) • v :=
    sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpMinus_eq_zero A hp hkerA
  have hpa : p * (p - 1) = ((a * (a + 1) : ℝ) : ℂ) :=
    smul_left_injective ℂ hv_ne (hlwc.symm.trans hcA)
  have hpa_re : p.re * p.re - p.re = a * (a + 1) := by
    have := congrArg Complex.re hpa
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      hp_im, Complex.ofReal_re, mul_zero, sub_zero] at this
    linarith [this]
  -- Hence p.re ≤ −a.
  have hp_le : p.re ≤ -a := by nlinarith [hpa_re, hp_nonpos, ha]
  -- ¬A magnitude bound on v: with (m − p) the ¬A-weight, m.re − p.re ≤ b.
  have hsucc := sublatticeSpinSquaredS_re_ge_sublatticeSpinSOp3_mul_succ
    (fun x => ! A x) hv_ne hcB hq
  have hpred := sublatticeSpinSquaredS_re_ge_sublatticeSpinSOp3_mul_pred
    (fun x => ! A x) hv_ne hcB hq
  -- m is real (Hermitian eigenvalue).
  have hm_im : m.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq (totalSpinSOp3_isHermitian Λ N) hztot hw_ne)
  -- Expand the real parts of the ¬A magnitude bounds (`x := m.re − p.re`).
  have hsucc' : (m.re - p.re) * ((m.re - p.re) + 1) ≤ b * (b + 1) := by
    simpa only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, hm_im, hp_im, Complex.ofReal_re,
      zero_sub, sub_zero, mul_zero, neg_zero, add_zero] using hsucc
  have hpred' : (m.re - p.re) * ((m.re - p.re) - 1) ≤ b * (b + 1) := by
    simpa only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
      Complex.sub_im, Complex.one_im, hm_im, hp_im, Complex.ofReal_re,
      zero_sub, sub_zero, mul_zero, neg_zero, add_zero] using hpred
  -- m.re − p.re ≤ b, hence m.re ≤ b + p.re ≤ b − a.
  have hx_le : m.re - p.re ≤ b := by nlinarith [hsucc', hpred', hb]
  linarith [hx_le, hp_le]

end LatticeSystem.Quantum
