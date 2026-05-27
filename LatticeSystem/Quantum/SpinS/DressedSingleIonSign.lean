import LatticeSystem.Quantum.SpinS.SingleIonOffDiag
import LatticeSystem.Quantum.SpinS.MarshallSign

/-!
# Marshall-dressed single-ion off-diagonal sign (case (i))

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For `D ≥ 0` (case (i)) the Marshall-dressed off-diagonal entries of the single-ion term
`D Σ_x (Ŝ²_x)²` have **non-positive real part**.  Each site contributes
`marshallSignS A σ · marshallSignS A σ' · (Ŝ²)²_{σ'_x σ_x}`; the `(Ŝ²)²` entry vanishes unless the
shift is `±2` (even), where the same-site Marshall sign is `+1`, leaving the already
non-positive `(Ŝ²)²` off-diagonal entry.  Multiplying by `D ≥ 0` and summing over the (single)
differing site preserves the sign.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Per-site dressed single-ion sign: the Marshall-dressed `onSiteS x (Ŝ²)²` off-diagonal entry
has non-positive real part. -/
theorem dressed_onSiteS_spinSOp2_sq_re_nonpos
    (A : Λ → Bool) (x : Λ) {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (marshallSignS A σ * marshallSignS A σ' *
      (onSiteS x (spinSOp2 N * spinSOp2 N)) σ' σ).re ≤ 0 := by
  rw [onSiteS_apply]
  by_cases hagree : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos hagree]
    have hsx : σ' x ≠ σ x := by
      intro hx
      exact hne (funext fun k => by
        by_cases hkx : k = x
        · rw [hkx]; exact hx
        · exact hagree k hkx)
    by_cases hpar : Odd ((σ' x).val + (σ x).val)
    · rw [spinSOp2_mul_spinSOp2_apply_eq_zero_of_odd N hpar, mul_zero, Complex.zero_re]
    · have heven : marshallSignS A σ' * marshallSignS A σ = 1 := by
        rw [Nat.not_odd_iff_even] at hpar
        rw [marshallSignS_mul_of_agree_off_site A x hagree]
        split_ifs with hAx
        · rw [Even.neg_one_pow hpar]
        · rfl
      rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'), heven, one_mul]
      exact spinSOp2_mul_spinSOp2_apply_offdiag_re_nonpos N hsx
  · rw [if_neg hagree, mul_zero, Complex.zero_re]

/-- **Dressed single-ion off-diagonal non-positivity** (case (i), `D ≥ 0`). -/
theorem dressed_singleIonAnisotropyS2_re_nonpos
    (A : Λ → Bool) {D : ℂ} (hDim : D.im = 0) (hDnn : 0 ≤ D.re)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ) :
    (marshallSignS A σ * marshallSignS A σ' * (singleIonAnisotropyS2 D N) σ' σ).re ≤ 0 := by
  rw [singleIonAnisotropyS2,
    show (∑ x : Λ, onSiteS x (spinSOp2 N) * onSiteS x (spinSOp2 N) : ManyBodyOpS Λ N) =
      ∑ x : Λ, onSiteS x (spinSOp2 N * spinSOp2 N) from
      Finset.sum_congr rfl (fun x _ => onSiteS_mul_onSiteS_same x _ _),
    Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    mul_left_comm, Finset.mul_sum, Complex.mul_re, hDim, zero_mul, sub_zero]
  apply mul_nonpos_of_nonneg_of_nonpos hDnn
  rw [Complex.re_sum]
  exact Finset.sum_nonpos (fun x _ => dressed_onSiteS_spinSOp2_sq_re_nonpos A x hne)

end LatticeSystem.Quantum
