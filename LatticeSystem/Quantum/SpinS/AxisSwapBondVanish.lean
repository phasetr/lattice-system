import LatticeSystem.Quantum.SpinS.AxisSwapBondOffDiag

/-!
# Vanishing of the axis-swapped bond entry away from a single ladder step

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Every ladder term of the axis-swapped bond `spinSDotXXZSwap x y λ` raises or lowers each of the
sites `x, y` by exactly one unit.  Hence if the configurations `σ', σ` differ at `x` by anything
other than `±1` (i.e. `x` is neither raised nor lowered by a single step), the off-diagonal bond
entry vanishes.  This is the structural input that, in the Marshall-dressed sign analysis,
restricts the non-vanishing cases to a `±1` shift on the `A`-site — where the Marshall sign is
`−1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- If `x` is neither raised nor lowered by a single step, every ladder `x`-factor vanishes, so
the off-diagonal bond entry is zero (`σ' ≠ σ` kills the diagonal `Ŝ³Ŝ³` part). -/
theorem spinSDotXXZSwap_apply_eq_zero_of_x_not_pm1
    {x y : Λ} (hxy : x ≠ y) (lam : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hxr : (σ x).val + 1 ≠ (σ' x).val) (hxl : (σ' x).val + 1 ≠ (σ x).val) :
    spinSDotXXZSwap x y lam N σ' σ = 0 := by
  have hP : (spinSOpPlus N) (σ' x) (σ x) = 0 := spinSOpPlus_apply_other N hxl
  have hM : (spinSOpMinus N) (σ' x) (σ x) = 0 := spinSOpMinus_apply_other N hxr
  have hladder := congrFun (congrFun (spinSDotXXZSwap_ladder_form (Λ := Λ) x y lam) σ') σ
  rw [hladder, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul,
    onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_ne hxy hne, add_zero]
  rw [Matrix.add_apply, Matrix.add_apply,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy,
    onSiteS_mul_onSiteS_apply_eq hxy, onSiteS_mul_onSiteS_apply_eq hxy, hP, hM]
  simp

end LatticeSystem.Quantum
