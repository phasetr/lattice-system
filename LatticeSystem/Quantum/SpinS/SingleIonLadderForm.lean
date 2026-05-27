import LatticeSystem.Quantum.SpinS.SpinSTransverseLadder
import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg

/-!
# Ladder form of the single-ion anisotropy term

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The single-site square `(Ŝ²)²` rewrites in raising/lowering form as
`¼(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺) − ¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)`.  The off-diagonal part is the `−¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)` term, which
changes the local magnetization by `±2`; with the crystal-field coefficient `D` this contributes
the same-site `±2` parity coupling of `Ĥ'`.  For case (i) (`D ≥ 0`) its coefficient `−D/4 ≤ 0`,
and the same-site Marshall sign is `+1` (the shift `±2` is even), so the dressed single-ion
off-diagonal entry stays `≤ 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Ladder form of the single-site square** `(Ŝ²)²`:
`Ŝ²_x Ŝ²_x = ¼(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺) − ¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)`. -/
theorem spinSOp2_mul_spinSOp2_ladder_form (N : ℕ) :
    spinSOp2 N * spinSOp2 N =
      (1 / 4 : ℂ) • (spinSOpPlus N * spinSOpMinus N + spinSOpMinus N * spinSOpPlus N) -
        (1 / 4 : ℂ) • (spinSOpPlus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N) := by
  have hadd := spinSOp1_mul_spinSOp1_add_spinSOp2_mul_spinSOp2 N
  have hsub := spinSOp1_mul_spinSOp1_sub_spinSOp2_mul_spinSOp2 N
  linear_combination (norm := module) (1 / 2 : ℂ) • hadd - (1 / 2 : ℂ) • hsub

/-- **Ladder form of the single-ion anisotropy term**:
`D Σ_x (Ŝ²_x)² = D Σ_x [ ¼(Ŝ⁺_x Ŝ⁻_x + Ŝ⁻_x Ŝ⁺_x) − ¼(Ŝ⁺_x Ŝ⁺_x + Ŝ⁻_x Ŝ⁻_x) ]`.
The `−¼(Ŝ⁺_x Ŝ⁺_x + Ŝ⁻_x Ŝ⁻_x)` part is the same-site `±2` parity coupling. -/
theorem singleIonAnisotropyS2_ladder_form (D : ℂ) (N : ℕ) :
    singleIonAnisotropyS2 (Λ := Λ) D N =
      D • ∑ x : Λ, onSiteS x
        ((1 / 4 : ℂ) • (spinSOpPlus N * spinSOpMinus N + spinSOpMinus N * spinSOpPlus N) -
          (1 / 4 : ℂ) • (spinSOpPlus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N)) := by
  rw [singleIonAnisotropyS2]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [onSiteS_mul_onSiteS_same, spinSOp2_mul_spinSOp2_ladder_form]

end LatticeSystem.Quantum
