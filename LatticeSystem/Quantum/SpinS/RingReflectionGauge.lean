/-
The right-half DLS/Marshall gauge and its site-dependent conjugation
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 24).

The DLS/Marshall gauge turning the ungauged ring antiferromagnet into reflection-positive form is
a `π`-rotation around axis 2 applied to the **right half** of the ring only.  Abstracting the
single-site
`π`-rotation as an interface `AxisTwoPiRotS` (following `AxisSwapUnitaryS`; the conjugation laws
`U Ŝ^1 U⁻¹ = −Ŝ^1`, `U Ŝ^2 U⁻¹ = Ŝ^2`, `U Ŝ^3 U⁻¹ = −Ŝ^3` are recorded as fields and instantiated at
spin-1/2), this file builds the **site-dependent** tensor conjugation
(`manyBodyTensorS_conj_onSiteS_dep`) and the right-half gauge `rightGauge`, whose conjugation
acts as `U·A·U⁻¹` on right sites and trivially on left sites.
-/
import LatticeSystem.Quantum.SpinS.ManyBodyTensorConj
import LatticeSystem.Quantum.SpinS.Operators

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Conjugation of a single-site operator by a site-dependent tensor unitary**: if
`W i · Winv i = 1` for every site `i`, then
`(⊗_i W i) (onSiteS z A) (⊗_i Winv i) = onSiteS z (W z · A · Winv z)`. -/
theorem manyBodyTensorS_conj_onSiteS_dep {W Winv : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hWW : ∀ i, W i * Winv i = 1) (z : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyTensorS W * onSiteS z A * manyBodyTensorS Winv = onSiteS z (W z * A * Winv z) := by
  rw [onSiteS_eq_manyBodyTensorS, manyBodyTensorS_mul, manyBodyTensorS_mul,
    onSiteS_eq_manyBodyTensorS]
  congr 1
  funext x
  by_cases h : x = z
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h, mul_one, hWW]

/-- **Single-site `π`-rotation around axis 2** (interface, following `AxisSwapUnitaryS`).  An
invertible `U` with `U Ŝ^1 U⁻¹ = −Ŝ^1`, `U Ŝ^2 U⁻¹ = Ŝ^2`, `U Ŝ^3 U⁻¹ = −Ŝ^3` — the DLS/Marshall
gauge rotation.  Non-vacuous at spin-1/2; records the conjugation laws abstractly otherwise. -/
structure AxisTwoPiRotS (N : ℕ) where
  /-- The rotation matrix. -/
  U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  /-- Its inverse. -/
  Uinv : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  /-- `U Uinv = 1`. -/
  U_mul_Uinv : U * Uinv = 1
  /-- `Uinv U = 1`. -/
  Uinv_mul_U : Uinv * U = 1
  /-- `U Ŝ^1 U⁻¹ = −Ŝ^1`. -/
  conj_spinSOp1 : U * spinSOp1 N * Uinv = -spinSOp1 N
  /-- `U Ŝ^2 U⁻¹ = Ŝ^2`. -/
  conj_spinSOp2 : U * spinSOp2 N * Uinv = spinSOp2 N
  /-- `U Ŝ^3 U⁻¹ = −Ŝ^3`. -/
  conj_spinSOp3 : U * spinSOp3 N * Uinv = -spinSOp3 N

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- The **right-half gauge unitary**: `U` on the right sites `{n,…,2n−1}`, identity on the left. -/
noncomputable def rightGauge : ManyBodyOpS (Fin (2 * n)) N :=
  manyBodyTensorS (fun i : Fin (2 * n) => if n ≤ (i : ℕ) then G.U else 1)

/-- The inverse right-half gauge unitary. -/
noncomputable def rightGaugeInv : ManyBodyOpS (Fin (2 * n)) N :=
  manyBodyTensorS (fun i : Fin (2 * n) => if n ≤ (i : ℕ) then G.Uinv else 1)

/-- The right-half gauge unitary is invertible. -/
theorem rightGaugeInv_mul_rightGauge : G.rightGaugeInv n * G.rightGauge n = 1 := by
  rw [rightGaugeInv, rightGauge, manyBodyTensorS_mul]
  rw [show (fun i : Fin (2 * n) => (if n ≤ (i : ℕ) then G.Uinv else 1)
      * (if n ≤ (i : ℕ) then G.U else 1)) = fun _ => 1 from ?_]
  · exact manyBodyTensorS_one
  · funext i; split <;> simp [G.Uinv_mul_U]

/-- **Conjugation of a single-site operator by the right-half gauge**: it acts as `U·A·U⁻¹` on right
sites and trivially on left sites. -/
theorem rightGauge_conj_onSiteS (z : Fin (2 * n)) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    G.rightGauge n * onSiteS z A * G.rightGaugeInv n
      = onSiteS z (if n ≤ (z : ℕ) then G.U * A * G.Uinv else A) := by
  rw [rightGauge, rightGaugeInv,
    manyBodyTensorS_conj_onSiteS_dep (fun i => by split <;> simp [G.U_mul_Uinv])]
  congr 1
  split <;> simp

end AxisTwoPiRotS

end LatticeSystem.Quantum
