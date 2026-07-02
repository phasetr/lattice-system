import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheoremCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinTotHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinChargeCommutation
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingSpinCompress
import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMultiplet

/-!
# The total-spin Casimir commutes with the `U(1)` charges (Tasaki §9.3.3, §10.2)

The total-spin Casimir `(Ŝ_tot)² = Ŝ⁻_tot Ŝ⁺_tot + Ŝ³_tot(Ŝ³_tot + 1)` commutes with the raising
operator `Ŝ⁺_tot`, with the total particle number `N̂`, with `Ŝ³_tot`, and hence with the per-spin
number operators `N̂_↑`, `N̂_↓`.  These are the SU(2)/U(1) compatibility facts that let `(Ŝ_tot)²`
preserve a balanced ground eigenspace defined by `N̂_↑ = N̂_↓ = k`.

The lowering companion `[(Ŝ_tot)², Ŝ⁻_tot] = 0` is proved upstream
(`fermionTotalSpinSquared_commute_fermionTotalSpinMinus`, `WeakNagaokaTheoremCore`).

| Lean name | Statement |
|---|---|
| `fermionTotalSpinSquared_commute_fermionTotalSpinPlus` | `[(Ŝ_tot)², Ŝ⁺_tot] = 0` |
| `fermionTotalSpinSquared_commute_fermionTotalNumber` | `[(Ŝ_tot)², N̂] = 0` |
| `fermionTotalSpinSquared_commute_fermionTotalSpinZ` | `[(Ŝ_tot)², Ŝ³_tot] = 0` |
| `fermionTotalSpinSquared_commute_fermionTotalUpNumber` | `[(Ŝ_tot)², N̂_↑] = 0` |
| `fermionTotalSpinSquared_commute_fermionTotalDownNumber` | `[(Ŝ_tot)², N̂_↓] = 0` |

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §9.3.3, p. 332; §10.2.1, pp. 348–349; §11.1.1, p. 372.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

/-- **`[(Ŝ_tot)², Ŝ⁺_tot] = 0`**: the total-spin Casimir commutes with the raising operator.
Adjoint of the lowering commute `fermionTotalSpinSquared_commute_fermionTotalSpinMinus`, using that
`(Ŝ_tot)²` is Hermitian and `(Ŝ⁻_tot)ᴴ = Ŝ⁺_tot`.  Reference: Tasaki §9.3.3, p. 332. -/
theorem fermionTotalSpinSquared_commute_fermionTotalSpinPlus (N : ℕ) :
    Commute (fermionTotalSpinSquared N) (fermionTotalSpinPlus N) := by
  have h := (fermionTotalSpinSquared_commute_fermionTotalSpinMinus N).eq
  have h2 := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    (fermionTotalSpinSquared_isHermitian N).eq,
    fermionTotalSpinMinus_conjTranspose N] at h2
  exact h2.symm

/-- **`[(Ŝ_tot)², N̂] = 0`**: the total-spin Casimir commutes with the total particle number.
Assembled from `[Ŝ⁻_tot, N̂] = [Ŝ⁺_tot, N̂] = [Ŝ³_tot, N̂] = 0` term by term, exactly as for the
Hamiltonian.  Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinSquared_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinSquared N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinSquared
  apply Commute.add_left
  · exact (fermionTotalSpinMinus_commute_fermionTotalNumber N).mul_left
      (fermionTotalSpinPlus_commute_fermionTotalNumber N)
  · have h_z := fermionTotalSpinZ_commute_fermionTotalNumber N
    exact h_z.mul_left (h_z.add_left (Commute.one_left _))

/-- **`[(Ŝ_tot)², Ŝ³_tot] = 0`**: the total-spin Casimir commutes with the `z`-component.  From
`[(Ŝ_tot)², Ŝ⁺_tot] = [(Ŝ_tot)², Ŝ⁻_tot] = 0` the Casimir commutes with both `Ŝ⁺Ŝ⁻` and `Ŝ⁻Ŝ⁺`,
hence with their difference `Ŝ⁺Ŝ⁻ − Ŝ⁻Ŝ⁺ = 2 Ŝ³_tot`; dividing by the unit `2` gives the claim.
Reference: Tasaki §9.3.3, p. 332. -/
theorem fermionTotalSpinSquared_commute_fermionTotalSpinZ (N : ℕ) :
    Commute (fermionTotalSpinSquared N) (fermionTotalSpinZ N) := by
  have hplus := fermionTotalSpinSquared_commute_fermionTotalSpinPlus N
  have hminus := fermionTotalSpinSquared_commute_fermionTotalSpinMinus N
  have hcomm : Commute (fermionTotalSpinSquared N) ((2 : ℂ) • fermionTotalSpinZ N) := by
    rw [← fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N]
    exact (hplus.mul_right hminus).sub_right (hminus.mul_right hplus)
  exact (Commute.smul_right_iff₀ (by norm_num : (2 : ℂ) ≠ 0)).mp hcomm

/-- **`[(Ŝ_tot)², N̂_↑] = 0`**: the total-spin Casimir commutes with the spin-up number.  Using
`N̂_↑ = ½ N̂ + Ŝ³_tot` (from `N̂ = N̂_↑ + N̂_↓` and `Ŝ³_tot = ½(N̂_↑ − N̂_↓)`), this reduces to
`[(Ŝ_tot)², N̂] = 0` and `[(Ŝ_tot)², Ŝ³_tot] = 0`.  Reference: Tasaki §10.2.1, pp. 348–349. -/
theorem fermionTotalSpinSquared_commute_fermionTotalUpNumber (N : ℕ) :
    Commute (fermionTotalSpinSquared N) (fermionTotalUpNumber N) := by
  have hid : fermionTotalUpNumber N =
      (1 / 2 : ℂ) • fermionTotalNumber (2 * N + 1) + fermionTotalSpinZ N := by
    rw [fermionTotalNumber_eq_up_add_down, fermionTotalSpinZ]
    module
  rw [hid]
  exact ((fermionTotalSpinSquared_commute_fermionTotalNumber N).smul_right _).add_right
    (fermionTotalSpinSquared_commute_fermionTotalSpinZ N)

/-- **`[(Ŝ_tot)², N̂_↓] = 0`**: the total-spin Casimir commutes with the spin-down number.  Using
`N̂_↓ = ½ N̂ − Ŝ³_tot`, this reduces to `[(Ŝ_tot)², N̂] = 0` and `[(Ŝ_tot)², Ŝ³_tot] = 0`.
Reference: Tasaki §10.2.1, pp. 348–349. -/
theorem fermionTotalSpinSquared_commute_fermionTotalDownNumber (N : ℕ) :
    Commute (fermionTotalSpinSquared N) (fermionTotalDownNumber N) := by
  have hid : fermionTotalDownNumber N =
      (1 / 2 : ℂ) • fermionTotalNumber (2 * N + 1) - fermionTotalSpinZ N := by
    rw [fermionTotalNumber_eq_up_add_down, fermionTotalSpinZ]
    module
  rw [hid]
  exact ((fermionTotalSpinSquared_commute_fermionTotalNumber N).smul_right _).sub_right
    (fermionTotalSpinSquared_commute_fermionTotalSpinZ N)

end LatticeSystem.Fermion
