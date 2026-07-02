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

end LatticeSystem.Fermion
