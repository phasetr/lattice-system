import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry
import LatticeSystem.Math.AnticommuteCommute

/-!
# Per-site fermionic spin operators and the two-site spin dot `Ŝ_x · Ŝ_y`

Towards Tasaki §11.5 (the ferromagnetic t-J model, eq. (11.5.4)), whose Heisenberg coupling
`Σ_{⟨x,y⟩} (n̂_x n̂_y / 4 − Ŝ_x · Ŝ_y)` needs the *per-site* spin operators of the Hubbard /
Jordan–Wigner fermions:
`Ŝ^+_x = ĉ†_{x↑} ĉ_{x↓}`, `Ŝ^-_x = ĉ†_{x↓} ĉ_{x↑}`,
`Ŝ^z_x = (n̂_{x↑} − n̂_{x↓}) / 2`,
`Ŝ_x · Ŝ_y = ½(Ŝ^+_x Ŝ^-_y + Ŝ^-_x Ŝ^+_y) + Ŝ^z_x Ŝ^z_y`.
These are the per-site summands of the total spin operators (`fermionTotalSpinPlus`, …).

The different-site commutation `Ŝ^-_x Ŝ^+_y = Ŝ^+_y Ŝ^-_x` (`x ≠ y`) belongs to this layer too:
it is a property of the per-site ladders alone, the `(-1)^4 = 1` cancellation of four cross-site
anticommutations, obtained from the model-agnostic ring helpers of
`LatticeSystem.Math.AnticommuteCommute`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §9.3.3 (spin operators) and §11.5.2, eq. (11.5.4).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Per-site spin raising operator** `Ŝ^+_x = ĉ†_{x↑} ĉ_{x↓}`. -/
noncomputable def fermionSiteSpinPlus (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionUpCreation N i * fermionDownAnnihilation N i

/-- **Per-site spin lowering operator** `Ŝ^-_x = ĉ†_{x↓} ĉ_{x↑}`. -/
noncomputable def fermionSiteSpinMinus (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionDownCreation N i * fermionUpAnnihilation N i

/-- **Per-site spin-z operator** `Ŝ^z_x = (n̂_{x↑} − n̂_{x↓}) / 2`. -/
noncomputable def fermionSiteSpinZ (N : ℕ) (i : Fin (N + 1)) : ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) • (fermionUpCreation N i * fermionUpAnnihilation N i -
    fermionDownCreation N i * fermionDownAnnihilation N i)

/-- **The two-site spin dot product** `Ŝ_x · Ŝ_y = ½(Ŝ^+_x Ŝ^-_y + Ŝ^-_x Ŝ^+_y) + Ŝ^z_x Ŝ^z_y`. -/
noncomputable def fermionSpinDot (N : ℕ) (i j : Fin (N + 1)) : ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) • (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j +
      fermionSiteSpinMinus N i * fermionSiteSpinPlus N j) +
    fermionSiteSpinZ N i * fermionSiteSpinZ N j

/-- **Different-site spin ladders commute.**  For `x ≠ y` the bilinear (even) operators
`Ŝ⁻_x = ĉ†_{x↓}ĉ_{x↑}` and `Ŝ⁺_y = ĉ†_{y↑}ĉ_{y↓}` act on disjoint mode sets, so they commute:
`Ŝ⁻_x Ŝ⁺_y = Ŝ⁺_y Ŝ⁻_x` (four cross-site anticommutations combine to `(-1)^4 = +1`). -/
theorem fermionSiteSpinMinus_mul_Plus_comm (N : ℕ) (x y : Fin (N + 1)) (hxy : x ≠ y) :
    fermionSiteSpinMinus N x * fermionSiteSpinPlus N y
      = fermionSiteSpinPlus N y * fermionSiteSpinMinus N x := by
  unfold fermionSiteSpinMinus fermionSiteSpinPlus
  exact anticomm_commute_mul_mul
    (fermionDownCreation_upCreation_anticomm N x y)
    (fermionDownCreation_downAnnihilation_anticomm_ne N hxy)
    (fermionUpAnnihilation_upCreation_anticomm_ne N hxy)
    (fermionUpAnnihilation_downAnnihilation_anticomm N x y)

/-- The total spin raising operator is the sum of the per-site ones (consistency with
`fermionTotalSpinPlus`). -/
theorem fermionTotalSpinPlus_eq_sum_siteSpinPlus (N : ℕ) :
    fermionTotalSpinPlus N = ∑ i : Fin (N + 1), fermionSiteSpinPlus N i := rfl

/-- The total spin lowering operator is the sum of the per-site ones. -/
theorem fermionTotalSpinMinus_eq_sum_siteSpinMinus (N : ℕ) :
    fermionTotalSpinMinus N = ∑ i : Fin (N + 1), fermionSiteSpinMinus N i := rfl

end LatticeSystem.Fermion
