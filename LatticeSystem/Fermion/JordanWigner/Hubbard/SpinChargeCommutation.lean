import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Commutation of the total lowering operator with the particle number

Model-agnostic spin/charge lemmas for the spinful Hubbard chain: the total
lowering operator `Ŝ^-_tot` conserves the total particle number, and consequently
the spin-lowering tower `(Ŝ^-_tot)^k v` keeps the `N̂`-eigenvalue of `v`.  These
are used by both Nagaoka's theorem (§11.2) and the flat-band ferromagnetism
capstone (§11.3.1), and apply to any model on the spinful chain, so they live in
their own small file rather than being duplicated.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- `Ŝ^-_tot` conserves the total particle number (it is `Σ_i c†_{i↓} c_{i↑}`,
a sum of number-conserving hops). -/
theorem fermionTotalSpinMinus_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinMinus N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinMinus
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  unfold fermionDownCreation fermionUpAnnihilation
  exact (fermionTotalNumber_commute_hopping (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N i 0)).symm

/-- **The lowering tower preserves the total-number eigenvalue** (general
eigenvalue `lam`): since `Ŝ^-_tot` commutes with `N̂`, `(Ŝ^-_tot)^k v` keeps the
`N̂`-eigenvalue of `v`. -/
theorem fermionTotalNumber_mulVec_spinMinusPow_eigenvalue (N : ℕ) (k : ℕ) (lam : ℂ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = lam • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      lam • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  have hcomm : Commute (fermionTotalNumber (2 * N + 1))
      ((fermionTotalSpinMinus N) ^ k) :=
    ((fermionTotalSpinMinus_commute_fermionTotalNumber N).symm).pow_right k
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

end LatticeSystem.Fermion
