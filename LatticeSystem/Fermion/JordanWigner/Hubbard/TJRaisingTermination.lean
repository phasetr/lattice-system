import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisingTower
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetry

/-!
# Tasaki 11.5: the spin-raising tower terminates (Prop 11.24 E3b PR3)

A vector `Φ` with spin-down number `N̂_↓ Φ = m Φ` is annihilated by `m + 1` raisings:
`(Ŝ⁺_tot)^(m+1) Φ = 0`.  Each `Ŝ⁺` step lowers the `N̂_↓` eigenvalue by one (`[N̂_↓, Ŝ⁺] = −Ŝ⁺`), so
`(Ŝ⁺)^(m+1) Φ` would be an `N̂_↓`-eigenvector at `−1`; but `N̂_↓` is diagonal with non-negative
integer entries, so such an eigenvector vanishes.

Applied to a `Ŝ³ = ½`, `N̂ = Ne` sector ground state (where `N̂_↓ = (Ne−1)/2`), this says the top of
the raising tower `Ω = (Ŝ⁺)^((Ne−1)/2) Φ` satisfies `Ŝ⁺ Ω = 0` — `Ω` is a highest weight.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- Per-site `[N̂_↓, Ŝ⁺_x] = −Ŝ⁺_x` (local copy of the `TJSpinSymmetry` private helper). -/
private theorem totalDownNumber_mul_siteSpinPlus (N : ℕ) (x : Fin (N + 1)) :
    fermionTotalDownNumber N * fermionSiteSpinPlus N x =
      fermionSiteSpinPlus N x * fermionTotalDownNumber N - fermionSiteSpinPlus N x := by
  unfold fermionSiteSpinPlus
  have hup := (fermionTotalDownNumber_commute_fermionUpCreation N x).eq
  have han : fermionTotalDownNumber N * fermionDownAnnihilation N x =
      fermionDownAnnihilation N x * fermionTotalDownNumber N - fermionDownAnnihilation N x := by
    have h := fermionTotalDownNumber_commutator_fermionDownAnnihilation N x
    linear_combination (norm := noncomm_ring) h
  calc fermionTotalDownNumber N * (fermionUpCreation N x * fermionDownAnnihilation N x)
      = (fermionTotalDownNumber N * fermionUpCreation N x) * fermionDownAnnihilation N x := by
        rw [← mul_assoc]
    _ = (fermionUpCreation N x * fermionTotalDownNumber N) * fermionDownAnnihilation N x := by
        rw [hup]
    _ = fermionUpCreation N x * (fermionTotalDownNumber N * fermionDownAnnihilation N x) := by
        rw [mul_assoc]
    _ = fermionUpCreation N x *
          (fermionDownAnnihilation N x * fermionTotalDownNumber N -
            fermionDownAnnihilation N x) := by
        rw [han]
    _ = fermionUpCreation N x * fermionDownAnnihilation N x * fermionTotalDownNumber N -
          fermionUpCreation N x * fermionDownAnnihilation N x := by noncomm_ring

/-- **Total `[N̂_↓, Ŝ⁺_tot] = −Ŝ⁺_tot`.**  Each raising removes one down-spin. -/
theorem fermionTotalDownNumber_mul_fermionTotalSpinPlus (N : ℕ) :
    fermionTotalDownNumber N * fermionTotalSpinPlus N =
      fermionTotalSpinPlus N * fermionTotalDownNumber N - fermionTotalSpinPlus N := by
  rw [fermionTotalSpinPlus_eq_sum_siteSpinPlus, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun x _ => totalDownNumber_mul_siteSpinPlus N x)

/-- **`N̂_↓` lowers by one along the raising tower.**  `N̂_↓ (Ŝ⁺)^k v = (m − k)(Ŝ⁺)^k v`. -/
theorem fermionTotalDownNumber_mulVec_spinPlusPow (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m : ℂ) (k : ℕ)
    (hd : (fermionTotalDownNumber N).mulVec v = m • v) :
    (fermionTotalDownNumber N).mulVec (((fermionTotalSpinPlus N) ^ k).mulVec v) =
      (m - k) • (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
  have hcomm := fermionTotalDownNumber_mul_fermionTotalSpinPlus N
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, sub_zero]
    exact hd
  | succ k ih =>
    have hexp : ((fermionTotalSpinPlus N) ^ (k + 1)).mulVec v =
        (fermionTotalSpinPlus N).mulVec
          (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hexp, Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, Nat.cast_succ]
    module

/-- **The raising tower terminates.**  A vector with `N̂_↓ v = m v` is annihilated by `m + 1`
raisings: `(Ŝ⁺)^(m+1) v = 0` (the would-be `N̂_↓`-eigenvalue `−1` is impossible). -/
theorem spinPlusPow_succ_eq_zero_of_downNumber (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m : ℕ)
    (hd : (fermionTotalDownNumber N).mulVec v = (m : ℂ) • v) :
    ((fermionTotalSpinPlus N) ^ (m + 1)).mulVec v = 0 := by
  set ψ := ((fermionTotalSpinPlus N) ^ (m + 1)).mulVec v with hψ
  have hdψ : (fermionTotalDownNumber N).mulVec ψ = (-1 : ℂ) • ψ := by
    have h := fermionTotalDownNumber_mulVec_spinPlusPow N v (m : ℂ) (m + 1) hd
    rw [hψ, h]
    congr 1
    push_cast
    ring
  funext w
  have key : (fermionTotalDownNumber N).mulVec ψ w = (-1 : ℂ) * ψ w := by
    rw [hdψ, Pi.smul_apply, smul_eq_mul]
  rw [fermionTotalDownNumber_mulVec_apply] at key
  have hsum : ((∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) + 1) * ψ w = 0 := by
    linear_combination key
  have hne : ((∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) + 1) ≠ 0 := by
    rw [← Nat.cast_sum]
    exact Nat.cast_add_one_ne_zero _
  simpa using (mul_eq_zero.mp hsum).resolve_left hne

end LatticeSystem.Fermion
