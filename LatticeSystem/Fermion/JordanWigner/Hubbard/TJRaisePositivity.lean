import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisePositivityStep
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaiseHardcore
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisingTower
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisingTermination

/-!
# Tasaki 11.5: the raised vector is nonzero (Prop 11.24 E3b PR5d)

The positivity finale: a hard-core `N̂ = Ne` vector `Φ₀` with `N̂_↓ Φ₀ = m Φ₀` and nonzero
coefficient sum satisfies `(Ŝ⁺_tot)^m Φ₀ ≠ 0`.  Each raising step multiplies the coefficient sum
by the current down-count eigenvalue `m − k`, nonzero for `k < m`; so the coefficient sum stays
nonzero up to `k = m`, hence the vector is nonzero.

Applied to the lifted Perron–Frobenius ground vector `Φ₀ = tJExpansion (ℂ ∘ v)` (`coeffSum = Σ v_q
> 0` from `v > 0`, `m = (Ne−1)/2`), this is the Marshall positivity input `(Ŝ⁺)^((Ne−1)/2) Φ₀ ≠ 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Coefficient sum of a `Ŝ³ = ½` sector expansion.**  `coeffSum (tJExpansion v) = Σ_s v_s`. -/
theorem coeffSum_tJExpansion (N Ne : ℕ) (v : TJSpinHalfFillingSector N Ne → ℂ) :
    ∑ c, tJExpansion N Ne v c = ∑ s, v s := by
  unfold tJExpansion
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, coeffSum_basisVec, mul_one]

/-- **The raised vector is nonzero.**  A hard-core `N̂ = Ne` vector `Φ₀` with `N̂_↓ Φ₀ = m Φ₀` and
nonzero coefficient sum has `(Ŝ⁺_tot)^m Φ₀ ≠ 0`. -/
theorem spinPlusPow_ne_zero_of_coeffSum_ne_zero (Ne m : ℕ)
    (Φ₀ : (Fin (2 * N + 2) → Fin 2) → ℂ) (hhc : Φ₀ ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec Φ₀ = (Ne : ℂ) • Φ₀)
    (hd : (fermionTotalDownNumber N).mulVec Φ₀ = (m : ℂ) • Φ₀)
    (hcs : ∑ c, Φ₀ c ≠ 0) :
    ((fermionTotalSpinPlus N) ^ m).mulVec Φ₀ ≠ 0 := by
  have key : ∀ k, k ≤ m → ∑ c, ((fermionTotalSpinPlus N) ^ k).mulVec Φ₀ c ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; rwa [pow_zero, Matrix.one_mulVec]
    | succ k ih =>
      intro hk
      have hkm : k < m := hk
      have hrec : ∑ c, ((fermionTotalSpinPlus N) ^ (k + 1)).mulVec Φ₀ c =
          ((m : ℂ) - k) * ∑ c, ((fermionTotalSpinPlus N) ^ k).mulVec Φ₀ c := by
        have heq : ((fermionTotalSpinPlus N) ^ (k + 1)).mulVec Φ₀ =
            (fermionTotalSpinPlus N).mulVec (((fermionTotalSpinPlus N) ^ k).mulVec Φ₀) := by
          rw [pow_succ', Matrix.mulVec_mulVec]
        rw [heq]
        exact coeffSum_fermionTotalSpinPlus_eq_of_downEigen Ne _
          (fermionTotalSpinPlus_pow_mulVec_mem_hardcore N k hhc)
          (fermionTotalNumber_mulVec_spinPlusPow N Φ₀ (Ne : ℂ) k hN) ((m : ℂ) - k)
          (fermionTotalDownNumber_mulVec_spinPlusPow N Φ₀ (m : ℂ) k hd)
      rw [hrec]
      refine mul_ne_zero ?_ (ih (le_of_lt hkm))
      rw [show ((m : ℂ) - (k : ℂ)) = (((m - k : ℕ)) : ℂ) from by rw [Nat.cast_sub (le_of_lt hkm)]]
      exact_mod_cast Nat.sub_ne_zero_of_lt hkm
  intro hzero
  exact key m (le_refl m) (by rw [hzero]; simp)

end LatticeSystem.Fermion
