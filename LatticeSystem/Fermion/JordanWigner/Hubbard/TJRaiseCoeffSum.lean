import LatticeSystem.Fermion.JordanWigner.Hubbard.TJTotalRaiseAction

/-!
# Tasaki 11.5: coefficient sum of the raising action (Prop 11.24 E3b PR5b-2)

The linear functional `coeffSum ψ = Σ_c ψ_c` (sum of all configuration coefficients) tracks the
positivity of the iterated raising:

* `coeffSum_basisVec` — `coeffSum |c⟩ = 1`;
* `coeffSum_fermionTotalSpinPlus_tJConfigOf` — `coeffSum (Ŝ⁺_tot |Φ_s⟩) = #↓(s)`, since each of the
  `#↓(s)` raised basis states contributes `1` (sign-free, all coefficients `+1`).

Combined with the uniform sector down-count `#↓ = (Ne−1)/2`, this gives `coeffSum (Ŝ⁺ Φ₀) =
(Ne−1)/2 · coeffSum Φ₀`, and iterating shows `coeffSum ((Ŝ⁺)^((Ne−1)/2) Φ₀) = ((Ne−1)/2)! · Σ v_q >
0` (from `v > 0`), so the raised vector is nonzero.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The coefficient sum of a basis vector is `1`. -/
theorem coeffSum_basisVec (w : Fin (2 * N + 2) → Fin 2) :
    ∑ c, basisVec w c = 1 := by
  simp only [basisVec, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Coefficient sum of the raising action.**  `coeffSum (Ŝ⁺_tot |Φ_s⟩) = #↓(s)` — each of the
`#↓(s)` raised basis states contributes `1`. -/
theorem coeffSum_fermionTotalSpinPlus_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    ∑ c, (fermionTotalSpinPlus N).mulVec (basisVec (tJConfigOf N s)) c =
      ((Finset.univ.filter (fun x => s x = 2)).card : ℂ) := by
  rw [fermionTotalSpinPlus_mulVec_tJConfigOf]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x _ => coeffSum_basisVec (tJConfigOf N (Function.update s x 1))]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end LatticeSystem.Fermion
