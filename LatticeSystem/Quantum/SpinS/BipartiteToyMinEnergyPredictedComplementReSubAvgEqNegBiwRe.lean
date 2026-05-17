import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `(pm¬A).re − avg = −biw.re` unconditionally

Mirror of PR #3157. The complement predicted-min energy minus the
orientation-pair average equals the negative imbalance-weight real
part:

  `(predicted_min ¬A).re − ((predicted_min A).re + (predicted_min ¬A).re) / 2
    = −biw.re = −(|A| − |¬A|) · N / 2 = (|¬A| − |A|) · N / 2`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re − avg = −biw.re** unconditionally. Mirror of PR #3157. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_sub_avg_complement_re_eq_neg_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      -(bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteImbalanceWeight_re_eq]
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N,
      bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero]
  have hfilter : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases A x <;> simp
  rw [hfilter]
  ring

end LatticeSystem.Quantum
