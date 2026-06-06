import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingEigenLift
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorSpin

/-!
# Tasaki 11.5: `Ŝ³` is diagonal on filling expansions; odd `Ne` has no `Ŝ³ = 0` state (Prop 11.24)

`Ŝ³_tot` acts diagonally on the filling basis: on `tJFillingExpansion Φ` it scales each coefficient by
`½(#↑ − #↓)` (`fermionTotalSpinZ_mulVec_tJFillingExpansion`).  For **odd** `Ne` every filling
site-state has `#↑ ≠ #↓` (since `#↑ + #↓ = Ne` is odd), so the scale is nonzero — hence the only
`Ŝ³ = 0` filling state is the zero vector (`tJFillingExpansion_eq_zero_of_spinZ_mulVec_eq_zero`).

This kills the `Ŝ³ = 0` branch of the W-restricted A.17 for odd `Ne`, forcing the `Ŝ³ = ½` sector —
the last ingredient of `groundEnergyAtFilling = μ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The filling coefficient functional vanishes on the zero vector. -/
theorem tJFillingExpansionCoeff_zero (Ne : ℕ) :
    tJFillingExpansionCoeff N Ne (0 : (Fin (2 * N + 2) → Fin 2) → ℂ) = 0 := by
  funext s
  unfold tJFillingExpansionCoeff
  simp

/-- **`Ŝ³_tot` is diagonal on filling expansions:** it scales the coefficient at `s` by
`½(#↑(s) − #↓(s))`. -/
theorem fermionTotalSpinZ_mulVec_tJFillingExpansion (Ne : ℕ) (Φ : TJFillingSector N Ne → ℂ) :
    (fermionTotalSpinZ N).mulVec (tJFillingExpansion N Ne Φ) =
      tJFillingExpansion N Ne (fun s =>
        Φ s * ((((Finset.univ.filter (fun k => s.val k = 1)).card : ℂ) -
          ((Finset.univ.filter (fun k => s.val k = 2)).card : ℂ)) / 2)) := by
  unfold tJFillingExpansion
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.mulVec_smul, fermionTotalSpinZ_mulVec_tJConfigOf, smul_smul]

/-- **No `Ŝ³ = 0` filling state for odd `Ne`.**  If `Ŝ³_tot (tJFillingExpansion Φ) = 0` and `Ne` is
odd, then `Φ = 0` (the diagonal scale `½(#↑ − #↓)` is nonzero on every filling site-state). -/
theorem tJFillingExpansion_eq_zero_of_spinZ_mulVec_eq_zero (Ne : ℕ) (hodd : Odd Ne)
    {Φ : TJFillingSector N Ne → ℂ}
    (h : (fermionTotalSpinZ N).mulVec (tJFillingExpansion N Ne Φ) = 0) :
    Φ = 0 := by
  rw [fermionTotalSpinZ_mulVec_tJFillingExpansion] at h
  have hcoeff := tJFillingExpansionCoeff_tJFillingExpansion Ne
    (fun s => Φ s * ((((Finset.univ.filter (fun k => s.val k = 1)).card : ℂ) -
      ((Finset.univ.filter (fun k => s.val k = 2)).card : ℂ)) / 2))
  rw [h, tJFillingExpansionCoeff_zero] at hcoeff
  funext s
  have hs := congrFun hcoeff s
  simp only [Pi.zero_apply] at hs
  -- hs : Φ s * (((#↑ - #↓)/2)) = 0
  have hcard : (Finset.univ.filter (fun k => s.val k = 1)).card ≠
      (Finset.univ.filter (fun k => s.val k = 2)).card := by
    intro hc
    obtain ⟨m, hm⟩ := hodd
    have hp := s.property
    omega
  have hne : (((Finset.univ.filter (fun k => s.val k = 1)).card : ℂ) -
      ((Finset.univ.filter (fun k => s.val k = 2)).card : ℂ)) / 2 ≠ 0 := by
    have h1 : ((Finset.univ.filter (fun k => s.val k = 1)).card : ℂ) ≠
        ((Finset.univ.filter (fun k => s.val k = 2)).card : ℂ) := by exact_mod_cast hcard
    exact div_ne_zero (sub_ne_zero.mpr h1) (by norm_num)
  exact (mul_eq_zero.mp hs.symm).resolve_right hne

end LatticeSystem.Fermion
