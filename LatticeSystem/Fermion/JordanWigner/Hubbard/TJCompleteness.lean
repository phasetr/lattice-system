import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExpansion
import LatticeSystem.Math.FinCases

/-!
# Tasaki 11.5: completeness of the sector basis (Prop 11.24 PR-E1b-A)

A vector supported on the sector configurations (the image of `tJConfigOf` over the
`N̂ = Ne`, `Ŝ³ = ½` sector) is reconstructed by its sector expansion:
`v = tJExpansion (tJExpansionCoeff v)`.  This is the completeness counterpart of the left inverse
`tJExpansionCoeff_tJExpansion` (mirrors Nagaoka `tasaki_completeness`), and is the bridge that turns
the operator action `Ĥ_tJ |Φ_s⟩` (once shown sector-supported) into its sector-matrix column.  The
inverse map `tJSiteStateOf` (with `tJConfigOf ∘ tJSiteStateOf = id` on hard-core configs) gives the
surjectivity used to recognise a hard-core configuration as a sector basis index.

The sector basis `|Φ_s⟩ = basisVec (tJConfigOf s)` consists of plain (sign-free) computational basis
vectors, so the proof is the direct orthogonality argument — no Jordan–Wigner sign bookkeeping.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Completeness of the sector basis.**  If `v` vanishes off the sector configurations (the image
of `tJConfigOf` over the sector), then `v` equals its own sector expansion
`tJExpansion (tJExpansionCoeff v)`. -/
theorem tJ_completeness (Ne : ℕ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hsupp : ∀ w, (¬ ∃ s : TJSpinHalfFillingSector N Ne, tJConfigOf N s.val = w) → v w = 0) :
    v = tJExpansion N Ne (tJExpansionCoeff N Ne v) := by
  funext w
  unfold tJExpansion tJExpansionCoeff
  rw [Finset.sum_apply]
  by_cases hw : ∃ s : TJSpinHalfFillingSector N Ne, tJConfigOf N s.val = w
  · obtain ⟨s₀, rfl⟩ := hw
    rw [Finset.sum_eq_single s₀]
    · rw [Pi.smul_apply, smul_eq_mul, basisVec_apply, if_pos rfl, mul_one, basisVec_sum_mul]
    · intro s _ hss₀
      rw [Pi.smul_apply, smul_eq_mul, basisVec_apply,
        if_neg (fun h => hss₀ (Subtype.ext (tJConfigOf_injective N h.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  · rw [hsupp w hw]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    rw [Pi.smul_apply, smul_eq_mul, basisVec_apply, if_neg (fun h => hw ⟨s, h.symm⟩), mul_zero]

/-- **The inverse site-state of a spinful configuration**: read off site `i`'s state from its two
orbitals (`↑` if the up-orbital is occupied, else `↓` if the down-orbital is, else empty). -/
def tJSiteStateOf (N : ℕ) (w : Fin (2 * N + 2) → Fin 2) : Fin (N + 1) → Fin 3 :=
  fun i => if w (spinfulIndex N i 0) = 1 then 1 else if w (spinfulIndex N i 1) = 1 then 2 else 0

/-- **`tJConfigOf` is a left inverse on hard-core configurations.**  If no site has both orbitals
occupied, then `tJConfigOf (tJSiteStateOf w) = w`; in particular every hard-core configuration is a
sector basis index `tJConfigOf s`. -/
theorem tJConfigOf_tJSiteStateOf_of_hardcore (N : ℕ) (w : Fin (2 * N + 2) → Fin 2)
    (hhc : ∀ i : Fin (N + 1), ¬ (w (spinfulIndex N i 0) = 1 ∧ w (spinfulIndex N i 1) = 1)) :
    tJConfigOf N (tJSiteStateOf N w) = w := by
  funext k
  obtain ⟨i, r, rfl⟩ := exists_spinfulIndex N k
  have hhci := hhc i
  rcases fin2_eq_zero_or_one (w (spinfulIndex N i 0)) with h0 | h0 <;>
    rcases fin2_eq_zero_or_one (w (spinfulIndex N i 1)) with h1 | h1 <;>
    rcases fin2_eq_zero_or_one r with rfl | rfl <;>
    simp only [tJConfigOf_apply_up, tJConfigOf_apply_down, tJSiteStateOf, h0, h1] <;>
    simp_all

end LatticeSystem.Fermion
