import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorMatrix

/-!
# Tasaki 11.5: the sector expansion `Φ = Σ_s v_s |Φ_s⟩` and its left inverse (Prop 11.24 PR-E1)

Toward lifting the Perron–Frobenius sector eigenvector to a Hamiltonian eigenstate, this file sets
up the bridge between sector coefficient vectors and full Hilbert-space vectors:

* `tJExpansion v = Σ_s v_s • |Φ_s⟩` — the full-space vector with sector coefficients `v`;
* `tJExpansionCoeff u s = ⟨Φ_s, u⟩` — the coefficient functional;
* `tJExpansionCoeff_tJExpansion` — the left inverse `tJExpansionCoeff (tJExpansion v) = v` (the
  sector basis `|Φ_s⟩` is orthonormal), so the expansion is injective.

This mirrors the Nagaoka `tasakiCoeff` / `tasakiCoeff_expansion` bridge; the operator lift
`Ĥ_tJ (tJExpansion v) = (μ) • tJExpansion v` (the sector closure of `Ĥ_tJ`) is the next PR.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The sector expansion** `Φ = Σ_s v_s |Φ_s⟩` — the full computational-basis vector built from
the sector coefficient vector `v`. -/
noncomputable def tJExpansion (N Ne : ℕ) (v : TJSpinHalfFillingSector N Ne → ℂ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  ∑ s, v s • basisVec (tJConfigOf N s.val)

/-- **The coefficient functional** `⟨Φ_s, u⟩ = Σ_w |Φ_s⟩(w) · u(w)`. -/
noncomputable def tJExpansionCoeff (N Ne : ℕ) (u : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    TJSpinHalfFillingSector N Ne → ℂ :=
  fun s => ∑ w, basisVec (tJConfigOf N s.val) w * u w

/-- **Left inverse: the coefficient functional inverts the sector expansion.**
`tJExpansionCoeff (Σ_s v_s |Φ_s⟩) = v`, since the sector basis is orthonormal.  Hence the
expansion is injective. -/
theorem tJExpansionCoeff_tJExpansion (Ne : ℕ) (v : TJSpinHalfFillingSector N Ne → ℂ) :
    tJExpansionCoeff N Ne (tJExpansion N Ne v) = v := by
  funext s
  unfold tJExpansionCoeff tJExpansion
  have hstep : ∀ w, basisVec (tJConfigOf N s.val) w *
        (∑ s', v s' • basisVec (tJConfigOf N s'.val)) w
      = ∑ s', v s' * (basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w) := by
    intro w
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s' _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)
  rw [Finset.sum_congr rfl (fun w _ => hstep w), Finset.sum_comm]
  rw [show (∑ s', ∑ w, v s' * (basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w))
      = ∑ s', v s' * (∑ w, basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w) from
    Finset.sum_congr rfl (fun s' _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_congr rfl (fun s' _ => by rw [tJConfigOf_basisVec_inner])]
  simp only [← Subtype.ext_iff, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ s (fun s' => v s'), if_pos (Finset.mem_univ s)]

end LatticeSystem.Fermion
