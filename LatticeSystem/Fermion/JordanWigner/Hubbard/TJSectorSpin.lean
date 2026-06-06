import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis

/-!
# Tasaki 11.5: spin eigenvalues of the t-J sector basis (Prop 11.24 PR3a)

For a site-state `s : Fin (N+1) -> Fin 3`, `basisVec (tJConfigOf s)` is a simultaneous eigenvector
of the total up/down number and the total `S^z`: `N_up` eigenvalue `#{s i = up}`, `N_down`
eigenvalue `#{s i = down}`, `S^z_tot` eigenvalue `(1/2)(#up - #down)`.  A site state with one more
up than down thus lands in the `S^z_tot = 1/2` sector of Proposition 11.24, upgrading the basis
skeleton (`TJSectorBasis.lean`) toward a basis of the physical sector.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), 11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The number of ↑-occupied orbitals of `tJConfigOf s` equals `#{i | s i = ↑}`. -/
theorem tJConfigOf_up_count (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (∑ k : Fin (N + 1), (tJConfigOf N s (spinfulIndex N k 0)).val)
      = (Finset.univ.filter (fun k => s k = 1)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tJConfigOf_apply_up]
  split <;> rfl

/-- The number of ↓-occupied orbitals of `tJConfigOf s` equals `#{i | s i = ↓}`. -/
theorem tJConfigOf_down_count (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (∑ k : Fin (N + 1), (tJConfigOf N s (spinfulIndex N k 1)).val)
      = (Finset.univ.filter (fun k => s k = 2)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tJConfigOf_apply_down]
  split <;> rfl

/-- `N̂_↑` acts on `basisVec (tJConfigOf s)` with eigenvalue `#{i | s i = ↑}`. -/
theorem fermionTotalUpNumber_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (fermionTotalUpNumber N).mulVec (basisVec (tJConfigOf N s))
      = ((Finset.univ.filter (fun k => s k = 1)).card : ℂ) • basisVec (tJConfigOf N s) := by
  unfold fermionTotalUpNumber fermionUpNumber
  rw [Matrix.sum_mulVec, Finset.sum_congr rfl (fun k _ =>
    fermionMultiNumber_mulVec_basisVec (2 * N + 1) (spinfulIndex N k 0) _), ← Finset.sum_smul,
    ← Nat.cast_sum, tJConfigOf_up_count]

/-- `N̂_↓` acts on `basisVec (tJConfigOf s)` with eigenvalue `#{i | s i = ↓}`. -/
theorem fermionTotalDownNumber_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (fermionTotalDownNumber N).mulVec (basisVec (tJConfigOf N s))
      = ((Finset.univ.filter (fun k => s k = 2)).card : ℂ) • basisVec (tJConfigOf N s) := by
  unfold fermionTotalDownNumber fermionDownNumber
  rw [Matrix.sum_mulVec, Finset.sum_congr rfl (fun k _ =>
    fermionMultiNumber_mulVec_basisVec (2 * N + 1) (spinfulIndex N k 1) _), ← Finset.sum_smul,
    ← Nat.cast_sum, tJConfigOf_down_count]

/-- `Ŝ³_tot` acts on `basisVec (tJConfigOf s)` with eigenvalue `½(#↑ − #↓)`. -/
theorem fermionTotalSpinZ_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (fermionTotalSpinZ N).mulVec (basisVec (tJConfigOf N s))
      = ((((Finset.univ.filter (fun k => s k = 1)).card : ℂ) -
          ((Finset.univ.filter (fun k => s k = 2)).card : ℂ)) / 2)
        • basisVec (tJConfigOf N s) := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, fermionTotalUpNumber_mulVec_tJConfigOf,
    fermionTotalDownNumber_mulVec_tJConfigOf, ← sub_smul, smul_smul]
  congr 1
  ring

/-- **`Ŝ³_tot = ½` on the sector basis**: a site state with one more ↑ than ↓ lies in the
`Ŝ³_tot = ½` sector. -/
theorem fermionTotalSpinZ_mulVec_tJConfigOf_half (N : ℕ) (s : Fin (N + 1) → Fin 3)
    (h : (Finset.univ.filter (fun k => s k = 1)).card
      = (Finset.univ.filter (fun k => s k = 2)).card + 1) :
    (fermionTotalSpinZ N).mulVec (basisVec (tJConfigOf N s))
      = ((1 / 2 : ℝ) : ℂ) • basisVec (tJConfigOf N s) := by
  rw [fermionTotalSpinZ_mulVec_tJConfigOf]
  congr 1
  rw [h]
  push_cast
  ring

end LatticeSystem.Fermion
