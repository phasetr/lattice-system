import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedPosSemidefGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionTrace

/-!
# Sector-compression glue for the balanced-sector positive-definite ground (Tasaki §10.2.4)

Layer toward discharging `theorem_10_2_lieb_attractive_unique_singlet` (Tasaki Lemma 10.10). The
abstract connected-support dichotomy (`posDef_or_eq_zero_of_connected_support`) and the separating
projection kernel argument (`basis_mem_ker_of_separating_projections`) run on the *sector* index
type `hubbardSpinCountSector N k`, whereas the concrete operators (kinetic matrix, site-occupation
diagonals) live on the full `W`-index space `hubbardSpinConfig N`. Bridging the two requires reading
off entries through the standard-basis isometry `J = hubbardCountSectorEmbedding N k`.

Since each column `J · s` of the embedding is the standard basis vector `|s.val⟩`, conjugation by
`Jᴴ · (−) · J` simply reads off the `(s.val, s'.val)` matrix entry:

* the **entry readoff** `(Jᴴ · M · J) s s' = M s.val s'.val` (`basisVec` selector-sum
  collapse), which makes the compressed kinetic matrix's adjacency match
  `hubbardKineticSectorGraph_adj_entry_ne`, and
* the **occupation diagonal compression** `Jᴴ · D_x · J = diagonal (s ↦ (s.val x))`, immediate from
  the readoff plus injectivity of the subtype value, feeding the separating-projection kernel step.

## Main results

* `hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply` — the entry readoff
  `(Jᴴ · M · J) s s' = M s.val s'.val`.
* `hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul` — the site-`x` up-occupation
  diagonal compresses to the sector-restricted occupation diagonal
  `diagonal (s ↦ (s.val x))`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Entry readoff through the sector embedding.** Since column `s` of the isometry
`J = hubbardCountSectorEmbedding N k` is the standard basis vector `|s.val⟩`, the conjugation
`Jᴴ · M · J` reads off the `(s.val, s'.val)` entry of `M`:
`(Jᴴ · M · J) s s' = M s.val s'.val`. Both collapses use `basisVec` selector sums. -/
theorem hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply (k : ℕ)
    (M : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ)
    (s s' : hubbardSpinCountSector N k) :
    ((hubbardCountSectorEmbedding N k)ᴴ * M * hubbardCountSectorEmbedding N k) s s'
      = M s.val s'.val := by
  set J := hubbardCountSectorEmbedding N k with hJ
  -- Entrywise readouts of `J` and `Jᴴ` (columns are standard basis vectors).
  have hJapply : ∀ (w : hubbardSpinConfig N) (t : hubbardSpinCountSector N k),
      J w t = basisVec t.val w := fun w t => by
    rw [hJ, hubbardCountSectorEmbedding, Matrix.of_apply]
  have hJHapply : ∀ (t : hubbardSpinCountSector N k) (w : hubbardSpinConfig N),
      Jᴴ t w = basisVec t.val w := fun t w => by
    rw [Matrix.conjTranspose_apply, hJapply,
      show star (basisVec t.val w) = basisVec t.val w from by
        rw [basisVec_apply]; split <;> simp]
  -- Outer product: collapse the right factor `J _ s' = basisVec s'.val _`.
  rw [Matrix.mul_apply,
    show (∑ w', (Jᴴ * M) s w' * J w' s')
        = ∑ w', (Jᴴ * M) s w' * basisVec s'.val w' from
      Finset.sum_congr rfl (fun w' _ => by rw [hJapply]),
    sum_mul_basisVec s'.val (fun w' => (Jᴴ * M) s w')]
  -- Inner product: collapse the left factor `Jᴴ s _ = basisVec s.val _`.
  rw [Matrix.mul_apply,
    show (∑ w, Jᴴ s w * M w s'.val) = ∑ w, basisVec s.val w * M w s'.val from
      Finset.sum_congr rfl (fun w _ => by rw [hJHapply]),
    basisVec_sum_mul s.val (fun w => M w s'.val)]

/-- **Occupation diagonal compression.** The full-space site-`x` up-occupation diagonal
`D_x = hubbardUpOccupationDiag N x` compresses through the sector embedding to the
sector-restricted occupation diagonal `diagonal (s ↦ (s.val x))`. Immediate from the entry
readoff plus injectivity of the subtype value. -/
theorem hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul (k : ℕ)
    (x : Fin (N + 1)) :
    (hubbardCountSectorEmbedding N k)ᴴ * hubbardUpOccupationDiag N x
        * hubbardCountSectorEmbedding N k
      = Matrix.diagonal (fun s : hubbardSpinCountSector N k => ((s.val x).val : ℂ)) := by
  ext s s'
  rw [hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply, hubbardUpOccupationDiag,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : s = s'
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]

end LatticeSystem.Fermion
