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
* `blockWCoeff_sectorCompress_ne_zero_of_ne_zero` — for a nonzero balanced state `ψ`, the
  sector-compressed coefficient `R_k = Jᴴ · blockWCoeff ψ · J` is nonzero (the nonvanishing input
  to the connected-support dichotomy `R ≠ 0 ⟹ R.PosDef`).

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

/-- **Nonvanishing of the sector-compressed coefficient.** For a nonzero state `ψ` in the balanced
sector (`N̂_↑ ψ = N̂_↓ ψ = k·ψ`), its sector compression `R_k = Jᴴ · blockWCoeff ψ · J` through the
embedding `J = hubbardCountSectorEmbedding N k` is nonzero. Indeed, if `R_k = 0` then the balanced
principal-block rewrite `blockWCoeff ψ = J · R_k · Jᴴ` (`blockWCoeff_eq_embed_compress_of_balanced`)
collapses to `blockWCoeff ψ = 0`; but the coordinate map `ψ ↦ blockWCoeff ψ` is a norm isometry
(`blockWCoeff_dotProduct_eq`), so `⟨ψ, ψ⟩ = Σ |blockWCoeff ψ|² = 0` would force `ψ = 0`, a
contradiction. This is the nonvanishing input `R ≠ 0` feeding the connected-support dichotomy
`R ≠ 0 ⟹ R.PosDef` of Tasaki §10.2.4 Lemma 10.10. -/
theorem blockWCoeff_sectorCompress_ne_zero_of_ne_zero (k : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (hψ : ψ ≠ 0)
    (hUp : (fermionTotalUpNumber N).mulVec ψ = (k : ℂ) • ψ)
    (hDn : (fermionTotalDownNumber N).mulVec ψ = (k : ℂ) • ψ) :
    (hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N ψ
        * hubbardCountSectorEmbedding N k ≠ 0 := by
  intro hRk0
  -- `R_k = 0` collapses the balanced principal-block rewrite to `blockWCoeff ψ = 0`.
  have hW0 : blockWCoeff N ψ = 0 := by
    have h := blockWCoeff_eq_embed_compress_of_balanced k ψ hUp hDn
    rw [hRk0] at h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  -- The isometry `⟨ψ, ψ⟩ = Σ |blockWCoeff ψ|²` then forces every coordinate of `ψ` to vanish.
  apply hψ
  funext c
  have hdot : dotProduct (star ψ) ψ = 0 := by
    rw [blockWCoeff_dotProduct_eq, hW0]
    simp
  rw [dotProduct_star_self_eq_sum_normSq] at hdot
  have hreal : (∑ c, Complex.normSq (ψ c)) = 0 := by
    have h2 : ((∑ c, Complex.normSq (ψ c) : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum]; exact hdot
    exact_mod_cast h2
  have hc : Complex.normSq (ψ c) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Complex.normSq_nonneg _)).mp hreal c
      (Finset.mem_univ c)
  exact Complex.normSq_eq_zero.mp hc

end LatticeSystem.Fermion
