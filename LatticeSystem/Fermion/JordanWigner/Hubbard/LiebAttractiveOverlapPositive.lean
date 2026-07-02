import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedPosSemidefGround

/-!
# Balanced-sector reduction of the cross-overlap trace (Tasaki §10.2.4)

Endgame layer toward `theorem_10_2_lieb_attractive_unique_singlet` (Lemma 10.9 →
uniqueness). The cross overlap of two balanced ground states `φ, φ'` is, by the polarized
coordinate isometry (`blockWCoeff_dotProduct_cross_eq`), the Frobenius pairing
`tr((blockWCoeff φ')ᴴ · blockWCoeff φ)` of their reconciliation coefficient matrices. Both
matrices are supported on the principal count-`k` sector block, so this full-space trace
collapses onto the *compressed* sector via the isometry `J = hubbardCountSectorEmbedding N k`.

Writing `W_S = Jᴴ · blockWCoeff φ · J`, `W'_S = Jᴴ · blockWCoeff φ' · J`, the balanced-support
rewrite `blockWCoeff φ = J · W_S · Jᴴ` (`blockWCoeff_eq_embed_compress_of_balanced`) together
with the orthonormality `Jᴴ · J = 1` (`hubbardCountSectorEmbedding_conjTranspose_mul_self`) and
trace cyclicity reduce the overlap trace to the compressed-sector trace `tr(W'_Sᴴ · W_S)`.

## Main results

* `blockWCoeff_trace_reduce_to_sector` — for balanced `φ, φ'`,
  `tr((blockWCoeff φ')ᴴ · blockWCoeff φ) = tr(W'_Sᴴ · W_S)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.9), pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix

variable {N : ℕ}

/-- **Balanced-embedding reduction of the cross-overlap trace.** For two balanced ground states
`φ, φ'` (both satisfying `N̂_↑ = N̂_↓ = k`), the full-space Frobenius pairing of their
reconciliation coefficients equals the compressed-sector pairing
`tr(W'_Sᴴ · W_S)` with `W_S = Jᴴ · blockWCoeff φ · J`, `W'_S = Jᴴ · blockWCoeff φ' · J`, and
`J = hubbardCountSectorEmbedding N k`. Uses the balanced-support block rewrite
`blockWCoeff φ = J · W_S · Jᴴ`, the orthonormality `Jᴴ · J = 1`, and trace cyclicity. -/
theorem blockWCoeff_trace_reduce_to_sector (k : ℕ)
    (φ φ' : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hφUp : (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ)
    (hφDn : (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ)
    (hφ'Up : (fermionTotalUpNumber N).mulVec φ' = (k : ℂ) • φ')
    (hφ'Dn : (fermionTotalDownNumber N).mulVec φ' = (k : ℂ) • φ') :
    Matrix.trace ((blockWCoeff N φ')ᴴ * blockWCoeff N φ)
      = Matrix.trace
          (((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ'
              * hubbardCountSectorEmbedding N k)ᴴ
            * ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
                * hubbardCountSectorEmbedding N k)) := by
  have hJ : (hubbardCountSectorEmbedding N k)ᴴ * hubbardCountSectorEmbedding N k = 1 :=
    hubbardCountSectorEmbedding_conjTranspose_mul_self k
  have hemb : blockWCoeff N φ
      = hubbardCountSectorEmbedding N k
          * ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
              * hubbardCountSectorEmbedding N k)
          * (hubbardCountSectorEmbedding N k)ᴴ :=
    blockWCoeff_eq_embed_compress_of_balanced k φ hφUp hφDn
  have hemb' : blockWCoeff N φ'
      = hubbardCountSectorEmbedding N k
          * ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ'
              * hubbardCountSectorEmbedding N k)
          * (hubbardCountSectorEmbedding N k)ᴴ :=
    blockWCoeff_eq_embed_compress_of_balanced k φ' hφ'Up hφ'Dn
  set J := hubbardCountSectorEmbedding N k with hJdef
  set WS := Jᴴ * blockWCoeff N φ * J with hWSdef
  set WS' := Jᴴ * blockWCoeff N φ' * J with hWS'def
  -- After folding, `hemb : blockWCoeff N φ = J * WS * Jᴴ` and `hemb' : ... = J * WS' * Jᴴ`.
  have hprod : (blockWCoeff N φ')ᴴ * blockWCoeff N φ = J * (WS'ᴴ * WS) * Jᴴ := by
    conv_lhs => rw [hemb', hemb]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J (WS * Jᴴ), hJ, Matrix.one_mul]
  rw [hprod, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end LatticeSystem.Fermion
