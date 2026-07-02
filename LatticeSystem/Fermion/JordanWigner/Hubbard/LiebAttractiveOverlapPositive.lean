import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedPosSemidefGround
import LatticeSystem.Math.PosSemidef.TraceProductPos

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
* `balanced_signDefinite_ground_dotProduct_ne_zero` — **the balanced ground-state overlap
  is nonzero.** For two balanced ground states `φ, φ'` whose compressed sector coefficients
  `W_S, W'_S` are each sign-definite (positive definite up to an overall sign), the overlap
  `⟨Γ(φ'), Γ(φ)⟩ = dotProduct (star φ') φ` is nonzero. This is the non-orthogonality core of
  Lieb's uniqueness theorem; `finrank ≤ 1` / singlet uniqueness is deferred to the capstone.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Theorem 10.2 uniqueness, Lemma 10.9), pp. 363–367;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped ComplexOrder

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

/-- **The balanced ground-state overlap is nonzero (non-orthogonality core).** Let `φ, φ'` be
two balanced ground states (each satisfying `N̂_↑ = N̂_↓ = k`) of the attractive Hubbard model
whose compressed sector coefficient matrices
`W_S = Jᴴ · blockWCoeff φ · J`, `W'_S = Jᴴ · blockWCoeff φ' · J`
(`J = hubbardCountSectorEmbedding N k`) are each *sign-definite* — positive definite up to an
overall sign, `W_S.PosDef ∨ (-W_S).PosDef` (the conclusion of Lemma 10.9). Then the overlap
`⟨Γ(φ'), Γ(φ)⟩ = dotProduct (star φ') φ` is nonzero.

The overlap equals `tr(W'_Sᴴ · W_S) = tr(W'_S · W_S)` (both compressions are Hermitian, being
sign-definite). Splitting on the four sign combinations, `tr(W'_S · W_S)` is strictly positive
or strictly negative by `Matrix.PosDef.trace_mul_pos` (the trace of a product of two
positive-definite matrices is positive), the opposite-sign cases reducing to it via
`neg_mul` / `mul_neg` / `neg_mul_neg` and `Matrix.trace_neg`. In every case the trace is
nonzero, hence so is the overlap.

This is the non-orthogonality core of the uniqueness half of Tasaki §10.2.4 Theorem 10.2
(Lieb's theorem for the attractive Hubbard model). The passage from pairwise
non-orthogonality to `finrank ≤ 1` / singlet uniqueness is deferred to the capstone.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.4 (Theorem 10.2 uniqueness), pp. 363–367. -/
theorem balanced_signDefinite_ground_dotProduct_ne_zero (k : ℕ)
    [Nonempty (hubbardSpinCountSector N k)]
    (φ φ' : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hφUp : (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ)
    (hφDn : (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ)
    (hφ'Up : (fermionTotalUpNumber N).mulVec φ' = (k : ℂ) • φ')
    (hφ'Dn : (fermionTotalDownNumber N).mulVec φ' = (k : ℂ) • φ')
    (hSD : ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
              * hubbardCountSectorEmbedding N k).PosDef
          ∨ (-((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
              * hubbardCountSectorEmbedding N k)).PosDef)
    (hSD' : ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ'
              * hubbardCountSectorEmbedding N k).PosDef
          ∨ (-((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ'
              * hubbardCountSectorEmbedding N k)).PosDef) :
    dotProduct (star φ') φ ≠ 0 := by
  rw [blockWCoeff_dotProduct_cross_eq φ' φ,
    blockWCoeff_trace_reduce_to_sector k φ φ' hφUp hφDn hφ'Up hφ'Dn]
  set J := hubbardCountSectorEmbedding N k with hJdef
  set WS := Jᴴ * blockWCoeff N φ * J with hWSdef
  set WS' := Jᴴ * blockWCoeff N φ' * J with hWS'def
  -- The compressed `W'_S` is Hermitian (being sign-definite), so `W'_Sᴴ = W'_S`.
  have hHerm' : WS'ᴴ = WS' := by
    rcases hSD' with h | h
    · exact h.isHermitian
    · have h2 : (-WS')ᴴ = -WS' := h.isHermitian
      rw [Matrix.conjTranspose_neg] at h2
      exact neg_inj.mp h2
  rw [hHerm']
  -- Goal: `Matrix.trace (WS' * WS) ≠ 0`. Split on the four sign combinations.
  rcases hSD with hA | hA <;> rcases hSD' with hB | hB
  · exact (Matrix.PosDef.trace_mul_pos hB hA).ne'
  · have h0 := Matrix.PosDef.trace_mul_pos hB hA
    rw [neg_mul, Matrix.trace_neg] at h0
    exact (neg_pos.mp h0).ne
  · have h0 := Matrix.PosDef.trace_mul_pos hB hA
    rw [mul_neg, Matrix.trace_neg] at h0
    exact (neg_pos.mp h0).ne
  · have h0 := Matrix.PosDef.trace_mul_pos hB hA
    rw [neg_mul_neg] at h0
    exact h0.ne'

end LatticeSystem.Fermion
