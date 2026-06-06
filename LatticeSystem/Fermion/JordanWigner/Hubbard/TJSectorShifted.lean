import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJStepMatrixEntry

/-!
# Tasaki 11.5: the shifted sector matrix `B = c·1 − M` (Prop 11.24 PR-C3a)

The Perron–Frobenius input matrix `B = c·1 − M` for the real symmetric sector matrix
`M = tJEffReMatrixOnSector`.  This file collects its algebraic properties — symmetry, entrywise
non-negativity (for a shift `c` above the diagonal), and the single-step positivity feeding the
irreducibility:

* `tJSectorShifted_isSymm` — `B` is symmetric (from `M`'s symmetry);
* `tJSectorShifted_nonneg` — `0 ≤ B` entrywise (diagonal `c − M_{qq} ≥ 0`, off-diagonal
  `−M_{q,p} ≥ 0` from `tJEffMatrix_offdiag_nonpos`);
* `tJStep_ne` — a connectivity step changes the configuration;
* `tJSectorShifted_pos_of_step` — a `TJStep` between distinct sector states gives a strictly
  positive off-diagonal `B`-entry (from `tJEffMatrix_re_neg_of_step` + symmetry).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-- **The shifted sector matrix** `B = c·1 − M` for `M = tJEffReMatrixOnSector`. -/
noncomputable def tJSectorShifted (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (c : ℝ) :
    Matrix (TJSpinHalfFillingSector N Ne) (TJSpinHalfFillingSector N Ne) ℝ :=
  fun q p => (if q = p then c else 0) - tJEffReMatrixOnSector N Ne G τ J q p

/-- The diagonal entry of `B` is `c − M_{qq}`. -/
theorem tJSectorShifted_diag (Ne : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J c : ℝ) (q : TJSpinHalfFillingSector N Ne) :
    tJSectorShifted N Ne G τ J c q q = c - tJEffReMatrixOnSector N Ne G τ J q q := by
  simp [tJSectorShifted]

/-- The off-diagonal entry of `B` is `−M_{q,p}`. -/
theorem tJSectorShifted_off_diag (Ne : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J c : ℝ) {q p : TJSpinHalfFillingSector N Ne} (hqp : q ≠ p) :
    tJSectorShifted N Ne G τ J c q p = - tJEffReMatrixOnSector N Ne G τ J q p := by
  simp [tJSectorShifted, hqp]

/-- **`B` is symmetric** (from the symmetry of `M`). -/
theorem tJSectorShifted_isSymm (Ne : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J c : ℝ) : (tJSectorShifted N Ne G τ J c).IsSymm := by
  ext q p
  simp only [Matrix.transpose_apply, tJSectorShifted]
  rw [(tJEffReMatrixOnSector_isSymm N Ne G τ J).apply p q]
  by_cases h : q = p
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

/-- **A connectivity step changes the configuration** (`s ≠ s'`). -/
theorem tJStep_ne (s s' : Fin (N + 1) → Fin 3) (h : TJStep N s s') : s ≠ s' := by
  rcases h with ⟨a, b, _, hsa, _, rfl⟩ | ⟨i, j, _, hi, hj, rfl⟩
  · intro heq
    have : tJSiteHop s a b a = s a := by rw [← heq]
    rw [tJSiteHop, if_pos rfl] at this
    exact hsa this.symm
  · intro heq
    have : tJSpinSwap s i j i = s i := by rw [← heq]
    rw [tJSpinSwap, if_pos rfl, hj, hi] at this
    exact absurd this (by decide)

/-- **`B` is entrywise non-negative** for a shift `c` at least the diagonal entries: the diagonal is
`c − M_{qq} ≥ 0` and the off-diagonal is `−M_{q,p} ≥ 0` (`tJEffMatrix_offdiag_nonpos`). -/
theorem tJSectorShifted_nonneg (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (c : ℝ)
    (hc : ∀ q : TJSpinHalfFillingSector N Ne,
        tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q ≤ c)
    (q p : TJSpinHalfFillingSector N Ne) :
    0 ≤ tJSectorShifted N Ne (cycleGraph (N + 1)) τ J c q p := by
  by_cases hqp : q = p
  · subst hqp; rw [tJSectorShifted_diag]; linarith [hc q]
  · rw [tJSectorShifted_off_diag Ne (cycleGraph (N + 1)) τ J c hqp,
      show tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q p
        = (tJEffMatrix N (cycleGraph (N + 1)) τ J q.val p.val).re from rfl]
    have hne : q.val ≠ p.val := fun h => hqp (Subtype.ext h)
    linarith [(tJEffMatrix_offdiag_nonpos N hpos p.val q.val Ne p.property.2 hodd τ J hτ hJ
      hne).1]

/-- **A `TJStep` between distinct sector states gives a strictly positive off-diagonal `B`-entry.**
From `tJEffMatrix_re_neg_of_step` (`M_{q,p} < 0` for a step) and the symmetry of `M`. -/
theorem tJSectorShifted_pos_of_step (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (c : ℝ)
    {q p : TJSpinHalfFillingSector N Ne} (hstep : TJStep N q.val p.val) (hqp : q ≠ p) :
    0 < tJSectorShifted N Ne (cycleGraph (N + 1)) τ J c q p := by
  rw [tJSectorShifted_off_diag Ne (cycleGraph (N + 1)) τ J c hqp,
    show tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q p
      = (tJEffMatrix N (cycleGraph (N + 1)) τ J q.val p.val).re from rfl]
  have hne : p.val ≠ q.val := fun h => hqp (Subtype.ext h.symm)
  -- symmetry: `M_{q,p} = M_{p,q}`, and `M_{p,q} < 0` by the step lemma.
  have hsymm : (tJEffMatrix N (cycleGraph (N + 1)) τ J q.val p.val).re
      = (tJEffMatrix N (cycleGraph (N + 1)) τ J p.val q.val).re := by
    have h := congr_fun₂ (tJEffMatrix_isHermitian N (cycleGraph (N + 1)) τ J) q.val p.val
    rw [Matrix.conjTranspose_apply] at h
    rw [← h, Complex.star_def, Complex.conj_re]
  rw [hsymm]
  linarith [tJEffMatrix_re_neg_of_step N hpos q.val p.val Ne q.property.2 hodd τ J hτ hJ hstep hne]

end LatticeSystem.Fermion
