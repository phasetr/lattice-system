import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorShifted
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSwapReachable
import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowExtend

/-!
# Tasaki 11.5: the shifted t-J sector matrix is irreducible (Prop 11.24 PR-C3b)

The Perron–Frobenius irreducibility of `B = c·1 − M` on the `N̂ = Ne`, `Ŝ³ = ½` sector.  Using the
sector connectivity (`adjacentSwapReachable_of_same_counts` + the `TJStep` bridge) and single-step
positivity (`tJSectorShifted_pos_of_step`):

* `tJSectorShifted_pow_pos_of_reachable` — a `TJStep`-reachable chain from a sector state lifts to a
  strictly positive matrix-power entry of `B` (via `matrix_pow_succ_pos_of_pow_pos_step`);
* `tJSectorShifted_isIrreducible` — `B` is irreducible (via `isIrreducible_iff_exists_pow_pos`): the
  diagonal is positive for `c` above the diagonal, and distinct sector states have equal counts
  hence are reachable.

This is the input to Tasaki Theorem A.18 (`perronFrobenius_real_symmetric`, applied in the next PR).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- A `Fin 3` value is `0`, `1`, or `2`. -/
private theorem fin3_cases' (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp

/-- **The three value-counts partition the sites.**  Every site is empty, `↑`, or `↓`, so the
counts sum to `N + 1`. -/
theorem tJ_value_count_total (s : Fin (N + 1) → Fin 3) :
    (Finset.univ.filter (fun k => s k = 0)).card
      + (Finset.univ.filter (fun k => s k = 1)).card
      + (Finset.univ.filter (fun k => s k = 2)).card = N + 1 := by
  classical
  have h1 : ∀ k : Fin (N + 1),
      ((if s k = 0 then 1 else 0) + (if s k = 1 then 1 else 0)) + (if s k = 2 then (1 : ℕ) else 0)
        = 1 := fun k => by rcases fin3_cases' (s k) with h | h | h <;> simp [h]
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  trans (∑ _k : Fin (N + 1), 1)
  · exact Finset.sum_congr rfl fun k _ => h1 k
  · simp

/-- **Distinct sector states have equal value-counts.**  Within the `N̂ = Ne`, `Ŝ³ = ½` sector,
`#↑`, `#↓` are pinned by `#↑ = #↓ + 1`, `#↑ + #↓ = Ne`, and `#∅` by the total count, so all three
agree between any two sector states. -/
theorem tJSector_same_counts (Ne : ℕ) (q p : TJSpinHalfFillingSector N Ne) (v : Fin 3) :
    (Finset.univ.filter (fun k => q.val k = v)).card
      = (Finset.univ.filter (fun k => p.val k = v)).card := by
  obtain ⟨hq1, hq2⟩ := q.property
  obtain ⟨hp1, hp2⟩ := p.property
  have htq := tJ_value_count_total q.val
  have htp := tJ_value_count_total p.val
  rcases fin3_cases' v with rfl | rfl | rfl
  · omega
  · omega
  · omega

/-- **A reachable chain lifts to matrix-power positivity.**  If `ξ` is `TJStep`-reachable from a
sector state `q.val`, then `ξ` stays in the sector and some power of `B = c·1 − M` is strictly
positive at `(q, ⟨ξ⟩)`. -/
theorem tJSectorShifted_pow_pos_of_reachable (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (c : ℝ)
    (hc : ∀ q : TJSpinHalfFillingSector N Ne,
        tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q ≤ c)
    (q : TJSpinHalfFillingSector N Ne) (ξ : Fin (N + 1) → Fin 3)
    (hreach : Relation.ReflTransGen (TJStep N) q.val ξ) :
    ∃ (hmem : (Finset.univ.filter (fun k => ξ k = 1)).card
          = (Finset.univ.filter (fun k => ξ k = 2)).card + 1 ∧
        (Finset.univ.filter (fun k => ξ k = 1)).card
          + (Finset.univ.filter (fun k => ξ k = 2)).card = Ne) (m : ℕ),
      0 < ((tJSectorShifted N Ne (cycleGraph (N + 1)) τ J c) ^ m) q ⟨ξ, hmem⟩ := by
  have hB_nn := tJSectorShifted_nonneg hpos Ne hodd τ J (le_of_lt hτ) (le_of_lt hJ) c hc
  induction hreach with
  | refl =>
    refine ⟨q.property, 0, ?_⟩
    rw [pow_zero,
      show (⟨q.val, q.property⟩ : TJSpinHalfFillingSector N Ne) = q from Subtype.ext rfl,
      Matrix.one_apply_eq]
    exact zero_lt_one
  | @tail ξ_mid ξ_curr _ h_step ih =>
    obtain ⟨hmem_mid, m, hpow⟩ := ih
    have hmem_curr := tJStep_preserves_sector Ne ξ_mid ξ_curr h_step hmem_mid
    have hne : (⟨ξ_mid, hmem_mid⟩ : TJSpinHalfFillingSector N Ne) ≠ ⟨ξ_curr, hmem_curr⟩ :=
      fun h => tJStep_ne ξ_mid ξ_curr h_step (congrArg Subtype.val h)
    have hstep_pos : 0 < tJSectorShifted N Ne (cycleGraph (N + 1)) τ J c
        ⟨ξ_mid, hmem_mid⟩ ⟨ξ_curr, hmem_curr⟩ :=
      tJSectorShifted_pos_of_step hpos Ne hodd τ J hτ hJ c h_step hne
    exact ⟨hmem_curr, m + 1, LatticeSystem.Math.matrix_pow_succ_pos_of_pow_pos_step hB_nn hpow
      hstep_pos⟩

/-- **The shifted sector matrix is irreducible.**  For `τ, J > 0`, odd `Ne`, and a shift `c`
above every diagonal entry, `B = c·1 − M` is irreducible: the diagonal is positive, and any two
distinct sector states have equal value-counts, hence are connected by adjacent swaps. -/
theorem tJSectorShifted_isIrreducible (hpos : 0 < N) (Ne : ℕ) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (c : ℝ)
    (hc : ∀ q : TJSpinHalfFillingSector N Ne,
        tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q < c) :
    (tJSectorShifted N Ne (cycleGraph (N + 1)) τ J c).IsIrreducible := by
  have hc_le : ∀ q, tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q ≤ c :=
    fun q => le_of_lt (hc q)
  have hB_nn := tJSectorShifted_nonneg hpos Ne hodd τ J (le_of_lt hτ) (le_of_lt hJ) c hc_le
  rw [Matrix.isIrreducible_iff_exists_pow_pos hB_nn]
  intro q p
  by_cases hqp : q = p
  · subst hqp
    exact ⟨1, Nat.one_pos, by rw [pow_one, tJSectorShifted_diag]; linarith [hc q]⟩
  · have hreach : Relation.ReflTransGen (TJStep N) q.val p.val :=
      tjReachable_of_adjacentSwapReachable q.val p.val
        (adjacentSwapReachable_of_same_counts hpos q.val p.val (tJSector_same_counts Ne q p))
    obtain ⟨hmem, m, hpow⟩ :=
      tJSectorShifted_pow_pos_of_reachable hpos Ne hodd τ J hτ hJ c hc_le q p.val hreach
    rw [show (⟨p.val, hmem⟩ : TJSpinHalfFillingSector N Ne) = p from Subtype.ext rfl] at hpow
    refine ⟨m, ?_, hpow⟩
    by_contra h0
    interval_cases m
    rw [pow_zero, Matrix.one_apply_ne hqp] at hpow
    exact lt_irrefl 0 hpow

end LatticeSystem.Fermion
