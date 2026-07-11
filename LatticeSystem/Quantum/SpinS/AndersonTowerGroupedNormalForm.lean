import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra

/-!
# Tasaki §4.2.2 Proposition 4.10: grouped normal form of a `Fin 3` order word

The pinch step of Proposition 4.10 collapses an arbitrary `Fin 3`-valued Cartesian order word
`List.ofFn f` (`f : Fin M → Fin 3`) to its **grouped normal form**, the canonical word that lists
all `0`-letters, then all `1`-letters, then all `2`-letters, each repeated its multiplicity.  The
number of adjacent `±`-style transpositions needed to reach the normal form is bounded by `M²`
(a loose bubble-sort diameter), which is exactly the input the band-stage bound
`cartWord_swapChain_re_diff_norm_le` consumes.

This file records the purely combinatorial ingredients:

* `groupedFin3` — the canonical grouped word of a `Fin 3` count vector;
* `groupedFin3_count` — the grouped word preserves per-letter counts;
* `ofFn_swapChain_groupedFin3` — every `List.ofFn f` reaches its grouped normal form by a swap
  chain of length `≤ M²`.

The swap-chain machinery (`SwapChain`, `bringToFront`, `swapDist_le_length_sq`) is the generic
alphabet version defined in `OrderOperatorAlgebra`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.58)–(4.2.59), p. 108.
-/

namespace LatticeSystem.Quantum

/-- The **canonical grouped word** of a `Fin 3` count vector `k`: all `0`-letters (`k 0` copies),
then all `1`-letters (`k 1` copies), then all `2`-letters (`k 2` copies). -/
def groupedFin3 (k : Fin 3 → ℕ) : List (Fin 3) :=
  List.replicate (k 0) 0 ++ List.replicate (k 1) 1 ++ List.replicate (k 2) 2

/-- The grouped word preserves per-letter counts: `(groupedFin3 k).count i = k i`. -/
theorem groupedFin3_count (k : Fin 3 → ℕ) (i : Fin 3) : (groupedFin3 k).count i = k i := by
  simp only [groupedFin3, List.count_append, List.count_replicate]
  fin_cases i <;> simp

/-- **Grouped normal form via a bounded swap chain**: any `Fin 3`-valued Cartesian order word
`List.ofFn f` reaches its grouped normal form `groupedFin3 (count)` by a swap chain of length at
most `M²`.  The word and its normal form share every per-letter count (`groupedFin3_count`), hence
are permutations (`List.perm_iff_count`), so the generic swap-diameter bound `swapDist_le_length_sq`
applies with `(List.ofFn f).length = M`. -/
theorem ofFn_swapChain_groupedFin3 {M : ℕ} (f : Fin M → Fin 3) :
    ∃ k, k ≤ M * M ∧
      SwapChain k (List.ofFn f) (groupedFin3 (fun i => (List.ofFn f).count i)) := by
  have hperm : (List.ofFn f).Perm (groupedFin3 (fun i => (List.ofFn f).count i)) := by
    rw [List.perm_iff_count]
    intro i
    rw [groupedFin3_count]
  obtain ⟨k, hk, hchain⟩ := swapDist_le_length_sq hperm
  refine ⟨k, ?_, hchain⟩
  rwa [List.length_ofFn] at hk

end LatticeSystem.Quantum
