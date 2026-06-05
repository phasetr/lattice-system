import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorNumber

/-!
# Tasaki 11.5: total occupation count and the three-way mode split (Prop 11.24 PR3c-6)

Infrastructure for the wrap-bond hop sign of the d=1 t-J cycle.  The wrap bond `{0, N}` gives a
forward hop `0 → N` whose source and target orbitals are *not* mode-adjacent: the Jordan–Wigner
string between them runs over all the other electrons, so the strictly-between occupation equals
`Ne − 1` and the sign is `(-1)^(Ne-1) = +1` for **odd** `Ne`.

To count `Ne − 1` one needs (i) the total electron number `∑_k (tJConfigOf s k).val = #↑ + #↓`, and
(ii) a three-way split of the modes into `{k ≤ q}`, the strictly-between range, and `{k ≥ p}`.  This
file proves both; the wrap-bond hop matrix element itself follows in the next step.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The total occupation of `tJConfigOf s` over all Jordan–Wigner modes equals `#↑ + #↓` (the
electron number). -/
theorem tJConfigOf_total_count (N : ℕ) (s : Fin (N + 1) → Fin 3) :
    (∑ k : Fin (2 * N + 2), (tJConfigOf N s k).val)
      = (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card := by
  rw [sum_spinful_reindex N (fun k => (tJConfigOf N s k).val)]
  simp_rw [Fin.sum_univ_two]
  rw [Finset.sum_add_distrib, tJConfigOf_up_count, tJConfigOf_down_count]

/-- **Three-way split of the total occupation** by a forward pair `q < p`: modes below-or-at `q`,
strictly between `q` and `p`, and at-or-above `p`. -/
theorem sum_split_le_between_ge (M : ℕ) (c : Fin (M + 1) → Fin 2) (q p : Fin (M + 1))
    (hqp : q.val < p.val) :
    (∑ k : Fin (M + 1), (c k).val)
      = (∑ k ∈ Finset.univ.filter (fun k => k.val ≤ q.val), (c k).val)
        + (∑ k ∈ Finset.univ.filter (fun k => q.val < k.val ∧ k.val < p.val), (c k).val)
        + ∑ k ∈ Finset.univ.filter (fun k => p.val ≤ k.val), (c k).val := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h1 : k.val ≤ q.val
  · rw [if_pos h1, if_neg (show ¬(q.val < k.val ∧ k.val < p.val) by omega),
      if_neg (show ¬ p.val ≤ k.val by omega)]; ring
  · by_cases h2 : k.val < p.val
    · rw [if_neg h1, if_pos (show q.val < k.val ∧ k.val < p.val by omega),
        if_neg (show ¬ p.val ≤ k.val by omega)]; ring
    · rw [if_neg h1, if_neg (show ¬(q.val < k.val ∧ k.val < p.val) by omega),
        if_pos (show p.val ≤ k.val by omega)]; ring

end LatticeSystem.Fermion
