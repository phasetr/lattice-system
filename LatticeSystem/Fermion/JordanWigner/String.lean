/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Fermion.Mode

/-!
# Jordan–Wigner string (Tasaki §2 / standard JW mapping)

The Jordan–Wigner string at site `i` on a chain `Fin (N + 1)` is
the product `∏_{j.val < i.val} σ^z_j` of `σ^z` operators on all
sites strictly to the left of `i`. The string makes the otherwise-
bosonic spin raising / lowering operators anticommute across
distinct sites, giving the correct fermion statistics.

This file contains the JW string base definition + the empty
product at site 0 + the recursive factorisation extending the
product by one `σ^z` factor on the right.

(Refactor Phase 2 PR 10 — first step of the JordanWigner 5-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Jordan–Wigner string -/

/-- The Jordan–Wigner string at site `i` on a chain of `N + 1` sites:
the product `∏_{j.val < i.val} σ^z_j` of `σ^z` operators on all
sites strictly to the left of `i`.

Uses `Finset.noncommProd` because `ManyBodyOp` is a non-commutative
ring. The pairwise-commutativity certificate comes from
`onSite_mul_onSite_of_ne` (different-site `σ^z` operators commute). -/
noncomputable def jwString (N : ℕ) (i : Fin (N + 1)) :
    ManyBodyOp (Fin (N + 1)) :=
  ((Finset.univ.filter fun j : Fin (N + 1) => j.val < i.val)).noncommProd
    (fun j => onSite j pauliZ)
    (fun _ _ _ _ hab => onSite_mul_onSite_of_ne hab pauliZ pauliZ)

/-- The Jordan–Wigner string at site `0` is the identity (empty
product, since no `j` satisfies `j.val < 0`). -/
theorem jwString_zero (N : ℕ) :
    jwString N (0 : Fin (N + 1)) = 1 := by
  unfold jwString
  simp

/-- Recursive factorisation of the JW string: adding a new site `i`
at the right extends the product by one `σ^z_i` factor.
`jwString N ⟨i.val + 1, _⟩ = jwString N i * onSite i pauliZ`. -/
theorem jwString_succ_eq (N : ℕ) (i : Fin (N + 1)) (hi : i.val + 1 < N + 1) :
    jwString N ⟨i.val + 1, hi⟩ = jwString N i * onSite i pauliZ := by
  unfold jwString
  have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
      (fun j => j.val < (⟨i.val + 1, hi⟩ : Fin (N + 1)).val) =
      insert i ((Finset.univ : Finset (Fin (N + 1))).filter
        (fun j => j.val < i.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      show k = i ∨ k.val < i.val
      by_cases heq : k.val = i.val
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (by omega)
    · intro h
      rcases h with h | h
      · rw [h]; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  have hi_notmem : i ∉ (Finset.univ : Finset (Fin (N + 1))).filter
      (fun j => j.val < i.val) := by
    simp
  rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
  rw [Finset.noncommProd_insert_of_notMem' _ _ _ _ hi_notmem]


end LatticeSystem.Fermion
