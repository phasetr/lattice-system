import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopAction

/-!
# The forward-hop Jordan–Wigner sign as a parity over the intervening modes

For a single forward hop `q → p` (`q.val < p.val`) on a computational basis state with the source
`q` occupied, the matrix element of `ĉ†_p ĉ_q` carries the product of two Jordan–Wigner string signs
`jwSign q c · jwSign p (update c q 0)`.  This file shows that product equals `(-1)` to the number of
occupied modes *strictly between* `q` and `p`: the contribution `E_q` of the modes below the source
appears in both signs, so it doubles and cancels in the parity, leaving only the strictly-between
occupations.

This is the model-agnostic "fermionic hop sign is local to the intervening modes" identity used to
show the d=1 ferromagnetic t-J hopping is sign-free (Tasaki §11.5, Proposition 11.24).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2 / §11.5.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

/-- **Forward-hop sign as a strictly-between parity.**  For a forward hop `q → p` (`q.val < p.val`)
with the source occupied (`c q = 1`), the product of the two Jordan–Wigner string signs equals
`(-1)` to the number of occupied modes strictly between `q` and `p`.  The modes below the source
contribute `E_q` to both signs, so `2·E_q` cancels in the parity. -/
theorem jwSign_mul_jwSign_update_forward (M : ℕ) (q p : Fin (M + 1)) (c : Fin (M + 1) → Fin 2)
    (hqp : q.val < p.val) (hcq : c q = 1) :
    jwSign M q c * jwSign M p (Function.update c q 0)
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (M + 1))).filter
          (fun k => q.val < k.val ∧ k.val < p.val), (c k).val) := by
  rw [jwSign_eq_neg_one_pow, jwSign_eq_neg_one_pow, ← pow_add]
  -- partition the modes below `p` into: below `q`, the source `q`, strictly between `q` and `p`
  have hsplit : (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val))
      = (Finset.univ.filter (fun k => k.val < q.val))
        ∪ insert q (Finset.univ.filter (fun k => q.val < k.val ∧ k.val < p.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert]
    constructor
    · intro hk
      rcases lt_trichotomy k.val q.val with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr ⟨h, hk⟩)
    · rintro (h | rfl | ⟨_, h2⟩)
      · omega
      · exact hqp
      · exact h2
  have hqnotin : q ∉ (Finset.univ.filter (fun k : Fin (M + 1) =>
      q.val < k.val ∧ k.val < p.val)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hdisj : Disjoint (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val))
      (insert q (Finset.univ.filter (fun k => q.val < k.val ∧ k.val < p.val))) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hk hk'
    rcases hk' with rfl | ⟨h, _⟩
    · omega
    · omega
  -- `E_p' = E_q + inner`: the source term is zeroed, and on the other parts `update = c`
  have hEp : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < p.val)),
        ((Function.update c q 0) k).val)
      = (∑ k ∈ (Finset.univ.filter (fun k => k.val < q.val)), (c k).val)
        + ∑ k ∈ (Finset.univ.filter (fun k => q.val < k.val ∧ k.val < p.val)), (c k).val := by
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_insert hqnotin, Function.update_self]
    have h1 : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val)),
        ((Function.update c q 0) k).val)
        = ∑ k ∈ (Finset.univ.filter (fun k => k.val < q.val)), (c k).val :=
      Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Function.update_of_ne (fun h => by rw [h] at hk; omega)]
    have h2 : (∑ k ∈ (Finset.univ.filter (fun k : Fin (M + 1) =>
          q.val < k.val ∧ k.val < p.val)), ((Function.update c q 0) k).val)
        = ∑ k ∈ (Finset.univ.filter (fun k => q.val < k.val ∧ k.val < p.val)), (c k).val :=
      Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Function.update_of_ne (fun h => by rw [h] at hk; omega)]
    rw [h1, h2]; simp
  -- assemble: `E_q + E_p' = 2·E_q + inner`, and `(-1)^(2·E_q) = 1`
  rw [hEp, show ∀ a b : ℕ, a + (a + b) = 2 * a + b from fun a b => by ring, pow_add, pow_mul]
  norm_num
