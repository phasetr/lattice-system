import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionicTranslation
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopActionCore

/-!
# The Jordan–Wigner sign cocycle: one-mode-update parity (Tasaki §10.2.1)

Fourteenth layer (PR14) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR12/PR13 introduced the unitary signed permutation operator `U = permutationOperator π`
and computed the basis action of a conjugated single hopping term `U (ĉ†_p ĉ_q) Uᴴ` with
an explicit composite Jordan–Wigner / permutation sign `permutationHopConjSign`.  To
reduce that composite sign to a *permuted bare hop sign* (the cocycle property, PR15) and
finally to the operator identity `U·Ĥ_block·Uᴴ = Ĥ_interleaved` (PR16), the key algebraic
input is how the permutation sign `translationJwSign π` of a configuration changes under a
single-mode update.

This file proves that **one-mode-update parity law**: the product of `translationJwSign π`
before and after zeroing one occupied mode `q` of the permuted configuration `σ ∘ π` equals
the product of the bare Jordan–Wigner string signs `jwSign q (σ∘π) · jwSign (π q) σ`.

## Main results

* `update_comp_perm` — `update (σ∘π) a v = (update σ (π a) v) ∘ π`: updating a permuted
  configuration commutes with precomposition by `π`.
* `translationJwSign_mul_update_zero_comp_eq_jwSign_mul` — for `(σ∘π) q = 1`,
  `translationJwSign π (σ∘π) · translationJwSign π (update (σ∘π) q 0)
     = jwSign M q (σ∘π) · jwSign M (π q) σ`.
* `translationJwSign_mul_update_one_comp_eq_jwSign_mul` — the dual for `(σ∘π) p = 0` and
  `update … p 1` (derived from the previous via `update_comp_perm`).

## Proof of the parity law

Write `c = σ ∘ π` and `c' = update c q 0`.  Unfolding both sides to `(-1)^…`, the claim is
`#S(c) + #S(c') ≡ E_q(c) + E_{πq}(σ)  (mod 2)`, where `S(c)` is the set of *occupied
inversions* of `π` and `E_j` the occupied-modes-below-`j` count.  Partition the occupied
`k ≠ q` by `(k < q?) × (π k < π q?)` into `A, B, C, D`.  Zeroing `q` removes exactly the
inversions involving `q`, so `#S(c) = #S(c') + (#B + #C)`, while `E_q(c) = #A + #B` and
(after reindexing by `π`) `E_{πq}(σ) = #A + #C`.  Both exponents are then `#B + #C` modulo
the cancelling even terms `2·#S(c')` resp. `2·#A`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- Updating a permuted configuration `σ ∘ π` at a mode `a` is the same as updating `σ` at
`π a` and then precomposing by `π`: `update (σ∘π) a v = (update σ (π a) v) ∘ π`. -/
theorem update_comp_perm (π : Equiv.Perm (Fin M)) (σ : Fin M → Fin 2) (a : Fin M)
    (v : Fin 2) :
    Function.update (σ ∘ π) a v = (Function.update σ (π a) v) ∘ π := by
  funext x
  by_cases hx : x = a
  · subst hx
    simp [Function.update_self, Function.comp_apply]
  · rw [Function.update_of_ne hx, Function.comp_apply, Function.comp_apply,
      Function.update_of_ne (fun h => hx (π.injective h))]

/-- The occupied count `∑_{k∈s} (c k).val` equals the cardinality of the occupied modes in
`s`: `(s.filter (c · = 1)).card`. -/
private theorem occ_sum_eq_card (s : Finset (Fin (M + 1))) (c : Fin (M + 1) → Fin 2) :
    ∑ k ∈ s, (c k).val = (s.filter (fun k => c k = 1)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases eq_or_ne (c k) 1 with h | h
  · simp [h]
  · have h0 : c k = 0 :=
      Fin.ext (by have := (c k).isLt; have : (c k).val ≠ 1 := fun hh => h (Fin.ext hh); omega)
    simp [h0]

/-- **The one-mode-update parity law (remove an occupied mode).**  For the permuted
configuration `c = σ ∘ π` with `c q = 1`, the product of `translationJwSign π` before and
after zeroing mode `q` equals the bare Jordan–Wigner hop signs `jwSign q c · jwSign (π q) σ`.
This is the cocycle input that lets the PR13 composite sign be rewritten as a permuted bare
hop sign. -/
theorem translationJwSign_mul_update_zero_comp_eq_jwSign_mul
    (π : Equiv.Perm (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) (q : Fin (M + 1))
    (hq : (σ ∘ π) q = 1) :
    translationJwSign π (σ ∘ π) * translationJwSign π (Function.update (σ ∘ π) q 0)
      = jwSign M q (σ ∘ π) * jwSign M (π q) σ := by
  set c : Fin (M + 1) → Fin 2 := σ ∘ π with hc
  -- the A / B / C occupied-mode partition (relative to `q` and `π q`)
  set Aset : Finset (Fin (M + 1)) :=
    Finset.univ.filter (fun k => k.val < q.val ∧ c k = 1 ∧ (π k).val < (π q).val) with hAset
  set Bset : Finset (Fin (M + 1)) :=
    Finset.univ.filter (fun k => k.val < q.val ∧ c k = 1 ∧ (π q).val < (π k).val) with hBset
  set Cset : Finset (Fin (M + 1)) :=
    Finset.univ.filter (fun k => q.val < k.val ∧ c k = 1 ∧ (π k).val < (π q).val) with hCset
  -- the occupied-inversion sets `S(c)` and `S(c')`
  set Sc : Finset (Fin (M + 1) × Fin (M + 1)) :=
    Finset.univ.filter
      (fun p => p.1 < p.2 ∧ c p.1 = 1 ∧ c p.2 = 1 ∧ π p.2 < π p.1) with hSc
  set Sc' : Finset (Fin (M + 1) × Fin (M + 1)) :=
    Finset.univ.filter
      (fun p => p.1 < p.2 ∧ (Function.update c q 0) p.1 = 1 ∧ (Function.update c q 0) p.2 = 1
        ∧ π p.2 < π p.1) with hSc'
  -- `E_q(c) = #A + #B`
  have hEq : ∑ k ∈ Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val), (c k).val
      = Aset.card + Bset.card := by
    rw [occ_sum_eq_card, Finset.filter_filter]
    have hunion :
        (Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val ∧ c k = 1))
          = Aset ∪ Bset := by
      rw [hAset, hBset]
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨hkq, hck⟩
        have hkne : k ≠ q := by intro he; rw [he] at hkq; omega
        have hne : (π k).val ≠ (π q).val := fun h => hkne (π.injective (Fin.ext h))
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨hkq, hck, h⟩
        · exact Or.inr ⟨hkq, hck, h⟩
      · rintro (⟨hkq, hck, _⟩ | ⟨hkq, hck, _⟩) <;> exact ⟨hkq, hck⟩
    have hdisj : Disjoint Aset Bset := by
      rw [hAset, hBset, Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- `E_{πq}(σ) = #A + #C` (after reindexing the sum over `m < π q` by `m = π k`)
  have hEpq : ∑ m ∈ Finset.univ.filter (fun m : Fin (M + 1) => m.val < (π q).val), (σ m).val
      = Aset.card + Cset.card := by
    rw [occ_sum_eq_card]
    -- reindex `{m : m < π q ∧ σ m = 1}` by `m = π k` to `{k : π k < π q ∧ c k = 1}`
    have hreindex :
        ((Finset.univ.filter (fun m : Fin (M + 1) => m.val < (π q).val)).filter
            (fun m => σ m = 1)).card
          = (Finset.univ.filter
              (fun k : Fin (M + 1) => (π k).val < (π q).val ∧ c k = 1)).card := by
      refine Finset.card_bij' (fun m _ => π.symm m) (fun k _ => π k) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        refine ⟨?_, ?_⟩
        · rw [Equiv.apply_symm_apply]; exact hm.1
        · rw [hc, Function.comp_apply, Equiv.apply_symm_apply]; exact hm.2
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        refine ⟨hk.1, ?_⟩
        have hk2 := hk.2
        rw [hc, Function.comp_apply] at hk2
        exact hk2
      · intro m _; exact π.apply_symm_apply m
      · intro k _; exact π.symm_apply_apply k
    rw [hreindex]
    have hunion :
        (Finset.univ.filter (fun k : Fin (M + 1) => (π k).val < (π q).val ∧ c k = 1))
          = Aset ∪ Cset := by
      rw [hAset, hCset]
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨hpk, hck⟩
        have hne : k ≠ q := by
          rintro rfl; exact (lt_irrefl _) hpk
        rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : k.val ≠ q.val) with h | h
        · exact Or.inl ⟨h, hck, hpk⟩
        · exact Or.inr ⟨h, hck, hpk⟩
      · rintro (⟨_, hck, hpk⟩ | ⟨_, hck, hpk⟩) <;> exact ⟨hpk, hck⟩
    have hdisj : Disjoint Aset Cset := by
      rw [hAset, hCset, Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- `#S(c) = #S(c') + (#B + #C)`: zeroing `q` removes exactly the inversions through `q`
  have hScard : Sc.card = Sc'.card + (Bset.card + Cset.card) := by
    -- `S(c')` is the part of `S(c)` avoiding `q`
    have hSc'eq : Sc' = Sc.filter (fun p => p.1 ≠ q ∧ p.2 ≠ q) := by
      rw [hSc, hSc', Finset.filter_filter]
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : ∀ x : Fin (M + 1), (Function.update c q 0) x = 1 ↔ (x ≠ q ∧ c x = 1) := by
        intro x
        by_cases hx : x = q
        · subst hx; simp [Function.update_self]
        · rw [Function.update_of_ne hx]; exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
      rw [hval, hval]
      constructor
      · rintro ⟨h1, ⟨hp1, hc1⟩, ⟨hp2, hc2⟩, h4⟩; exact ⟨⟨h1, hc1, hc2, h4⟩, hp1, hp2⟩
      · rintro ⟨⟨h1, hc1, hc2, h4⟩, hp1, hp2⟩; exact ⟨h1, ⟨hp1, hc1⟩, ⟨hp2, hc2⟩, h4⟩
    -- the complementary part (inversions through `q`) biject onto `B ∪ C`
    have hneg : (Sc.filter (fun p => ¬ (p.1 ≠ q ∧ p.2 ≠ q))).card = Bset.card + Cset.card := by
      have hdisjBC : Disjoint Bset Cset := by
        rw [hBset, hCset, Finset.disjoint_left]
        intro k hk hk'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
        omega
      rw [← Finset.card_union_of_disjoint hdisjBC]
      refine Finset.card_nbij' (fun p => if p.1 = q then p.2 else p.1)
        (fun k => if k.val < q.val then (k, q) else (q, k)) ?_ ?_ ?_ ?_
      · -- forward lands in `B ∪ C`
        intro p hp
        rw [Finset.mem_coe, Finset.mem_filter, hSc, Finset.mem_filter] at hp
        obtain ⟨⟨_, hlt, hc1, hc2, hπ⟩, hq12⟩ := hp
        simp only [not_and_or, not_not] at hq12
        rw [Finset.mem_coe, Finset.mem_union, hBset, hCset]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hp1 : p.1 = q
        · rw [if_pos hp1]
          exact Or.inr ⟨by rw [← hp1]; exact hlt, hc2, by rw [← hp1]; exact hπ⟩
        · have hp2 : p.2 = q := by rcases hq12 with h | h; exacts [absurd h hp1, h]
          rw [if_neg hp1]
          exact Or.inl ⟨by rw [← hp2]; exact hlt, hc1, by rw [← hp2]; exact hπ⟩
      · -- inverse lands in the complementary part
        intro k hk
        rw [Finset.mem_coe, Finset.mem_union, hBset, hCset] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Finset.mem_coe, Finset.mem_filter, hSc, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, not_and_or, not_not]
        have hcq : c q = 1 := hq
        rcases hk with ⟨hkq, hck, hπ⟩ | ⟨hkq, hck, hπ⟩
        · rw [if_pos hkq]
          exact ⟨⟨hkq, hck, hcq, hπ⟩, Or.inr rfl⟩
        · have hkq' : ¬ k.val < q.val := by omega
          rw [if_neg hkq']
          exact ⟨⟨hkq, hcq, hck, hπ⟩, Or.inl rfl⟩
      · -- round trip on the complementary part
        intro p hp
        rw [Finset.mem_coe, Finset.mem_filter, hSc, Finset.mem_filter] at hp
        obtain ⟨⟨_, hlt, _, _, _⟩, hq12⟩ := hp
        simp only [not_and_or, not_not] at hq12
        have hltv : p.1.val < p.2.val := hlt
        dsimp only
        by_cases hp1 : p.1 = q
        · rw [if_pos hp1]
          rw [hp1] at hltv
          rw [if_neg (by omega : ¬ p.2.val < q.val), ← hp1]
        · have hp2 : p.2 = q := by rcases hq12 with h | h; exacts [absurd h hp1, h]
          rw [if_neg hp1, if_pos (by rw [← hp2]; exact hltv), ← hp2]
      · -- round trip on `B ∪ C`
        intro k hk
        rw [Finset.mem_coe, Finset.mem_union, hBset, hCset] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        dsimp only
        rcases hk with ⟨hkq, _, _⟩ | ⟨hkq, _, _⟩
        · rw [if_pos hkq]
          have hkne : k ≠ q := by intro h; rw [h] at hkq; omega
          rw [if_neg (show ((k, q) : Fin (M + 1) × Fin (M + 1)).1 ≠ q from hkne)]
        · rw [if_neg (by omega : ¬ k.val < q.val),
            if_pos (rfl : ((q, k) : Fin (M + 1) × Fin (M + 1)).1 = q)]
    calc Sc.card
        = (Sc.filter (fun p => p.1 ≠ q ∧ p.2 ≠ q)).card
            + (Sc.filter (fun p => ¬ (p.1 ≠ q ∧ p.2 ≠ q))).card :=
          (Finset.card_filter_add_card_filter_not _).symm
      _ = Sc'.card + (Bset.card + Cset.card) := by rw [← hSc'eq, hneg]
  -- assemble the parity identity
  rw [translationJwSign, translationJwSign, ← pow_add, jwSign_eq_neg_one_pow,
    jwSign_eq_neg_one_pow, ← pow_add]
  -- rewrite the four exponents
  have hLHS : (Finset.univ.filter
        (fun p : Fin (M + 1) × Fin (M + 1) => p.1 < p.2 ∧ c p.1 = 1 ∧ c p.2 = 1
          ∧ π p.2 < π p.1)).card
      + (Finset.univ.filter
        (fun p : Fin (M + 1) × Fin (M + 1) => p.1 < p.2
          ∧ (Function.update c q 0) p.1 = 1 ∧ (Function.update c q 0) p.2 = 1
          ∧ π p.2 < π p.1)).card
      = 2 * Sc'.card + (Bset.card + Cset.card) := by
    rw [← hSc, ← hSc', hScard]; ring
  have hRHS : (∑ k ∈ Finset.univ.filter (fun k : Fin (M + 1) => k.val < q.val), ((σ ∘ π) k).val)
      + (∑ m ∈ Finset.univ.filter (fun m : Fin (M + 1) => m.val < (π q).val), (σ m).val)
      = 2 * Aset.card + (Bset.card + Cset.card) := by
    rw [← hc, hEq, hEpq]; ring
  have h2 : ∀ n : ℕ, ((-1 : ℂ)) ^ (2 * n) = 1 := fun n => by rw [pow_mul]; norm_num
  rw [hLHS, hRHS, pow_add (-1 : ℂ) (2 * Sc'.card) (Bset.card + Cset.card),
    pow_add (-1 : ℂ) (2 * Aset.card) (Bset.card + Cset.card), h2, h2]

/-- **The one-mode-update parity law (add to an empty mode).**  For the permuted
configuration `c = σ ∘ π` with `c p = 0`, the product of `translationJwSign π` before and
after setting mode `p` to occupied equals the bare Jordan–Wigner hop signs
`jwSign p (σ∘π) · jwSign (π p) σ`.  Derived from the remove-mode law applied to the lifted
configuration `update σ (π p) 1`. -/
theorem translationJwSign_mul_update_one_comp_eq_jwSign_mul
    (π : Equiv.Perm (Fin (M + 1))) (σ : Fin (M + 1) → Fin 2) (p : Fin (M + 1))
    (hp : (σ ∘ π) p = 0) :
    translationJwSign π (σ ∘ π) * translationJwSign π (Function.update (σ ∘ π) p 1)
      = jwSign M p (σ ∘ π) * jwSign M (π p) σ := by
  -- lift: `update (σ∘π) p 1 = (update σ (π p) 1) ∘ π =: σ'' ∘ π`, occupied at `p`
  set σ'' : Fin (M + 1) → Fin 2 := Function.update σ (π p) 1 with hσ''
  have hlift : Function.update (σ ∘ π) p 1 = σ'' ∘ π := update_comp_perm π σ p 1
  have hocc : (σ'' ∘ π) p = 1 := by rw [← hlift, Function.update_self]
  -- apply the remove-mode law to `σ''`
  have hkey := translationJwSign_mul_update_zero_comp_eq_jwSign_mul π σ'' p hocc
  -- `update (σ''∘π) p 0 = σ ∘ π`
  have hback : Function.update (σ'' ∘ π) p 0 = σ ∘ π := by
    rw [← hlift, Function.update_idem, show (0 : Fin 2) = (σ ∘ π) p from hp.symm,
      Function.update_eq_self]
  -- `jwSign p (σ''∘π) = jwSign p (σ∘π)` (depends only on modes below `p`, unchanged)
  have hjw1 : jwSign M p (σ'' ∘ π) = jwSign M p (σ ∘ π) := by
    rw [← hlift, jwSign_update_eq]
  -- `jwSign (π p) σ'' = jwSign (π p) σ`
  have hjw2 : jwSign M (π p) σ'' = jwSign M (π p) σ := by
    rw [hσ'', jwSign_update_eq]
  rw [hback, hjw1, hjw2] at hkey
  rw [hlift, mul_comm (translationJwSign π (σ ∘ π)) (translationJwSign π (σ'' ∘ π))]
  exact hkey

end LatticeSystem.Fermion
