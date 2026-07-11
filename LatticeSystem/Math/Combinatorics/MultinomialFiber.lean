/-
Generic multinomial fiber cardinality.

This file proves a purely combinatorial counting identity: for a finite alphabet `ι`, the number of
words `List.ofFn f` (`f : Fin n → ι`) whose letter `i` occurs exactly `k i` times equals the
multinomial coefficient `Nat.multinomial Finset.univ k = n! / ∏ i, (k i)!`
(under the size condition `∑ i, k i = n`).

It generalises the binary special case `card_ofFn_count_true_eq`
(`LatticeSystem/Quantum/SpinS/AndersonTowerTanakaDenominator.lean`), and is consumed by the
Prop 4.10 (Tasaki §4.2.2, p. 108) pinch estimate to convert the per-configuration multiplicity of
order words into the exact multinomial factor needed for the sphere-moment (double-factorial) match.

The proof is an induction on the word length `n`, peeling the first letter `f 0` via
`List.ofFn_succ` and partitioning by its value with `Finset.card_eq_sum_card_fiberwise`; the
per-fibre count is
identified with a decremented multinomial through the `Fin.cons`/`Fin.tail` bijection and the
Pascal-type identity `(∑ k) · multinomial (k − eⱼ) = k j · multinomial k`.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §4.2.2, p. 108,
eqs. (4.2.58)/(4.2.59).
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Count
import Mathlib.Data.Fin.Tuple.Basic

namespace LatticeSystem.Math

open Finset List

/-- **Multinomial Pascal step**: decrementing the count at one occupied letter `j` scales the
multinomial coefficient by `k j / (∑ k)`.  Precisely, for `1 ≤ k j`,
`(∑ i, k i) · multinomial univ (k − eⱼ) = k j · multinomial univ k`, where `k − eⱼ` is
`Function.update k j (k j - 1)`.

Proved without natural-number division by clearing denominators with `Nat.multinomial_spec`: both
sides, multiplied by `∏ i, (k − eⱼ)ᵢ!`, equal `(∑ i, k i)!`. -/
private lemma multinomial_mul_update_pred {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (j : ι) (hj : 1 ≤ k j) :
    (∑ i, k i) * Nat.multinomial univ (Function.update k j (k j - 1))
      = k j * Nat.multinomial univ k := by
  set m := k j - 1 with hm
  have hkj : k j = m + 1 := by omega
  have hP : 0 < ∏ i, (Function.update k j m i).factorial :=
    Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  have herase : ∏ i ∈ univ.erase j, (Function.update k j m i).factorial
      = ∏ i ∈ univ.erase j, (k i).factorial :=
    Finset.prod_congr rfl (fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  have hQP : (∏ i, (k i).factorial) = k j * ∏ i, (Function.update k j m i).factorial := by
    rw [← Finset.mul_prod_erase univ (fun i => (k i).factorial) (Finset.mem_univ j),
      ← Finset.mul_prod_erase univ (fun i => (Function.update k j m i).factorial)
        (Finset.mem_univ j)]
    simp only [Function.update_self]
    rw [herase, hkj, Nat.factorial_succ]
    ring
  have hSU : (∑ i, Function.update k j m i) + 1 = ∑ i, k i := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← Finset.erase_eq,
      ← Finset.add_sum_erase univ k (Finset.mem_univ j)]
    omega
  have specU := Nat.multinomial_spec (univ : Finset ι) (Function.update k j m)
  have specK := Nat.multinomial_spec (univ : Finset ι) k
  set A := ∑ i, Function.update k j m i with hA
  set S := ∑ i, k i with hS
  apply Nat.eq_of_mul_eq_mul_left hP
  calc (∏ i, (Function.update k j m i).factorial)
          * (S * Nat.multinomial univ (Function.update k j m))
      = S * ((∏ i, (Function.update k j m i).factorial)
          * Nat.multinomial univ (Function.update k j m)) := by ring
    _ = S * A.factorial := by rw [specU]
    _ = (A + 1) * A.factorial := by rw [hSU]
    _ = (A + 1).factorial := (Nat.factorial_succ A).symm
    _ = S.factorial := by rw [hSU]
    _ = (∏ i, (k i).factorial) * Nat.multinomial univ k := specK.symm
    _ = (k j * ∏ i, (Function.update k j m i).factorial) * Nat.multinomial univ k := by rw [hQP]
    _ = (∏ i, (Function.update k j m i).factorial) * (k j * Nat.multinomial univ k) := by ring

/-- **Generic multinomial fiber cardinality**: the number of functions `f : Fin n → ι` whose
induced word `List.ofFn f` contains each letter `i` exactly `k i` times equals the multinomial
coefficient `Nat.multinomial univ k`, provided the counts sum to the length (`∑ i, k i = n`).

This generalises `card_ofFn_count_true_eq` (the two-letter/`Bool` case, a binomial coefficient) to
an arbitrary finite alphabet.  The proof inducts on `n`, splitting off the first letter with
`List.ofFn_succ`, grouping the words by the value `f 0` (`Finset.card_eq_sum_card_fiberwise`),
identifying each fibre with a length-`n` count problem via the `Fin.cons`/`Fin.tail` bijection, and
closing with the multinomial Pascal step `multinomial_mul_update_pred`. -/
theorem card_ofFn_count_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (n : ℕ) (k : ι → ℕ), (∑ i, k i) = n →
      (univ.filter (fun f : Fin n → ι => ∀ i, (List.ofFn f).count i = k i)).card
        = Nat.multinomial univ k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : ∀ i, k i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hk) i (Finset.mem_univ i)
    have hfilter :
        (univ.filter (fun f : Fin 0 → ι => ∀ i, (List.ofFn f).count i = k i)) = univ := by
      apply Finset.filter_true_of_mem
      intro f _ i
      simp [List.ofFn_zero, hk0 i]
    have hmul : Nat.multinomial univ k = 1 := by
      rw [Nat.multinomial, hk, Finset.prod_eq_one (fun i _ => by rw [hk0 i, Nat.factorial_zero]),
        Nat.factorial_zero, Nat.div_one]
    rw [hfilter, Finset.card_univ, hmul]
    simp
  | succ n ih =>
    intro k hk
    -- Partition the words by their first letter `f 0`.
    have hpart : (univ.filter (fun f : Fin (n + 1) → ι =>
          ∀ i, (List.ofFn f).count i = k i)).card
        = ∑ j : ι, ((univ.filter (fun f : Fin (n + 1) → ι =>
            (∀ i, (List.ofFn f).count i = k i) ∧ f 0 = j)).card) := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun f : Fin (n + 1) → ι => f 0) (t := univ)
        (fun f _ => Finset.mem_univ _)]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.filter_filter])
    -- Per-fibre count, scaled by `n + 1`.
    have hfib : ∀ j : ι, (n + 1) * (univ.filter (fun f : Fin (n + 1) → ι =>
          (∀ i, (List.ofFn f).count i = k i) ∧ f 0 = j)).card
        = k j * Nat.multinomial univ k := by
      intro j
      by_cases hj : k j = 0
      · -- If `k j = 0` the fibre is empty: `f 0 = j` forces `count j ≥ 1`.
        have hempty : (univ.filter (fun f : Fin (n + 1) → ι =>
            (∀ i, (List.ofFn f).count i = k i) ∧ f 0 = j)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro F _ hF
          obtain ⟨hcount, hf0⟩ := hF
          have h1 : (List.ofFn F).count j = 0 := by rw [hcount j, hj]
          have hmem : j ∈ List.ofFn F := List.mem_ofFn.mpr ⟨0, hf0⟩
          exact absurd (List.count_pos_iff.mpr hmem) (by omega)
        rw [hempty, hj]; ring
      · -- If `k j ≥ 1`, the fibre biject with length-`n` words of the decremented counts.
        have hjpos : 1 ≤ k j := Nat.one_le_iff_ne_zero.mpr hj
        have hsum : (∑ i, Function.update k j (k j - 1) i) = n := by
          have e : (∑ i, Function.update k j (k j - 1) i) + 1 = ∑ i, k i := by
            rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← Finset.erase_eq,
              ← Finset.add_sum_erase univ k (Finset.mem_univ j)]
            omega
          omega
        have hcard : (univ.filter (fun f : Fin (n + 1) → ι =>
            (∀ i, (List.ofFn f).count i = k i) ∧ f 0 = j)).card
            = Nat.multinomial univ (Function.update k j (k j - 1)) := by
          rw [← ih (Function.update k j (k j - 1)) hsum]
          apply Finset.card_nbij'
            (fun f : Fin (n + 1) → ι => fun x : Fin n => f x.succ)
            (fun g => Fin.cons j g)
          · -- forward map lands in the length-`n` fibre
            intro F hF
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hF ⊢
            obtain ⟨hcount, hf0⟩ := hF
            intro i
            have hFc : (List.ofFn F).count i = k i := hcount i
            rw [List.ofFn_succ, List.count_cons, hf0] at hFc
            by_cases hij : i = j
            · subst hij
              rw [Function.update_self]
              simp only [beq_self_eq_true, if_true] at hFc
              omega
            · rw [Function.update_of_ne hij]
              rw [if_neg (by simpa using Ne.symm hij)] at hFc
              simpa using hFc
          · -- backward map lands in the original fibre
            intro g hg
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hg ⊢
            refine ⟨fun i => ?_, Fin.cons_zero _ _⟩
            rw [List.ofFn_succ, List.count_cons]
            have hc0 : (Fin.cons j g : Fin (n + 1) → ι) 0 = j := Fin.cons_zero _ _
            have hcs : (fun x : Fin n => (Fin.cons j g : Fin (n + 1) → ι) x.succ) = g :=
              funext (fun x => Fin.cons_succ _ _ _)
            rw [hc0, hcs, hg i]
            by_cases hij : i = j
            · subst hij
              rw [Function.update_self, if_pos (by simp)]; omega
            · rw [Function.update_of_ne hij, if_neg (by simpa using Ne.symm hij), add_zero]
          · -- left inverse
            intro F hF
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hF
            rw [← hF.2]
            exact Fin.cons_self_tail F
          · -- right inverse
            intro g _
            funext x
            exact Fin.cons_succ _ _ _
        rw [hcard]
        have hstep := multinomial_mul_update_pred k j hjpos
        rw [hk] at hstep
        exact hstep
    -- Assemble: `(n+1) · #words = (∑ k) · multinomial = (n+1) · multinomial`, then cancel.
    have hfinal : (n + 1) * (univ.filter (fun f : Fin (n + 1) → ι =>
          ∀ i, (List.ofFn f).count i = k i)).card
        = (n + 1) * Nat.multinomial univ k := by
      rw [hpart, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun j _ => hfib j), ← Finset.sum_mul, hk]
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) hfinal

end LatticeSystem.Math
