/-
Weighted binomial fiber sum over site configurations.

For a finite site set `V` and a one-site alphabet `Fin (N + 1)`, summing the product weight
`∏ x, binom N (σ x)` over the fiber `{σ | ∑ x, σ x = k}` collapses to the single binomial
coefficient `binom (|V| · N) k`.  This is the `|V|`-fold Vandermonde convolution, obtained by
comparing the `k`-th coefficient of `(1 + X)^{|V|N} = ∏_{x ∈ V} (1 + X)^N` after expanding each
factor by the binomial theorem.

It is the combinatorial input that turns the site-product Clebsch–Gordan weights `√(binom N ·)` of
a spin-`S` ladder iterate into the global binomial `binom (|V|N) k` of the magnetisation sector, so
it carries no spin or lattice content and is stated for a bare configuration type.  Its
unweighted binary special case is `card_ofFn_count_true_eq`
(`LatticeSystem/Quantum/SpinS/AndersonTowerTanakaDenominator.lean`), which counts configurations
instead of weighting them.
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators

namespace LatticeSystem.Math

/-- **Binomial theorem in the `Fin (N + 1)`-indexed form.**  The `N`-th power of `1 + X` over `ℕ`
expands into the `N + 1` terms `binom N j · X^j` indexed by `j : Fin (N + 1)`, i.e. exactly the
one-site alphabet of a spin-`S` configuration.  Proved by comparing coefficients. -/
private lemma one_add_X_pow_eq_sum (N : ℕ) :
    ((1 + Polynomial.X : Polynomial ℕ)) ^ N
      = ∑ j : Fin (N + 1), Polynomial.C (N.choose j.val) * Polynomial.X ^ j.val := by
  ext m
  rw [Polynomial.coeff_one_add_X_pow, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Nat.cast_id]
  by_cases hm : m ≤ N
  · rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (N + 1))]
    · rw [if_pos rfl]
    · intro b _ hb
      exact if_neg fun hbm => hb (Fin.ext hbm.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    refine if_neg fun hj => hm ?_
    have hjN : (j : ℕ) < N + 1 := j.isLt
    omega

/-- **Weighted fiber sum of binomial site weights** (the `|V|`-fold Vandermonde convolution):
summing `∏ x, binom N (σ x)` over all configurations `σ : V → Fin (N + 1)` of fixed total index
`∑ x, σ x = k` gives `binom (|V| · N) k`.

The proof expands `(1 + X)^{|V| N} = ∏_{x ∈ V} (1 + X)^N` over `ℕ[X]`, distributes the product of
the `N + 1`-term binomial expansions into a sum over configurations, and reads off the coefficient
of `X^k` on both sides. -/
theorem sum_prod_choose_fiber (V : Type*) [Fintype V] [DecidableEq V] (N k : ℕ) :
    ∑ σ ∈ Finset.univ.filter (fun σ : V → Fin (N + 1) => ∑ x, (σ x).val = k),
        ∏ x, N.choose (σ x).val
      = (Fintype.card V * N).choose k := by
  have key : ((1 + Polynomial.X : Polynomial ℕ)) ^ (Fintype.card V * N)
      = ∑ σ : V → Fin (N + 1),
          Polynomial.C (∏ x, N.choose (σ x).val) * Polynomial.X ^ (∑ x, (σ x).val) := by
    calc ((1 + Polynomial.X : Polynomial ℕ)) ^ (Fintype.card V * N)
        = ∏ _x : V, ((1 + Polynomial.X : Polynomial ℕ)) ^ N := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm]
      _ = ∏ _x : V, ∑ j : Fin (N + 1), Polynomial.C (N.choose j.val) * Polynomial.X ^ j.val :=
          Finset.prod_congr rfl fun _ _ => one_add_X_pow_eq_sum N
      _ = ∑ σ ∈ Fintype.piFinset fun _ : V => (Finset.univ : Finset (Fin (N + 1))),
            ∏ x : V, Polynomial.C (N.choose (σ x).val) * Polynomial.X ^ (σ x).val :=
          Finset.prod_univ_sum _ _
      _ = ∑ σ : V → Fin (N + 1),
            Polynomial.C (∏ x, N.choose (σ x).val) * Polynomial.X ^ (∑ x, (σ x).val) := by
          rw [Fintype.piFinset_univ]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  have hcoeff := congrArg (fun p : Polynomial ℕ => p.coeff k) key
  simp only [Polynomial.coeff_one_add_X_pow, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Nat.cast_id] at hcoeff
  rw [Finset.sum_filter, hcoeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∑ x, (σ x).val = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun hc => h hc.symm]

end LatticeSystem.Math
