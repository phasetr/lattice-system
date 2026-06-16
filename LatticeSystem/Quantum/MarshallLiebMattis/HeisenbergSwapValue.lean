import LatticeSystem.Quantum.MarshallLiebMattis.SpinDotOffBond

set_option linter.unusedSectionVars false

/-!
# Heisenberg matrix entry on swap-related configurations

This module assembles the **explicit value** of the Heisenberg
matrix entry between configurations related by a single bond swap:

  `(heisenbergHamiltonian J) σ (basisSwap σ x y) = (J x y + J y x) / 2`

for `x ≠ y` and antiparallel `σ_x ≠ σ_y`.

Decomposition `H = Σ_{u, v} J u v · spinHalfDot u v` gives the
double-sum form. By the building blocks of PRs α-5e and α-5g, only
the pairs `(u, v) ∈ {(x, y), (y, x)}` contribute, each with value
`J(·, ·) · 1/2`. Summing yields the displayed formula.

For symmetric `J`, the formula simplifies to `J x y` exactly
(not stated here separately).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

omit [Fintype Λ] in
/-- `basisSwap` is symmetric in the two site arguments:
`basisSwap σ x y = basisSwap σ y x`. -/
private theorem basisSwap_swap_args (σ : Λ → Fin 2) {x y : Λ} (hxy : x ≠ y) :
    basisSwap σ x y = basisSwap σ y x := by
  unfold basisSwap
  rw [Function.update_comm hxy.symm]

/-- For `(u, v) ≠ (a, b)` (as ordered pairs),
`Σ_v ite (u = a ∧ v = b) c 0 = ite (u = a) c 0` after summing over `v`. -/
private theorem sum_ite_pair_eq_single (a b : Λ) (c : ℂ) (u : Λ) :
    (∑ v : Λ, (if u = a ∧ v = b then c else 0)) = if u = a then c else 0 := by
  by_cases hua : u = a
  · rw [if_pos hua]
    rw [show (∑ v : Λ, (if u = a ∧ v = b then c else 0)) =
            (∑ v : Λ, (if v = b then c else 0)) from ?_]
    · rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    · refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hvb : v = b
      · rw [if_pos ⟨hua, hvb⟩, if_pos hvb]
      · rw [if_neg (fun ⟨_, hh⟩ => hvb hh), if_neg hvb]
  · rw [if_neg hua]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [if_neg (fun ⟨hh, _⟩ => hua hh)]

/-- Summing the indicator `ite (u = a ∧ v = b) c 0` over both `u` and `v`
collapses to `c`. -/
private theorem sum_sum_ite_pair (a b : Λ) (c : ℂ) :
    (∑ u : Λ, ∑ v : Λ, (if u = a ∧ v = b then c else 0)) = c := by
  rw [show (fun (u : Λ) => ∑ v : Λ, (if u = a ∧ v = b then c else 0)) =
          (fun u : Λ => if u = a then c else 0) from ?_]
  · rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  · funext u; exact sum_ite_pair_eq_single a b c u

/-- The Heisenberg Hamiltonian matrix entry on swap-related configurations.

For `x ≠ y` and antiparallel `σ_x ≠ σ_y`,
`(heisenbergHamiltonian J) σ (basisSwap σ x y) = (J x y + J y x) / 2`. -/
theorem heisenbergHamiltonian_apply_basisSwap
    (J : Λ → Λ → ℂ) {x y : Λ} (hxy : x ≠ y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    (heisenbergHamiltonian J) σ (basisSwap σ x y) =
      (J x y + J y x) / 2 := by
  -- Per-pair value formula.
  have hpair : ∀ u v : Λ,
      J u v * (spinHalfDot u v) σ (basisSwap σ x y) =
      (if u = x ∧ v = y then J x y * (1 / 2 : ℂ) else 0) +
      (if u = y ∧ v = x then J y x * (1 / 2 : ℂ) else 0) := by
    intro u v
    by_cases hxy_pair : u = x ∧ v = y
    · obtain ⟨hux, hvy⟩ := hxy_pair
      subst hux; subst hvy
      rw [spinHalfDot_apply_basisSwap hxy h]
      rw [if_pos ⟨rfl, rfl⟩]
      rw [if_neg (by rintro ⟨_, hxy_eq⟩; exact hxy hxy_eq.symm)]
      ring
    · by_cases hyx_pair : u = y ∧ v = x
      · obtain ⟨huy, hvx⟩ := hyx_pair
        subst huy; subst hvx
        rw [basisSwap_swap_args σ hxy,
            spinHalfDot_apply_basisSwap hxy.symm h.symm]
        rw [if_neg hxy_pair]
        rw [if_pos ⟨rfl, rfl⟩]
        ring
      · -- Off-bond case: spinHalfDot value is 0.
        have hbond : ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) := by
          rintro (h1 | h2)
          · exact hxy_pair h1
          · exact hyx_pair h2
        rw [spinHalfDot_apply_basisSwap_off_bond_eq_zero hxy h hbond]
        rw [if_neg hxy_pair, if_neg hyx_pair, mul_zero, add_zero]
  -- Decomposition of H entry as a double sum.
  have hdecomp : (heisenbergHamiltonian J) σ (basisSwap σ x y) =
      ∑ u : Λ, ∑ v : Λ, J u v * (spinHalfDot u v) σ (basisSwap σ x y) := by
    unfold heisenbergHamiltonian
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [hdecomp]
  -- Apply per-pair value formula.
  rw [show (∑ u : Λ, ∑ v : Λ, J u v * (spinHalfDot u v) σ (basisSwap σ x y)) =
      ∑ u : Λ, ∑ v : Λ,
        ((if u = x ∧ v = y then J x y * (1 / 2 : ℂ) else 0) +
         (if u = y ∧ v = x then J y x * (1 / 2 : ℂ) else 0)) from
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hpair u v]
  -- Split the (a + b) sum into separate sums.
  rw [show (∑ u : Λ, ∑ v : Λ,
        ((if u = x ∧ v = y then J x y * (1 / 2 : ℂ) else 0) +
         (if u = y ∧ v = x then J y x * (1 / 2 : ℂ) else 0))) =
      (∑ u : Λ, ∑ v : Λ,
        (if u = x ∧ v = y then J x y * (1 / 2 : ℂ) else 0)) +
      (∑ u : Λ, ∑ v : Λ,
        (if u = y ∧ v = x then J y x * (1 / 2 : ℂ) else 0)) from ?_]
  · -- Each indicator sum collapses via sum_sum_ite_pair.
    rw [sum_sum_ite_pair x y (J x y * (1 / 2 : ℂ))]
    rw [sum_sum_ite_pair y x (J y x * (1 / 2 : ℂ))]
    ring
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]

end LatticeSystem.Quantum
