import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCorrelation

/-!
# Lieb's ferrimagnetism: the staggered order parameter (Tasaki §10.2.3, Theorem 10.6)

This file formalizes the statement of **Tasaki Theorem 10.6** (Shen, Qiu,
and Tian's ferrimagnetism bound; Hal Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3, p. 356,
eqs. (10.2.16)/(10.2.17)): for the repulsive Hubbard model at half-filling
(Theorem 10.4), the squared staggered magnetization order parameter has a
ground-state expectation bounded below by `((|A| − |B|)/2)²`:

  `⟨ΦGS| (Ô_L)² |ΦGS⟩ ≥ ((|A| − |B|)/2)²`,   `(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y`,

where `ε_x = +1` on `A` and `−1` on `B`. The left-hand side is independent
of the choice of ground state. This exhibits ferrimagnetic long-range order.

## Status

Tasaki proves this exactly as Theorem 4.4 (Tasaki, 1st ed., Springer 2020,
§10.2.3, p. 356, the paragraph immediately preceding Theorem 10.6), building on
**both** Theorem 10.4 (`theorem_10_4_lieb_repulsive_half_filling`) and inequality
(10.2.7) — Theorem 10.5's transverse-correlation sign
(`theorem_10_5_shen_qiu_tian_transverse_sign`), used in place of the spin-`S`
argument's (4.1.15) — **not** on reflection positivity: reflection positivity is
Theorem 10.4's own proof method, and Theorem 10.6 reuses Theorem 10.4's
already-discharged ground subspace together with Theorem 10.5's correlation-sign
step. This is currently an `axiom` pending discharge (Issue #5347), reusing the
packaged model hypotheses `IsLiebRepulsiveModel` and the ground subspace from
`LiebRepulsive.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The squared staggered magnetization order parameter
`(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` (Tasaki eq. (10.2.16)), where the
staggered sign `ε_x` is `+1` on the sublattice `A` and `−1` on `B = Aᶜ`. -/
noncomputable def fermionStaggeredCasimirOp (N : ℕ) (A : Finset (Fin (N + 1))) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
    ((if x ∈ A then (1 : ℂ) else -1) * (if y ∈ A then (1 : ℂ) else -1)) •
      fermionSpinDot N x y

/-- **Tasaki Theorem 10.6** (Shen–Qiu–Tian ferrimagnetism; 1st ed., Springer
2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17), **AXIOM**). Under the
hypotheses of Theorem 10.4, every normalized ground state `v` of the
repulsive Hubbard model satisfies the ferrimagnetic order-parameter bound

  `⟨v| (Ô_L)² |v⟩ ≥ ((|A| − |B|)/2)²`.

(The book also notes the left-hand side is independent of the ground state.)
Proved via Theorem 10.4, exactly as Theorem 4.4 (not reflection positivity); recorded
as an axiom pending discharge (Issue #5347). -/
axiom theorem_10_6_lieb_ferrimagnetism
    (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2)))
    (hModel : IsLiebRepulsiveModel A T H)
    (E₀ : ℂ)
    (hGS_ne : hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1) ≠ ⊥)
    (hMin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ≠ ⊥ →
      E₀.re ≤ E.re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1))
    (hnorm : dotProduct (star v) v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re

end LatticeSystem.Fermion
