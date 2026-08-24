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
ground subspace together with Theorem 10.5's correlation-sign step.

This file keeps the order parameter `fermionStaggeredCasimirOp` itself, which the
whole proof chain is stated in terms of and therefore imports. The theorem
`theorem_10_6_lieb_ferrimagnetism` lives at the far end of that chain, in
`LiebFerrimagnetismDischarge.lean`, together with the assembly of Theorems 10.4
and 10.5 that proves it; it reuses the packaged model hypotheses
`IsLiebRepulsiveModel` and the ground subspace from `LiebRepulsive.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

/-- The squared staggered magnetization order parameter
`(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` (Tasaki eq. (10.2.16)), where the
staggered sign `ε_x` is `+1` on the sublattice `A` and `−1` on `B = Aᶜ`. -/
noncomputable def fermionStaggeredCasimirOp (N : ℕ) (A : Finset (Fin (N + 1))) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
    ((if x ∈ A then (1 : ℂ) else -1) * (if y ∈ A then (1 : ℂ) else -1)) •
      fermionSpinDot N x y

end LatticeSystem.Fermion
