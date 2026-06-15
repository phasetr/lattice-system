import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsive

/-!
# Lieb–Shen–Qiu superconductivity: off-diagonal long-range order (Tasaki §10.2.3, Theorem 10.8)

This file formalizes the statement of **Tasaki Theorem 10.8** (Lieb–Shen–Qiu
superconductivity; Hal Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer 2020, §10.2.3, p. 359, eq. (10.2.22)): for the
attractive Hubbard model on a bipartite lattice, the unique ground state
(Theorem 10.2) exhibits off-diagonal long-range order of the fermion-pair
operator,

  `⟨ΦGS| b̂† b̂ |ΦGS⟩ ≥ (|A| − N/2)(N/2 − |B|)`,   `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}`,

whenever the (even) electron number `N` satisfies `2|B| ≤ N ≤ 2|A|`. The
positivity of this pair correlation is the standard criterion for
superconductivity (condensation of fermion pairs).

## Status

Theorem 10.8 rests on Lieb's spin-space reflection-positivity method
(Shen–Qiu–Tian extension) and the uniqueness of the attractive-Hubbard ground
state (Theorem 10.2); per the project policy it is recorded as a faithful
documented `axiom`, built on the concrete attractive Hubbard Hamiltonian and
the total pair operator, reusing `IsLiebRepulsiveModel`-style bipartition
vocabulary and the `EuclideanSpace` ground-state representation of Theorem 10.2.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The total on-site pair annihilation operator `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}`
(Tasaki eq. (10.2.22)). -/
noncomputable def totalPairAnnihilationOperator (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), fermionDownAnnihilation N x * fermionUpAnnihilation N x

/-- The total on-site pair creation operator `b̂† = Σ_x ĉ†_{x,↑} ĉ†_{x,↓}`,
the adjoint of `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}` (the creation factors are written in
the order `ĉ†_↑ ĉ†_↓`, the genuine adjoint of `ĉ_↓ ĉ_↑`). -/
noncomputable def totalPairCreationOperator (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), fermionUpCreation N x * fermionDownCreation N x

/-- The off-diagonal-long-range-order observable `b̂† b̂` of Theorem 10.8. -/
noncomputable def totalPairCorrelationOperator (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  totalPairCreationOperator N * totalPairAnnihilationOperator N

/-- The lower bound `(|A| − N/2)(N/2 − |B|)` of Theorem 10.8 (eq. (10.2.22)). -/
noncomputable def liebShenQiuPairLowerBound (A : Finset (Fin (N + 1))) (Ne : ℕ) : ℝ :=
  ((A.card : ℝ) - (Ne : ℝ) / 2) * ((Ne : ℝ) / 2 - ((bipartitionComplement A).card : ℝ))

/-- **Tasaki Theorem 10.8** (Lieb–Shen–Qiu superconductivity; 1st ed., Springer
2020, §10.2.3, p. 359, eq. (10.2.22), **AXIOM**). For the attractive Hubbard
model with a bipartite (`Λ = A ⊔ B`) real symmetric connected hopping matrix
`T` and site-dependent attraction `U_x > 0`, and an even electron number `N`
with `2|B| ≤ N ≤ 2|A|`, the unique ground state `φ` (Theorem 10.2) satisfies the
pair off-diagonal-long-range-order bound

  `⟨φ| b̂† b̂ |φ⟩ ≥ (|A| − N/2)(N/2 − |B|)`,

with `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}`. The strictly positive regime exhibits
condensation of fermion pairs (superconductivity). Recorded as a faithful
documented axiom (Lieb's reflection positivity, Shen–Qiu–Tian). -/
axiom theorem_10_8_lieb_shen_qiu_superconductivity (N Ne : ℕ)
    (A : Finset (Fin (N + 1)))
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne)
    (hLower : 2 * (bipartitionComplement A).card ≤ Ne) (hUpper : Ne ≤ 2 * A.card)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x)
    (hT_bip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N T U) E φ) :
    liebShenQiuPairLowerBound A Ne ≤
        (euclideanExpectation (totalPairCorrelationOperator N) φ).re ∧
      (euclideanExpectation (totalPairCorrelationOperator N) φ).im = 0

end LatticeSystem.Fermion
