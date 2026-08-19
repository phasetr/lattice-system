import LatticeSystem.Quantum.SpinS.GeneralSOpenChainBondTerm
import LatticeSystem.Math.PosSemidef.AnnihilatingPolynomial

/-!
# Tasaki §7.3.1: positive semidefiniteness of the general-`S` AKLT bond term

The two-site bond Casimir `Ĉ = bondCasimirS 0 1 N` satisfies the annihilating polynomial
`∏_{J=0}^{N} (Ĉ − J(J+1)) = 0` (its eigenvalue on the spin-`J` bond subspace is exactly `J(J+1)`
for `J = 0,…,N`), with distinct real nodes `J(J+1)`.  Tasaki's penalty polynomial `q_S =
∏_{j=0}^{S}(X − j(j+1))` (eq. (7.3.3), p. 208) has degree `S + 1 < 2S + 1 = N + 1` (the number of
nodes) and is nonnegative at every node (`casimirPenaltyWeight_eq_zero`/`_pos`), so the generic
Lagrange-interpolation route of `Math/PosSemidef/AnnihilatingPolynomial` gives positive
semidefiniteness of the local bond term `localCasimirPenalty S = aeval Ĉ q_S` directly, with no
projection operator named at the spin level.

The global bond term `bondCasimirPenaltyS` inherits positivity from the local one through the
block embedding `onEmbS` (`bondCasimirPenaltyS_eq_onEmbS`, `onEmbS_posSemidef`): no second
annihilating-polynomial argument is needed at the chain level.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.3.1, eqs. (7.3.1)–(7.3.3) and footnote 40, pp. 208–209.
-/

open MvPolynomial Matrix
open scoped ComplexOrder

namespace LatticeSystem.Quantum

open LatticeSystem.Math
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The **Casimir eigenvalue nodes** `r_J = J(J+1)`, `J = 0,…,N`, of the two-site bond Casimir on
`ℂ^{N+1} ⊗ ℂ^{N+1}`. -/
noncomputable def casimirNode (N : ℕ) (J : Fin (N + 1)) : ℝ := (J : ℕ) * ((J : ℕ) + 1)

/-- **The Casimir nodes are pairwise distinct.**  `J ↦ J(J+1)` is strictly increasing on `ℕ`. -/
theorem casimirNode_injective (N : ℕ) : Function.Injective (casimirNode N) := by
  sorry -- dev-implement: `Fin.val` injective + strict monotonicity of `J ↦ J(J+1)`.

/-- **The two-site bond Casimir satisfies `∏_{J=0}^{N} (Ĉ − J(J+1)) = 0`** (§7.3.1,
eqs. (7.3.1)–(7.3.3), p. 208): the annihilating polynomial with nodes `casimirNode N`. -/
theorem aeval_nodal_bondCasimirS (N : ℕ) :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N) (Lagrange.nodal Finset.univ (casimirNode N))
      = 0 := by
  sorry -- dev-implement: `Matrix.ext_of_mulVec_single` + `map_prod` + `List.prod_ofFn`
        -- + `weylMap_mulVec_casimir_list` + `casimirDescentFold_self_eq_zero`
        -- + `weylMap_injective`.

/-- **Tasaki's penalty polynomial** `q_S = ∏_{j=0}^{S} (X − j(j+1))` (eq. (7.3.3), p. 208), whose
`aeval` at the bond Casimir is `localCasimirPenalty S`. -/
noncomputable def casimirPenaltyPoly (S : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range (S + 1), (Polynomial.X - Polynomial.C ((j : ℝ) * (j + 1)))

/-- **`q_S` evaluated at a node equals the scalar weight** `casimirPenaltyWeight S J`. -/
theorem casimirPenaltyPoly_eval (S J : ℕ) :
    (casimirPenaltyPoly S).eval ((J : ℝ) * (J + 1)) = casimirPenaltyWeight S J := by
  sorry -- dev-implement: unfold both sides as `Finset.prod` and match term-by-term.

/-- **`q_S` has degree `S + 1`.**  Load-bearing for `localCasimirPenalty_posSemidef`'s degree
hypothesis; pinned separately so a later change of the index range in `bondCasimirPenaltyS`
breaks the build rather than the mathematics. -/
theorem casimirPenaltyPoly_degree (S : ℕ) : (casimirPenaltyPoly S).degree = (S : ℕ) + 1 := by
  sorry -- dev-implement: `Polynomial.degree_prod` of `S + 1` monic linear factors.

/-- **`aeval` of `q_S` at the bond Casimir is the local bond term.** -/
theorem aeval_casimirPenaltyPoly (S : ℕ) :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 (2 * S)) (casimirPenaltyPoly S)
      = localCasimirPenalty S := by
  sorry -- dev-implement: `casimirPenaltyPoly`, `localCasimirPenalty`, `bondCasimirPenaltyS`,
        -- `map_prod`/`Polynomial.aeval_X_sub_C` unfolded against `List.ofFn … |>.prod`.

/-- **The local general-`S` bond term is positive semidefinite** (Tasaki §7.3.1, eq. (7.3.3),
p. 208): `q_S(Ĉ) ≥ 0`.  Via `posSemidef_aeval_of_aeval_nodal_eq_zero` with the annihilating
polynomial `aeval_nodal_bondCasimirS`, the injective node family `casimirNode_injective`, the
degree bound `casimirPenaltyPoly_degree` (`S + 1 < 2S + 1`, needing `S ≠ 0`), and nonnegativity at
every node from `casimirPenaltyWeight_eq_zero`/`_pos` via `casimirPenaltyPoly_eval`. -/
theorem localCasimirPenalty_posSemidef {S : ℕ} (hS : S ≠ 0) :
    (localCasimirPenalty S).PosSemidef := by
  sorry -- dev-implement: as documented above.

/-- **Every bond term of the chain is positive semidefinite.**  The local positivity above
transported through the block embedding `onEmbS` (`bondCasimirPenaltyS_eq_onEmbS`,
`onEmbS_posSemidef`, `injective_bondEmb`); no global annihilating-polynomial argument is needed. -/
theorem bondCasimirPenaltyS_posSemidef {x y : Λ} (hxy : x ≠ y) {S : ℕ} (hS : S ≠ 0) :
    (bondCasimirPenaltyS x y S).PosSemidef := by
  sorry -- dev-implement: `bondCasimirPenaltyS_eq_onEmbS` + `onEmbS_posSemidef`
        -- + `localCasimirPenalty_posSemidef hS` + `injective_bondEmb hxy`.

end LatticeSystem.Quantum
