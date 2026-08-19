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
  have hmono : StrictMono fun k : ℕ => (k : ℝ) * ((k : ℝ) + 1) := by
    intro a b hab
    have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have hnn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  intro i j hij
  exact Fin.val_injective (hmono.injective hij)

/-- **The two-site bond Casimir satisfies `∏_{J=0}^{N} (Ĉ − J(J+1)) = 0`** (§7.3.1,
eqs. (7.3.1)–(7.3.3), p. 208): the annihilating polynomial with nodes `casimirNode N`. -/
theorem aeval_nodal_bondCasimirS (N : ℕ) :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N) (Lagrange.nodal Finset.univ (casimirNode N))
      = 0 := by
  set bs : List ℂ := List.ofFn fun J : Fin (N + 1) => ((J : ℕ) : ℂ) * (((J : ℕ) : ℂ) + 1)
    with hbs
  have hprod : Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N)
      (Lagrange.nodal Finset.univ (casimirNode N))
      = (bs.map fun b =>
          bondCasimirS (0 : Fin 2) 1 N - b • (1 : ManyBodyOpS (Fin 2) N)).prod := by
    rw [Lagrange.nodal_eq, ← List.prod_ofFn, map_list_prod, List.map_ofFn, hbs, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun J => ?_))
    have hc : (algebraMap ℝ ℂ) (casimirNode N J) = ((J : ℕ) : ℂ) * (((J : ℕ) : ℂ) + 1) := by
      change ((casimirNode N J : ℝ) : ℂ) = _
      simp only [casimirNode]
      push_cast
      ring
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      IsScalarTower.algebraMap_apply ℝ ℂ (ManyBodyOpS (Fin 2) N), Algebra.algebraMap_eq_smul_one,
      hc]
  have hscal : (bs.map fun b => ((N : ℕ) : ℂ) * (((N : ℕ) : ℂ) + 1) - b)
      = casimirPenaltyScalars N N := by
    rw [hbs, casimirPenaltyScalars, List.map_ofFn]
    rfl
  have hzero : ∀ φ : (Fin 2 → Fin (N + 1)) → ℂ,
      (Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N)
        (Lagrange.nodal Finset.univ (casimirNode N))).mulVec φ = 0 := by
    intro φ
    have hfold := weylMap_mulVec_casimir_list N bs φ
    rw [hscal] at hfold
    have hhom := weylMap_isWeightedHomogeneous (L := 2) φ
    rw [show (∑ x : Fin 2, Finsupp.single x N : Fin 2 →₀ ℕ)
        = Finsupp.single 0 N + Finsupp.single 1 N by rw [Fin.sum_univ_two]] at hhom
    rw [casimirDescentFold_self_eq_zero hhom] at hfold
    rw [hprod]
    exact weylMap_injective (by rw [hfold, map_zero])
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [Matrix.zero_mulVec]
  exact hzero _

/-- **Tasaki's penalty polynomial** `q_S = ∏_{j=0}^{S} (X − j(j+1))` (eq. (7.3.3), p. 208), whose
`aeval` at the bond Casimir is `localCasimirPenalty S`. -/
noncomputable def casimirPenaltyPoly (S : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range (S + 1), (Polynomial.X - Polynomial.C ((j : ℝ) * (j + 1)))

/-- **`q_S` evaluated at a node equals the scalar weight** `casimirPenaltyWeight S J`. -/
theorem casimirPenaltyPoly_eval (S J : ℕ) :
    (casimirPenaltyPoly S).eval ((J : ℝ) * (J + 1)) = casimirPenaltyWeight S J := by
  rw [casimirPenaltyPoly, casimirPenaltyWeight, Polynomial.eval_prod]
  simp

/-- **`q_S` has degree `S + 1`.**  Load-bearing for `localCasimirPenalty_posSemidef`'s degree
hypothesis; pinned separately so a later change of the index range in `bondCasimirPenaltyS`
breaks the build rather than the mathematics. -/
theorem casimirPenaltyPoly_degree (S : ℕ) : (casimirPenaltyPoly S).degree = (S : ℕ) + 1 := by
  rw [casimirPenaltyPoly, Polynomial.degree_prod,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.range (S + 1)) =>
      Polynomial.degree_X_sub_C ((j : ℝ) * ((j : ℝ) + 1))]
  simp

/-- **`aeval` of `q_S` at the bond Casimir is the local bond term.** -/
theorem aeval_casimirPenaltyPoly (S : ℕ) :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 (2 * S)) (casimirPenaltyPoly S)
      = localCasimirPenalty S := by
  rw [casimirPenaltyPoly, localCasimirPenalty, bondCasimirPenaltyS,
    ← Fin.prod_univ_eq_prod_range
      (fun j : ℕ => Polynomial.X - Polynomial.C ((j : ℝ) * ((j : ℝ) + 1))) (S + 1),
    ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
  have hc : (algebraMap ℝ ℂ) (((j : ℕ) : ℝ) * (((j : ℕ) : ℝ) + 1))
      = ((j : ℕ) : ℂ) * (((j : ℕ) : ℂ) + 1) := by
    change ((((j : ℕ) : ℝ) * (((j : ℕ) : ℝ) + 1) : ℝ) : ℂ) = _
    push_cast
    ring
  simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    IsScalarTower.algebraMap_apply ℝ ℂ (ManyBodyOpS (Fin 2) (2 * S)),
    Algebra.algebraMap_eq_smul_one, hc]

/-- **The local general-`S` bond term is positive semidefinite** (Tasaki §7.3.1, eq. (7.3.3),
p. 208): `q_S(Ĉ) ≥ 0`.  Via `posSemidef_aeval_of_aeval_nodal_eq_zero` with the annihilating
polynomial `aeval_nodal_bondCasimirS`, the injective node family `casimirNode_injective`, the
degree bound `casimirPenaltyPoly_degree` (`S + 1 < 2S + 1`, needing `S ≠ 0`), and nonnegativity at
every node from `casimirPenaltyWeight_eq_zero`/`_pos` via `casimirPenaltyPoly_eval`. -/
theorem localCasimirPenalty_posSemidef {S : ℕ} (hS : S ≠ 0) :
    (localCasimirPenalty S).PosSemidef := by
  rw [← aeval_casimirPenaltyPoly S]
  refine posSemidef_aeval_of_aeval_nodal_eq_zero (bondCasimirS_isHermitian _ _ _)
    (casimirNode_injective (2 * S)) (aeval_nodal_bondCasimirS (2 * S)) ?_ fun J => ?_
  · rw [casimirPenaltyPoly_degree, Fintype.card_fin]
    exact_mod_cast Nat.cast_lt.mpr (by omega : S + 1 < 2 * S + 1)
  · rw [casimirNode, casimirPenaltyPoly_eval]
    rcases le_or_gt (J : ℕ) S with h | h
    · exact (casimirPenaltyWeight_eq_zero h).ge
    · exact (casimirPenaltyWeight_pos h).le

/-- **Every bond term of the chain is positive semidefinite.**  The local positivity above
transported through the block embedding `onEmbS` (`bondCasimirPenaltyS_eq_onEmbS`,
`onEmbS_posSemidef`, `injective_bondEmb`); no global annihilating-polynomial argument is needed. -/
theorem bondCasimirPenaltyS_posSemidef {x y : Λ} (hxy : x ≠ y) {S : ℕ} (hS : S ≠ 0) :
    (bondCasimirPenaltyS x y S).PosSemidef := by
  rw [bondCasimirPenaltyS_eq_onEmbS hxy]
  exact onEmbS_posSemidef (injective_bondEmb hxy) (localCasimirPenalty_posSemidef hS)

end LatticeSystem.Quantum
