import LatticeSystem.Math.PosSemidef.AnnihilatingPolynomial
import LatticeSystem.Quantum.SpinS.GeneralSCasimirSpectrum

/-!
# Positivity of the general-`S` AKLT bond term

Regression gate for the annihilating-polynomial positivity route: the generic Lagrange-based
lemma `Math/PosSemidef/AnnihilatingPolynomial.posSemidef_aeval_of_aeval_nodal_eq_zero`, and its
AKLT instantiation in `Quantum.GeneralSCasimirSpectrum` (`bondCasimirS_isHermitian`, `casimirNode`,
`aeval_nodal_bondCasimirS`, `casimirPenaltyPoly`, `localCasimirPenalty_posSemidef`,
`bondCasimirPenaltyS_posSemidef`).  No production code is written here.

This file pins the exact signatures of those declarations together with the numeric identities the
argument depends on.

Four groups:

1. **Generic-lemma oracle** — a fully worked `n = ι = Fin 1` instance of
   `posSemidef_aeval_of_aeval_nodal_eq_zero`, independent of the AKLT context.
2. **`N = 1` annihilating-polynomial oracle** — `casimirNode`'s nodal factorization at the
   smallest nontrivial case, `X (X − 2)`, together with the matrix-layer statement it certifies:
   `Ĉ (Ĉ − 2) = 0` for the two-site bond Casimir, which exercises `bondCasimirS`, `weylMap` and
   the descent fold rather than `Polynomial` alone.
3. **`S = 1` positivity oracle** — `localCasimirPenalty 1` is PSD both via the new
   `localCasimirPenalty_posSemidef` and, independently, via `bondCasimirPenaltyS_one` +
   `bondSpin2ProjectionS_posSemidef` (`24 • P̂₂ ≥ 0`); the two routes must prove the *same*
   proposition.
4. **Signature pins** for the remaining new declarations, including the `hdeg`-load-bearing
   `casimirPenaltyPoly_degree` (a later change of the index range in `bondCasimirPenaltyS` must
   break this pin, not silently pass).
-/

open MvPolynomial Matrix LatticeSystem.Math LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

namespace LatticeSystem.Tests.GeneralSCasimirPositivity

/-! ## Group 1: generic-lemma oracle (`n = ι = Fin 1`) -/

/-- **Generic-lemma oracle.**  `A = 0` on a single site annihilates its own single node
`r 0 = 0` (`aeval A X = A = 0`), and the constant polynomial `q = C 1` has degree `0 < 1 = card ι`
and is nonnegative (`= 1`) at that node, so `aeval A q` must be positive semidefinite — a fact that
does not depend on any AKLT-specific data. -/
example :
    (Polynomial.aeval (0 : Matrix (Fin 1) (Fin 1) ℂ) (Polynomial.C (1 : ℝ))).PosSemidef :=
  posSemidef_aeval_of_aeval_nodal_eq_zero
    (A := (0 : Matrix (Fin 1) (Fin 1) ℂ)) Matrix.isHermitian_zero
    (r := fun _ : Fin 1 => (0 : ℝ)) (Function.injective_of_subsingleton _)
    (by simp [Lagrange.nodal_eq])
    (q := Polynomial.C (1 : ℝ))
    (by
      rw [Polynomial.degree_C (by norm_num : (1 : ℝ) ≠ 0), Fintype.card_fin]
      exact_mod_cast (by norm_num : (0 : ℕ) < 1))
    (fun _ => by norm_num)

/-! ## Group 2: `N = 1` annihilating-polynomial oracle -/

/-- **`N = 1` node-polynomial pin.**  At `N = 1` (two spin-`1/2` sites) the nodal polynomial of
`casimirNode` is exactly `X (X − 2)`, the smallest nontrivial instance of the Casimir eigenvalue
family of Tasaki §7.3.1, eq. (7.3.1), p. 208.  A pure `Polynomial` computation, independent of the
bond-Casimir matrix layer. -/
private theorem nodal_casimirNode_one :
    Lagrange.nodal (Finset.univ : Finset (Fin 2)) (casimirNode 1)
      = Polynomial.X * (Polynomial.X - Polynomial.C (2 : ℝ)) := by
  rw [Lagrange.nodal_eq, Fin.prod_univ_two]
  norm_num [casimirNode]

/-- **`N = 1` matrix-layer oracle.**  The concrete content of the annihilating polynomial at the
smallest nontrivial case: the two-site bond Casimir satisfies `Ĉ (Ĉ − 2) = 0` (eigenvalue `0` on
the singlet, `2` on the triplet; Tasaki §7.3.1, eq. (7.3.1), p. 208).  Unlike the node-polynomial
pin above, this evaluates the annihilating polynomial on the matrix layer, so it exercises
`bondCasimirS`, `weylMap` and the descent fold. -/
example :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 1)
        (Polynomial.X * (Polynomial.X - Polynomial.C (2 : ℝ))) = 0 := by
  rw [← nodal_casimirNode_one]
  exact aeval_nodal_bondCasimirS 1

/-! ## Group 3: `S = 1` positivity oracle -/

/-- **`S = 1` positivity oracle, independent route.**  `localCasimirPenalty 1 = 24 •
bondSpin2ProjectionS 0 1` (`bondCasimirPenaltyS_one`), and `24 ≥ 0` scales a positive-semidefinite
matrix (`bondSpin2ProjectionS_posSemidef`) to a positive-semidefinite one. -/
example : (localCasimirPenalty 1).PosSemidef := by
  rw [localCasimirPenalty, bondCasimirPenaltyS_one]
  exact Matrix.PosSemidef.smul (bondSpin2ProjectionS_posSemidef (by decide)) (by norm_num)

/-- **`S = 1` positivity oracle, target route.**  The same proposition as the independent route
above, proved instead through the new headline `localCasimirPenalty_posSemidef`: since both prove
the identical statement, they cannot disagree. -/
example : (localCasimirPenalty 1).PosSemidef :=
  localCasimirPenalty_posSemidef (S := 1) (by norm_num)

/-! ## Group 4: signature pins -/

/-- **Signature pin: the bond Casimir is Hermitian.** -/
example {L : ℕ} (x y : Fin L) (N : ℕ) : (bondCasimirS x y N).IsHermitian :=
  bondCasimirS_isHermitian x y N

/-- **Signature pin: the Casimir nodes are pairwise distinct.** -/
example (N : ℕ) : Function.Injective (casimirNode N) :=
  casimirNode_injective N

/-- **Signature pin: the annihilating polynomial of the two-site bond Casimir.** -/
example (N : ℕ) :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 N) (Lagrange.nodal Finset.univ (casimirNode N))
      = 0 :=
  aeval_nodal_bondCasimirS N

/-- **Signature pin: the penalty polynomial evaluated at a node equals the scalar weight.** -/
example (S J : ℕ) :
    (casimirPenaltyPoly S).eval ((J : ℝ) * (J + 1)) = casimirPenaltyWeight S J :=
  casimirPenaltyPoly_eval S J

/-- **Signature pin, `hdeg`-load-bearing.**  `q_S` has degree `S + 1`, strictly below the
`2S + 1` Casimir nodes — the degree bound that makes the Lagrange-interpolation route apply.  A
later change of the index range in `bondCasimirPenaltyS` (e.g. `j < S` instead of `j ≤ S`) must
break this pin. -/
example (S : ℕ) : (casimirPenaltyPoly S).degree = (S : ℕ) + 1 :=
  casimirPenaltyPoly_degree S

/-- **Signature pin: `aeval` of the penalty polynomial at the bond Casimir is the local bond
term.** -/
example (S : ℕ) :
    Polynomial.aeval (bondCasimirS (0 : Fin 2) 1 (2 * S)) (casimirPenaltyPoly S)
      = localCasimirPenalty S :=
  aeval_casimirPenaltyPoly S

/-- **Signature pin: every bond term of the chain is positive semidefinite.** -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {x y : Λ} (hxy : x ≠ y) {S : ℕ} (hS : S ≠ 0) :
    (bondCasimirPenaltyS x y S).PosSemidef :=
  bondCasimirPenaltyS_posSemidef hxy hS

end LatticeSystem.Tests.GeneralSCasimirPositivity
