import LatticeSystem.Quantum.SpinS.GeneralSOpenChainGroundSpace

/-!
# Tasaki §8.3.1: the `(S+1)²` lower bound for the general-`S` open AKLT ground space

Regression pins for the general-`S` VBS boundary layer of
`Quantum.SpinS.GeneralSOpenChainGroundSpace`: the boundary states `openVBSStateGeneralS`, their
Weyl image (`weylMap_openVBSStateGeneralS`), their membership and independence, the headline lower
bound `succ_sq_le_finrank_openAKLTGroundSpaceGeneralS`, and the attainment fact
`isGroundEnergy_openAKLTHamiltonianGeneralS`.

Beyond the signature pins the file fixes the numerical values (`S = 1` gives `4 ≤ dim`, an `m = 0`
instance of the nine-fold `S = 2` degeneracy Tasaki states for the open `S = 2` chain on p. 252),
the cardinality `(S+1)²` of the index type consumed by `finrank_span_eq_card`, the nonzero witness
attainment needs, and two shape controls: the degenerate `S = 0` collapse of both the boundary
monomial and the bond product, and the `S = 1`, `m = 0` Weyl image `X_{(1,a)} X_{(2,b)} f_1`
predicted by `weylMap_openGroundForm_eq_boundary_smul_prod`.
-/

open Matrix MvPolynomial
open LatticeSystem.Quantum LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness
open scoped ComplexOrder

namespace LatticeSystem.Tests.GeneralSEdgeDegeneracyLowerBound

/-! ### 1. Signature pins -/

/-- **Signature pin: the general-`S` open VBS boundary states.** -/
noncomputable example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    (Fin (m + 2) → Fin (2 * S + 1)) → ℂ :=
  openVBSStateGeneralS m S ab

/-- **Signature pin: the Weyl image of a boundary state** is the boundary monomial times the
product of the `S`-th powers of the open bond factors. -/
example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    weylMap (openVBSStateGeneralS m S ab)
      = monomial (boundaryDeg m S ab) 1 * ∏ x ∈ openBonds (m + 2), fBond x ^ S :=
  weylMap_openVBSStateGeneralS m S ab

/-- **Signature pin: membership.**  Every boundary state lies in the ground space. -/
example {m S : ℕ} (hS : S ≠ 0) (ab : Fin (S + 1) × Fin (S + 1)) :
    openVBSStateGeneralS m S ab ∈ openAKLTGroundSpaceGeneralS (m + 2) S :=
  openVBSStateGeneralS_mem_openAKLTGroundSpaceGeneralS hS ab

/-- **Signature pin: independence.**  The `(S+1)²` boundary states are linearly independent. -/
example (m S : ℕ) :
    LinearIndependent ℂ fun ab : Fin (S + 1) × Fin (S + 1) => openVBSStateGeneralS m S ab :=
  openVBSStateGeneralS_linearIndependent m S

/-- **Signature pin, headline: the `(S+1)²` lower bound.** -/
example {m S : ℕ} (hS : S ≠ 0) :
    (S + 1) ^ 2 ≤ Module.finrank ℂ (openAKLTGroundSpaceGeneralS (m + 2) S) :=
  succ_sq_le_finrank_openAKLTGroundSpaceGeneralS hS

/-- **Signature pin: attainment.**  `0` is really the ground energy of the general-`S` open
chain. -/
example {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    IsGroundEnergy (openAKLTHamiltonianGeneralS L S) 0 :=
  isGroundEnergy_openAKLTHamiltonianGeneralS hL hS

/-! ### 2. `S = 1` value: the `4 ≤ finrank` bound of Problem 7.2.3.a -/

/-- At `S = 1` the lower bound reproduces the `4 ≤ finrank` bound of the `S = 1` open chain
(`four_le_finrank_openAKLTGroundSpace`), stated through the general-`S` ground space: this pin is
about the lower-bound theorem alone, so it does not travel along the separate identification
`openAKLTGroundSpaceGeneralS_one` (pinned in `Tests/GeneralSEdgeDegeneracy.lean`). -/
example (m : ℕ) : 4 ≤ Module.finrank ℂ (openAKLTGroundSpaceGeneralS (m + 2) 1) := by
  have h := succ_sq_le_finrank_openAKLTGroundSpaceGeneralS (m := m) (S := 1) (by norm_num)
  norm_num at h
  exact h

/-! ### 3. `S = 2`, `m = 0` value: the nine-fold case Tasaki names on p. 252 -/

/-- The single-bond (`m = 0`) two-site chain at `S = 2` has ground space dimension at least `9`. -/
example : 9 ≤ Module.finrank ℂ (openAKLTGroundSpaceGeneralS 2 2) := by
  have h := succ_sq_le_finrank_openAKLTGroundSpaceGeneralS (m := 0) (S := 2) (by norm_num)
  norm_num at h
  exact h

/-! ### 4. Cardinality pin -/

/-- **Cardinality pin.**  The count `finrank_span_eq_card` consumes: the boundary-edge-spin index
type `Fin (S+1) × Fin (S+1)` really has `(S+1)²` elements, guarding against an off-by-one in
`boundaryDeg`'s domain. -/
example (S : ℕ) : Fintype.card (Fin (S + 1) × Fin (S + 1)) = (S + 1) ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_fin]
  ring

/-! ### 5. Nonzero witness — the attainment input -/

/-- `Φ_{0,0}` is a nonzero ground state, the input attainment needs (derived from independence, not
pinned as its own production lemma). -/
example (m S : ℕ) : openVBSStateGeneralS m S (0, 0) ≠ 0 :=
  (openVBSStateGeneralS_linearIndependent m S).ne_zero (0, 0)

/-! ### 6. `S = 0` degenerate control -/

/-- At `S = 0` both the boundary monomial and the bond product collapse to `1`: the Weyl image of
every boundary state is the constant `1`.  Catches a wrong `S − a` truncation or an empty-product
slip in `openVBSStateGeneralS`'s definition. -/
example (m : ℕ) (ab : Fin 1 × Fin 1) : weylMap (openVBSStateGeneralS m 0 ab) = 1 := by
  rw [weylMap_openVBSStateGeneralS]
  simp [boundaryDeg, mdSite]

/-! ### 7. Bond-membership control: `m = 0`, `S = 1` matches the `S = 1` boundary shape -/

/-- At `m = 0`, `S = 1` the boundary state's Weyl image is `X (0,a) * X (1,b) * fBond 0` — the
`L = 2` instance of the shape `weylMap_openGroundForm_eq_boundary_smul_prod` predicts. -/
example (a b : Fin 2) :
    weylMap (openVBSStateGeneralS 0 1 (a, b))
      = X ((0 : Fin 2), a) * X ((1 : Fin 2), b) * fBond (0 : Fin 2) := by
  have hbonds : openBonds 2 = {(0 : Fin 2)} := by decide
  have hlast : (Fin.last 1 : Fin 2) = 1 := rfl
  rw [weylMap_openVBSStateGeneralS, hbonds, Finset.prod_singleton, pow_one, boundaryDeg_one,
    hlast]
  congr 1
  rw [X, X, monomial_mul, mul_one]

end LatticeSystem.Tests.GeneralSEdgeDegeneracyLowerBound
