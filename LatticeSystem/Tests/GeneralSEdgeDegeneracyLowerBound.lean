import LatticeSystem.Quantum.SpinS.GeneralSOpenChainGroundSpace

/-!
# Tasaki §8.3.1: the `(S+1)²` lower bound for the general-`S` open AKLT ground space (PR-6b, Red)

Acceptance gate for the not-yet-implemented PR-6b layer of the `#5292` arc (design report
`.self-local/reports/design-5292-pr6-finrank-lower-bound-round1-20260820.md` §4/§7): the general-`S`
open VBS boundary states `openVBSStateGeneralS`, their Weyl image (`weylMap_openVBSStateGeneralS`),
the headline lower bound `succ_sq_le_finrank_openAKLTGroundSpaceGeneralS`, and the attainment fact
`isGroundEnergy_openAKLTHamiltonianGeneralS`.

**TDD status: RED.**  None of `openVBSStateGeneralS`, `weylMap_openVBSStateGeneralS`,
`boundaryMonomial_mul_prod_isWeightedHomogeneous`,
`openVBSStateGeneralS_mem_openAKLTGroundSpaceGeneralS`,
`openVBSStateGeneralS_linearIndependent`, `succ_sq_le_finrank_openAKLTGroundSpaceGeneralS`, or
`isGroundEnergy_openAKLTHamiltonianGeneralS` exist on `main` yet, so this file does **not** build:
every example naming one of them fails with an unknown-identifier error until PR-6b's
`dev-implement` step lands those declarations in `Quantum/SpinS/GeneralSOpenChainGroundSpace.lean`.
Every proof left in place (rather than immediately failing on the missing name) is marked `sorry` so
that, once the declarations exist, only the `sorry`s — not the statements — need to be discharged.

The one exception is test point 4 (the cardinality pin), which needs no new production code and is
a genuine green regression check today.
-/

open Matrix MvPolynomial
open LatticeSystem.Quantum LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness
open scoped ComplexOrder

namespace LatticeSystem.Tests.GeneralSEdgeDegeneracyLowerBound

/-! ### 1. Signature pins -/

/-- **Signature pin: the general-`S` open VBS boundary states.** -/
example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
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

/-- **Signature pin: attainment.**  `0` is really the ground energy of the general-`S` open chain. -/
example {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    IsGroundEnergy (openAKLTHamiltonianGeneralS L S) 0 :=
  isGroundEnergy_openAKLTHamiltonianGeneralS hL hS

/-! ### 2. `S = 1` value: matches the merged `four_le_finrank_openAKLTGroundSpace` -/

/-- At `S = 1` the lower bound reproduces the merged `4 ≤ finrank` fact for the `S = 1` open chain,
now stated through the general-`S` ground space (`openAKLTGroundSpaceGeneralS L 1 =
openAKLTGroundSpace L` is out of scope for PR-6b per the design report §5 item 9, so this test does
**not** compare against `openAKLTGroundSpace`). -/
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

/-! ### 4. Cardinality pin — a genuine (green) regression guard, no new production code needed -/

/-- **Cardinality pin.** `finrank_span_eq_card` will consume this: the boundary-edge-spin index type
`Fin (S+1) × Fin (S+1)` really has `(S+1)²` elements, guarding against an off-by-one in
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
  sorry

/-! ### 7. Bond-membership control: `m = 0`, `S = 1` matches the merged `S = 1` shape -/

/-- At `m = 0`, `S = 1` the boundary state's Weyl image is `X (0,a) * X (1,b) * fBond 0` — the
`L = 2` instance the merged `weylMap_openGroundForm_eq_boundary_smul_prod` shape predicts. -/
example (a b : Fin 2) :
    weylMap (openVBSStateGeneralS 0 1 (a, b))
      = X ((0 : Fin 2), a) * X ((1 : Fin 2), b) * fBond (0 : Fin 2) := by
  rw [weylMap_openVBSStateGeneralS]
  sorry

end LatticeSystem.Tests.GeneralSEdgeDegeneracyLowerBound
