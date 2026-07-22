import LatticeSystem.Quantum.SpinS.AKLTKnabe.WindowTransportD6c
import Mathlib

/-!
# Gate D6d Stage C: Knabe aggregation and the `L`-uniform bound `(Ĥ')² ≥ (1/10) Ĥ'`

This module belongs to Issue #5094 (Tasaki §7.1.4, Knabe's argument,
pp. 188–190).  Gate D6b (Stage A) supplied the bond-local operator algebra and Gate D6c
(Stage B) transported the four-site window certificate

  `akltWindowAt_knabe_posSemidef : (ĥ_x ĥ_x − (2/5) ĥ_x) ≥ 0`,   i.e. `ε₃ ≥ 2/5`,

to every site `x` of a chain `Fin L`.  Stage C aggregates those `L` local certificates into the
single global inequality

  `(Ĥ')² − (1/10) Ĥ' ≥ 0`,   `Ĥ' = Ĥ'_AKLT = Σ_{y} P̂_{y,y+1}`  (Tasaki eq. (7.1.7)),

with `1/10 = {3/(3−1)}{2/5 − 1/3}` the constant of Tasaki eq. (7.1.38) at `ℓ = 3`.  The constant
is a *literal* under a `∀ L`, so `L`-uniformity is delivered in full.

## The master identity, and why `Ĉ_r` is not formalised

Tasaki organises the cross terms of `(Ĥ')²` into the operators `Ĉ_r` of eqs. (7.1.27)–(7.1.29),
which are *symmetrised* (anticommutator) pairings.  This file uses instead the **ordered offset
sums**

  `D_d := Σ_{y : Fin L} P̂_{y,y+1} P̂_{y+d,y+d+1}`   (`bondPairSum`),

for which `D₀ = Ĥ'` and `(Ĥ')² = Σ_{d : Fin L} D_d`.  Rewriting eqs. (7.1.26)–(7.1.38) in these
terms collapses the whole chain of operator inequalities into the single **master identity**
(`ringProjHamiltonianS_sq_sub_smul_eq`)

  `(Ĥ')² − (1/10) Ĥ' = (1/2) Σ_x (ĥ_x² − (2/5) ĥ_x) + (1/2) D₂ + (1/2) D₋₂
                        + Σ_{d ∉ {0,1,2,−1,−2}} D_d`.

Two points are essential and must not be "simplified":

* **`D₁` and `D₋₁` cancel exactly, term by term as ordered pairs.**  They are Tasaki's `Ĉ₁`, and
  they are *not* positive semidefinite — `D₁` is not even Hermitian, because the bonds `{y,y+1}`
  and `{y+1,y+2}` overlap in the site `y+1` and the two projections do not commute.  Any argument
  that "drops `Ĉ₁` because it is `≥ 0`" is **false**.  Here they never have to be discarded: the
  coefficient of `D₁` produced by `(1/2) Σ_x ĥ_x²` is exactly `1`, which is exactly its
  coefficient in `(Ĥ')² = Σ_d D_d`, so the two occurrences cancel in the identity itself.  This is
  precisely the role of Tasaki's prefactor `1/(ℓ−1)` in eq. (7.1.36).
* **`Ĉ_r` is never defined, and no anticommutator is introduced.**  Everything is an ordered
  product, which is what makes the cancellation term-by-term rather than up to symmetrisation.

The residual offsets `d ∉ {0, 1, −1}` are exactly those for which the two bonds `{y,y+1}` and
`{y+d,y+d+1}` are **disjoint**; there the two projections commute, their product is a Hermitian
idempotent, and `D_d ≥ 0` (`posSemidef_bondPairSum`, from Gate D6b item A7).

## Periodic ring versus open window (design risk R3 — this file owns the PERIODIC side)

Stage A was on neither side; Stage B was on the **open** side (the window `ĥ_x` has exactly three
bonds and never a fourth).  **This file owns the periodic side**, and it is the file that must get
it right:

* `ringProjHamiltonianS L = Σ_{y : Fin L} ringBond y` sums over **all** `y : Fin L`, and
  `ringBond y = P̂_{y, y+1}` uses the *group* successor of `Fin L`.  Therefore the summand at
  `y = L−1` is the **wrap bond** `{L−1, 0}`, and it **is included**.  Dropping it would falsify
  eq. (7.1.31) `Σ_x ĥ_x = 3 Ĥ'` and hence the master identity (the exact rational contrast run
  before this file was written confirms that the identity fails for the open-chain `Ĥ'`).
* Conversely, `akltWindowAt x` (Stage B) must stay **open**: adding the fourth bond
  `{x+3, x+4}` also falsifies the master identity (likewise confirmed by contrast).  Nothing in
  this file redefines the window.

The two errors pull in opposite directions and neither is caught by a type check, so both are
recorded here and both were checked numerically before any Lean was written.

## Hypothesis: `L ≥ 5`, with no parity restriction

The identity needs the five offsets `0, 1, 2, −1, −2` to be **pairwise distinct in `Fin L`**,
i.e. `5 ≤ L`; that is the only place `L` enters.  Tasaki assumes `L` even and `1 < ℓ < L/2`
(which at `ℓ = 3` would force `L ≥ 8`); those restrictions are artefacts of the `Ĉ_r` packaging
(the `r`-range and the special `Ĉ_{L/2}` of eq. (7.1.29)) and dissolve under the ordered-offset
reorganisation.  The bound `5 ≤ L` is sharp for this route: the exact rational contrast confirms
the master identity for `L = 5, …, 14` and its failure at `L = 3, 4`.

This is a reorganisation of Knabe's argument as presented by Tasaki, not a new proof.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4, eqs. (7.1.7), (7.1.26)–(7.1.38), pp. 188–190.
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open scoped ComplexOrder MatrixOrder

/-- **The AKLT ring projector Hamiltonian**, Tasaki `Ĥ'_AKLT` of eq. (7.1.7):
`Ĥ' = Σ_{y : Fin L} P̂_{y,y+1}`, the sum of the bond spin-2 projections over the **periodic**
chain.  The summand at `y = L−1` is `ringBond (L−1) = P̂_{L−1, 0}`, the **wrap bond**, and it is
deliberately included: Tasaki's §7.1.4 argument is stated for a periodic chain, and eq. (7.1.31)
`Σ_x ĥ_{x,x+3} = 3 Ĥ'` (used below) is false for the open chain. -/
noncomputable def ringProjHamiltonianS (L : ℕ) [NeZero L] : ManyBodyOpS (Fin L) 2 :=
  ∑ y : Fin L, ringBond y

/-- Two elements of `Fin L` with different underlying values are different.  Stated outside the
`Aggregation` section below because it needs no `NeZero L` instance (the linter rejects an
automatically included but unused section variable). -/
private theorem fin_ne_of_val_ne {L : ℕ} {a b : Fin L} {m n : ℕ} (ha : a.val = m)
    (hb : b.val = n) (hmn : m ≠ n) : a ≠ b := by
  intro hab
  apply hmn
  rw [← ha, ← hb, hab]

section Aggregation

variable {L : ℕ} [NeZero L]

/-- The **ordered offset sum** `D_d = Σ_{y : Fin L} P̂_{y,y+1} P̂_{y+d,y+d+1}`.  The product is
taken in this order and is *not* symmetrised: `D_d` and `D_{−d}` are different operators, and it
is exactly this that makes Tasaki's `Ĉ₁` cancel term by term below instead of having to be
bounded.  `D₀ = Ĥ'` by idempotence, and `Σ_{d} D_d = (Ĥ')²`. -/
noncomputable def bondPairSum (d : Fin L) : ManyBodyOpS (Fin L) 2 :=
  ∑ y : Fin L, ringBond y * ringBond (y + d)

/-! ### `Fin L` numeral arithmetic

`Fin.instAddMonoidWithOne` is a *scoped* instance (`Fin.NatCast`, so that the coercion `ℕ → Fin L`
does not loop), so in this import context `Fin L` has **no** `NatCast`: neither `push_cast` nor
`one_add_one_eq_two` is available, and numerals must be compared at the level of `Fin.val`.  The
negatives `−1, −2` are handled purely algebraically (never through `Fin.val`, whose values there
are `L−1`, `L−2` and are not reachable by `Nat.mod_eq_of_lt`). -/

/-- The underlying value of `(0 : Fin L)`. -/
private theorem fin_val_zero : ((0 : Fin L)).val = 0 := by simp

/-- The underlying value of `(1 : Fin L)` on a chain with at least two sites. -/
private theorem fin_val_one (hL : 2 ≤ L) : ((1 : Fin L)).val = 1 := by
  change 1 % L = 1
  exact Nat.mod_eq_of_lt (by omega)

/-- The underlying value of `(2 : Fin L)` on a chain with at least three sites. -/
private theorem fin_val_two (hL : 3 ≤ L) : ((2 : Fin L)).val = 2 := by
  change 2 % L = 2
  exact Nat.mod_eq_of_lt (by omega)

/-- The underlying value of `(3 : Fin L)` on a chain with at least four sites. -/
private theorem fin_val_three (hL : 4 ≤ L) : ((3 : Fin L)).val = 3 := by
  change 3 % L = 3
  exact Nat.mod_eq_of_lt (by omega)

/-- The underlying value of `(4 : Fin L)` on a chain with at least five sites. -/
private theorem fin_val_four (hL : 5 ≤ L) : ((4 : Fin L)).val = 4 := by
  change 4 % L = 4
  exact Nat.mod_eq_of_lt (by omega)

/-- `1 ≠ 0` in `Fin L` for `2 ≤ L`. -/
private theorem fin_one_ne_zero (hL : 2 ≤ L) : (1 : Fin L) ≠ 0 :=
  fin_ne_of_val_ne (fin_val_one hL) fin_val_zero (by omega)

/-- `2 ≠ 0` in `Fin L` for `3 ≤ L`. -/
private theorem fin_two_ne_zero (hL : 3 ≤ L) : (2 : Fin L) ≠ 0 :=
  fin_ne_of_val_ne (fin_val_two hL) fin_val_zero (by omega)

/-- `3 ≠ 0` in `Fin L` for `4 ≤ L`. -/
private theorem fin_three_ne_zero (hL : 4 ≤ L) : (3 : Fin L) ≠ 0 :=
  fin_ne_of_val_ne (fin_val_three hL) fin_val_zero (by omega)

/-- `4 ≠ 0` in `Fin L` for `5 ≤ L`.  This is the fact that fails at `L = 4` and is the reason the
master identity needs `5 ≤ L`: at `L = 4` the two offsets `2` and `−2` coincide. -/
private theorem fin_four_ne_zero (hL : 5 ≤ L) : (4 : Fin L) ≠ 0 :=
  fin_ne_of_val_ne (fin_val_four hL) fin_val_zero (by omega)

/-- `1 ≠ 2` in `Fin L` for `3 ≤ L`. -/
private theorem fin_one_ne_two (hL : 3 ≤ L) : (1 : Fin L) ≠ 2 :=
  fin_ne_of_val_ne (fin_val_one (by omega)) (fin_val_two hL) (by omega)

/-- `1 + 1 = 2` in `Fin L` for `3 ≤ L`. -/
private theorem fin_one_add_one (hL : 3 ≤ L) : (1 : Fin L) + 1 = 2 := by
  refine Fin.ext ?_
  rw [Fin.val_add, fin_val_one (by omega), fin_val_two hL,
    Nat.mod_eq_of_lt (show 1 + 1 < L by omega)]

/-- `1 + 2 = 3` in `Fin L` for `4 ≤ L`. -/
private theorem fin_one_add_two (hL : 4 ≤ L) : (1 : Fin L) + 2 = 3 := by
  refine Fin.ext ?_
  rw [Fin.val_add, fin_val_one (by omega), fin_val_two (by omega), fin_val_three hL,
    Nat.mod_eq_of_lt (show 1 + 2 < L by omega)]

/-- `2 + 1 = 3` in `Fin L` for `4 ≤ L`. -/
private theorem fin_two_add_one (hL : 4 ≤ L) : (2 : Fin L) + 1 = 3 := by
  refine Fin.ext ?_
  rw [Fin.val_add, fin_val_one (by omega), fin_val_two (by omega), fin_val_three hL,
    Nat.mod_eq_of_lt (show 2 + 1 < L by omega)]

/-- `2 + 2 = 4` in `Fin L` for `5 ≤ L`. -/
private theorem fin_two_add_two (hL : 5 ≤ L) : (2 : Fin L) + 2 = 4 := by
  refine Fin.ext ?_
  rw [Fin.val_add, fin_val_two (by omega), fin_val_four hL,
    Nat.mod_eq_of_lt (show 2 + 2 < L by omega)]

/-- `2 − 1 = 1` in `Fin L` for `3 ≤ L`; the offset of the ordered pair `(x+1, x+2)`. -/
private theorem fin_two_sub_one (hL : 3 ≤ L) : (2 : Fin L) - 1 = 1 := by
  rw [← fin_one_add_one hL]
  abel

/-- `1 − 2 = −1` in `Fin L` for `3 ≤ L`; the offset of the ordered pair `(x+2, x+1)`. -/
private theorem fin_one_sub_two (hL : 3 ≤ L) : (1 : Fin L) - 2 = -1 := by
  rw [← fin_one_add_one hL]
  abel

/-- `0 ≠ 1` in `Fin L` for `2 ≤ L`. -/
private theorem fin_zero_ne_one (hL : 2 ≤ L) : (0 : Fin L) ≠ 1 := (fin_one_ne_zero hL).symm

/-- `0 ≠ 2` in `Fin L` for `3 ≤ L`. -/
private theorem fin_zero_ne_two (hL : 3 ≤ L) : (0 : Fin L) ≠ 2 := (fin_two_ne_zero hL).symm

/-- `0 ≠ −1` in `Fin L` for `2 ≤ L`. -/
private theorem fin_zero_ne_neg_one (hL : 2 ≤ L) : (0 : Fin L) ≠ -1 := fun h =>
  fin_one_ne_zero hL (neg_eq_zero.mp h.symm)

/-- `0 ≠ −2` in `Fin L` for `3 ≤ L`. -/
private theorem fin_zero_ne_neg_two (hL : 3 ≤ L) : (0 : Fin L) ≠ -2 := fun h =>
  fin_two_ne_zero hL (neg_eq_zero.mp h.symm)

/-- `1 ≠ −1` in `Fin L` for `3 ≤ L` (otherwise `2 = 0`). -/
private theorem fin_one_ne_neg_one (hL : 3 ≤ L) : (1 : Fin L) ≠ -1 := by
  intro h
  have h0 : (1 : Fin L) + 1 = 0 := eq_neg_iff_add_eq_zero.mp h
  rw [fin_one_add_one hL] at h0
  exact fin_two_ne_zero hL h0

/-- `1 ≠ −2` in `Fin L` for `4 ≤ L` (otherwise `3 = 0`). -/
private theorem fin_one_ne_neg_two (hL : 4 ≤ L) : (1 : Fin L) ≠ -2 := by
  intro h
  have h0 : (1 : Fin L) + 2 = 0 := eq_neg_iff_add_eq_zero.mp h
  rw [fin_one_add_two hL] at h0
  exact fin_three_ne_zero hL h0

/-- `2 ≠ −1` in `Fin L` for `4 ≤ L` (otherwise `3 = 0`). -/
private theorem fin_two_ne_neg_one (hL : 4 ≤ L) : (2 : Fin L) ≠ -1 := by
  intro h
  have h0 : (2 : Fin L) + 1 = 0 := eq_neg_iff_add_eq_zero.mp h
  rw [fin_two_add_one hL] at h0
  exact fin_three_ne_zero hL h0

/-- `2 ≠ −2` in `Fin L` for `5 ≤ L` (otherwise `4 = 0`).  This is the distinctness that fails at
`L = 4`, and hence the load-bearing use of the hypothesis `5 ≤ L`. -/
private theorem fin_two_ne_neg_two (hL : 5 ≤ L) : (2 : Fin L) ≠ -2 := by
  intro h
  have h0 : (2 : Fin L) + 2 = 0 := eq_neg_iff_add_eq_zero.mp h
  rw [fin_two_add_two hL] at h0
  exact fin_four_ne_zero hL h0

/-- `−1 ≠ −2` in `Fin L` for `3 ≤ L`. -/
private theorem fin_neg_one_ne_neg_two (hL : 3 ≤ L) : (-1 : Fin L) ≠ -2 := fun h =>
  fin_one_ne_two hL (neg_inj.mp h)

/-- A site is never equal to its ring successor, on a chain with at least two sites.  This is what
makes each `ringBond` a bond between two *distinct* sites, so that Gate D6b's idempotence and
product lemmas apply. -/
private theorem fin_ne_add_one (hL : 2 ≤ L) (y : Fin L) : y ≠ y + 1 := fun h =>
  fin_one_ne_zero hL (left_eq_add.mp h)

/-! ### C1–C3: the offset sums and the square of `Ĥ'` -/

/-- **Translation invariance of the ordered pair sums** (design item C1).  Shifting both bonds of
an ordered pair by the same amount changes nothing, so a pair sum depends only on the offset
`b − a`.  This is the one reindexing lemma of Stage C, and it is used nine times (once per term of
the expanded window square). -/
theorem bondPairSum_shift (a b : Fin L) :
    (∑ y : Fin L, ringBond (y + a) * ringBond (y + b)) = bondPairSum (b - a) := by
  simp only [bondPairSum]
  refine Fintype.sum_bijective (fun y => y + a) (Equiv.addRight a).bijective _ _ fun y => ?_
  change ringBond (y + a) * ringBond (y + b) = ringBond (y + a) * ringBond (y + a + (b - a))
  rw [show y + a + (b - a) = y + b from by abel]

/-- **`D₀ = Ĥ'`** (design item C2).  Tasaki's `P̂² = P̂` (Gate D6b item A3): the offset-zero pair
sum is the sum of the squares of the bond projections, i.e. `Ĥ'` itself.  This is the step that
turns the diagonal of `(Ĥ')²` into a linear term in eq. (7.1.26). -/
theorem bondPairSum_zero (hL : 2 ≤ L) : bondPairSum (0 : Fin L) = ringProjHamiltonianS L := by
  simp only [bondPairSum, ringProjHamiltonianS, add_zero]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [ringBond]
  exact bondSpin2ProjectionS_mul_self (fin_ne_add_one hL y)

/-- **`(Ĥ')² = Σ_d D_d`** (design item C3), the ordered-offset form of Tasaki eq. (7.1.26).
Expanding the square gives a double sum over ordered pairs of bonds `(y, z)`; reindexing the
inner sum by `z = y + d` groups the pairs by their offset.  No positivity and no commutation is
used here — it is a pure bookkeeping identity. -/
theorem ringProjHamiltonianS_sq :
    ringProjHamiltonianS L * ringProjHamiltonianS L = ∑ d : Fin L, bondPairSum d := by
  have hR : (∑ d : Fin L, bondPairSum d)
      = ∑ y : Fin L, ∑ z : Fin L, ringBond y * ringBond z := by
    simp only [bondPairSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact Fintype.sum_bijective (fun d => y + d) (Equiv.addLeft y).bijective _ _ fun _ => rfl
  rw [hR]
  simp only [ringProjHamiltonianS]
  exact Finset.sum_mul_sum _ _ _ _

/-! ### C4–C5: the two Knabe window sums -/

/-- Shifting the summation index of the ring bond sum leaves `Ĥ'` unchanged. -/
private theorem sum_ringBond_shift (a : Fin L) :
    (∑ y : Fin L, ringBond (y + a)) = ringProjHamiltonianS L := by
  simp only [ringProjHamiltonianS]
  exact Fintype.sum_bijective (fun y => y + a) (Equiv.addRight a).bijective _ _ fun _ => rfl

/-- **`Σ_x ĥ_x = 3 Ĥ'`** (design item C4), Tasaki eq. (7.1.31) at `ℓ = 3`.  Each of the three
bonds of the window contributes, after translation of the summation index, a full copy of `Ĥ'`.
This is the identity that would fail if the wrap bond were dropped from `Ĥ'`. -/
theorem sum_akltWindowAt : (∑ x : Fin L, akltWindowAt x) = (3 : ℂ) • ringProjHamiltonianS L := by
  have h0 : (∑ x : Fin L, ringBond x) = ringProjHamiltonianS L := rfl
  simp only [akltWindowAt, Finset.sum_add_distrib, sum_ringBond_shift, h0]
  module

/-- The nine ordered products of the expanded window square.  Kept in its own lemma so that the
nine-term noncommutative expansion never has to happen inside a `Finset` goal. -/
private theorem akltWindowAt_sq_expand (x : Fin L) :
    akltWindowAt x * akltWindowAt x
      = ringBond x * ringBond x + ringBond x * ringBond (x + 1)
        + ringBond x * ringBond (x + 2)
        + ringBond (x + 1) * ringBond x + ringBond (x + 1) * ringBond (x + 1)
        + ringBond (x + 1) * ringBond (x + 2)
        + ringBond (x + 2) * ringBond x + ringBond (x + 2) * ringBond (x + 1)
        + ringBond (x + 2) * ringBond (x + 2) := by
  simp only [akltWindowAt]
  noncomm_ring

/-- **`Σ_x ĥ_x² = 3 D₀ + 2 D₁ + D₂ + 2 D₋₁ + D₋₂`** (design item C5), the ordered-offset form of
Tasaki eqs. (7.1.32)/(7.1.35) at `ℓ = 3`.  The nine ordered products of the window square carry
the offsets `0, 1, 2, −1, 0, 1, −2, −1, 0` respectively, and each sums to the corresponding `D_d`
by translation invariance.  The coefficient `2` of `D₁` (and of `D₋₁`) is what will cancel
against `(Ĥ')²`'s single `D₁` after the global factor `1/2`; getting it wrong breaks the identity
(checked by exact rational contrast). -/
theorem sum_akltWindowAt_sq (hL : 3 ≤ L) :
    (∑ x : Fin L, akltWindowAt x * akltWindowAt x)
      = (3 : ℂ) • bondPairSum (0 : Fin L) + (2 : ℂ) • bondPairSum (1 : Fin L)
        + bondPairSum (2 : Fin L) + (2 : ℂ) • bondPairSum (-1 : Fin L)
        + bondPairSum (-2 : Fin L) := by
  have e1 : (∑ x : Fin L, ringBond x * ringBond x) = bondPairSum (0 : Fin L) := by
    simp only [bondPairSum, add_zero]
  have e2 : (∑ x : Fin L, ringBond x * ringBond (x + 1)) = bondPairSum (1 : Fin L) := rfl
  have e3 : (∑ x : Fin L, ringBond x * ringBond (x + 2)) = bondPairSum (2 : Fin L) := rfl
  have e4 : (∑ x : Fin L, ringBond (x + 1) * ringBond x) = bondPairSum (-1 : Fin L) := by
    have h := bondPairSum_shift (1 : Fin L) 0
    simp only [add_zero, zero_sub] at h
    exact h
  have e5 : (∑ x : Fin L, ringBond (x + 1) * ringBond (x + 1)) = bondPairSum (0 : Fin L) := by
    have h := bondPairSum_shift (1 : Fin L) 1
    simp only [sub_self] at h
    exact h
  have e6 : (∑ x : Fin L, ringBond (x + 1) * ringBond (x + 2)) = bondPairSum (1 : Fin L) := by
    have h := bondPairSum_shift (1 : Fin L) 2
    rw [fin_two_sub_one hL] at h
    exact h
  have e7 : (∑ x : Fin L, ringBond (x + 2) * ringBond x) = bondPairSum (-2 : Fin L) := by
    have h := bondPairSum_shift (2 : Fin L) 0
    simp only [add_zero, zero_sub] at h
    exact h
  have e8 : (∑ x : Fin L, ringBond (x + 2) * ringBond (x + 1)) = bondPairSum (-1 : Fin L) := by
    have h := bondPairSum_shift (2 : Fin L) 1
    rw [fin_one_sub_two hL] at h
    exact h
  have e9 : (∑ x : Fin L, ringBond (x + 2) * ringBond (x + 2)) = bondPairSum (0 : Fin L) := by
    have h := bondPairSum_shift (2 : Fin L) 2
    simp only [sub_self] at h
    exact h
  simp only [akltWindowAt_sq_expand, Finset.sum_add_distrib, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  module

/-! ### C6: the residual offset sums are positive semidefinite -/

/-- **`D_d ≥ 0` for every offset `d ∉ {0, 1, −1}`** (design item C6).  For such `d` the four sites
`y, y+1, y+d, y+d+1` are pairwise distinct, i.e. the two bonds are **disjoint**, so their
projections commute and the product is a Hermitian idempotent (Gate D6b item A7), hence positive
semidefinite; a sum of positive-semidefinite matrices is positive semidefinite.  The excluded
offsets are exactly Tasaki's overlapping cases: `d = 0` is the diagonal `D₀ = Ĥ'`, and
`d = ±1` is `Ĉ₁`, which is **not** positive semidefinite (`D₁` is not even Hermitian) and must be
cancelled rather than discarded. -/
theorem posSemidef_bondPairSum (hL : 2 ≤ L) {d : Fin L}
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hdm : d ≠ -1) :
    (bondPairSum d : ManyBodyOpS (Fin L) 2).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  simp only [bondPairSum]
  refine Finset.sum_nonneg fun y _ => ?_
  rw [Matrix.nonneg_iff_posSemidef]
  simp only [ringBond]
  refine posSemidef_bondSpin2ProjectionS_mul (fin_ne_add_one hL y)
    (fin_ne_add_one hL (y + d)) ?_ ?_ ?_ ?_
  · exact fun h => hd0 (left_eq_add.mp h)
  · intro h
    rw [add_assoc] at h
    exact hdm (eq_neg_iff_add_eq_zero.mpr (left_eq_add.mp h))
  · exact fun h => hd1 (add_left_cancel h).symm
  · exact fun h => hd0 (left_eq_add.mp (add_right_cancel h))

/-! ### C7: the master identity -/

/-- **The Knabe master identity** (design item C7): the whole of Tasaki
eqs. (7.1.26)–(7.1.38) at `ℓ = 3`, as a single operator equation,

  `(Ĥ')² − (1/10) Ĥ' = (1/2) Σ_x (ĥ_x² − (2/5) ĥ_x) + (1/2) D₂ + (1/2) D₋₂
                        + Σ_{d ∉ {0,1,2,−1,−2}} D_d`.

Every term on the right is positive semidefinite (the first by the transported window certificate
of Gate D6c, the rest by `posSemidef_bondPairSum`), which is exactly Knabe's conclusion.

**How `D₁` and `D₋₁` disappear.**  They are Tasaki's `Ĉ₁` of eq. (7.1.27), and they are *not*
discarded — they **cancel exactly**.  On the left, `(Ĥ')² = Σ_d D_d` contributes `D₁ + D₋₁` with
coefficient `1` each.  On the right, `Σ_x ĥ_x²` contributes `2 D₁ + 2 D₋₁` (eq. (7.1.32)), and the
global factor `1/2` — Tasaki's `1/(ℓ−1) = 1/2` of eq. (7.1.36) — turns these into `D₁ + D₋₁` as
well.  The two occurrences are identical *ordered* sums, so they cancel term by term; no
anticommutator, no symmetrisation and no positivity claim about `D₁` is involved anywhere.  (A
proof that instead "dropped `Ĉ₁` because it is `≥ 0`" would be **false**: `D₁` is not Hermitian.)

The arithmetic of the constants: `Σ_x ĥ_x² − (2/5) Σ_x ĥ_x = 3 D₀ + 2D₁ + D₂ + 2D₋₁ + D₋₂
− (2/5)·3 Ĥ'` and `D₀ = Ĥ'`, so half of it is `(9/10) Ĥ' + D₁ + (1/2)D₂ + D₋₁ + (1/2)D₋₂`, while
the left-hand side is `(1 − 1/10) Ĥ' + D₁ + D₂ + D₋₁ + D₋₂ + (rest)`.  The two `(1/2)D₂`,
`(1/2)D₋₂` corrections and the residual sum make up the difference; `1 − 1/10 = 9/10` is Tasaki's
`{ℓ/(ℓ−1)}{ε_ℓ − 1/ℓ} = (3/2)(2/5 − 1/3) = 1/10` of eq. (7.1.38) in disguise.

The hypothesis `5 ≤ L` is used exactly once, to know that the five offsets `0, 1, 2, −1, −2` are
pairwise distinct in `Fin L`; there is **no parity restriction** on `L`. -/
theorem ringProjHamiltonianS_sq_sub_smul_eq (hL : 5 ≤ L) :
    ringProjHamiltonianS L * ringProjHamiltonianS L
        - ((1 : ℂ) / 10) • ringProjHamiltonianS L
      = ((1 : ℂ) / 2) • (∑ x : Fin L,
            (akltWindowAt x * akltWindowAt x - ((2 : ℂ) / 5) • akltWindowAt x))
        + ((1 : ℂ) / 2) • bondPairSum (2 : Fin L)
        + ((1 : ℂ) / 2) • bondPairSum (-2 : Fin L)
        + ∑ d ∈ Finset.univ \ ({0, 1, 2, -1, -2} : Finset (Fin L)), bondPairSum d := by
  have hne0 : (0 : Fin L) ∉ ({1, 2, -1, -2} : Finset (Fin L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fin_zero_ne_one (by omega), fin_zero_ne_two (by omega),
      fin_zero_ne_neg_one (by omega), fin_zero_ne_neg_two (by omega)⟩
  have hne1 : (1 : Fin L) ∉ ({2, -1, -2} : Finset (Fin L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fin_one_ne_two (by omega), fin_one_ne_neg_one (by omega),
      fin_one_ne_neg_two (by omega)⟩
  have hne2 : (2 : Fin L) ∉ ({-1, -2} : Finset (Fin L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fin_two_ne_neg_one (by omega), fin_two_ne_neg_two hL⟩
  have hne3 : (-1 : Fin L) ∉ ({-2} : Finset (Fin L)) := by
    simp only [Finset.mem_singleton]
    exact fin_neg_one_ne_neg_two (by omega)
  have hfive : (∑ d ∈ ({0, 1, 2, -1, -2} : Finset (Fin L)), bondPairSum d)
      = bondPairSum (0 : Fin L) + bondPairSum (1 : Fin L) + bondPairSum (2 : Fin L)
        + bondPairSum (-1 : Fin L) + bondPairSum (-2 : Fin L) := by
    rw [Finset.sum_insert hne0, Finset.sum_insert hne1, Finset.sum_insert hne2,
      Finset.sum_insert hne3, Finset.sum_singleton]
    abel
  have hsplit : (∑ d : Fin L, bondPairSum d)
      = (∑ d ∈ Finset.univ \ ({0, 1, 2, -1, -2} : Finset (Fin L)), bondPairSum d)
        + (bondPairSum (0 : Fin L) + bondPairSum (1 : Fin L) + bondPairSum (2 : Fin L)
          + bondPairSum (-1 : Fin L) + bondPairSum (-2 : Fin L)) := by
    rw [← hfive, Finset.sum_sdiff (Finset.subset_univ _)]
  have hwin : (∑ x : Fin L,
        (akltWindowAt x * akltWindowAt x - ((2 : ℂ) / 5) • akltWindowAt x))
      = (∑ x : Fin L, akltWindowAt x * akltWindowAt x)
        - ((2 : ℂ) / 5) • (∑ x : Fin L, akltWindowAt x) := by
    rw [Finset.sum_sub_distrib, Finset.smul_sum]
  rw [ringProjHamiltonianS_sq, hsplit, hwin, sum_akltWindowAt_sq (by omega), sum_akltWindowAt,
    bondPairSum_zero (by omega)]
  module

/-! ### C8: the capstone -/

/-- **Knabe's inequality for the AKLT ring projector Hamiltonian** (design item C8, Tasaki
eq. (7.1.38) at `ℓ = 3`):

  `(Ĥ')² ≥ (1/10) Ĥ'`,   equivalently   `(Ĥ')² − (1/10) Ĥ' ≥ 0`,

for the periodic chain `Fin L` with `5 ≤ L` — **no parity restriction**, and the constant `1/10`
is a literal, hence **uniform in `L`**.  It says that every nonzero eigenvalue of `Ĥ'` is at
least `1/10`.

The proof is the master identity `ringProjHamiltonianS_sq_sub_smul_eq` followed by four
positivity facts: the transported four-site Knabe certificate `ε₃ ≥ 2/5` at each of the `L` sites
(Gate D6c), and `D_d ≥ 0` for the offsets `2`, `−2` and all `d ∉ {0, 1, 2, −1, −2}`.  Tasaki's
`Ĉ₁` never has to be bounded, because it has already cancelled inside the identity.

This is the *gap-conjunct* input of Tasaki Theorem 7.1: it becomes a spectral gap only together
with `Ĥ' ≥ 0` and the frustration-freeness of the ring VBS state (ground energy `0`), which are
not addressed here. -/
theorem ringProjHamiltonianS_knabe_posSemidef (hL : 5 ≤ L) :
    Matrix.PosSemidef (ringProjHamiltonianS L * ringProjHamiltonianS L
      - ((1 : ℂ) / 10) • ringProjHamiltonianS L) := by
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by rw [Complex.le_def]; norm_num
  have hwin : (∑ x : Fin L,
      (akltWindowAt x * akltWindowAt x - ((2 : ℂ) / 5) • akltWindowAt x)).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    refine Finset.sum_nonneg fun x _ => ?_
    rw [Matrix.nonneg_iff_posSemidef]
    exact akltWindowAt_knabe_posSemidef (by omega) x
  have hrest : (∑ d ∈ Finset.univ \ ({0, 1, 2, -1, -2} : Finset (Fin L)),
      bondPairSum d).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    refine Finset.sum_nonneg fun d hd => ?_
    rw [Finset.mem_sdiff] at hd
    rw [Matrix.nonneg_iff_posSemidef]
    have hd' := hd.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
    exact posSemidef_bondPairSum (by omega) hd'.1 hd'.2.1 hd'.2.2.2.1
  rw [ringProjHamiltonianS_sq_sub_smul_eq hL]
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.add
    (Matrix.PosSemidef.add ?_ ?_) ?_) hrest
  · exact hwin.smul hhalf
  · exact (posSemidef_bondPairSum (by omega) (fin_two_ne_zero (by omega))
      (Ne.symm (fin_one_ne_two (by omega))) (fin_two_ne_neg_one (by omega))).smul hhalf
  · exact (posSemidef_bondPairSum (by omega) (neg_ne_zero.mpr (fin_two_ne_zero (by omega)))
      (Ne.symm (fin_one_ne_neg_two (by omega)))
      (Ne.symm (fin_neg_one_ne_neg_two (by omega)))).smul hhalf

end Aggregation

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
