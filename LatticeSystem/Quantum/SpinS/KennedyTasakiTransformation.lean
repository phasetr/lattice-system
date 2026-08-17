import LatticeSystem.Quantum.SpinS.SiteComponent
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Tasaki §8.2.2–§8.2.3: the Kennedy–Tasaki transformation and Proposition 8.4

The picture of **hidden Z₂ × Z₂ symmetry breaking** in the Haldane phase is made precise by the
**Kennedy–Tasaki transformation**, the non-local unitary (eq. (8.2.5))
`Û_KT = ∏_{u < v} exp(iπ Ŝ_u^{(3)} Ŝ_v^{(1)})`,
written in this concise form by Oshikawa.  The commuting factors each square to the identity, so
`Û_KT² = 1` and `Û_KT = Û_KT†` (a self-adjoint involution).  Conjugating by `Û_KT` turns the
*hidden*
antiferromagnetic order of the Haldane phase into *manifest* Z₂ × Z₂ symmetry breaking.

The relevant symmetry is **Z₂ × Z₂**: the three π-rotations `Û_π^{(α)} = ∏_x exp(iπ Ŝ_x^{(α)})`
about the spin axes (any two generate the group).  A Hamiltonian is Z₂ × Z₂ invariant when
`(Û_π^{(α)})† Ĥ Û_π^{(α)} = Ĥ` for `α = 1, 2, 3`.

**Proposition 8.4** (Pollmann–Turner–Berg–Oshikawa): for an `S = 1` open chain `Ĥ` with short-range
interactions, the transformed Hamiltonian `Û_KT Ĥ Û_KT` again has only short-range interactions
**iff**
`Ĥ` is Z₂ × Z₂ invariant.  So the hidden-symmetry-breaking picture is effective exactly when the
original Hamiltonian has Z₂ × Z₂ symmetry.

The π-rotations and the Z₂ × Z₂ invariance condition are *defined concretely* (via the on-site
matrix
exponentials).  The non-local Kennedy–Tasaki unitary is recorded as an operator with its defining
involutive/self-adjoint properties as documented axioms (its explicit nonlocal exponential product
is
not built), and Proposition 8.4 — together with the short-range-interaction predicate — is a
documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2–§8.2.3, Proposition 8.4, eqs. (8.2.5)–(8.2.7), pp. 241–251; T. Kennedy, H. Tasaki,
Commun. Math. Phys. **147**, 431 (1992); F. Pollmann, A. M. Turner, E. Berg, M. Oshikawa, Phys. Rev.
B **81**, 064439 (2010).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **Kennedy–Tasaki unitary** `Û_KT = ∏_{u < v} exp(iπ Ŝ_u^{(3)} Ŝ_v^{(1)})` (eq. (8.2.5)), the
non-local transformation turning hidden Z₂ × Z₂ symmetry breaking into manifest symmetry breaking.
Its explicit nonlocal exponential product is not built; it is recorded as an operator with the
defining properties `ktUnitaryS_sq` and `ktUnitaryS_selfAdjoint` below. -/
axiom ktUnitaryS (L : ℕ) : ManyBodyOpS (Fin L) 2

/-- **`Û_KT² = 1`** (eq. (8.2.5) ff.): the commuting two-site factors each square to the identity,
so
the Kennedy–Tasaki unitary is an involution. -/
axiom ktUnitaryS_sq (L : ℕ) : ktUnitaryS L * ktUnitaryS L = 1

/-- **`Û_KT = Û_KT†`**: the Kennedy–Tasaki unitary is self-adjoint (hence `Û_KT` and `Û_KT†` may be
used interchangeably). -/
axiom ktUnitaryS_selfAdjoint (L : ℕ) : (ktUnitaryS L).conjTranspose = ktUnitaryS L

/-- The **π-rotation** `Û_π^{(α)} = ∏_x exp(iπ Ŝ_x^{(α)})` about the spin axis `α : Fin 3`: the
product of the on-site π-rotations.  Together the three generate the Z₂ × Z₂ group. -/
noncomputable def piRotationS (L : ℕ) (α : Fin 3) : ManyBodyOpS (Fin L) 2 :=
  (List.ofFn fun x : Fin L =>
    NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) • spinSSiteComponentS α x)).prod

/-- **Z₂ × Z₂ invariance** of a Hamiltonian `H`: `(Û_π^{(α)})† H Û_π^{(α)} = H` for every spin axis
`α = 1, 2, 3`, i.e. `H` commutes with each of the three π-rotations. -/
def IsZ2Z2Invariant (H : ManyBodyOpS (Fin L) 2) : Prop :=
  ∀ α : Fin 3, (piRotationS L α).conjTranspose * H * piRotationS L α = H

/-- The **word-indexed spin monomial** `O_w = ∏_i Ŝ_{w_i.1}^{(w_i.2)}` for a word
`w : List (Fin L × Fin 3)` of (site, axis) letters, read left to right in list order.  Same-site
letters do not commute (`Ŝ^{(1)} Ŝ^{(2)} ≠ Ŝ^{(2)} Ŝ^{(1)}`) and the book's own example
`Ŝ_x^{(1)} Ŝ_{x+1}^{(2)} (Ŝ_{x+2}^{(3)})²` repeats a letter, so a `List`, not a `Finset`/`Multiset`,
is the right bookkeeping (idiom precedent: `cartWord`, `AndersonTowerCartWord.lean:33`). -/
noncomputable def spinMonomialS {L : ℕ} (w : List (Fin L × Fin 3)) : ManyBodyOpS (Fin L) 2 :=
  (w.map fun p => spinSSiteComponentS p.2 p.1).prod

/-- **Commutant-form window locality** `IsLocalWindowS L N a b op`: the operator `op` acts only on
sites inside the window `[a, b] ⊆ Fin L`, recorded as the commutant condition that `op` commutes
with every single-site operator `onSiteS z A` placed at a site `z` outside the window.  This is the
open-chain, explicit-window analogue of the ring-distance predicate `IsLocalRangeR`
(`LiebSchultzMattisGeneral.lean:52`), and is the contentful replacement for the deleted opaque axiom
`HasShortRangeInteraction`: unlike an `∃ r, …` range-existence form, which is vacuously true for
every operator once `r ≥ L` (ring distance on `Fin L` is bounded by `L / 2`), a fixed window
`[a, b]` is genuinely restrictive at fixed finite `L`. -/
def IsLocalWindowS (L N a b : ℕ) (op : ManyBodyOpS (Fin L) N) : Prop :=
  ∀ z : Fin L, (z.val < a ∨ b < z.val) →
    ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute op (onSiteS z A)

/-- **Tasaki Proposition 8.4 (Pollmann–Turner–Berg–Oshikawa), single-local-monomial form.**  The
printed Proposition quantifies over Hamiltonians with short-range interactions, but §8.2.2–§8.2.3
(pp. 241–251) argue, and prove, only the single-local-monomial statement below; the step from a
non-invariant local term to a non-short-ranged *sum* is made nowhere in the book (it would need to
rule out cancellation between distinct non-invariant terms) and is deliberately out of scope here.

For a word `w` supported in the interior window `[a, b]` (`hw`), with genuine margin on both sides
(`hleft : 0 < a`, `hright : b + 1 < L`): the Kennedy–Tasaki-transformed monomial
`Û_KT O_w Û_KT` is again local in `[a, b]` **iff** `O_w` is Z₂ × Z₂ invariant, and Z₂ × Z₂ invariance
of `O_w` is preserved by the transformation (the printed parenthetical "(In this case `Ĥ` is also
`Z₂ × Z₂` invariant.)", which for the primed `Ĥ'` costs nothing since `Û_KT` commutes with every
`Û_π^{(α)}`, p. 250).

The interior-window hypothesis is **not** removable: `O = Ŝ_0^{(3)}` has odd left parity
(`n₂ + n₃ = 1`) yet `Û_KT Ŝ_0^{(3)} Û_KT = Ŝ_0^{(3)}` is exactly local, because the (8.2.13)/(8.2.14)
strings are half-open (`u < x` on the left, `v > x` on the right) and so are empty at an edge site.
No `O_w ≠ 0` hypothesis is needed: non-invariance itself forces `O_w ≠ 0`
(`(-1)^c • O_w = O_w` failing implies `O_w ≠ 0`), and `O_w = 0` makes both sides of the
biconditional and the implication true.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2–§8.2.3, Proposition 8.4, eqs. (8.2.12)–(8.2.15), (8.2.17), p. 250. -/
theorem tasaki_prop_8_4_local_monomial {L : ℕ} (w : List (Fin L × Fin 3)) (a b : ℕ)
    (hw : ∀ p ∈ w, a ≤ (p.1 : Fin L).val ∧ (p.1 : Fin L).val ≤ b)
    (hleft : 0 < a) (hright : b + 1 < L) :
    (IsLocalWindowS L 2 a b (ktUnitaryS L * spinMonomialS w * ktUnitaryS L)
        ↔ IsZ2Z2Invariant (spinMonomialS w))
      ∧ (IsZ2Z2Invariant (spinMonomialS w) →
          IsZ2Z2Invariant (ktUnitaryS L * spinMonomialS w * ktUnitaryS L)) := by
  sorry

/-- **Verification viewpoint 2 (boundary sanity, `L = 0, 1`).** The pairwise product defining
`Û_KT` (eq. (8.2.5)) ranges over `u < v` in `Fin L`; with `L = 0` there are no sites at all and
with `L = 1` there is a single site but no pair `u < v`, so in both cases the product is empty and
`Û_KT` must reduce to the identity. This is genuinely open at the current opaque-axiom stage:
`ktUnitaryS_sq`/`ktUnitaryS_selfAdjoint` alone do not pin down the value of `ktUnitaryS L` (an
involutive self-adjoint operator need not be `1`; `-1` also satisfies both axioms), so this fact
constrains the future concrete implementation of `ktUnitaryS` directly and is not derivable from
the axioms already on file. -/
theorem ktUnitaryS_boundary_sanity : ktUnitaryS 0 = 1 ∧ ktUnitaryS 1 = 1 := by
  sorry

/-- **Verification viewpoint 3 (Red regression guard for the interior-window hypothesis).**
(8.2.14) at `x = 0`: the left string `∏_{u < x} Ŝ_u^{(3)}`-rotation is empty at the left edge of
the chain, so the transformed operator is literally the untransformed `Ŝ_0^{(3)}`, not merely
local in some window around `0`. This is the cheapest instance of the boundary counterexample (C2
of `.self-local/docs/tasaki-8-2-prop-8-4-design.md` §7.2): it is a direct witness that
`tasaki_prop_8_4_local_monomial`'s hypothesis `hleft : 0 < a` is not removable, and it must NEVER
be discharged by later weakening that hypothesis. -/
theorem ktUnitaryS_conj_site0_axis3 {L : ℕ} :
    ktUnitaryS (L + 1) * spinSSiteComponentS 2 (0 : Fin (L + 1)) * ktUnitaryS (L + 1)
      = spinSSiteComponentS 2 (0 : Fin (L + 1)) := by
  sorry

/-- **Verification viewpoint 4 (the sign law on the book's own examples, p. 250).** The word
`Ŝ_x^{(1)} Ŝ_{x+1}^{(2)} Ŝ_{x+2}^{(3)}` has axis counts `n₁ = n₂ = n₃ = 1`, so both parities
`p_L = n₂ + n₃ = 2` and `p_R = n₁ + n₂ = 2` are even and it **is** Z₂ × Z₂ invariant. The word
`Ŝ_x^{(1)} Ŝ_{x+1}^{(2)} (Ŝ_{x+2}^{(3)})²` has `n₁ = n₂ = 1`, `n₃ = 2`, so `p_L = n₂ + n₃ = 3` is
odd and it is **not** Z₂ × Z₂ invariant, exactly as §3.3 of the design note predicts. -/
theorem spinMonomialS_examples_sign_law {L : ℕ} (x : Fin L) (hx : x.val + 2 < L) :
    IsZ2Z2Invariant
        (spinMonomialS [(x, (0 : Fin 3)), (⟨x.val + 1, by omega⟩, (1 : Fin 3)),
          (⟨x.val + 2, hx⟩, (2 : Fin 3))])
      ∧ ¬ IsZ2Z2Invariant
        (spinMonomialS [(x, (0 : Fin 3)), (⟨x.val + 1, by omega⟩, (1 : Fin 3)),
          (⟨x.val + 2, hx⟩, (2 : Fin 3)), (⟨x.val + 2, hx⟩, (2 : Fin 3))]) := by
  sorry

/-- **Verification viewpoint 5 ((8.2.15), the book's worked cancellation, p. 243).**
`Û_KT Ŝ_x^{(3)} Ŝ_{x+1}^{(3)} Û_KT = -Ŝ_x^{(3)} Ŝ_{x+1}^{(3)}`: the two axis-3 strings generated by
(8.2.14) on each factor pair up and collapse via the `S = 1` identity `exp(iπ Ŝ^{(α)}) Ŝ^{(α)} =
-Ŝ^{(α)}`, leaving a bare sign rather than the identity. This is the best end-to-end check of the
tail law's sign bookkeeping and the model instance of the structure lemma in §3.2 of the design
note. -/
theorem ktUnitaryS_conj_ss3_ss3_eq_neg {L : ℕ} (x : Fin L) (hx : x.val + 1 < L) :
    ktUnitaryS L * (spinSSiteComponentS 2 x * spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L)) *
        ktUnitaryS L
      = -(spinSSiteComponentS 2 x * spinSSiteComponentS 2 (⟨x.val + 1, hx⟩ : Fin L)) := by
  sorry

end LatticeSystem.Quantum
