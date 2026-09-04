import LatticeSystem.Quantum.SpinS.KennedyTasakiMonomial

/-!
# Tasaki §8.2.3, Proposition 8.4: the single-local-monomial form

The printed Proposition 8.4 quantifies over Hamiltonians with short-range interactions, but
§8.2.2–§8.2.3 (pp. 241–251) argue, and prove, only the statement about a **single local product of
spin operators**: strings cancel iff both `n₁ + n₂` and `n₂ + n₃` are even, and that parity
condition is exactly `Z₂ × Z₂` invariance.  This module formalizes that statement and both of its
directions.

Two facts fix the shape of the formal statement and neither may be dropped.

* **Locality must be a fixed window, not a range-existence.**  At fixed finite `L` the shape
  "`∃ r`, every term has range `r`" is vacuously true for every operator, because the chain has
  diameter at most `L`.  `IsLocalWindowS` therefore names a concrete window `[a, b]` and, following
  the house precedent `IsLocalRangeR`, states locality as a commutant condition.
* **The window must be interior.**  The strings of (8.2.13)/(8.2.14) are half-open (`u < x` on the
  left, `v > x` on the right), so at an edge site the corresponding string is empty.  Concretely
  `Û_KT Ŝ_0^{(3)} Û_KT = Ŝ_0^{(3)}` is exactly local while `Ŝ_0^{(3)}` is *not* `Z₂ × Z₂` invariant
  (`ktUnitaryS_conj_site0_axis3`).  The hypotheses `0 < a` and `b + 1 < L` are exactly this
  boundary margin, and are consumed by the necessity direction.

**Deliberate scope note.**  The step from "each non-invariant local term keeps an uncancelled
string" to "the *sum* is not short-ranged" is made nowhere in the book — it would have to rule out
cancellation between distinct non-invariant terms, for which the honest tool is a `Z₂ × Z₂` group
average into four sign sectors.  It is deliberately out of scope here, and nothing in this arc is
left as an axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.2–§8.2.3, Proposition 8.4, eqs. (8.2.12)–(8.2.15), (8.2.17), pp. 241–251;
F. Pollmann, A. M. Turner, E. Berg, M. Oshikawa, *Symmetry protection of topological phases in
one-dimensional quantum spin systems*, Phys. Rev. B **85**, 075125 (2012).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- **Commutant-form window locality** `IsLocalWindowS L N a b op`: the operator `op` acts only on
sites inside the window `[a, b] ⊆ Fin L`, recorded as the commutant condition that `op` commutes
with every single-site operator `onSiteS z A` placed at a site `z` outside the window.  This is the
open-chain, explicit-window analogue of the ring-distance predicate `IsLocalRangeR`
(`LiebSchultzMattisGeneral.lean`): unlike an `∃ r, …` range-existence form, which is vacuously
true for every operator once `r ≥ L` (ring distance on `Fin L` is bounded by `L / 2`), a fixed
window `[a, b]` is genuinely restrictive at fixed finite `L`. -/
def IsLocalWindowS (L N a b : ℕ) (op : ManyBodyOpS (Fin L) N) : Prop :=
  ∀ z : Fin L, (z.val < a ∨ b < z.val) →
    ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute op (onSiteS z A)

/-! ## The printed parenthetical -/

/-- Conjugation by `Û_KT` is invisible to the `Z₂ × Z₂` group, since `Û_KT` commutes with every
`π` rotation. -/
private theorem commute_ktConj_piRotationS {X : ManyBodyOpS (Fin L) 2} (alpha : Fin 3)
    (h : Commute X (piRotationS L alpha)) :
    Commute (ktUnitaryS L * X * ktUnitaryS L) (piRotationS L alpha) :=
  Commute.mul_left (Commute.mul_left (ktUnitaryS_commute_piRotationS L alpha) h)
    (ktUnitaryS_commute_piRotationS L alpha)

/-- Conjugating twice by the involution `Û_KT` is the identity. -/
private theorem ktUnitaryS_conj_conj (X : ManyBodyOpS (Fin L) 2) :
    ktUnitaryS L * (ktUnitaryS L * X * ktUnitaryS L) * ktUnitaryS L = X := by
  rw [show ktUnitaryS L * (ktUnitaryS L * X * ktUnitaryS L) * ktUnitaryS L
      = ktUnitaryS L * ktUnitaryS L * X * (ktUnitaryS L * ktUnitaryS L) from by noncomm_ring,
    ktUnitaryS_sq, one_mul, mul_one]

/-- `Z₂ × Z₂` invariance is commutation with each of the three `π` rotations. -/
private theorem isZ2Z2Invariant_iff_commute (H : ManyBodyOpS (Fin L) 2) :
    IsZ2Z2Invariant H ↔ ∀ alpha : Fin 3, Commute H (piRotationS L alpha) := by
  rw [isZ2Z2Invariant_iff]
  refine forall_congr' fun alpha => ⟨fun h => ?_, fun h => ?_⟩
  · have hstep := congrArg (fun M => M * piRotationS L alpha) h
    simp only [mul_assoc, piRotationS_mul_self, mul_one] at hstep
    exact hstep.symm
  · rw [← h.eq, mul_assoc, piRotationS_mul_self, mul_one]

/-- **The printed parenthetical of Proposition 8.4, in full generality** (Tasaki p. 250): since
`Û_KT` commutes with every `π` rotation, the transformed operator `Û_KT H Û_KT` is `Z₂ × Z₂`
invariant exactly when `H` is.  No monomial structure and no locality is needed. -/
theorem ktUnitaryS_conj_isZ2Z2Invariant_iff (H : ManyBodyOpS (Fin L) 2) :
    IsZ2Z2Invariant (ktUnitaryS L * H * ktUnitaryS L) ↔ IsZ2Z2Invariant H := by
  rw [isZ2Z2Invariant_iff_commute, isZ2Z2Invariant_iff_commute]
  refine ⟨fun h alpha => ?_, fun h alpha => commute_ktConj_piRotationS alpha (h alpha)⟩
  have := commute_ktConj_piRotationS alpha (h alpha)
  rwa [ktUnitaryS_conj_conj] at this

/-! ## Half-turn powers by parity -/

/-- An even power of a half turn is the identity. -/
private theorem halfTurn_pow_even (alpha : Fin 3) {n : ℕ} (hn : Even n) :
    spinOneHalfTurnS alpha ^ n = 1 := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  rw [pow_add, ← (Commute.refl (spinOneHalfTurnS alpha)).mul_pow, spinOneHalfTurnS_mul_self,
    one_pow]

/-- An odd power of a half turn is the half turn. -/
private theorem halfTurn_pow_odd (alpha : Fin 3) {n : ℕ} (hn : ¬ Even n) :
    spinOneHalfTurnS alpha ^ n = spinOneHalfTurnS alpha := by
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hn
  subst hk
  rw [pow_succ, halfTurn_pow_even alpha ⟨k, by omega⟩, one_mul]

/-! ## Proposition 8.4, single-local-monomial form -/

/-- **Tasaki Proposition 8.4 (Pollmann–Turner–Berg–Oshikawa), single-local-monomial form.**  The
printed Proposition quantifies over Hamiltonians with short-range interactions, but §8.2.2–§8.2.3
(pp. 241–251) argue, and prove, only the single-local-monomial statement below; the step from a
non-invariant local term to a non-short-ranged *sum* is made nowhere in the book (it would need to
rule out cancellation between distinct non-invariant terms) and is deliberately out of scope here.

For a word `w` supported in the interior window `[a, b]` (`hw`), with genuine margin on both sides
(`hleft : 0 < a`, `hright : b + 1 < L`): the Kennedy–Tasaki-transformed monomial
`Û_KT O_w Û_KT` is again local in `[a, b]` **iff** `O_w` is Z₂ × Z₂ invariant, and Z₂ × Z₂
invariance of `O_w` is preserved by the transformation (the printed parenthetical
"(In this case `Ĥ'` is also `Z₂ × Z₂` invariant.)", which for the primed `Ĥ'` costs nothing since
`Û_KT` commutes with every `Û_π^{(α)}`, p. 250).

The interior-window hypothesis is **not** removable: `O = Ŝ_0^{(3)}` has odd left parity
(`n₂ + n₃ = 1`) yet `Û_KT Ŝ_0^{(3)} Û_KT = Ŝ_0^{(3)}` is exactly local, because the
(8.2.13)/(8.2.14) strings are half-open (`u < x` on the left, `v > x` on the right) and so are
empty at an edge site.
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
  refine ⟨⟨fun hloc => ?_, fun hinv => ?_⟩,
    fun hinv => (ktUnitaryS_conj_isZ2Z2Invariant_iff (spinMonomialS w)).mpr hinv⟩
  · -- Necessity: an uncancelled string forces a nonzero commutator with a probe outside `[a, b]`.
    by_contra hnotinv
    have hne : spinMonomialS w ≠ 0 := spinMonomialS_ne_zero_of_not_isZ2Z2Invariant w hnotinv
    have hzero : ktUnitaryS L * spinMonomialS w * ktUnitaryS L = 0 → False := by
      intro h0
      exact hne (by rw [← ktUnitaryS_conj_conj (spinMonomialS w), h0, mul_zero, zero_mul])
    rcases odd_countP_of_not_isZ2Z2Invariant hnotinv with hodd | hodd
    · have hL : 0 < L := by omega
      refine hzero (eq_zero_of_onSiteS_twist 2 (⟨0, hL⟩ : Fin L) fun A => ?_)
      have htwist := ktConj_spinMonomialS_left a (z := (⟨0, hL⟩ : Fin L)) hleft w
        (fun p hp => (hw p hp).1) A
      rw [halfTurn_pow_odd 2 hodd] at htwist
      have hcomm := (hloc (⟨0, hL⟩ : Fin L) (Or.inl hleft) A).eq
      rw [onSiteS_sub, sub_mul, ← hcomm, htwist, sub_self]
    · have hbz : b < (⟨b + 1, hright⟩ : Fin L).val := Nat.lt_succ_self b
      refine hzero (eq_zero_of_onSiteS_twist 0 (⟨b + 1, hright⟩ : Fin L) fun A => ?_)
      have htwist := ktConj_spinMonomialS_right b (z := (⟨b + 1, hright⟩ : Fin L)) hbz w
        (fun p hp => (hw p hp).2) A
      rw [halfTurn_pow_odd 0 hodd] at htwist
      have hcomm := (hloc (⟨b + 1, hright⟩ : Fin L) (Or.inr hbz) A).eq
      rw [onSiteS_sub, sub_mul, ← hcomm, htwist, sub_self]
  · -- Sufficiency: even string counts make both tails cancel.
    by_cases hO : spinMonomialS w = 0
    · intro z _ A
      rw [hO, mul_zero, zero_mul]
      exact Commute.zero_left _
    · have heven := even_countP_of_isZ2Z2Invariant hO hinv
      intro z hz A
      rcases hz with hz | hz
      · have htwist := ktConj_spinMonomialS_left a (z := z) hz w (fun p hp => (hw p hp).1) A
        rw [halfTurn_pow_even 2 (heven 0), one_mul, mul_one] at htwist
        exact htwist
      · have htwist := ktConj_spinMonomialS_right b (z := z) hz w (fun p hp => (hw p hp).2) A
        rw [halfTurn_pow_even 0 (heven 2), one_mul, mul_one] at htwist
        exact htwist

end LatticeSystem.Quantum
