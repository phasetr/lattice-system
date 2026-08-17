import LatticeSystem.Quantum.SpinS.SiteComponent
import LatticeSystem.Quantum.SpinS.SpinOneHalfTurnRegion
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality
import LatticeSystem.Math.ComplexVectorKernel

/-!
# Tasaki §8.1.2: the global prefix-string order operator and hidden order (8.1.8)–(8.1.10)

The den Nijs–Rommelse hidden order of the `S = 1` chain is measured by the **global string
operator**

  `Ô^{(α)}_string = Σ_{x} Ŝ_x^{(α)} exp(i π Σ_{y < x} Ŝ_y^{(α)})`   (Tasaki (8.1.8), p. 236),

whose exponential factor is, at `S = 1`, the product of the per-site half turns `u_α` over the sites
strictly to the left of `x` — a `π` rotation of the sub-chain `{0, …, x-1}`, i.e. the prefix
instance of the region half turn `halfTurnRegionS`.  This module builds that operator, proves it
self-adjoint, states the hidden-order hypothesis (8.1.10) as a concrete Rayleigh bound, and converts
it into the norm lower bound used by the variational argument.

Note that this left **prefix** string is a different operator from the strict two-endpoint window
string `stringOperatorS` / `stringOperatorAxisS` of `AKLTStringOrderDefs`; only the `onSiteS`
product idiom is shared.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.2, eqs. (8.1.8) and (8.1.10), pp. 236–237.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {L : ℕ}

/-! ## Definitions -/

/-- The **prefix rotation** `R^{(α)}_{<m} = ∏_{y < m} u_α^{(y)}`, the `π` rotation about axis `α` of
the sub-chain `{0, …, m-1}`, i.e. the region half turn `halfTurnRegionS` on the prefix set
`{y | y < m}`.  It is indexed by `m : ℕ` rather than by a site, so that the same declaration serves
both the string operator (at `m = x.val`) and the support-count argument (which compares `m ≤ z`
and `z + 2 ≤ m`). -/
noncomputable def edgeStringPrefixRotationS (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    ManyBodyOpS (Fin L) 2 :=
  halfTurnRegionS L alpha (Finset.univ.filter fun y : Fin L => y.val < m)

/-- The **global edge-string order operator** `Ô^{(α)}_string = Σ_x Ŝ_x^{(α)} R^{(α)}_{<x}`
(Tasaki (8.1.8), p. 236). -/
noncomputable def edgeStringOrderOpS (L : ℕ) (alpha : Fin 3) : ManyBodyOpS (Fin L) 2 :=
  ∑ x : Fin L, spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val

/-- **Hidden (string) long-range order**, Tasaki (8.1.10), p. 237: for every axis `α` the Rayleigh
expectation of `(Ô^{(α)}_string / L)²` in the state `Φ` is at least the `L`-independent constant
`q_α`.  The anisotropy `D` is deliberately absent: the ratio form *is* (8.1.10), not a
`D`-dependent hypothesis. -/
def HasStringLRO (L : ℕ) (Phi : (Fin L → Fin 3) → ℂ) (q : Fin 3 → ℝ) : Prop :=
  ∀ alpha : Fin 3, q alpha ≤ expectationRatioRe
    (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)) Phi

/-! ## The prefix rotation as a region half turn -/

/-- Membership in the prefix site set is the numerical prefix condition. -/
theorem mem_edgeStringPrefixSites {L m : ℕ} (y : Fin L) :
    y ∈ (Finset.univ.filter fun z : Fin L => z.val < m) ↔ y.val < m := by
  simp

/-! ## Algebraic properties of the prefix rotation -/

/-- **The prefix rotation is an involution**: `R² = 1`, since each `u_α` is. -/
theorem edgeStringPrefixRotationS_mul_self (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    edgeStringPrefixRotationS L alpha m * edgeStringPrefixRotationS L alpha m = 1 :=
  halfTurnRegionS_mul_self L alpha _

/-- **The prefix rotation is self-adjoint**, hence unitary. -/
theorem edgeStringPrefixRotationS_isHermitian (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    (edgeStringPrefixRotationS L alpha m).IsHermitian :=
  halfTurnRegionS_isHermitian L alpha _

/-- The prefix rotation is unitary: `RᴴR = 1`. -/
theorem edgeStringPrefixRotationS_conjTranspose_mul_self (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    Matrix.conjTranspose (edgeStringPrefixRotationS L alpha m) *
        edgeStringPrefixRotationS L alpha m = 1 :=
  halfTurnRegionS_conjTranspose_mul_self L alpha _

/-- **Sites at or beyond the prefix are untouched**: `R^{(α)}_{<m}` commutes with any operator
supported at a site `w` with `m ≤ w`. -/
theorem edgeStringPrefixRotationS_commute_onSiteS_of_le (L : ℕ) (alpha : Fin 3) (m : ℕ)
    {w : Fin L} (h : m ≤ w.val) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Commute (edgeStringPrefixRotationS L alpha m) (onSiteS w A) :=
  halfTurnRegionS_commute_onSiteS_of_not_mem L alpha _
    (fun hw => absurd ((mem_edgeStringPrefixSites w).mp hw) (by omega)) A

/-- **Sites inside the prefix are conjugated by the half turn**: for `w < m`,
`R^{(α)}_{<m} A_w R^{(α)}_{<m} = (u_α A u_α)_w`. -/
theorem edgeStringPrefixRotationS_conj_onSiteS_of_lt (L : ℕ) (alpha : Fin 3) (m : ℕ)
    {w : Fin L} (h : w.val < m) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    edgeStringPrefixRotationS L alpha m * onSiteS w A * edgeStringPrefixRotationS L alpha m
      = onSiteS w (spinOneHalfTurnS alpha * A * spinOneHalfTurnS alpha) :=
  halfTurnRegionS_conj_onSiteS_of_mem L alpha _ ((mem_edgeStringPrefixSites w).mpr h) A

/-- **The prefix rotation commutes with its own axis component at every site**: inside the prefix
because `u_α` commutes with `Ŝ^{(α)}`, outside because the supports are disjoint. -/
theorem edgeStringPrefixRotationS_commute_component (L : ℕ) (alpha : Fin 3) (m : ℕ) (x : Fin L) :
    Commute (edgeStringPrefixRotationS L alpha m) (spinSSiteComponentS alpha x) :=
  halfTurnRegionS_commute_component L alpha _ x

/-- **The empty prefix carries the identity**: `R^{(α)}_{<0} = 1`.  This is why the left string of
the Kennedy–Tasaki rule (8.2.14) disappears at the left edge of an open chain. -/
theorem edgeStringPrefixRotationS_zero (L : ℕ) (alpha : Fin 3) :
    edgeStringPrefixRotationS L alpha 0 = 1 := by
  rw [edgeStringPrefixRotationS,
    show (Finset.univ.filter fun y : Fin L => y.val < 0) = ∅ by ext y; simp,
    halfTurnRegionS_empty]

/-- **Extending the prefix past one more site**: `R^{(α)}_{<x+1} = u_α^{(x)} R^{(α)}_{<x}`. -/
theorem edgeStringPrefixRotationS_succ (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    edgeStringPrefixRotationS L alpha (x.val + 1)
      = onSiteS x (spinOneHalfTurnS alpha) * edgeStringPrefixRotationS L alpha x.val := by
  have hset : (Finset.univ.filter fun y : Fin L => y.val < x.val + 1)
      = insert x (Finset.univ.filter fun y : Fin L => y.val < x.val) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h) <;> omega
  rw [edgeStringPrefixRotationS, edgeStringPrefixRotationS, hset,
    halfTurnRegionS_insert L alpha _ (by simp)]

/-- Two prefix rotations about the same axis commute. -/
theorem edgeStringPrefixRotationS_commute_self (L : ℕ) (alpha : Fin 3) (m m' : ℕ) :
    Commute (edgeStringPrefixRotationS L alpha m) (edgeStringPrefixRotationS L alpha m') :=
  halfTurnRegionS_commute L alpha alpha _ _

/-! ## The string operator -/

/-- The string operator's site-`x` term `A_x = Ŝ_x^{(α)} R^{(α)}_{<x}` is Hermitian, since its two
factors are Hermitian and commute. -/
theorem edgeStringTerm_isHermitian (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val).IsHermitian := by
  rw [spinSSiteComponentS_eq_onSiteS]
  refine Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinOneAxisS_isHermitian alpha))
    (edgeStringPrefixRotationS_isHermitian L alpha x.val) ?_
  have h := edgeStringPrefixRotationS_commute_component L alpha x.val x
  rw [spinSSiteComponentS_eq_onSiteS] at h
  exact h.symm

/-- **The string operator is self-adjoint** (Tasaki p. 236: at `S = 1` the exponential factor is its
own adjoint, and its factors act on sites disjoint from the leading spin component). -/
theorem edgeStringOrderOpS_isHermitian (L : ℕ) (alpha : Fin 3) :
    (edgeStringOrderOpS L alpha).IsHermitian := by
  change Matrix.conjTranspose (edgeStringOrderOpS L alpha) = edgeStringOrderOpS L alpha
  rw [edgeStringOrderOpS, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun x _ => (edgeStringTerm_isHermitian L alpha x).eq

/-- All string terms mutually commute: `u_α` commutes with `Ŝ^{(α)}`, prefix rotations commute with
each other, and distinct sites are disjoint.  This is the crux of the support argument for the
double commutator. -/
theorem edgeStringTerm_commute (L : ℕ) (alpha : Fin 3) (x y : Fin L) :
    Commute (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val)
      (spinSSiteComponentS alpha y * edgeStringPrefixRotationS L alpha y.val) := by
  have hcomp : Commute (spinSSiteComponentS alpha x) (spinSSiteComponentS alpha y) := by
    by_cases hxy : x = y
    · rw [hxy]
    · rw [spinSSiteComponentS_eq_onSiteS, spinSSiteComponentS_eq_onSiteS]
      exact onSiteS_commute_of_ne hxy _ _
  refine Commute.mul_left (Commute.mul_right hcomp ?_) ?_
  · exact (edgeStringPrefixRotationS_commute_component L alpha y.val x).symm
  · exact Commute.mul_right (edgeStringPrefixRotationS_commute_component L alpha x.val y)
      (edgeStringPrefixRotationS_commute_self L alpha x.val y.val)

/-! ## Conjugation by a global on-site involution -/

/-- **The prefix rotation is invariant under any global half turn**: if the involution `U` acts
site-wise by conjugation with a single-site involution `V` that fixes `u_α`, then `U R U = R`.
This is the many-body lift of `spinOneHalfTurnS_conj_spinOneHalfTurnS`. -/
theorem edgeStringPrefixRotationS_conj (L : ℕ) (alpha : Fin 3) (m : ℕ)
    (U : ManyBodyOpS (Fin L) 2) (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : U * U = 1) (hV : V * V = 1)
    (hVhalf : V * spinOneHalfTurnS alpha * V = spinOneHalfTurnS alpha)
    (hconj : ∀ (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ),
      U * onSiteS z A * U = onSiteS z (V * A * V)) :
    U * edgeStringPrefixRotationS L alpha m * U = edgeStringPrefixRotationS L alpha m :=
  halfTurnRegionS_conj L alpha _ U V hU hV hVhalf hconj

/-- **The conjugation law of the string operator** (Tasaki (8.1.12), p. 238): a global half turn
`U` acting site-wise by a single-site involution `V` that fixes `u_α` and sends `Ŝ^{(α)}` to
`c Ŝ^{(α)}` conjugates the string operator to `c` times itself. -/
theorem edgeStringOrderOpS_conj (L : ℕ) (alpha : Fin 3)
    (U : ManyBodyOpS (Fin L) 2) (V : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ)
    (hU : U * U = 1) (hV : V * V = 1)
    (hVhalf : V * spinOneHalfTurnS alpha * V = spinOneHalfTurnS alpha)
    (hVaxis : V * spinOneAxisS alpha * V = c • spinOneAxisS alpha)
    (hconj : ∀ (z : Fin L) (A : Matrix (Fin 3) (Fin 3) ℂ),
      U * onSiteS z A * U = onSiteS z (V * A * V)) :
    U * edgeStringOrderOpS L alpha * U = c • edgeStringOrderOpS L alpha := by
  rw [edgeStringOrderOpS, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conj_mul_of_mul_self hU, edgeStringPrefixRotationS_conj L alpha x.val U V hU hV hVhalf hconj,
    spinSSiteComponentS_eq_onSiteS, hconj, hVaxis, onSiteS_smul, Matrix.smul_mul]

/-- Every string term commutes with the whole string operator, since all string terms mutually
commute. -/
theorem edgeStringTerm_commute_edgeStringOrderOpS (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    Commute (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val)
      (edgeStringOrderOpS L alpha) := by
  rw [edgeStringOrderOpS]
  exact Commute.sum_right _ _ _ fun y _ => edgeStringTerm_commute L alpha x y

/-! ## The hidden-order norm bound -/

/-- **The proof-facing form of (8.1.10)**: hidden order gives the norm lower bound
`q_α L² ‖Φ‖² ≤ ‖Ô^{(α)}_string Φ‖²`, using only self-adjointness of the string operator.  In
particular the trial vector `Ô^{(α)}_string Φ` is nonzero when `q_α > 0` and `0 < L`. -/
theorem hasStringLRO_vecNormSqRe_bound (L : ℕ) (alpha : Fin 3) {q : Fin 3 → ℝ}
    {Phi : (Fin L → Fin 3) → ℂ} (hPhi : Phi ≠ 0) (hLRO : HasStringLRO L Phi q) :
    q alpha * (L : ℝ) ^ 2 * vecNormSqRe Phi
      ≤ vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) := by
  have hden : 0 < (star Phi ⬝ᵥ Phi).re := dotProduct_star_self_re_pos hPhi
  have hnn : (0 : ℝ) ≤ vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) :=
    (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  have hHerm := (edgeStringOrderOpS_isHermitian L alpha).eq
  have hnum : star Phi ⬝ᵥ (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)).mulVec Phi
      = ((L : ℂ)⁻¹ * (L : ℂ)⁻¹) *
        (star ((edgeStringOrderOpS L alpha).mulVec Phi) ⬝ᵥ
          (edgeStringOrderOpS L alpha).mulVec Phi) := by
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
      star_dotProduct_mulVec_conjTranspose, hHerm]
  have hnumre : (star Phi ⬝ᵥ (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)).mulVec Phi).re
      = ((L : ℝ)⁻¹ * (L : ℝ)⁻¹) *
        vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) := by
    rw [hnum, show ((L : ℂ)⁻¹ * (L : ℂ)⁻¹) = ((((L : ℝ)⁻¹ * (L : ℝ)⁻¹ : ℝ)) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    rfl
  have hq := hLRO alpha
  rw [expectationRatioRe, hnumre, le_div_iff₀ hden] at hq
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    simpa using hnn
  · have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hq (le_of_lt (pow_pos hL0 2))
    have hsimp : (L : ℝ) ^ 2 * (((L : ℝ)⁻¹ * (L : ℝ)⁻¹) *
        vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi))
        = vecNormSqRe ((edgeStringOrderOpS L alpha).mulVec Phi) := by
      field_simp
    rw [hsimp] at hmul
    have hcast : (star Phi ⬝ᵥ Phi).re = vecNormSqRe Phi := rfl
    rw [hcast] at hmul
    linarith

end LatticeSystem.Quantum
