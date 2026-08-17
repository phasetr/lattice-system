import LatticeSystem.Quantum.SpinS.AKLTStability
import LatticeSystem.Quantum.SpinS.AnisotropicEdgeSymmetry
import LatticeSystem.Quantum.SpinS.ManyBodyOperatorNorm
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46

/-!
# Tasaki §8.1.3: locality and the uniform double-commutator bound

The variational argument of §8.1.3 needs three quantitative facts about the open anisotropic chain:

* the Hamiltonian is a sum of local terms `ĥ_z` of range `r = 1` with `L`-independent norm;
* each string term `A_x = Ŝ_x^{(α)} R^{(α)}_{<x}` commutes with `ĥ_z` unless `x ∈ {z, z+1}` — for
  `x` to the left by disjointness, and for `x` to the right because the prefix rotation then covers
  the whole bond and its `Z₂ × Z₂` action squares away;
* consequently the double commutator `[Ô_string, [Ĥ, Ô_string]]` has norm `O(L)`, not `O(L³)`.

Tasaki (p. 238) proves only the single-commutator vanishing and then asserts the key estimate
`‖[Ô_string, [Ĥ, Ô_string]]‖ ≤ (const.) L` without a constant; the counting below is therefore
supplied here, in the shape of Problem 3.4.a, (3.4.13), p. 67.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eqs. (3.4.8)–(3.4.13), pp. 66–67; §8.1.3, p. 238.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-! ## The local decomposition of the open chain Hamiltonian -/

/-- The **right bond partner** of a site: `z + 1` when it exists, and `z` itself at the right
boundary (where the open chain has no bond).  The support of the local term `ĥ_z` is contained in
`{z, edgeBondPartner L z}`. -/
def edgeBondPartner (L : ℕ) (z : Fin L) : Fin L :=
  if h : z.val + 1 < L then ⟨z.val + 1, h⟩ else z

/-- The **local term** `ĥ_z = Ŝ_z · Ŝ_{z+1} + D (Ŝ_z^{(3)})²` of the open anisotropic chain (the
bond term is dropped at the right boundary).  Its support is `{z, z+1}`, so the interaction range
is `r = 1`. -/
noncomputable def edgeLocalTermS (L : ℕ) (D : ℝ) (z : Fin L) : ManyBodyOpS (Fin L) 2 :=
  (if h : z.val + 1 < L then spinSDot z ⟨z.val + 1, h⟩ 2 else 0) +
    (D : ℂ) • (spinSSiteOp3 z 2 * spinSSiteOp3 z 2)

/-- The open-chain Heisenberg part collapses to one bond per site: the doubled sum
`∑_{x,y} J x y Ŝ_x·Ŝ_y` has a single surviving `y` for each `x`. -/
private theorem heisenbergHamiltonianS_openAnisotropicChainCoupling_eq (L : ℕ) :
    heisenbergHamiltonianS (openAnisotropicChainCoupling L) 2
      = ∑ z : Fin L, (if h : z.val + 1 < L then spinSDot z ⟨z.val + 1, h⟩ 2 else 0) := by
  rw [heisenbergHamiltonianS]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x.val + 1 < L
  · rw [dif_pos h]
    refine (Finset.sum_eq_single (⟨x.val + 1, h⟩ : Fin L) ?_ ?_).trans ?_
    · intro y _ hy
      rw [openAnisotropicChainCoupling, if_neg, zero_smul]
      intro hcon
      exact hy (Fin.ext hcon)
    · intro hx
      exact absurd (Finset.mem_univ _) hx
    · rw [openAnisotropicChainCoupling, if_pos rfl, one_smul]
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [openAnisotropicChainCoupling, if_neg, zero_smul]
    intro hcon
    have := y.isLt
    omega

/-- **The local decomposition** `Ĥ = ∑_z ĥ_z` of the open anisotropic chain Hamiltonian. -/
theorem openAnisotropicChainHamiltonianS_eq_sum_local (L : ℕ) (D : ℝ) :
    openAnisotropicChainHamiltonianS L D = ∑ z : Fin L, edgeLocalTermS L D z := by
  simp only [edgeLocalTermS]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, openAnisotropicChainHamiltonianS,
    heisenbergHamiltonianS_openAnisotropicChainCoupling_eq]

/-- **The open chain Hamiltonian is Hermitian**: the coupling is real and the anisotropy term is a
real multiple of a sum of squares of Hermitian operators. -/
theorem openAnisotropicChainHamiltonianS_isHermitian (L : ℕ) (D : ℝ) :
    (openAnisotropicChainHamiltonianS L D).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ ?_
  · refine heisenbergHamiltonianS_isHermitian_of_real (fun x y => ?_) 2
    rw [openAnisotropicChainCoupling]
    split <;> simp
  · change Matrix.conjTranspose ((D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2)
      = (D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, Complex.star_def,
      Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp3_isHermitian 2))
      (onSiteS_isHermitian x (spinSOp3_isHermitian 2)) rfl).eq

/-! ## Locality of the local term -/

/-- **Range `r = 1`**: a single-site operator away from `{z, z+1}` commutes with `ĥ_z`. -/
theorem edgeLocalTermS_commute_onSiteS (L : ℕ) (D : ℝ) (z : Fin L) {w : Fin L}
    (hw : w ≠ z) (hw' : w ≠ edgeBondPartner L z) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Commute (onSiteS w A) (edgeLocalTermS L D z) := by
  rw [edgeLocalTermS]
  refine Commute.add_right ?_ ?_
  · by_cases hz : z.val + 1 < L
    · rw [dif_pos hz]
      have hz' : w ≠ (⟨z.val + 1, hz⟩ : Fin L) := by
        rw [edgeBondPartner, dif_pos hz] at hw'
        exact hw'
      rw [spinSDot]
      refine Commute.add_right (Commute.add_right ?_ ?_) ?_ <;>
        exact Commute.mul_right (onSiteS_commute_of_ne hw _ _) (onSiteS_commute_of_ne hz' _ _)
    · rw [dif_neg hz]
      exact Commute.zero_right _
  · exact Commute.smul_right
      (Commute.mul_right (onSiteS_commute_of_ne hw _ _) (onSiteS_commute_of_ne hw _ _)) _

/-- **A prefix rotation stopping at or before `z` is disjoint from `ĥ_z`.** -/
theorem edgeStringPrefixRotationS_commute_edgeLocalTermS_of_le (L : ℕ) (D : ℝ) (alpha : Fin 3)
    (m : ℕ) (z : Fin L) (h : m ≤ z.val) :
    Commute (edgeStringPrefixRotationS L alpha m) (edgeLocalTermS L D z) := by
  rw [edgeLocalTermS]
  refine Commute.add_right ?_ ?_
  · by_cases hz : z.val + 1 < L
    · rw [dif_pos hz, spinSDot]
      refine Commute.add_right (Commute.add_right ?_ ?_) ?_ <;>
        exact Commute.mul_right
          (edgeStringPrefixRotationS_commute_onSiteS_of_le L alpha m h _)
          (edgeStringPrefixRotationS_commute_onSiteS_of_le L alpha m
            (Nat.le_succ_of_le h) _)
    · rw [dif_neg hz]
      exact Commute.zero_right _
  · exact Commute.smul_right (Commute.mul_right
      (edgeStringPrefixRotationS_commute_onSiteS_of_le L alpha m h _)
      (edgeStringPrefixRotationS_commute_onSiteS_of_le L alpha m h _)) _

/-- **A prefix rotation covering the whole bond leaves `ĥ_z` invariant** — the `Z₂ × Z₂` action
squares away on the bond and on the on-site anisotropy — hence commutes with it.  This is the case
Tasaki's "the string is a `π` rotation of the sub-chain" remark covers (p. 238), and it is where the
open boundary condition is essential. -/
theorem edgeStringPrefixRotationS_commute_edgeLocalTermS_of_lt (L : ℕ) (D : ℝ) (alpha : Fin 3)
    (m : ℕ) (z : Fin L) (h : z.val + 1 < m) :
    Commute (edgeStringPrefixRotationS L alpha m) (edgeLocalTermS L D z) := by
  have hU := edgeStringPrefixRotationS_mul_self L alpha m
  have hconj : edgeStringPrefixRotationS L alpha m * edgeLocalTermS L D z *
      edgeStringPrefixRotationS L alpha m = edgeLocalTermS L D z := by
    rw [edgeLocalTermS, Matrix.mul_add, Matrix.add_mul]
    congr 1
    · by_cases hz : z.val + 1 < L
      · rw [dif_pos hz]
        exact spinSDot_conj_of_onSiteS_conj alpha hU
          (fun A => edgeStringPrefixRotationS_conj_onSiteS_of_lt L alpha m
            (Nat.lt_of_succ_lt h) A)
          (fun A => edgeStringPrefixRotationS_conj_onSiteS_of_lt L alpha m h A)
      · rw [dif_neg hz]
        simp
    · rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      exact spinSSiteOp3_sq_conj_of_onSiteS_conj alpha hU
        (fun A => edgeStringPrefixRotationS_conj_onSiteS_of_lt L alpha m
          (Nat.lt_of_succ_lt h) A)
  have hstep := congrArg (fun M => M * edgeStringPrefixRotationS L alpha m) hconj
  simp only [mul_assoc, hU, mul_one] at hstep
  exact hstep

/-- **The support of a string term**: `A_x = Ŝ_x^{(α)} R^{(α)}_{<x}` commutes with `ĥ_z` whenever
`x ∉ {z, z+1}`.  Left of the bond the supports are disjoint; right of the bond the prefix rotation
covers the whole bond and acts trivially on it. -/
theorem edgeStringTerm_commute_edgeLocalTermS (L : ℕ) (D : ℝ) (alpha : Fin 3) (z : Fin L)
    {x : Fin L} (hx : x ≠ z) (hx' : x ≠ edgeBondPartner L z) :
    Commute (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val)
      (edgeLocalTermS L D z) := by
  refine Commute.mul_left ?_ ?_
  · rw [spinSSiteComponentS_eq_onSiteS]
    exact edgeLocalTermS_commute_onSiteS L D z hx hx' _
  · by_cases hle : x.val ≤ z.val
    · exact edgeStringPrefixRotationS_commute_edgeLocalTermS_of_le L D alpha x.val z hle
    · refine edgeStringPrefixRotationS_commute_edgeLocalTermS_of_lt L D alpha x.val z ?_
      by_cases hz : z.val + 1 < L
      · have hne : x.val ≠ z.val + 1 := by
          intro hcon
          exact hx' (by rw [edgeBondPartner, dif_pos hz]; exact Fin.ext hcon)
        omega
      · have := x.isLt
        omega

/-! ## Uniform operator-norm bounds -/

/-- The prefix rotation is unitary, hence of operator norm one. -/
theorem manyBodyOperatorNormS_edgeStringPrefixRotationS (L : ℕ) (alpha : Fin 3) (m : ℕ) :
    manyBodyOperatorNormS (edgeStringPrefixRotationS L alpha m) = 1 :=
  manyBodyOperatorNormS_eq_one_of_unitary
    (edgeStringPrefixRotationS_conjTranspose_mul_self L alpha m)

/-- Each site-embedded half turn is a Hermitian involution, hence of operator norm one. -/
private theorem manyBodyOperatorNormS_onSiteS_halfTurn (alpha : Fin 3) (x : Fin L) :
    manyBodyOperatorNormS (onSiteS x (spinOneHalfTurnS alpha) : ManyBodyOpS (Fin L) 2) = 1 := by
  refine manyBodyOperatorNormS_eq_one_of_unitary ?_
  rw [(onSiteS_isHermitian x (spinOneHalfTurnS_isHermitian alpha)).eq,
    onSiteS_mul_onSiteS_same, spinOneHalfTurnS_mul_self, onSiteS_one]

/-- **The spin-one axis components have operator norm at most one**: their square is
`(1 - u_α)/2`, a mean of two unitaries. -/
theorem manyBodyOperatorNormS_spinSSiteComponentS_le (alpha : Fin 3) (x : Fin L) :
    manyBodyOperatorNormS (spinSSiteComponentS alpha x) ≤ 1 := by
  have hHerm : (spinSSiteComponentS alpha x).IsHermitian := by
    rw [spinSSiteComponentS_eq_onSiteS]
    exact onSiteS_isHermitian x (spinOneAxisS_isHermitian alpha)
  have hu : spinOneAxisS alpha * spinOneAxisS alpha
      = (2 : ℂ)⁻¹ • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - spinOneHalfTurnS alpha) := by
    rw [spinOneHalfTurnS_eq_one_sub_two_smul_sq, sub_sub_cancel, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul, pow_two]
  have hsq : manyBodyOperatorNormS (spinSSiteComponentS alpha x) ^ 2
      = manyBodyOperatorNormS
          (onSiteS x (spinOneAxisS alpha * spinOneAxisS alpha) : ManyBodyOpS (Fin L) 2) := by
    rw [← manyBodyOperatorNormS_conjTranspose_mul_self, hHerm.eq, spinSSiteComponentS_eq_onSiteS,
      onSiteS_mul_onSiteS_same]
  have hbound : manyBodyOperatorNormS
      (onSiteS x (spinOneAxisS alpha * spinOneAxisS alpha) : ManyBodyOpS (Fin L) 2) ≤ 1 := by
    rw [hu, onSiteS_smul, manyBodyOperatorNormS_smul, onSiteS_sub, onSiteS_one]
    have htri := manyBodyOperatorNormS_sub_le (1 : ManyBodyOpS (Fin L) 2)
      (onSiteS x (spinOneHalfTurnS alpha))
    rw [manyBodyOperatorNormS_one, manyBodyOperatorNormS_onSiteS_halfTurn alpha x] at htri
    have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by norm_num
    rw [hc]
    linarith
  nlinarith [manyBodyOperatorNormS_nonneg (spinSSiteComponentS alpha x)]

/-- **Each string term has operator norm at most one**: a spin component times a unitary. -/
theorem manyBodyOperatorNormS_edgeStringTerm_le (L : ℕ) (alpha : Fin 3) (x : Fin L) :
    manyBodyOperatorNormS
        (spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val) ≤ 1 := by
  refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
  rw [manyBodyOperatorNormS_edgeStringPrefixRotationS, mul_one]
  exact manyBodyOperatorNormS_spinSSiteComponentS_le alpha x

/-- A product of two operators of norm at most one has norm at most one. -/
private theorem manyBodyOperatorNormS_mul_le_one {A B : ManyBodyOpS (Fin L) 2}
    (hA : manyBodyOperatorNormS A ≤ 1) (hB : manyBodyOperatorNormS B ≤ 1) :
    manyBodyOperatorNormS (A * B) ≤ 1 :=
  le_trans (manyBodyOperatorNormS_mul_le A B)
    (mul_le_one₀ hA (manyBodyOperatorNormS_nonneg B) hB)

/-- **The local terms have an `L`-independent norm bound** `‖ĥ_z‖ ≤ 3 + D`: three bond factors of
norm at most one, plus the anisotropy. -/
theorem manyBodyOperatorNormS_edgeLocalTermS_le (L : ℕ) {D : ℝ} (hD : 0 ≤ D) (z : Fin L) :
    manyBodyOperatorNormS (edgeLocalTermS L D z) ≤ 3 + D := by
  have h1 : ∀ w : Fin L,
      manyBodyOperatorNormS (onSiteS w (spinSOp1 2) : ManyBodyOpS (Fin L) 2) ≤ 1 :=
    fun w => manyBodyOperatorNormS_spinSSiteComponentS_le 0 w
  have h2 : ∀ w : Fin L,
      manyBodyOperatorNormS (onSiteS w (spinSOp2 2) : ManyBodyOpS (Fin L) 2) ≤ 1 :=
    fun w => manyBodyOperatorNormS_spinSSiteComponentS_le 1 w
  have h3 : ∀ w : Fin L,
      manyBodyOperatorNormS (onSiteS w (spinSOp3 2) : ManyBodyOpS (Fin L) 2) ≤ 1 :=
    fun w => manyBodyOperatorNormS_spinSSiteComponentS_le 2 w
  have hbond : manyBodyOperatorNormS
      (if h : z.val + 1 < L then spinSDot z ⟨z.val + 1, h⟩ 2 else 0) ≤ 3 := by
    by_cases hz : z.val + 1 < L
    · rw [dif_pos hz, spinSDot]
      have e1 := manyBodyOperatorNormS_mul_le_one (h1 z) (h1 (⟨z.val + 1, hz⟩ : Fin L))
      have e2 := manyBodyOperatorNormS_mul_le_one (h2 z) (h2 (⟨z.val + 1, hz⟩ : Fin L))
      have e3 := manyBodyOperatorNormS_mul_le_one (h3 z) (h3 (⟨z.val + 1, hz⟩ : Fin L))
      refine le_trans (manyBodyOperatorNormS_add_le _ _) ?_
      have e12 := manyBodyOperatorNormS_add_le
        ((onSiteS z (spinSOp1 2) : ManyBodyOpS (Fin L) 2) *
          onSiteS (⟨z.val + 1, hz⟩ : Fin L) (spinSOp1 2))
        ((onSiteS z (spinSOp2 2) : ManyBodyOpS (Fin L) 2) *
          onSiteS (⟨z.val + 1, hz⟩ : Fin L) (spinSOp2 2))
      linarith
    · rw [dif_neg hz, manyBodyOperatorNormS_zero]
      linarith
  have honsite : manyBodyOperatorNormS
      ((D : ℂ) • ((spinSSiteOp3 z 2 : ManyBodyOpS (Fin L) 2) * spinSSiteOp3 z 2)) ≤ D := by
    have hsq : manyBodyOperatorNormS
        ((spinSSiteOp3 z 2 : ManyBodyOpS (Fin L) 2) * spinSSiteOp3 z 2) ≤ 1 :=
      manyBodyOperatorNormS_mul_le_one (h3 z) (h3 z)
    rw [manyBodyOperatorNormS_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD]
    nlinarith
  refine le_trans (manyBodyOperatorNormS_add_le _ _) ?_
  linarith

/-! ## The uniform double-commutator bound -/

/-- The at most two sites carrying the support of the local term `ĥ_z`. -/
private def edgeBondSupport (L : ℕ) (z : Fin L) : Finset (Fin L) := {z, edgeBondPartner L z}

/-- The support of a local term has at most two sites — the source of the `O(L)` (rather than
`O(L³)`) size of the double commutator. -/
private theorem edgeBondSupport_card_le (L : ℕ) (z : Fin L) :
    ((edgeBondSupport L z).card : ℝ) ≤ 2 := by
  have h : (edgeBondSupport L z).card ≤ 2 := by
    rw [edgeBondSupport]
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  exact_mod_cast h

/-- Membership outside the bond support means the site is neither endpoint. -/
private theorem not_mem_edgeBondSupport (L : ℕ) (z : Fin L) {x : Fin L}
    (hx : x ∉ edgeBondSupport L z) : x ≠ z ∧ x ≠ edgeBondPartner L z := by
  rw [edgeBondSupport, Finset.mem_insert, Finset.mem_singleton] at hx
  push Not at hx
  exact hx

/-- **The uniform `O(L)` double-commutator bound** for the string operator.  Tasaki (p. 238) states
this as `‖[Ô_string, [Ĥ, Ô_string]]‖ ≤ (const.) L` without a constant; the explicit value below
comes from the Problem 3.4.a counting shape (3.4.13), p. 67: at most two sites carry each local
term, each string term and each prefix rotation has norm at most one, and `‖ĥ_z‖ ≤ 3 + D`.  The
numeral is deliberately generous; the invariant is that no factor of `L` hides in it. -/
theorem edgeDoubleCommutator_manyBodyOperatorNormS_le (L : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (alpha : Fin 3) :
    manyBodyOperatorNormS
        (Matrix.conjTranspose (edgeStringOrderOpS L alpha) *
            (openAnisotropicChainHamiltonianS L D * edgeStringOrderOpS L alpha -
              edgeStringOrderOpS L alpha * openAnisotropicChainHamiltonianS L D) -
          (openAnisotropicChainHamiltonianS L D * edgeStringOrderOpS L alpha -
            edgeStringOrderOpS L alpha * openAnisotropicChainHamiltonianS L D) *
            Matrix.conjTranspose (edgeStringOrderOpS L alpha))
      ≤ 64 * (3 + D) * (L : ℝ) := by
  classical
  set O : ManyBodyOpS (Fin L) 2 := edgeStringOrderOpS L alpha with hOdef
  set A : Fin L → ManyBodyOpS (Fin L) 2 :=
    fun x => spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val with hAdef
  set hl : Fin L → ManyBodyOpS (Fin L) 2 := fun z => edgeLocalTermS L D z with hldef
  have hOsum : O = ∑ x : Fin L, A x := rfl
  have hAnorm : ∀ x : Fin L, manyBodyOperatorNormS (A x) ≤ 1 :=
    fun x => manyBodyOperatorNormS_edgeStringTerm_le L alpha x
  have hlnorm : ∀ z : Fin L, manyBodyOperatorNormS (hl z) ≤ 3 + D :=
    fun z => manyBodyOperatorNormS_edgeLocalTermS_le L hD z
  have hlnonneg : (0 : ℝ) ≤ 3 + D := by linarith
  -- per-site bound on the inner commutator and the full double commutator
  have hper : ∀ z : Fin L,
      manyBodyOperatorNormS (O * (hl z * O - O * hl z) - (hl z * O - O * hl z) * O)
        ≤ 16 * (3 + D) := by
    intro z
    set C : ManyBodyOpS (Fin L) 2 := hl z * O - O * hl z with hCdef
    have hCsum : C = ∑ y ∈ edgeBondSupport L z, (hl z * A y - A y * hl z) := by
      rw [hCdef, hOsum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro y _ hy
      obtain ⟨hy1, hy2⟩ := not_mem_edgeBondSupport L z hy
      rw [sub_eq_zero]
      exact ((edgeStringTerm_commute_edgeLocalTermS L D alpha z hy1 hy2).eq).symm
    have hCnorm : manyBodyOperatorNormS C ≤ 4 * (3 + D) := by
      rw [hCsum]
      refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
      have hterm : ∀ y ∈ edgeBondSupport L z,
          manyBodyOperatorNormS (hl z * A y - A y * hl z) ≤ 2 * (3 + D) := by
        intro y _
        refine le_trans (manyBodyOperatorNormS_sub_le _ _) ?_
        have e1 := le_trans (manyBodyOperatorNormS_mul_le (hl z) (A y))
          (mul_le_mul (hlnorm z) (hAnorm y) (manyBodyOperatorNormS_nonneg _) hlnonneg)
        have e2 := le_trans (manyBodyOperatorNormS_mul_le (A y) (hl z))
          (mul_le_mul (hAnorm y) (hlnorm z) (manyBodyOperatorNormS_nonneg _) zero_le_one)
        linarith
      refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
      rw [nsmul_eq_mul]
      nlinarith [edgeBondSupport_card_le L z]
    have hACcomm : ∀ x : Fin L, x ∉ edgeBondSupport L z → A x * C - C * A x = 0 := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := not_mem_edgeBondSupport L z hx
      rw [sub_eq_zero, hCdef]
      refine Commute.eq ?_
      refine Commute.sub_right ?_ ?_
      · exact Commute.mul_right (edgeStringTerm_commute_edgeLocalTermS L D alpha z hx1 hx2)
          (edgeStringTerm_commute_edgeStringOrderOpS L alpha x)
      · exact Commute.mul_right (edgeStringTerm_commute_edgeStringOrderOpS L alpha x)
          (edgeStringTerm_commute_edgeLocalTermS L D alpha z hx1 hx2)
    have hOCsum : O * C - C * O = ∑ x ∈ edgeBondSupport L z, (A x * C - C * A x) := by
      rw [hOsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hACcomm x hx).symm
    rw [hOCsum]
    refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
    have hterm : ∀ x ∈ edgeBondSupport L z,
        manyBodyOperatorNormS (A x * C - C * A x) ≤ 8 * (3 + D) := by
      intro x _
      refine le_trans (manyBodyOperatorNormS_sub_le _ _) ?_
      have hCnn : (0 : ℝ) ≤ manyBodyOperatorNormS C := manyBodyOperatorNormS_nonneg C
      have e1 := le_trans (manyBodyOperatorNormS_mul_le (A x) C)
        (mul_le_mul (hAnorm x) hCnorm hCnn zero_le_one)
      have e2 := le_trans (manyBodyOperatorNormS_mul_le C (A x))
        (mul_le_mul hCnorm (hAnorm x) (manyBodyOperatorNormS_nonneg _) (by linarith))
      linarith
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [nsmul_eq_mul]
    nlinarith [edgeBondSupport_card_le L z]
  have hOherm : Matrix.conjTranspose O = O := (edgeStringOrderOpS_isHermitian L alpha).eq
  rw [hOherm, openAnisotropicChainHamiltonianS_eq_sum_local L D]
  rw [show (∑ z : Fin L, edgeLocalTermS L D z) = ∑ z : Fin L, hl z from rfl]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ fun z _ => hper z) ?_
  rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  nlinarith [Nat.cast_nonneg (α := ℝ) L]

/-! ## The trial-state Rayleigh bound -/

/-- **The Koma–Tasaki variational estimate for the string trial state** (Tasaki (8.1.11), p. 237,
combined with the §3.4 gap bound (3.4.8), p. 66).  Under hidden order the trial state
`Ô^{(α)}_string Φ` has Rayleigh energy at most `E₀ + C_α / L` with the `L`-independent constant
`C_α = 64 (3 + D) / q_α`.

Convention note: the repository's `variational_gap_le_double_commutator` bounds the gap by the
*symmetrised* double commutator, which for a self-adjoint `A` is exactly twice Tasaki's (3.4.8)
right-hand side; the constant below is therefore twice Tasaki's sharp value.  Only the existence of
an `L`-independent constant is asserted by Theorem 8.2, so no sharper variant is introduced. -/
theorem edgeTrial_expectationRatioRe_le (L : ℕ) {D : ℝ} (hD : 0 ≤ D) (alpha : Fin 3)
    {q : Fin 3 → ℝ} (hq : 0 < q alpha) {E0 : ℝ} {Phi : (Fin L → Fin 3) → ℂ} (hL : 0 < L)
    (hGS : IsUniqueChainGroundState (openAnisotropicChainHamiltonianS L D) E0 Phi)
    (hLRO : HasStringLRO L Phi q) :
    expectationRatioRe (openAnisotropicChainHamiltonianS L D)
        ((edgeStringOrderOpS L alpha).mulVec Phi)
      ≤ E0 + 64 * (3 + D) / q alpha / (L : ℝ) := by
  obtain ⟨hPhi, hev, hground, _⟩ := hGS
  set H : ManyBodyOpS (Fin L) 2 := openAnisotropicChainHamiltonianS L D with hHdef
  set O : ManyBodyOpS (Fin L) 2 := edgeStringOrderOpS L alpha with hOdef
  have hHherm : H.IsHermitian := openAnisotropicChainHamiltonianS_isHermitian L D
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hPhiNorm : 0 < vecNormSqRe Phi := dotProduct_star_self_re_pos hPhi
  have hbridge : q alpha * (L : ℝ) ^ 2 * vecNormSqRe Phi
      ≤ vecNormSqRe (O.mulVec Phi) := hasStringLRO_vecNormSqRe_bound L alpha hPhi hLRO
  have hvpos : 0 < vecNormSqRe (O.mulVec Phi) := by
    have hp : 0 < q alpha * (L : ℝ) ^ 2 * vecNormSqRe Phi := by positivity
    linarith
  have hmin : ∀ (E : ℂ) (Psi : (Fin L → Fin 3) → ℂ), Psi ≠ 0 → H.mulVec Psi = E • Psi →
      ((E0 : ℂ)).re ≤ E.re := by
    intro E Psi hPsi hevPsi
    have him : E.im = 0 := hermitian_mulVec_eigenvalue_im_zero hHherm hPsi hevPsi
    have hE : ((E.re : ℝ) : ℂ) = E := Complex.ext (by simp) (by simp [him])
    have hmem : E.re ∈ realSpectrum H := ⟨Psi, hPsi, by rw [hE]; exact hevPsi⟩
    simpa using hground.2 _ hmem
  have hgap := variational_gap_le_double_commutator O H hHherm Phi (E0 : ℂ) hev hmin hPhi
  have hnorm := edgeDoubleCommutator_manyBodyOperatorNormS_le L hD alpha
  have hcs := abs_re_dotProduct_mulVec_le_norm_mul
    (Matrix.conjTranspose O * (H * O - O * H) - (H * O - O * H) * Matrix.conjTranspose O) Phi Phi
  have hPhiLp : ‖(WithLp.toLp 2 Phi : EuclideanSpace ℂ (Fin L → Fin 3))‖
      * ‖(WithLp.toLp 2 Phi : EuclideanSpace ℂ (Fin L → Fin 3))‖ = vecNormSqRe Phi := by
    rw [← sqrt_vecNormSqRe_eq_toLp_norm, Real.mul_self_sqrt hPhiNorm.le]
  have hnum : (star Phi ⬝ᵥ (Matrix.conjTranspose O * (H * O - O * H)
      - (H * O - O * H) * Matrix.conjTranspose O).mulVec Phi).re
      ≤ 64 * (3 + D) * (L : ℝ) * vecNormSqRe Phi := by
    refine le_trans (le_abs_self _) (le_trans hcs ?_)
    rw [mul_assoc, hPhiLp]
    exact mul_le_mul_of_nonneg_right hnorm hPhiNorm.le
  have hgap' : (star (O.mulVec Phi) ⬝ᵥ H.mulVec (O.mulVec Phi)).re
      - E0 * vecNormSqRe (O.mulVec Phi) ≤ 64 * (3 + D) * (L : ℝ) * vecNormSqRe Phi := by
    have hcomb := le_trans hgap hnum
    simpa using hcomb
  have hveq : (star (O.mulVec Phi) ⬝ᵥ O.mulVec Phi).re = vecNormSqRe (O.mulVec Phi) := rfl
  rw [expectationRatioRe, hveq, div_le_iff₀ hvpos]
  have hcnn : (0 : ℝ) ≤ 64 * (3 + D) / q alpha / (L : ℝ) := by positivity
  have hscale := mul_le_mul_of_nonneg_left hbridge hcnn
  have hcid : 64 * (3 + D) / q alpha / (L : ℝ) * (q alpha * (L : ℝ) ^ 2)
      = 64 * (3 + D) * (L : ℝ) := by
    field_simp
  nlinarith [hgap', hscale, hcid]

end LatticeSystem.Quantum
