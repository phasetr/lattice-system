/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 3 (Lemma R2) — locality layer.

This file develops the operator-norm locality of the double commutator
`ĝ_x = [Ô⁺, [ĥ_x, Ô⁻]]` driving the renormalized numerator estimate (Lemma R2, eq. (4.2.68)),
building on the Lemma R1 layer in `AndersonTowerEnergyBound`.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBound
import LatticeSystem.Quantum.SpinS.MultiSiteDot

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Per-site and per-bond operator-norm bounds (P9-1) -/

/-- **Per-site `Ŝ¹` norm bound** `‖Ŝₓ^{(1)}‖ ≤ N`: triangle inequality over `Ŝ¹ = (Ŝ⁺ + Ŝ⁻)/2`,
each ladder operator having norm `≤ N`. -/
theorem onSiteS_spinSOp1_manyBodyOperatorNormS_le (x : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (onSiteS x (spinSOp1 N)) ≤ (N : ℝ) := by
  rw [spinSOp1, onSiteS_smul, onSiteS_add, manyBodyOperatorNormS_smul,
    show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have h1 := spinSSiteOpPlus_manyBodyOperatorNormS_le (N := N) x hN
  have h2 := spinSSiteOpMinus_manyBodyOperatorNormS_le (N := N) x hN
  calc 1 / 2 * manyBodyOperatorNormS (onSiteS x (spinSOpPlus N) + onSiteS x (spinSOpMinus N))
      ≤ 1 / 2 * (manyBodyOperatorNormS (onSiteS x (spinSOpPlus N))
          + manyBodyOperatorNormS (onSiteS x (spinSOpMinus N))) :=
        mul_le_mul_of_nonneg_left (manyBodyOperatorNormS_add_le _ _) (by norm_num)
    _ ≤ 1 / 2 * ((N : ℝ) + (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = (N : ℝ) := by ring

/-- **Per-site `Ŝ²` norm bound** `‖Ŝₓ^{(2)}‖ ≤ N`: triangle over `Ŝ² = (Ŝ⁺ − Ŝ⁻)/(2i)`. -/
theorem onSiteS_spinSOp2_manyBodyOperatorNormS_le (x : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (onSiteS x (spinSOp2 N)) ≤ (N : ℝ) := by
  rw [spinSOp2, onSiteS_smul, onSiteS_sub, manyBodyOperatorNormS_smul,
    show ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 from by
      rw [norm_div, norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]]
  have h1 := spinSSiteOpPlus_manyBodyOperatorNormS_le (N := N) x hN
  have h2 := spinSSiteOpMinus_manyBodyOperatorNormS_le (N := N) x hN
  calc 1 / 2 * manyBodyOperatorNormS (onSiteS x (spinSOpPlus N) - onSiteS x (spinSOpMinus N))
      ≤ 1 / 2 * (manyBodyOperatorNormS (onSiteS x (spinSOpPlus N))
          + manyBodyOperatorNormS (onSiteS x (spinSOpMinus N))) :=
        mul_le_mul_of_nonneg_left (manyBodyOperatorNormS_sub_le _ _) (by norm_num)
    _ ≤ 1 / 2 * ((N : ℝ) + (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = (N : ℝ) := by ring

/-- **Per-bond norm bound** `‖Ŝ_x · Ŝ_y‖ ≤ 3 N²`: triangle over the three Cartesian products, each
factor having per-site norm `≤ N`. -/
theorem spinSDot_manyBodyOperatorNormS_le (x y : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (spinSDot x y N) ≤ 3 * (N : ℝ) ^ 2 := by
  have hp1x := onSiteS_spinSOp1_manyBodyOperatorNormS_le (N := N) x hN
  have hp1y := onSiteS_spinSOp1_manyBodyOperatorNormS_le (N := N) y hN
  have hp2x := onSiteS_spinSOp2_manyBodyOperatorNormS_le (N := N) x hN
  have hp2y := onSiteS_spinSOp2_manyBodyOperatorNormS_le (N := N) y hN
  have hhalf : (N : ℝ) / 2 ≤ N := by linarith
  have hp3x := le_trans (onSiteS_spinSOp3_manyBodyOperatorNormS_le (N := N) x) hhalf
  have hp3y := le_trans (onSiteS_spinSOp3_manyBodyOperatorNormS_le (N := N) y) hhalf
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hb : ∀ A B : ManyBodyOpS Λ N, manyBodyOperatorNormS A ≤ N → manyBodyOperatorNormS B ≤ N →
      manyBodyOperatorNormS (A * B) ≤ (N : ℝ) ^ 2 := by
    intro A B hA hB
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    calc manyBodyOperatorNormS A * manyBodyOperatorNormS B ≤ (N : ℝ) * (N : ℝ) :=
          mul_le_mul hA hB (manyBodyOperatorNormS_nonneg _) hN0
      _ = (N : ℝ) ^ 2 := by ring
  rw [spinSDot_def]
  refine le_trans (manyBodyOperatorNormS_add_le _ _) ?_
  refine le_trans (add_le_add (manyBodyOperatorNormS_add_le _ _) (le_refl _)) ?_
  have h1 := hb _ _ hp1x hp1y
  have h2 := hb _ _ hp2x hp2y
  have h3 := hb _ _ hp3x hp3y
  linarith

/-! ### Locality of the bond–order commutators (P9-2) -/

/-- **Disjoint commutation**: a bond operator `Ŝ_x · Ŝ_y` commutes with any site-`z` operator when
`z ∉ {x, y}` (the on-site factors live on disjoint sites). -/
theorem spinSDot_commute_onSiteS_of_ne (x y z : Λ) (hzx : z ≠ x) (hzy : z ≠ y)
    (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (spinSDot x y N) (onSiteS z B) := by
  have cx : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      Commute (onSiteS x A : ManyBodyOpS Λ N) (onSiteS z B) :=
    fun A => onSiteS_commute_of_ne (Ne.symm hzx) A B
  have cy : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      Commute (onSiteS y A : ManyBodyOpS Λ N) (onSiteS z B) :=
    fun A => onSiteS_commute_of_ne (Ne.symm hzy) A B
  rw [spinSDot_def]
  exact (((cx _).mul_left (cy _)).add_left ((cx _).mul_left (cy _))).add_left
    ((cx _).mul_left (cy _))

/-- The bond–staggered-lowering commutator `[Ŝ_x·Ŝ_y, Ŝ_z⁻]` vanishes off the bond (`z ∉ {x,y}`). -/
theorem spinSDot_commutator_spinSSiteOpMinus_eq_zero_of_ne (x y z : Λ)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    spinSDot x y N * spinSSiteOpMinus z N - spinSSiteOpMinus z N * spinSDot x y N = 0 := by
  have := spinSDot_commute_onSiteS_of_ne x y z hzx hzy (spinSOpMinus N)
  rw [spinSSiteOpMinus, sub_eq_zero]
  exact this.eq

/-- The bond–staggered-raising commutator `[Ŝ_x·Ŝ_y, Ŝ_z⁺]` vanishes off the bond (`z ∉ {x,y}`). -/
theorem spinSDot_commutator_spinSSiteOpPlus_eq_zero_of_ne (x y z : Λ)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    spinSDot x y N * spinSSiteOpPlus z N - spinSSiteOpPlus z N * spinSDot x y N = 0 := by
  have := spinSDot_commute_onSiteS_of_ne x y z hzx hzy (spinSOpPlus N)
  rw [spinSSiteOpPlus, sub_eq_zero]
  exact this.eq

/-- **Two-site restriction of the bond–order commutator**: for a bond `x ≠ y`, `[Ŝ_x·Ŝ_y, Ô_L⁻]`
collapses to the two on-bond contributions, since the staggered lowering operator's off-bond letters
commute with `Ŝ_x·Ŝ_y`. -/
theorem spinSDot_commutator_staggeredLoweringOpS_support (A : Λ → Bool) (x y : Λ) (hxy : x ≠ y) :
    spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N
      = (if A x then (1 : ℂ) else (-1 : ℂ))
          • (spinSDot x y N * spinSSiteOpMinus x N - spinSSiteOpMinus x N * spinSDot x y N)
        + (if A y then (1 : ℂ) else (-1 : ℂ))
          • (spinSDot x y N * spinSSiteOpMinus y N - spinSSiteOpMinus y N * spinSDot x y N) := by
  unfold staggeredLoweringOpS
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hterm : ∀ z : Λ,
      spinSDot x y N * ((if A z then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpMinus z N)
      - ((if A z then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpMinus z N) * spinSDot x y N
      = (if A z then (1 : ℂ) else (-1 : ℂ))
          • (spinSDot x y N * spinSSiteOpMinus z N - spinSSiteOpMinus z N * spinSDot x y N) := by
    intro z; rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [Finset.sum_congr rfl (fun z _ => hterm z)]
  rw [← Finset.sum_subset (Finset.subset_univ ({x, y} : Finset Λ)) (fun z _ hz => ?_)]
  · rw [Finset.sum_pair hxy]
  · have hzx : z ≠ x := fun h => hz (by rw [h]; exact Finset.mem_insert_self x {y})
    have hzy : z ≠ y := fun h => hz (by
      rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    rw [spinSDot_commutator_spinSSiteOpMinus_eq_zero_of_ne x y z hzx hzy, smul_zero]

/-- A single bond–site lowering commutator is bounded: `‖[Ŝ_x·Ŝ_y, Ŝ_z⁻]‖ ≤ 6 N³`. -/
theorem spinSDot_commutator_spinSSiteOpMinus_norm_le (x y z : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS
      (spinSDot x y N * spinSSiteOpMinus z N - spinSSiteOpMinus z N * spinSDot x y N)
      ≤ 6 * (N : ℝ) ^ 3 := by
  have hdot := spinSDot_manyBodyOperatorNormS_le (N := N) x y hN
  have hmin := spinSSiteOpMinus_manyBodyOperatorNormS_le (N := N) z hN
  refine le_trans (manyBodyOperatorNormS_sub_le _ _) ?_
  have h1 : manyBodyOperatorNormS (spinSDot x y N * spinSSiteOpMinus z N)
      ≤ 3 * (N : ℝ) ^ 2 * (N : ℝ) := by
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    exact mul_le_mul hdot hmin (manyBodyOperatorNormS_nonneg _) (by positivity)
  have h2 : manyBodyOperatorNormS (spinSSiteOpMinus z N * spinSDot x y N)
      ≤ (N : ℝ) * (3 * (N : ℝ) ^ 2) := by
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    exact mul_le_mul hmin hdot (manyBodyOperatorNormS_nonneg _) (by positivity)
  nlinarith [h1, h2]

/-- **Bond–order commutator norm bound** `‖[Ŝ_x·Ŝ_y, Ô_L⁻]‖ ≤ 12 N³` for `x ≠ y`. -/
theorem spinSDot_commutator_staggeredLoweringOpS_norm_le (A : Λ → Bool) (x y : Λ)
    (hxy : x ≠ y) (hN : 1 ≤ N) :
    manyBodyOperatorNormS
      (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
      ≤ 12 * (N : ℝ) ^ 3 := by
  rw [spinSDot_commutator_staggeredLoweringOpS_support A x y hxy]
  refine le_trans (manyBodyOperatorNormS_add_le _ _) ?_
  have hx := spinSDot_commutator_spinSSiteOpMinus_norm_le (N := N) x y x hN
  have hy := spinSDot_commutator_spinSSiteOpMinus_norm_le (N := N) x y y hN
  rw [manyBodyOperatorNormS_smul, manyBodyOperatorNormS_smul,
    show ‖(if A x then (1 : ℂ) else (-1 : ℂ))‖ = 1 from by split_ifs <;> simp,
    show ‖(if A y then (1 : ℂ) else (-1 : ℂ))‖ = 1 from by split_ifs <;> simp, one_mul, one_mul]
  linarith

/-- A site-`w` raising operator commutes with an on-bond lowering commutator when `w` is off the
bond and off `z` (everything is supported on `{x, y, z}`). -/
theorem spinSSiteOpPlus_commute_bondMinusTerm (w x y z : Λ)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    Commute (spinSSiteOpPlus w N)
      (spinSDot x y N * spinSSiteOpMinus z N - spinSSiteOpMinus z N * spinSDot x y N) := by
  have cdot : Commute (spinSSiteOpPlus w N) (spinSDot x y N) :=
    (spinSDot_commute_onSiteS_of_ne x y w hwx hwy (spinSOpPlus N)).symm
  have cmin : Commute (spinSSiteOpPlus w N) (spinSSiteOpMinus z N) :=
    onSiteS_commute_of_ne hwz (spinSOpPlus N) (spinSOpMinus N)
  exact (cdot.mul_right cmin).sub_right (cmin.mul_right cdot)

/-- A site-`w` raising operator commutes with the bond–order lowering commutator `[Ŝ_x·Ŝ_y, Ô_L⁻]`
when `w` is off the bond (it sees only the on-bond `{x,y}` support). -/
theorem spinSSiteOpPlus_commute_bondStaggeredLowering (A : Λ → Bool) (w x y : Λ)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    Commute (spinSSiteOpPlus w N)
      (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N) := by
  rw [spinSDot_commutator_staggeredLoweringOpS_support A x y hxy]
  exact ((spinSSiteOpPlus_commute_bondMinusTerm w x y x hwx hwy hwx).smul_right _).add_right
    ((spinSSiteOpPlus_commute_bondMinusTerm w x y y hwx hwy hwy).smul_right _)

/-- **Two-site restriction of the double commutator** `[Ô_L⁺, [Ŝ_x·Ŝ_y, Ô_L⁻]]`: collapses to the
two on-bond raising contributions. -/
theorem bondDoubleCommutator_support (A : Λ → Bool) (x y : Λ) (hxy : x ≠ y) :
    staggeredRaisingOpS A N
        * (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
      - (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
        * staggeredRaisingOpS A N
      = (if A x then (1 : ℂ) else (-1 : ℂ))
          • (spinSSiteOpPlus x N
              * (spinSDot x y N * staggeredLoweringOpS A N
                - staggeredLoweringOpS A N * spinSDot x y N)
            - (spinSDot x y N * staggeredLoweringOpS A N
                - staggeredLoweringOpS A N * spinSDot x y N) * spinSSiteOpPlus x N)
        + (if A y then (1 : ℂ) else (-1 : ℂ))
          • (spinSSiteOpPlus y N
              * (spinSDot x y N * staggeredLoweringOpS A N
                - staggeredLoweringOpS A N * spinSDot x y N)
            - (spinSDot x y N * staggeredLoweringOpS A N
                - staggeredLoweringOpS A N * spinSDot x y N) * spinSSiteOpPlus y N) := by
  conv_lhs => rw [staggeredRaisingOpS]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ w : Λ, (if A w then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpPlus w N
        * (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
      - (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
        * ((if A w then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpPlus w N)
      = (if A w then (1 : ℂ) else (-1 : ℂ))
          • (spinSSiteOpPlus w N
              * (spinSDot x y N * staggeredLoweringOpS A N
                - staggeredLoweringOpS A N * spinSDot x y N)
            - (spinSDot x y N * staggeredLoweringOpS A N
                - staggeredLoweringOpS A N * spinSDot x y N) * spinSSiteOpPlus w N) := by
    intro w; rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [Finset.sum_congr rfl (fun w _ => hterm w),
    ← Finset.sum_subset (Finset.subset_univ ({x, y} : Finset Λ)) (fun w _ hw => ?_)]
  · rw [Finset.sum_pair hxy]
  · have hwx : w ≠ x := fun h => hw (by rw [h]; exact Finset.mem_insert_self x {y})
    have hwy : w ≠ y := fun h => hw (by
      rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    rw [sub_eq_zero.mpr (spinSSiteOpPlus_commute_bondStaggeredLowering A w x y hwx hwy hxy).eq,
      smul_zero]

/-- **Per-bond double-commutator locality** `‖[Ô_L⁺, [Ŝ_x·Ŝ_y, Ô_L⁻]]‖ ≤ 48 N⁴` (`x ≠ y`):
`L`-independent, the structural fact driving Lemma R2. -/
theorem bondDoubleCommutator_norm_le (A : Λ → Bool) (x y : Λ) (hxy : x ≠ y) (hN : 1 ≤ N) :
    manyBodyOperatorNormS
      (staggeredRaisingOpS A N
          * (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
        - (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
          * staggeredRaisingOpS A N)
      ≤ 48 * (N : ℝ) ^ 4 := by
  have hinner := spinSDot_commutator_staggeredLoweringOpS_norm_le A x y hxy hN
  have hz : ∀ z : Λ, manyBodyOperatorNormS
      (spinSSiteOpPlus z N
          * (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
        - (spinSDot x y N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSDot x y N)
          * spinSSiteOpPlus z N) ≤ 24 * (N : ℝ) ^ 4 := by
    intro z
    have hplus := spinSSiteOpPlus_manyBodyOperatorNormS_le (N := N) z hN
    refine le_trans (manyBodyOperatorNormS_sub_le _ _) ?_
    have h1 : manyBodyOperatorNormS (spinSSiteOpPlus z N
        * (spinSDot x y N * staggeredLoweringOpS A N
          - staggeredLoweringOpS A N * spinSDot x y N)) ≤ (N : ℝ) * (12 * (N : ℝ) ^ 3) := by
      refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
      exact mul_le_mul hplus hinner (manyBodyOperatorNormS_nonneg _) (by positivity)
    have h2 : manyBodyOperatorNormS ((spinSDot x y N * staggeredLoweringOpS A N
          - staggeredLoweringOpS A N * spinSDot x y N) * spinSSiteOpPlus z N)
        ≤ (12 * (N : ℝ) ^ 3) * (N : ℝ) := by
      refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
      exact mul_le_mul hinner hplus (manyBodyOperatorNormS_nonneg _) (by positivity)
    nlinarith [h1, h2]
  rw [bondDoubleCommutator_support A x y hxy]
  refine le_trans (manyBodyOperatorNormS_add_le _ _) ?_
  rw [manyBodyOperatorNormS_smul, manyBodyOperatorNormS_smul,
    show ‖(if A x then (1 : ℂ) else (-1 : ℂ))‖ = 1 from by split_ifs <;> simp,
    show ‖(if A y then (1 : ℂ) else (-1 : ℂ))‖ = 1 from by split_ifs <;> simp, one_mul, one_mul]
  linarith [hz x, hz y]

/-! ### Coupling row-sum bound and the spatial average (P9-3) -/

/-- **Row-sum bound** `Σ_y ‖J x y‖ ≤ 2d` for the torus nearest-neighbor coupling: each row has at
most `2d` neighbors (`±1` in each of the `d` axes). -/
theorem torusNNCoupling_norm_rowSum_le (d L : ℕ) [NeZero L] (x : HypercubicTorus d L) :
    ∑ y : HypercubicTorus d L, ‖torusNNCoupling d L x y‖ ≤ 2 * (d : ℝ) := by
  classical
  -- the neighbor map (axis, direction) ↦ shifted point
  set nbr : Fin d × Bool → HypercubicTorus d L :=
    fun p => Function.update x p.1 (x p.1 + (if p.2 then (1 : ZMod L) else (-1 : ZMod L))) with hnbr
  have hnorm : ∀ y, ‖torusNNCoupling d L x y‖
      = (if (∃ i : Fin d, (∀ j, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)) then (1 : ℝ)
          else 0) := by
    intro y; unfold torusNNCoupling; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun y _ => hnorm y), Finset.sum_boole]
  have hsub : (Finset.univ.filter
      (fun y : HypercubicTorus d L =>
        ∃ i : Fin d, (∀ j, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)))
      ⊆ Finset.univ.image nbr := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨i, hagree, hval⟩ := hy.2
    rcases hval with hv | hv
    · refine Finset.mem_image.mpr ⟨(i, true), Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp only [hnbr, Function.update_self]; simp [hv]
      · simp only [hnbr, Function.update_of_ne hj]; exact hagree j hj
    · refine Finset.mem_image.mpr ⟨(i, false), Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp only [hnbr, Function.update_self]; simp [hv, sub_eq_add_neg]
      · simp only [hnbr, Function.update_of_ne hj]; exact hagree j hj
  calc ((Finset.univ.filter _).card : ℝ)
      ≤ ((Finset.univ.image nbr).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin d × Bool)).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ = 2 * (d : ℝ) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        push_cast; ring

/-- Scaling a double commutator: `[c·A, [H, c·B]] = c² [A, [H, B]]`. -/
theorem smul_double_commutator (c : ℂ) (A H B : ManyBodyOpS Λ N) :
    (c • A) * (H * (c • B) - (c • B) * H) - (H * (c • B) - (c • B) * H) * (c • A)
      = (c * c) • (A * (H * B - B * H) - (H * B - B * H) * A) := by
  have hINNER : H * (c • B) - c • B * H = c • (H * B - B * H) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [hINNER, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub]

/-- The per-bond double commutator `[Ô_L⁺, [Ŝ_x·Ŝ_y, Ô_L⁻]]`. -/
noncomputable def bondDoubleComm (d L N : ℕ) [NeZero L]
    (x y : HypercubicTorus d L) : ManyBodyOpS (HypercubicTorus d L) N :=
  staggeredRaisingOpS (torusParitySublattice d L) N
      * (spinSDot x y N * staggeredLoweringOpS (torusParitySublattice d L) N
        - staggeredLoweringOpS (torusParitySublattice d L) N * spinSDot x y N)
    - (spinSDot x y N * staggeredLoweringOpS (torusParitySublattice d L) N
        - staggeredLoweringOpS (torusParitySublattice d L) N * spinSDot x y N)
      * staggeredRaisingOpS (torusParitySublattice d L) N

/-- `‖[Ô⁺,[Ŝ_x·Ŝ_y,Ô⁻]]‖ ≤ 48 N⁴` for a genuine bond `x ≠ y` (restating
`bondDoubleCommutator_norm_le` for `bondDoubleComm`). -/
theorem bondDoubleComm_norm_le (d L N : ℕ) [NeZero L] {x y : HypercubicTorus d L}
    (hxy : x ≠ y) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (bondDoubleComm d L N x y) ≤ 48 * (N : ℝ) ^ 4 :=
  bondDoubleCommutator_norm_le (torusParitySublattice d L) x y hxy hN

/-- A commutator distributes over a scalar-weighted finite sum on the right. -/
theorem commutator_sum_smul_right {ι : Type*} (s : Finset ι) (A : ManyBodyOpS Λ N)
    (c : ι → ℂ) (B : ι → ManyBodyOpS Λ N) :
    A * (∑ i ∈ s, c i • B i) - (∑ i ∈ s, c i • B i) * A
      = ∑ i ∈ s, c i • (A * B i - B i * A) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [mul_smul_comm, smul_mul_assoc, smul_sub])

/-- A commutator distributes over a scalar-weighted finite sum on the left. -/
theorem commutator_sum_smul_left {ι : Type*} (s : Finset ι) (A : ManyBodyOpS Λ N)
    (c : ι → ℂ) (B : ι → ManyBodyOpS Λ N) :
    (∑ i ∈ s, c i • B i) * A - A * (∑ i ∈ s, c i • B i)
      = ∑ i ∈ s, c i • (B i * A - A * B i) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_mul_assoc, mul_smul_comm, smul_sub])

/-- **Bilinear expansion of the spatial double commutator** `[Ô⁺, [Ĥ, Ô⁻]] = Σ_{x,y} J x y ĝ_{x,y}`
over the bonds, by distributing the commutator across the Hamiltonian sum. -/
theorem heisenberg_orderDouble_commutator_eq (d L N : ℕ) [NeZero L] :
    staggeredRaisingOpS (torusParitySublattice d L) N
        * (heisenbergHamiltonianS (torusNNCoupling d L) N
            * staggeredLoweringOpS (torusParitySublattice d L) N
          - staggeredLoweringOpS (torusParitySublattice d L) N
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
      - (heisenbergHamiltonianS (torusNNCoupling d L) N
            * staggeredLoweringOpS (torusParitySublattice d L) N
          - staggeredLoweringOpS (torusParitySublattice d L) N
            * heisenbergHamiltonianS (torusNNCoupling d L) N)
        * staggeredRaisingOpS (torusParitySublattice d L) N
      = ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          torusNNCoupling d L p.1 p.2 • bondDoubleComm d L N p.1 p.2 := by
  have hH : heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          torusNNCoupling d L p.1 p.2 • spinSDot p.1 p.2 N := by
    rw [heisenbergHamiltonianS_def, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hH]
  simp only [commutator_sum_smul_left, commutator_sum_smul_right]
  rfl

/-- The nearest-neighbor coupling has no self-loop: `J x x = 0` (for `L ≥ 2`, since `±1 ≠ 0`). -/
theorem torusNNCoupling_self_eq_zero (d L : ℕ) [NeZero L] (hL : 2 ≤ L)
    (x : HypercubicTorus d L) : torusNNCoupling d L x x = 0 := by
  haveI : Fact (1 < L) := ⟨hL⟩
  unfold torusNNCoupling
  rw [if_neg]
  rintro ⟨i, _, h | h⟩
  · exact one_ne_zero (by linear_combination -h : (1 : ZMod L) = 0)
  · exact one_ne_zero (by linear_combination h : (1 : ZMod L) = 0)

/-- **Total coupling weight** `Σ_{x,y} ‖J x y‖ ≤ 2 d V` (`V = Lᵈ`). -/
theorem torusNNCoupling_total_norm_le (d L : ℕ) [NeZero L] :
    ∑ p : HypercubicTorus d L × HypercubicTorus d L, ‖torusNNCoupling d L p.1 p.2‖
      ≤ 2 * (d : ℝ) * (L : ℝ) ^ d := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  calc ∑ x : HypercubicTorus d L, ∑ y : HypercubicTorus d L, ‖torusNNCoupling d L x y‖
      ≤ ∑ _x : HypercubicTorus d L, 2 * (d : ℝ) :=
        Finset.sum_le_sum (fun x _ => torusNNCoupling_norm_rowSum_le d L x)
    _ = 2 * (d : ℝ) * (L : ℝ) ^ d := by
        rw [Finset.sum_const, Finset.card_univ, card_hypercubicTorus, nsmul_eq_mul]
        push_cast; ring

/-- **Spatial double-commutator norm bound (extensive)** `‖[Ô⁺, [Ĥ, Ô⁻]]‖ ≤ 96 d N⁴ V`: the bond
expansion has `≤ 2dV` nonzero terms each of `L`-independent norm `≤ 48 N⁴`. -/
theorem heisenberg_orderDouble_commutator_norm_le (d L N : ℕ) [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) :
    manyBodyOperatorNormS
      (staggeredRaisingOpS (torusParitySublattice d L) N
          * (heisenbergHamiltonianS (torusNNCoupling d L) N
              * staggeredLoweringOpS (torusParitySublattice d L) N
            - staggeredLoweringOpS (torusParitySublattice d L) N
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
        - (heisenbergHamiltonianS (torusNNCoupling d L) N
              * staggeredLoweringOpS (torusParitySublattice d L) N
            - staggeredLoweringOpS (torusParitySublattice d L) N
              * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredRaisingOpS (torusParitySublattice d L) N)
      ≤ 96 * (d : ℝ) * (N : ℝ) ^ 4 * (L : ℝ) ^ d := by
  rw [heisenberg_orderDouble_commutator_eq]
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  have hterm : ∀ p : HypercubicTorus d L × HypercubicTorus d L,
      manyBodyOperatorNormS (torusNNCoupling d L p.1 p.2 • bondDoubleComm d L N p.1 p.2)
        ≤ ‖torusNNCoupling d L p.1 p.2‖ * (48 * (N : ℝ) ^ 4) := by
    intro p
    rw [manyBodyOperatorNormS_smul]
    by_cases hp : p.1 = p.2
    · have hzero : torusNNCoupling d L p.1 p.2 = 0 := by
        rw [hp]; exact torusNNCoupling_self_eq_zero d L hL p.2
      rw [hzero]; simp
    · exact mul_le_mul_of_nonneg_left (bondDoubleComm_norm_le d L N hp hN) (norm_nonneg _)
  calc ∑ p : HypercubicTorus d L × HypercubicTorus d L,
        manyBodyOperatorNormS (torusNNCoupling d L p.1 p.2 • bondDoubleComm d L N p.1 p.2)
      ≤ ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          ‖torusNNCoupling d L p.1 p.2‖ * (48 * (N : ℝ) ^ 4) :=
        Finset.sum_le_sum (fun p _ => hterm p)
    _ = (∑ p : HypercubicTorus d L × HypercubicTorus d L, ‖torusNNCoupling d L p.1 p.2‖)
          * (48 * (N : ℝ) ^ 4) := by rw [← Finset.sum_mul]
    _ ≤ (2 * (d : ℝ) * (L : ℝ) ^ d) * (48 * (N : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right (torusNNCoupling_total_norm_le d L) (by positivity)
    _ = 96 * (d : ℝ) * (N : ℝ) ^ 4 * (L : ℝ) ^ d := by ring

/-- **Per-volume double-commutator locality (eq. 4.2.65)** `‖[ô⁺, [Ĥ, ô⁻]]‖ ≤ 96 d N⁴ / V`: the
spatial average is `O(1/V)`, the renormalized estimate driving Lemma R2. -/
theorem orderDensity_double_commutator_norm_le (d L N : ℕ) [NeZero L] (hL : 2 ≤ L) (hN : 1 ≤ N) :
    manyBodyOperatorNormS
      (staggeredOrderDensityOpS d L N true
          * (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * heisenbergHamiltonianS (torusNNCoupling d L) N)
        - (heisenbergHamiltonianS (torusNNCoupling d L) N * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * heisenbergHamiltonianS (torusNNCoupling d L) N)
          * staggeredOrderDensityOpS d L N true)
      ≤ 96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by
  have hV : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [show staggeredOrderDensityOpS d L N true
      = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl,
    show staggeredOrderDensityOpS d L N false
      = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl,
    smul_double_commutator, manyBodyOperatorNormS_smul,
    show ‖((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ from by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]]
  calc ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹
        * manyBodyOperatorNormS (staggeredRaisingOpS (torusParitySublattice d L) N
            * (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredLoweringOpS (torusParitySublattice d L) N
              - staggeredLoweringOpS (torusParitySublattice d L) N
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
          - (heisenbergHamiltonianS (torusNNCoupling d L) N
                * staggeredLoweringOpS (torusParitySublattice d L) N
              - staggeredLoweringOpS (torusParitySublattice d L) N
                * heisenbergHamiltonianS (torusNNCoupling d L) N)
            * staggeredRaisingOpS (torusParitySublattice d L) N)
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (96 * (d : ℝ) * (N : ℝ) ^ 4 * (L : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left (heisenberg_orderDouble_commutator_norm_le d L N hL hN)
          (by positivity)
    _ = 96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d := by field_simp

end LatticeSystem.Quantum
