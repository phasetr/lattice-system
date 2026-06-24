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

end LatticeSystem.Quantum
