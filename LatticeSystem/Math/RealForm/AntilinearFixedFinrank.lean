import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Real-form finrank toolkit for antilinear involutions and non-orthogonal pairs

Two generic finite-dimensional linear-algebra facts used to bound the (complex) dimension of a
ground eigenspace by `1`.  They are deliberately stated without instantiating an
`InnerProductSpace` on a custom submodule; the second one uses an abstract real bilinear form so
that a concrete pairing `(dotProduct (star ·) ·).re` can be plugged in directly.

## Contents

* `antilinearInvolutionFixed`: the real subspace of vectors fixed by an antilinear additive
  involution `Θ` on a complex vector space `V`.
* `finrank_complex_le_finrank_real_antilinearFixed`: the `Θ`-fixed real subspace spans `V` over
  `ℂ`, hence `finrank ℂ V ≤ finrank ℝ (antilinearInvolutionFixed Θ)`.  This is the standard
  "real form" bound, via the decomposition `x = ½(x + Θx) + i · (½ · (-i) · (x - Θx))` into
  `Θ`-fixed pieces.
* `finrank_le_one_of_pairwise_bilinForm_ne_zero`: if every pair of nonzero vectors in a real
  subspace `W` pairs to a nonzero value under a bilinear form `B`, then `finrank ℝ W ≤ 1`
  (one-step Gram–Schmidt).

These are generic (no model specifics); they are consumed by the Tasaki §10.2.4 balanced
ground-state uniqueness capstone (Issue #4852).
-/

namespace LatticeSystem.Math.RealForm

open Module

section AntilinearFixed

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- An antilinear additive map `Θ` on a complex vector space is `ℝ`-linear: the antilinearity
`Θ (z • x) = conj z • Θ x` specialises at real scalars `z = (r : ℂ)` to `Θ (r • x) = r • Θ x`,
because complex conjugation fixes real numbers. -/
theorem antilinear_real_smul (Θ : V → V)
    (hsmul : ∀ (z : ℂ) (x : V), Θ (z • x) = starRingEnd ℂ z • Θ x)
    (r : ℝ) (x : V) : Θ (r • x) = r • Θ x := by
  have hconj : starRingEnd ℂ (algebraMap ℝ ℂ r) = algebraMap ℝ ℂ r := Complex.conj_ofReal r
  rw [algebra_compatible_smul (A := ℂ) r x, hsmul, hconj,
    ← algebra_compatible_smul (A := ℂ) r (Θ x)]

/-- The `ℝ`-linear map underlying an antilinear additive map `Θ` (see `antilinear_real_smul`). -/
def thetaRealLinear (Θ : V → V) (hadd : ∀ x y, Θ (x + y) = Θ x + Θ y)
    (hsmul : ∀ (z : ℂ) (x : V), Θ (z • x) = starRingEnd ℂ z • Θ x) : V →ₗ[ℝ] V where
  toFun := Θ
  map_add' := hadd
  map_smul' r x := antilinear_real_smul Θ hsmul r x

/-- The real subspace of vectors fixed by an antilinear additive map `Θ`, realised as the kernel
of `Θ - id`.  When `Θ` is an involution this is a "real form" of the complex space. -/
def antilinearInvolutionFixed (Θ : V → V) (hadd : ∀ x y, Θ (x + y) = Θ x + Θ y)
    (hsmul : ∀ (z : ℂ) (x : V), Θ (z • x) = starRingEnd ℂ z • Θ x) : Submodule ℝ V :=
  LinearMap.ker (thetaRealLinear Θ hadd hsmul - LinearMap.id)

/-- Membership in the `Θ`-fixed real subspace is exactly being a fixed point of `Θ`. -/
theorem mem_antilinearInvolutionFixed {Θ : V → V}
    {hadd : ∀ x y, Θ (x + y) = Θ x + Θ y}
    {hsmul : ∀ (z : ℂ) (x : V), Θ (z • x) = starRingEnd ℂ z • Θ x} {x : V} :
    x ∈ antilinearInvolutionFixed Θ hadd hsmul ↔ Θ x = x := by
  simp only [antilinearInvolutionFixed, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  exact Iff.rfl

variable [Module.Finite ℂ V]

/-- **Real-form finrank bound.**  For an antilinear additive involution `Θ` on a
finite-dimensional complex vector space `V`, the `Θ`-fixed real subspace spans `V` over `ℂ`
(every `x` decomposes as `½(x + Θx) + i · (½ · (-i) · (x - Θx))` into two `Θ`-fixed pieces), so
`finrank ℂ V ≤ finrank ℝ (antilinearInvolutionFixed Θ)`. -/
theorem finrank_complex_le_finrank_real_antilinearFixed (Θ : V → V)
    (hadd : ∀ x y, Θ (x + y) = Θ x + Θ y)
    (hsmul : ∀ (z : ℂ) (x : V), Θ (z • x) = starRingEnd ℂ z • Θ x)
    (hinv : ∀ x, Θ (Θ x) = x) :
    finrank ℂ V ≤ finrank ℝ (antilinearInvolutionFixed Θ hadd hsmul) := by
  classical
  haveI : Module.Finite ℝ V := Module.Finite.trans ℂ V
  set W := antilinearInvolutionFixed Θ hadd hsmul with hW
  -- `Θ` is `ℝ`-linear on subtractions (used repeatedly below).
  have hsub : ∀ x, Θ (x - Θ x) = Θ x - x := by
    intro x
    have hrw : x - Θ x = x + (-1 : ℝ) • Θ x := by rw [neg_one_smul]; abel
    rw [hrw, hadd, antilinear_real_smul Θ hsmul, hinv, neg_one_smul]; abel
  -- An `ℝ`-basis of `W`, included into `V`.
  let b : Basis (Fin (finrank ℝ W)) ℝ W := Module.finBasis ℝ W
  set incl : Fin (finrank ℝ W) → V := fun i => (b i : V) with hincl
  -- The image of the basis spans `W` over `ℝ` inside `V`.
  have hWspan : Submodule.span ℝ (Set.range incl) = W := by
    have hcomp : Set.range incl = W.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hcomp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  -- The included basis spans `V` over `ℂ`.
  have hspan : Submodule.span ℂ (Set.range incl) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    set a : V := (1 / 2 : ℝ) • (v + Θ v) with ha_def
    set c : V := (1 / 2 : ℝ) • ((-Complex.I) • (v - Θ v)) with hc_def
    -- `a` is `Θ`-fixed.
    have ha_fix : a ∈ W := by
      rw [hW, mem_antilinearInvolutionFixed, ha_def, antilinear_real_smul Θ hsmul, hadd, hinv,
        add_comm]
    -- `c` is `Θ`-fixed.
    have hc_fix : c ∈ W := by
      rw [hW, mem_antilinearInvolutionFixed, hc_def, antilinear_real_smul Θ hsmul, hsmul, hsub,
        map_neg, Complex.conj_I, neg_neg]
      congr 1
      rw [smul_sub, smul_sub, neg_smul, neg_smul]
      abel
    -- Reconstruction `v = a + i • c`.
    have hIc : Complex.I • c = (1 / 2 : ℝ) • (v - Θ v) := by
      rw [hc_def, smul_comm Complex.I (1 / 2 : ℝ), smul_smul,
        show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]
    have hv : v = a + Complex.I • c := by
      rw [hIc, ha_def, ← smul_add, show v + Θ v + (v - Θ v) = (2 : ℝ) • v by rw [two_smul]; abel,
        smul_smul]
      norm_num
    -- Both pieces lie in the `ℂ`-span.
    have haS : a ∈ Submodule.span ℂ (Set.range incl) :=
      Submodule.span_subset_span ℝ ℂ _ (by rw [hWspan]; exact ha_fix)
    have hcS : c ∈ Submodule.span ℂ (Set.range incl) :=
      Submodule.span_subset_span ℝ ℂ _ (by rw [hWspan]; exact hc_fix)
    rw [hv]
    exact add_mem haS (Submodule.smul_mem _ _ hcS)
  calc finrank ℂ V ≤ Fintype.card (Fin (finrank ℝ W)) := finrank_le_of_span_eq_top hspan
    _ = finrank ℝ W := Fintype.card_fin _

end AntilinearFixed

section NonOrthogonal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Non-orthogonal pairs force dimension `≤ 1`.**  If a bilinear form `B` on a real vector
space pairs every two nonzero vectors of a subspace `W` to a nonzero value, then
`finrank ℝ W ≤ 1`.  (One-step Gram–Schmidt: `w - (B v w / B v v) • v` pairs to `0` with `v`, so
it must vanish, i.e. every `w` is a multiple of a fixed nonzero `v`.) -/
theorem finrank_le_one_of_pairwise_bilinForm_ne_zero (W : Submodule ℝ E)
    (B : LinearMap.BilinForm ℝ E)
    (hne : ∀ x ∈ W, ∀ y ∈ W, x ≠ 0 → y ≠ 0 → B x y ≠ 0) :
    finrank ℝ W ≤ 1 := by
  classical
  rcases eq_or_ne W ⊥ with hW | hW
  · rw [hW]; simp
  · -- Pick a nonzero anchor vector `v ∈ W`.
    obtain ⟨v, hvW, hv0⟩ := W.ne_bot_iff.1 hW
    have hvv : B v v ≠ 0 := hne v hvW v hvW hv0 hv0
    refine finrank_le_one (⟨v, hvW⟩ : W) ?_
    intro w
    refine ⟨B v w / B v v, ?_⟩
    set r : ℝ := B v w / B v v with hr
    -- `w - r • v` pairs to `0` with `v`.
    have hpair : B v (↑w - r • v) = 0 := by
      rw [map_sub, LinearMap.map_smul, smul_eq_mul, hr, div_mul_cancel₀ _ hvv, sub_self]
    -- Hence it must vanish (else `hne` gives a contradiction), so `w = r • v`.
    have hz : (↑w : E) - r • v = 0 := by
      by_contra hcontra
      exact hne v hvW (↑w - r • v) (W.sub_mem w.2 (W.smul_mem r hvW)) hv0 hcontra hpair
    apply Subtype.ext
    rw [Submodule.coe_smul]
    rw [sub_eq_zero] at hz
    exact hz.symm

end NonOrthogonal

end LatticeSystem.Math.RealForm
