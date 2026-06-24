import LatticeSystem.Quantum.SpinS.AndersonTower
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Tasaki §4.2.2: the order-operator algebra and Lemma 4.14

The proofs of the tower theorems use the per-volume order operators `ô^± = Ô_L^± / V` (`V = L^d`)
and
the `U(1)`-symmetric order operator `p̂ = ½(ô^+ ô^- + ô^- ô^+)` (eqs. (4.2.30)–(4.2.31)).  The
commutator `[Ô_L^+, Ô_L^-] = 2 Ŝ_tot^{(3)}` (eq. (4.2.32)) gives `‖[ô^+, ô^-]‖ ≤ o₀/V` with `o₀ =
2S`
(eq. (4.2.33)), whence the key elementary bound:

**Lemma 4.14** (eq. (4.2.34)): for any balanced sign sequence `s₁, …, s_{2n} ∈ {+, −}` (`n` pluses
and `n` minuses), the operator norm of the difference between the product and `p̂ⁿ` is small,
`‖ô^{s₁} ⋯ ô^{s_{2n}} − p̂ⁿ‖ ≤ n² (o₀)^{2n−1} / V`,
because any balanced product can be rearranged to any other by at most `n²` neighboring `±`
exchanges,
each costing `≤ ‖[ô^+, ô^-]‖ ≤ o₀/V`.

This file defines the order-operator algebra and records Lemma 4.14 as a documented axiom (the
operator-norm / commutator-rearrangement proof is elementary but involved; a finite-volume discharge
candidate).  The operator norm is the genuine `L²` operator norm `manyBodyOperatorNormS`, *not* the
default entrywise matrix norm.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Lemma 4.14, eqs. (4.2.30)–(4.2.34), pp. 104–105 (`S = N/2`, so `o₀ = 2S = N`).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **`L²` operator (spectral) norm** of a many-body operator, via the associated continuous
linear map on `EuclideanSpace ℂ (Λ → Fin (N+1))`.  This is submultiplicative and satisfies the
triangle inequality — unlike the default entrywise matrix norm — so it is the correct norm for the
order-operator bounds. -/
noncomputable def manyBodyOperatorNormS (M : ManyBodyOpS Λ N) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

/-- **Bridge to the bundled star-algebra image**: the many-body `L²` operator norm equals the
operator norm of the continuous-linear-map image `Matrix.toEuclideanCLM M` (the two coincide because
`toEuclideanCLM` is the bundled `toContinuousLinearMap ∘ toEuclideanLin`).  Routing through the
`StarAlgEquiv` `toEuclideanCLM` lets the norm-algebra inequalities follow from the continuous-linear
endomorphism `NormedRing`. -/
theorem manyBodyOperatorNormS_eq_toEuclideanCLM (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS M = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  rw [manyBodyOperatorNormS]
  congr 1

/-- The many-body `L²` operator norm is nonnegative. -/
theorem manyBodyOperatorNormS_nonneg (M : ManyBodyOpS Λ N) : 0 ≤ manyBodyOperatorNormS M :=
  norm_nonneg _

/-- The many-body `L²` operator norm of `0` is `0`. -/
@[simp] theorem manyBodyOperatorNormS_zero : manyBodyOperatorNormS (0 : ManyBodyOpS Λ N) = 0 := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_zero, norm_zero]

/-- **Triangle inequality** for the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_add_le (M₁ M₂ : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (M₁ + M₂) ≤ manyBodyOperatorNormS M₁ + manyBodyOperatorNormS M₂ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM,
    manyBodyOperatorNormS_eq_toEuclideanCLM, map_add]
  exact norm_add_le _ _

/-- **Subtraction triangle inequality** for the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_sub_le (M₁ M₂ : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (M₁ - M₂) ≤ manyBodyOperatorNormS M₁ + manyBodyOperatorNormS M₂ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM,
    manyBodyOperatorNormS_eq_toEuclideanCLM, map_sub]
  exact norm_sub_le _ _

/-- **Scalar homogeneity** of the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_smul (c : ℂ) (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (c • M) = ‖c‖ * manyBodyOperatorNormS M := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM, map_smul,
    norm_smul]

/-- **Submultiplicativity** of the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_mul_le (M₁ M₂ : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (M₁ * M₂) ≤ manyBodyOperatorNormS M₁ * manyBodyOperatorNormS M₂ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM,
    manyBodyOperatorNormS_eq_toEuclideanCLM, map_mul]
  exact norm_mul_le _ _

/-- **Power submultiplicativity** of the many-body `L²` operator norm (for `n > 0`). -/
theorem manyBodyOperatorNormS_pow_le (M : ManyBodyOpS Λ N) {n : ℕ} (hn : 0 < n) :
    manyBodyOperatorNormS (M ^ n) ≤ manyBodyOperatorNormS M ^ n := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_pow, manyBodyOperatorNormS_eq_toEuclideanCLM]
  exact norm_pow_le' _ hn

/-- **List-product submultiplicativity**: the norm of an ordered product is at most the product of
the norms.  Used to bound `balancedOrderProductS`. -/
theorem manyBodyOperatorNormS_list_prod_le (l : List (ManyBodyOpS Λ N)) :
    manyBodyOperatorNormS l.prod ≤ (l.map manyBodyOperatorNormS).prod := by
  induction l with
  | nil => simp [manyBodyOperatorNormS_eq_toEuclideanCLM]
  | cons a t ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    refine le_trans (manyBodyOperatorNormS_mul_le a t.prod) ?_
    exact mul_le_mul_of_nonneg_left ih (manyBodyOperatorNormS_nonneg a)

/-- **Finite-sum triangle inequality** for the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_sum_le {ι : Type*} (s : Finset ι) (f : ι → ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (∑ x ∈ s, f x) ≤ ∑ x ∈ s, manyBodyOperatorNormS (f x) := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_sum]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun x _ => (manyBodyOperatorNormS_eq_toEuclideanCLM (f x)).symm)

section L2Wrappers
open scoped Matrix.Norms.L2Operator

/-- The many-body `L²` operator norm coincides with the scoped `Matrix.Norms.L2Operator` norm. -/
theorem manyBodyOperatorNormS_eq_l2 (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS M = ‖M‖ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM]

/-- The many-body `L²` operator norm is invariant under conjugate transpose. -/
theorem manyBodyOperatorNormS_conjTranspose (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (Matrix.conjTranspose M) = manyBodyOperatorNormS M := by
  rw [manyBodyOperatorNormS_eq_l2, manyBodyOperatorNormS_eq_l2, Matrix.l2_opNorm_conjTranspose]

/-- `C*`-identity for the many-body `L²` operator norm: `‖MᴴM‖ = ‖M‖²`. -/
theorem manyBodyOperatorNormS_conjTranspose_mul_self (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (Matrix.conjTranspose M * M) = manyBodyOperatorNormS M ^ 2 := by
  rw [manyBodyOperatorNormS_eq_l2, manyBodyOperatorNormS_eq_l2,
    Matrix.l2_opNorm_conjTranspose_mul_self, sq]

/-- The `L²` operator norm of a diagonal many-body operator bounded by `C` when every entry is. -/
theorem manyBodyOperatorNormS_diagonal_le {v : (Λ → Fin (N + 1)) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ σ, ‖v σ‖ ≤ C) : manyBodyOperatorNormS (Matrix.diagonal v) ≤ C := by
  rw [manyBodyOperatorNormS_eq_l2, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 h

end L2Wrappers

/-- The site-embedded image of a diagonal single-site matrix is again diagonal, with entry indexed
by the local configuration value `σ i`. -/
theorem onSiteS_diagonal (i : Λ) (w : Fin (N + 1) → ℂ) :
    (onSiteS i (Matrix.diagonal w) : ManyBodyOpS Λ N)
      = Matrix.diagonal (fun σ => w (σ i)) := by
  ext σ' σ
  simp only [onSiteS_apply, Matrix.diagonal_apply]
  by_cases h : σ' = σ
  · subst h; simp
  · rw [if_neg h]
    by_cases hoff : ∀ k, k ≠ i → σ' k = σ k
    · have hi : ¬ σ' i = σ i := fun hi => h (funext fun k => by
        by_cases hk : k = i
        · rw [hk]; exact hi
        · exact hoff k hk)
      rw [if_pos hoff, if_neg hi]
    · rw [if_neg hoff]

/-- **Single-site `Ŝ⁻Ŝ⁺` is diagonal** with entry `k ↦ k(N−k+1)` at index `k` (`m = N/2 − k`):
the off-diagonal terms vanish (both factors require the same raising index), and the diagonal entry
is the squared raising amplitude `(√(k(N−k+1)))²`. -/
theorem spinSOpMinus_mul_spinSOpPlus_apply (N : ℕ) (i j : Fin (N + 1)) :
    (spinSOpMinus N * spinSOpPlus N) i j
      = if i = j then ((i.val : ℂ) * ((N : ℂ) - (i.val : ℂ) + 1)) else 0 := by
  rw [Matrix.mul_apply]
  have hg : ∀ l : Fin (N + 1), spinSOpMinus N i l * spinSOpPlus N l j
      = if (l.val + 1 = i.val ∧ l.val + 1 = j.val)
          then ((i.val : ℂ) * ((N : ℂ) - (i.val : ℂ) + 1)) else 0 := by
    intro l
    unfold spinSOpMinus spinSOpPlus
    by_cases hi : l.val + 1 = i.val
    · by_cases hj : l.val + 1 = j.val
      · rw [if_pos hi, if_pos hj, if_pos ⟨hi, hj⟩, ← Complex.ofReal_mul]
        have hiR : (l.val : ℝ) + 1 = (i.val : ℝ) := by exact_mod_cast hi
        have hjR : (l.val : ℝ) + 1 = (j.val : ℝ) := by exact_mod_cast hj
        have hN_le : (i.val : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
        have key : Real.sqrt (((N : ℝ) - (l.val : ℝ)) * ((l.val : ℝ) + 1))
            * Real.sqrt ((j.val : ℝ) * ((N : ℝ) - (j.val : ℝ) + 1))
              = (i.val : ℝ) * ((N : ℝ) - (i.val : ℝ) + 1) := by
          have e1 : ((N : ℝ) - (l.val : ℝ)) * ((l.val : ℝ) + 1)
              = (i.val : ℝ) * ((N : ℝ) - (i.val : ℝ) + 1) := by
            have hli : (l.val : ℝ) = (i.val : ℝ) - 1 := by linarith
            rw [hli]; ring
          have e2 : (j.val : ℝ) * ((N : ℝ) - (j.val : ℝ) + 1)
              = (i.val : ℝ) * ((N : ℝ) - (i.val : ℝ) + 1) := by
            have hji : (j.val : ℝ) = (i.val : ℝ) := by linarith
            rw [hji]
          rw [e1, e2]
          exact Real.mul_self_sqrt (by nlinarith [hN_le, show (0:ℝ) ≤ (i.val : ℝ) by positivity])
        rw [key]; push_cast; ring
      · rw [if_pos hi, if_neg hj, mul_zero, if_neg (by tauto)]
    · rw [if_neg hi, zero_mul, if_neg (by tauto)]
  rw [Finset.sum_congr rfl (fun l _ => hg l)]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi0 : i.val = 0
    · rw [Finset.sum_eq_zero (fun l _ => if_neg (by omega))]
      have : (i.val : ℂ) = 0 := by rw [hi0]; simp
      rw [this]; ring
    · have hlt : i.val - 1 < N + 1 := by omega
      have hval : (⟨i.val - 1, hlt⟩ : Fin (N + 1)).val = i.val - 1 := rfl
      refine (Finset.sum_eq_single (⟨i.val - 1, hlt⟩ : Fin (N + 1)) ?_ ?_).trans ?_
      · intro l _ hne
        refine if_neg ?_
        rintro ⟨h1, _⟩
        exact hne (Fin.ext (by omega))
      · intro h; exact absurd (Finset.mem_univ _) h
      · exact if_pos ⟨by rw [hval]; omega, by rw [hval]; omega⟩
  · rw [if_neg hij]
    refine Finset.sum_eq_zero (fun l _ => if_neg ?_)
    rintro ⟨h1, h2⟩
    exact hij (Fin.ext (by omega))

/-- The diagonal entry `k(N−k+1)` of `Ŝ⁻Ŝ⁺` is real, nonnegative and bounded by `N²` (`N ≥ 1`),
by the AM–GM bound `k(N−k+1) ≤ ((N+1)/2)² ≤ N²`. -/
private theorem spinSDiag_norm_le_sq (N : ℕ) (hN : 1 ≤ N) (k : Fin (N + 1)) :
    ‖((k.val : ℂ) * ((N : ℂ) - (k.val : ℂ) + 1))‖ ≤ (N : ℝ) ^ 2 := by
  have hle : ((k.val : ℝ)) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  have hge : (0 : ℝ) ≤ ((k.val : ℝ)) := by positivity
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hz : ((k.val : ℂ) * ((N : ℂ) - (k.val : ℂ) + 1))
      = (((k.val : ℝ) * ((N : ℝ) - (k.val : ℝ) + 1)) : ℝ) := by push_cast; ring
  rw [hz, Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]
  nlinarith

/-- **Per-site raising-operator norm bound** `‖Ŝₓ⁺‖ ≤ N` (`= 2S`): via
`‖Ŝₓ⁺‖² = ‖(Ŝₓ⁺)ᴴ Ŝₓ⁺‖ = ‖Ŝₓ⁻Ŝₓ⁺‖` and the diagonal bound `k(N−k+1) ≤ N²` (`N ≥ 1`). -/
theorem spinSSiteOpPlus_manyBodyOperatorNormS_le (x : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (spinSSiteOpPlus x N) ≤ (N : ℝ) := by
  have hconj : Matrix.conjTranspose (spinSSiteOpPlus x N) * spinSSiteOpPlus x N
      = onSiteS x (Matrix.diagonal (fun k : Fin (N + 1) =>
          ((k.val : ℂ) * ((N : ℂ) - (k.val : ℂ) + 1)))) := by
    unfold spinSSiteOpPlus
    rw [onSiteS_conjTranspose, spinSOpPlus_conjTranspose, onSiteS_mul_onSiteS_same]
    congr 1
    ext i j
    rw [spinSOpMinus_mul_spinSOpPlus_apply, Matrix.diagonal_apply]
  have hsq : manyBodyOperatorNormS (spinSSiteOpPlus x N) ^ 2 ≤ (N : ℝ) ^ 2 := by
    rw [← manyBodyOperatorNormS_conjTranspose_mul_self, hconj, onSiteS_diagonal]
    exact manyBodyOperatorNormS_diagonal_le (by positivity)
      (fun σ => spinSDiag_norm_le_sq N hN (σ x))
  have hnn : 0 ≤ manyBodyOperatorNormS (spinSSiteOpPlus x N) := manyBodyOperatorNormS_nonneg _
  nlinarith [hsq, hnn, (by positivity : (0:ℝ) ≤ (N:ℝ))]

/-- **Per-site lowering-operator norm bound** `‖Ŝₓ⁻‖ ≤ N`, by adjoint symmetry of the norm. -/
theorem spinSSiteOpMinus_manyBodyOperatorNormS_le (x : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (spinSSiteOpMinus x N) ≤ (N : ℝ) := by
  have hadj : spinSSiteOpMinus x N = Matrix.conjTranspose (spinSSiteOpPlus x N) := by
    unfold spinSSiteOpPlus spinSSiteOpMinus
    rw [onSiteS_conjTranspose, spinSOpPlus_conjTranspose]
  rw [hadj, manyBodyOperatorNormS_conjTranspose]
  exact spinSSiteOpPlus_manyBodyOperatorNormS_le x hN

/-- A sign sequence `s : Fin (2n) → Bool` (`true = +`, `false = −`) is **balanced** when it has
exactly `n` pluses (hence `n` minuses), i.e. `Σ s_j = 0` in `±1` terms. -/
def BalancedSigns {n : ℕ} (s : Fin (2 * n) → Bool) : Prop :=
  (Finset.univ.filter (fun i : Fin (2 * n) => s i = true)).card = n

/-- The **per-volume order operator** `ô^{±} = Ô_L^{±} / V` (`V = L^d`, eq. (4.2.30)): the staggered
raising (`b = true`) or lowering (`b = false`) order operator, divided by the volume. -/
noncomputable def staggeredOrderDensityOpS (d L N : ℕ) [NeZero L] (b : Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  ((L : ℂ) ^ d)⁻¹ •
    (if b then staggeredRaisingOpS (torusParitySublattice d L) N
      else staggeredLoweringOpS (torusParitySublattice d L) N)

/-- The **ordered product** `ô^{s₁} ⋯ ô^{s_{2n}}` of `2n` per-volume order operators along a sign
sequence `s`. -/
noncomputable def balancedOrderProductS (d L N n : ℕ) [NeZero L] (s : Fin (2 * n) → Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  (List.ofFn fun i : Fin (2 * n) => staggeredOrderDensityOpS d L N (s i)).prod

/-- The **`U(1)`-symmetric order operator** `p̂ = ½(ô^+ ô^- + ô^- ô^+) = (ô^{(1)})² + (ô^{(2)})²`
(eq. (4.2.31)). -/
noncomputable def staggeredPhatS (d L N : ℕ) [NeZero L] : ManyBodyOpS (HypercubicTorus d L) N :=
  (2 : ℂ)⁻¹ • (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false +
    staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)

/-- **Staggered order-operator norm bound** `‖Ô_L^±‖ ≤ V·N` (`V = card Λ`): triangle inequality over
the `V` sites, each per-site ladder operator having norm `≤ N` (`= 2S`) and the staggered sign
having unit modulus. -/
theorem staggeredRaisingOpS_manyBodyOperatorNormS_le (A : Λ → Bool) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (staggeredRaisingOpS A N) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) := by
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  calc ∑ x : Λ, manyBodyOperatorNormS ((if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpPlus x N)
      ≤ ∑ _x : Λ, (N : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [manyBodyOperatorNormS_smul]
        have h1 : ‖(if A x then (1 : ℂ) else (-1 : ℂ))‖ = 1 := by split_ifs <;> simp
        rw [h1, one_mul]
        exact spinSSiteOpPlus_manyBodyOperatorNormS_le x hN
    _ = (Fintype.card Λ : ℝ) * (N : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Staggered lowering order-operator norm bound** `‖Ô_L^−‖ ≤ V·N`. -/
theorem staggeredLoweringOpS_manyBodyOperatorNormS_le (A : Λ → Bool) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (staggeredLoweringOpS A N) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) := by
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  calc ∑ x : Λ, manyBodyOperatorNormS ((if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpMinus x N)
      ≤ ∑ _x : Λ, (N : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [manyBodyOperatorNormS_smul]
        have h1 : ‖(if A x then (1 : ℂ) else (-1 : ℂ))‖ = 1 := by split_ifs <;> simp
        rw [h1, one_mul]
        exact spinSSiteOpMinus_manyBodyOperatorNormS_le x hN
    _ = (Fintype.card Λ : ℝ) * (N : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Per-volume order-operator norm bound** `‖ô^±‖ ≤ N` (`= o₀`, eq. (4.2.33)): the staggered order
operator has norm `≤ V·N`, and the per-volume normalization `V⁻¹ = (L^d)⁻¹` brings it to `N`. -/
theorem staggeredOrderDensityOpS_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (b : Bool)
    (hN : 1 ≤ N) : manyBodyOperatorNormS (staggeredOrderDensityOpS d L N b) ≤ (N : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold staggeredOrderDensityOpS
  rw [manyBodyOperatorNormS_smul]
  have hc : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hcard : (Fintype.card (HypercubicTorus d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_hypercubicTorus]; push_cast; ring
  have hbound : manyBodyOperatorNormS
      (if b then staggeredRaisingOpS (torusParitySublattice d L) N
        else staggeredLoweringOpS (torusParitySublattice d L) N)
      ≤ (L : ℝ) ^ d * (N : ℝ) := by
    cases b with
    | true =>
      simpa [hcard] using staggeredRaisingOpS_manyBodyOperatorNormS_le
        (torusParitySublattice d L) hN
    | false =>
      simpa [hcard] using staggeredLoweringOpS_manyBodyOperatorNormS_le
        (torusParitySublattice d L) hN
  rw [hc]
  calc ((L : ℝ) ^ d)⁻¹ * manyBodyOperatorNormS _
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (N : ℝ) := by field_simp

/-- **Tasaki Lemma 4.14 (order-operator algebra estimate), AXIOM.**  For any balanced sign sequence
`s` of length `2n` (`n > 0`), the `L²` operator norm of the difference between the ordered product
`ô^{s₁} ⋯ ô^{s_{2n}}` and `p̂ⁿ` is bounded by `n² (o₀)^{2n−1} / V`, where `o₀ = 2S = N` and
`V = L^d` (eq. (4.2.34)):
`‖ô^{s₁} ⋯ ô^{s_{2n}} − p̂ⁿ‖ ≤ n² N^{2n−1} / L^d`.

Any balanced product rearranges to any other by `≤ n²` neighboring `±` exchanges, each costing
`≤ ‖[ô^+, ô^-]‖ ≤ o₀/V` (eq. (4.2.33)); the bound follows with `‖ô^{±}‖ ≤ o₀`.  An elementary but
involved finite-volume estimate — recorded as a documented axiom (discharge candidate). -/
axiom staggered_balanced_order_product_norm_le {d L N n : ℕ} [NeZero L] (hn : 0 < n)
    (s : Fin (2 * n) → Bool) (hbal : BalancedSigns s) :
    manyBodyOperatorNormS (balancedOrderProductS d L N n s - staggeredPhatS d L N ^ n) ≤
      (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d

open Filter in
/-- **Tasaki Lemma 4.15 (the order parameter as a `p̂`-ratio double limit), AXIOM.**  The
symmetry-breaking order parameter `m∗` is the iterated limit of the ground-state `p̂`-ratios
(eq. (4.2.38)): `m∗ = lim_{n↑∞} liminf_{L↑∞} ⟨p̂^{n+1}⟩ / ⟨p̂^n⟩` (the `n`-ratio is increasing and
bounded, so the outer limit exists; the inner is a `liminf` per footnote 31).  We state the sound
`liminf`-lower direction — for every `ε > 0`, for all large `n`, eventually in (even) `L` the ratio
exceeds `m∗ − ε` — which captures `lim_n liminf_L ⟨p̂^{n+1}⟩/⟨p̂^n⟩ ≥ m∗`.  The axiom also records
the
`U(1)`-optimal bound `√(2 q₀) ≤ m∗` (eq. (4.2.39), the weaker `√2` companion of Theorem 4.11's
`√3`).

`m∗` is the genuine order parameter, pinned (as in Theorems 4.11/4.13) by a realizing ground-state
family `Φ` with exact LRO limit `q₀`, staggered-moment limit `m∗`, `IsTanakaFullSSBConstants`, and
the
realizing slow tower `M` — unsatisfiable in `d = 1` (no LRO, Corollary 4.3), so vacuous there.  The
`p̂`-moment denominators are positive (`hPhat`, `⟨p̂^n⟩ ≥ (2q₀)^n > 0` under LRO, eq. (4.2.37)),
so the
Rayleigh-ratio division is meaningful. -/
axiom mStar_eq_phat_ratio_limit (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M)
    (hPhat : ∀ (n L : ℕ) [NeZero L], 2 ≤ L → Even L →
      0 < expectationRatioRe (staggeredPhatS d L N ^ n) (Φ L)) :
    (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        mStar - ε <
          expectationRatioRe (staggeredPhatS d L N ^ (n + 1)) (Φ L) /
            expectationRatioRe (staggeredPhatS d L N ^ n) (Φ L)) ∧
    Real.sqrt (2 * q₀) ≤ mStar

end LatticeSystem.Quantum
