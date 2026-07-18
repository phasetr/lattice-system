import LatticeSystem.Math.MatrixAnalysis.HermitianExpUnitary
import LatticeSystem.Quantum.SpinS.ManyBodyOperatorNorm

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

/-- The site-`x` raising operator commutes with the staggered lowering order operator except at its
own site, where the single-site Cartan relation contributes `ε_x · onSiteS x (2 Ŝ³)`. -/
private theorem spinSSiteOpPlus_commutator_staggeredLoweringOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOpPlus x N * staggeredLoweringOpS A N
      - staggeredLoweringOpS A N * spinSSiteOpPlus x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • onSiteS x ((2 : ℂ) • spinSOp3 N) := by
  unfold staggeredLoweringOpS spinSSiteOpPlus spinSSiteOpMinus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOpPlus_commutator_spinSOpMinus]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOpPlus N) (spinSOpMinus N)).eq, sub_self,
      smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Staggered order-operator commutator** (eq. (4.2.32)): `[Ô_L^+, Ô_L^-] = 2 Ŝ_tot^{(3)}`.  The
staggered signs square to `1`, so the commutator is the unsigned total `Ŝ³`; cross-site terms vanish
and each on-site term contributes the single-site Cartan relation `[Ŝ^+, Ŝ^-] = 2 Ŝ^{(3)}`. -/
theorem staggeredOrder_commutator (A : Λ → Bool) :
    staggeredRaisingOpS A N * staggeredLoweringOpS A N
      - staggeredLoweringOpS A N * staggeredRaisingOpS A N
      = (2 : ℂ) • (totalSpinSOp3 Λ N) := by
  have hsum : (totalSpinSOp3 Λ N) = ∑ x : Λ, onSiteS x (spinSOp3 N) := rfl
  unfold staggeredRaisingOpS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub,
    spinSSiteOpPlus_commutator_staggeredLoweringOpS, smul_smul,
    show (if A x then (1 : ℂ) else (-1 : ℂ)) * (if A x then (1 : ℂ) else (-1 : ℂ)) = 1
      from by split_ifs <;> ring, one_smul, onSiteS_smul]

/-- **Per-site `Ŝ³` norm bound** `‖Ŝₓ^{(3)}‖ ≤ N/2` (`= S`): `Ŝ^{(3)}` is the diagonal of magnetic
quantum numbers `m_k = N/2 − k ∈ [−N/2, N/2]`. -/
theorem onSiteS_spinSOp3_manyBodyOperatorNormS_le (x : Λ) :
    manyBodyOperatorNormS (onSiteS x (spinSOp3 N)) ≤ (N : ℝ) / 2 := by
  rw [show spinSOp3 N = Matrix.diagonal (fun k : Fin (N + 1) => ((N : ℂ) / 2 - (k.val : ℂ)))
      from rfl, onSiteS_diagonal]
  refine manyBodyOperatorNormS_diagonal_le (by positivity) (fun σ => ?_)
  have hk : ((σ x).val : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (σ x).isLt
  have hk0 : (0 : ℝ) ≤ ((σ x).val : ℝ) := by positivity
  rw [show ((N : ℂ) / 2 - ((σ x).val : ℂ)) = (((N : ℝ) / 2 - ((σ x).val : ℝ)) : ℝ)
      from by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **Total `Ŝ³` norm bound** `‖Ŝ_tot^{(3)}‖ ≤ V·N/2`: triangle inequality over the `V` sites. -/
theorem totalSpinSOp3_manyBodyOperatorNormS_le :
    manyBodyOperatorNormS (totalSpinSOp3 Λ N) ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [show (totalSpinSOp3 Λ N) = ∑ x : Λ, onSiteS x (spinSOp3 N) from rfl]
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  calc ∑ x : Λ, manyBodyOperatorNormS (onSiteS x (spinSOp3 N))
      ≤ ∑ _x : Λ, (N : ℝ) / 2 :=
        Finset.sum_le_sum (fun x _ => onSiteS_spinSOp3_manyBodyOperatorNormS_le x)
    _ = (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **Per-volume order-operator commutator norm bound** `‖[ô⁺, ô⁻]‖ ≤ N/V` (eq. (4.2.33),
`o₀ = N`): `[ô⁺, ô⁻] = V⁻² [Ô⁺, Ô⁻] = V⁻² · 2 Ŝ_tot^{(3)}`, with `‖Ŝ_tot^{(3)}‖ ≤ V·N/2`. -/
theorem staggeredOrderDensity_commutator_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L]
    (hN : 1 ≤ N) :
    manyBodyOperatorNormS
        (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
      ≤ (N : ℝ) / (L : ℝ) ^ d := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hcard : (Fintype.card (HypercubicTorus d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_hypercubicTorus]; push_cast; ring
  have htrue : staggeredOrderDensityOpS d L N true
      = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N := rfl
  have hfalse : staggeredOrderDensityOpS d L N false
      = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N := rfl
  have hcomm : staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
      - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
      = (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) •
          ((2 : ℂ) • (totalSpinSOp3 (HypercubicTorus d L) N)) := by
    rw [htrue, hfalse, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub,
      staggeredOrder_commutator]
  rw [hcomm, manyBodyOperatorNormS_smul, manyBodyOperatorNormS_smul]
  have hc1 : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  have hc : ‖((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ := by
    rw [norm_mul, hc1]
  have hc2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hc, hc2]
  have hS := totalSpinSOp3_manyBodyOperatorNormS_le (Λ := HypercubicTorus d L) (N := N)
  rw [hcard] at hS
  calc ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * manyBodyOperatorNormS _)
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * ((L : ℝ) ^ d * (N : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = (N : ℝ) / (L : ℝ) ^ d := by field_simp

/-! ### Combinatorial core: adjacent-swap chains on binary words

The rearrangement counting for Lemma 4.14 uses only adjacent transpositions of binary words (no
permutation-group or sorting theory): a length-indexed `SwapChain`, the `bringToFront` move, and the
diameter bound `swapDist ≤ (#true)·(#false)`. -/

/-- A single **adjacent transposition** of two neighbouring letters in a word (the letters
may be equal — the trivial swap is allowed and costs nothing).  Stated over an arbitrary letter
alphabet `α` so that both the `Bool` ladder words (Theorem 4.6) and the `Fin 3` Cartesian order
words (Proposition 4.10, `cartWord`) share the same swap-chain machinery. -/
def AdjSwap {α : Type*} (w w' : List α) : Prop :=
  ∃ (pre suf : List α) (a b : α), w = pre ++ a :: b :: suf ∧ w' = pre ++ b :: a :: suf

/-- An adjacent transposition preserves length. -/
theorem AdjSwap.length_eq {α : Type*} {w w' : List α} (h : AdjSwap w w') :
    w.length = w'.length := by
  obtain ⟨pre, suf, a, b, rfl, rfl⟩ := h; simp [List.length_append]

/-- A **length-`k` chain** of adjacent transpositions connecting `w` to `w'`, over an arbitrary
letter alphabet `α`. -/
inductive SwapChain {α : Type*} : ℕ → List α → List α → Prop
  | refl (w : List α) : SwapChain 0 w w
  | step {k : ℕ} {w w' w'' : List α} :
      AdjSwap w w' → SwapChain k w' w'' → SwapChain (k + 1) w w''

/-- Concatenation of swap chains. -/
theorem SwapChain.trans {α : Type*} {j k : ℕ} {w w' w'' : List α} :
    SwapChain j w w' → SwapChain k w' w'' → SwapChain (j + k) w w'' := by
  intro h1 h2
  induction h1 with
  | refl => simpa using h2
  | step hs _ ih => exact (Nat.succ_add _ _ ▸ SwapChain.step hs (ih h2))

/-- Prefixing a fixed letter to both endpoints preserves a swap chain (and its length). -/
theorem SwapChain.cons {α : Type*} {k : ℕ} {w w' : List α} (a : α) (h : SwapChain k w w') :
    SwapChain k (a :: w) (a :: w') := by
  induction h with
  | refl => exact SwapChain.refl _
  | step hs _ ih =>
    obtain ⟨pre, suf, x, y, rfl, rfl⟩ := hs
    exact SwapChain.step ⟨a :: pre, suf, x, y, by simp, by simp⟩ ih

/-- A swap chain preserves length. -/
theorem SwapChain.length_eq {α : Type*} {k : ℕ} {w w' : List α} (h : SwapChain k w w') :
    w.length = w'.length := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact (hs.length_eq).trans ih

/-- **Bring an occurrence of `a` to the front**: if `a ∈ w`, a swap chain of length at most the
number of letters `≠ a` moves an `a` to the head.  Stated over an arbitrary letter alphabet `α`
with decidable equality (the proof is `Bool`-independent), so that both the binary ladder words
(Theorem 4.6) and the `Fin 3` Cartesian order words (Proposition 4.10) reuse it. -/
theorem bringToFront {α : Type*} [DecidableEq α] : ∀ {a : α} {w : List α}, a ∈ w →
    ∃ (rest : List α) (k : ℕ), w.Perm (a :: rest) ∧
      k ≤ w.countP (· != a) ∧ SwapChain k w (a :: rest)
  | a, [], h => absurd h (by simp)
  | a, x :: xs, h => by
    by_cases hx : x = a
    · subst hx
      exact ⟨xs, 0, List.Perm.refl _, Nat.zero_le _, SwapChain.refl _⟩
    · have hmem : a ∈ xs := by
        rcases List.mem_cons.1 h with h' | h'
        · exact absurd h'.symm hx
        · exact h'
      obtain ⟨rest, k, hperm, hk, hchain⟩ := bringToFront hmem
      refine ⟨x :: rest, k + 1, ?_, ?_, ?_⟩
      · exact (hperm.cons x).trans (List.Perm.swap a x rest)
      · have hxa : (x != a) = true := bne_iff_ne.mpr hx
        simp only [List.countP_cons, hxa, if_true]
        omega
      · exact SwapChain.trans (SwapChain.cons x hchain)
          (SwapChain.step ⟨[], rest, x, a, by simp, by simp⟩ (SwapChain.refl _))

/-- For a binary word, the `true`- and `false`-counts sum to the length. -/
theorem count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases x <;> simp <;> omega

/-- Two binary words with the same `true`-count and length are permutations of each other. -/
theorem binary_perm_of_count {w w' : List Bool}
    (hlen : w.length = w'.length) (ht : w.count true = w'.count true) : w.Perm w' := by
  rw [List.perm_iff_count]
  intro b
  cases b with
  | true => exact ht
  | false =>
    have h1 := count_true_add_count_false w
    have h2 := count_true_add_count_false w'
    omega

/-- `countP (· != a)` counts the letters different from `a`, i.e. the `!a` letters. -/
private theorem countP_bne_eq_count_not (w : List Bool) (a : Bool) :
    w.countP (· != a) = w.count (!a) := by
  rw [List.count]
  refine List.countP_congr (fun b _ => ?_)
  cases a <;> cases b <;> rfl

/-- **Swap-diameter bound**: two binary words of the same multiset are connected by a swap chain of
length at most `(#true)·(#false)`.  Proved by induction on the *target* word via `bringToFront`. -/
theorem swapDist_le : ∀ {w w' : List Bool}, w.Perm w' →
    ∃ k, k ≤ w.count true * w.count false ∧ SwapChain k w w'
  | w, [], hperm => by
    rw [List.Perm.nil_eq (hperm.symm)]
    exact ⟨0, by simp, SwapChain.refl _⟩
  | w, a :: w'', hperm => by
    have hmem : a ∈ w := hperm.symm.subset (by simp)
    obtain ⟨rest, k, hpr, hk, hchain⟩ := bringToFront hmem
    have hrest : rest.Perm w'' := (List.perm_cons a).1 (hpr.symm.trans hperm)
    obtain ⟨k', hk', hchain'⟩ := swapDist_le hrest
    refine ⟨k + k', ?_, SwapChain.trans hchain (SwapChain.cons a hchain')⟩
    rw [countP_bne_eq_count_not] at hk
    have hct : w.count true = (a :: rest).count true := hpr.count_eq true
    have hcf : w.count false = (a :: rest).count false := hpr.count_eq false
    cases a with
    | true =>
      have e1 : w.count true = rest.count true + 1 := by rw [hct, List.count_cons]; simp
      have e2 : w.count false = rest.count false := by rw [hcf, List.count_cons]; simp
      have hk2 : k ≤ rest.count false := by rw [← e2]; simpa using hk
      rw [e1, e2]
      nlinarith [hk2, hk', Nat.zero_le (rest.count true), Nat.zero_le (rest.count false)]
    | false =>
      have e1 : w.count true = rest.count true := by rw [hct, List.count_cons]; simp
      have e2 : w.count false = rest.count false + 1 := by rw [hcf, List.count_cons]; simp
      have hk2 : k ≤ rest.count true := by rw [← e1]; simpa using hk
      rw [e1, e2]
      nlinarith [hk2, hk', Nat.zero_le (rest.count true), Nat.zero_le (rest.count false)]

/-- **Generic swap-diameter bound** over an arbitrary alphabet: two words of the same multiset are
connected by a swap chain of length at most `(length)²`.  Unlike the tight binary bound
`swapDist_le` (used at its `Bool` alphabet by Theorem 4.9), this holds for any alphabet: the loose
`length²` diameter suffices for the `Fin 3` Cartesian order words of Proposition 4.10.  Proved by
induction on the *target* word via `bringToFront`, bounding each front-move by `≤ length`. -/
theorem swapDist_le_length_sq {α : Type*} {w w' : List α} (hperm : w.Perm w') :
    ∃ k, k ≤ w.length * w.length ∧ SwapChain k w w' := by
  classical
  induction w' generalizing w with
  | nil =>
    rw [List.Perm.nil_eq (hperm.symm)]
    exact ⟨0, by simp, SwapChain.refl _⟩
  | cons a w'' ih =>
    have hmem : a ∈ w := hperm.symm.subset (by simp)
    obtain ⟨rest, k, hpr, hk, hchain⟩ := bringToFront hmem
    have hrest : rest.Perm w'' := (List.perm_cons a).1 (hpr.symm.trans hperm)
    obtain ⟨k', hk', hchain'⟩ := ih hrest
    refine ⟨k + k', ?_, hchain.trans (hchain'.cons a)⟩
    have hlen : w.length = rest.length + 1 := by rw [hpr.length_eq, List.length_cons]
    have hkle : k ≤ rest.length + 1 := by
      rw [← hlen]; exact le_trans hk List.countP_le_length
    calc k + k' ≤ (rest.length + 1) + rest.length * rest.length := Nat.add_le_add hkle hk'
      _ ≤ (rest.length + 1) * (rest.length + 1) := by nlinarith [Nat.zero_le rest.length]
      _ = w.length * w.length := by rw [hlen]

/-! ### Word products of order operators and their swap-difference norm bounds (§4) -/

/-- The **ordered product** of per-volume order operators along a binary word `w` (`true = ô⁺`,
`false = ô⁻`). -/
noncomputable def orderWordProd (d L N : ℕ) [NeZero L] (w : List Bool) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  (w.map (staggeredOrderDensityOpS d L N)).prod

/-- The word product over a length-`ℓ` word has norm `≤ N^ℓ` (each factor has norm `≤ N`). -/
theorem orderWordProd_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (w : List Bool) : manyBodyOperatorNormS (orderWordProd d L N w) ≤ (N : ℝ) ^ w.length := by
  induction w with
  | nil => simp [orderWordProd, manyBodyOperatorNormS_eq_toEuclideanCLM]
  | cons b t ih =>
    rw [orderWordProd, List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    refine mul_le_mul (staggeredOrderDensityOpS_manyBodyOperatorNormS_le d L N b hN) ih
      (manyBodyOperatorNormS_nonneg _) (by positivity)

/-- The single-swap commutator-norm cost `‖ô^a ô^b − ô^b ô^a‖ ≤ N/V` for any signs `a, b` (equal
signs give `0`; `(+,−)` is eq. (4.2.33); `(−,+)` follows by negation). -/
theorem orderOp_swapComm_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) (a b : Bool) :
    manyBodyOperatorNormS (staggeredOrderDensityOpS d L N a * staggeredOrderDensityOpS d L N b
        - staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N a)
      ≤ (N : ℝ) / (L : ℝ) ^ d := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  cases a <;> cases b
  · simp only [sub_self, manyBodyOperatorNormS_zero]; positivity
  · rw [show staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
        = -(staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        from by rw [neg_sub], manyBodyOperatorNormS_neg]
    exact staggeredOrderDensity_commutator_manyBodyOperatorNormS_le d L N hN
  · exact staggeredOrderDensity_commutator_manyBodyOperatorNormS_le d L N hN
  · simp only [sub_self, manyBodyOperatorNormS_zero]; positivity

/-- A single adjacent transposition of a length-`ℓ` word changes the order-word product by at most
`N^(ℓ−2)·(N/V)`: the difference factors as `pre · [ô^a, ô^b] · suf`. -/
theorem adjSwap_orderWordProd_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    {w w' : List Bool} (h : AdjSwap w w') :
    manyBodyOperatorNormS (orderWordProd d L N w - orderWordProd d L N w')
      ≤ (N : ℝ) ^ (w.length - 2) * ((N : ℝ) / (L : ℝ) ^ d) := by
  obtain ⟨pre, suf, a, b, rfl, rfl⟩ := h
  have hexp : ∀ x y : Bool, orderWordProd d L N (pre ++ x :: y :: suf)
      = orderWordProd d L N pre
        * (staggeredOrderDensityOpS d L N x * staggeredOrderDensityOpS d L N y)
        * orderWordProd d L N suf := by
    intro x y
    simp only [orderWordProd, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    noncomm_ring
  rw [hexp, hexp, ← sub_mul, ← mul_sub]
  refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
  refine le_trans (mul_le_mul_of_nonneg_right (manyBodyOperatorNormS_mul_le _ _)
    (manyBodyOperatorNormS_nonneg _)) ?_
  have hlen : (pre ++ a :: b :: suf).length - 2 = pre.length + suf.length := by
    simp [List.length_append]; omega
  rw [hlen, pow_add]
  have hpre := orderWordProd_manyBodyOperatorNormS_le d L N hN pre
  have hsuf := orderWordProd_manyBodyOperatorNormS_le d L N hN suf
  have hcomm := orderOp_swapComm_manyBodyOperatorNormS_le d L N hN a b
  have hNpre : (0 : ℝ) ≤ (N : ℝ) ^ pre.length := by positivity
  have hNsuf : (0 : ℝ) ≤ (N : ℝ) ^ suf.length := by positivity
  calc manyBodyOperatorNormS (orderWordProd d L N pre)
          * manyBodyOperatorNormS
            (staggeredOrderDensityOpS d L N a * staggeredOrderDensityOpS d L N b
              - staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N a)
          * manyBodyOperatorNormS (orderWordProd d L N suf)
      ≤ (N : ℝ) ^ pre.length * ((N : ℝ) / (L : ℝ) ^ d) * (N : ℝ) ^ suf.length := by
        refine mul_le_mul (mul_le_mul hpre hcomm (manyBodyOperatorNormS_nonneg _) hNpre) hsuf
          (manyBodyOperatorNormS_nonneg _) (by positivity)
    _ = (N : ℝ) ^ pre.length * (N : ℝ) ^ suf.length * ((N : ℝ) / (L : ℝ) ^ d) := by ring

/-- A swap chain of length `k` changes the order-word product by at most `k · N^(ℓ−1)/V`, where `ℓ`
is the (common) word length. -/
theorem swapChain_orderWordProd_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    {k : ℕ} {w w' : List Bool} (hc : SwapChain k w w') :
    manyBodyOperatorNormS (orderWordProd d L N w - orderWordProd d L N w')
      ≤ (k : ℝ) * ((N : ℝ) ^ (w.length - 1) / (L : ℝ) ^ d) := by
  induction hc with
  | refl w => simp [manyBodyOperatorNormS_zero]
  | @step j w w' w'' hs hchain ih =>
    have hlen : w.length = w'.length := hs.length_eq
    have hge2 : 2 ≤ w.length := by
      obtain ⟨pre, suf, a, b, rfl, _⟩ := hs; simp only [List.length_append, List.length_cons]; omega
    refine le_trans (manyBodyOperatorNormS_sub_le' _ (orderWordProd d L N w') _) ?_
    have h1 : manyBodyOperatorNormS (orderWordProd d L N w - orderWordProd d L N w')
        ≤ (N : ℝ) ^ (w.length - 1) / (L : ℝ) ^ d := by
      refine le_trans (adjSwap_orderWordProd_manyBodyOperatorNormS_le d L N hN hs) ?_
      rw [show (N : ℝ) ^ (w.length - 2) * ((N : ℝ) / (L : ℝ) ^ d)
          = (N : ℝ) ^ (w.length - 2) * (N : ℝ) / (L : ℝ) ^ d from by ring,
        ← pow_succ, show w.length - 2 + 1 = w.length - 1 from by omega]
    have ih' : manyBodyOperatorNormS (orderWordProd d L N w' - orderWordProd d L N w'')
        ≤ (j : ℝ) * ((N : ℝ) ^ (w.length - 1) / (L : ℝ) ^ d) := by rw [hlen]; exact ih
    refine le_trans (add_le_add h1 ih') (le_of_eq ?_)
    push_cast; ring

/-- The order-word products of two balanced words differ by at most `n²·N^(2n−1)/V`: combine the
swap-diameter bound (`≤ n²` adjacent swaps, `swapDist_le`) with the per-chain norm bound. -/
theorem orderWordProd_sub_balanced_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    {n : ℕ} {w w' : List Bool} (hperm : w.Perm w') (hL : w.length = 2 * n)
    (htrue : w.count true = n) :
    manyBodyOperatorNormS (orderWordProd d L N w - orderWordProd d L N w')
      ≤ (n : ℝ) ^ 2 * ((N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d) := by
  obtain ⟨k, hk, hchain⟩ := swapDist_le hperm
  have hfalse : w.count false = n := by
    have := count_true_add_count_false w; omega
  have hkn : (k : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hk2 : k ≤ n * n := by rw [htrue, hfalse] at hk; exact hk
    have hcast : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by rw [Nat.cast_mul, pow_two]
    rw [← hcast]; exact_mod_cast hk2
  refine le_trans (swapChain_orderWordProd_manyBodyOperatorNormS_le d L N hN hchain) ?_
  rw [hL]
  refine mul_le_mul_of_nonneg_right hkn ?_
  positivity

/-! ### Expansion of `p̂ⁿ` as a uniform combination of balanced words (§5) -/

/-- Snoc-decomposition of `Fin (n+1) → Bool` with `rfl`-clean components (init restriction and last
value), used to expand the noncommutative `(A+B)^n`. -/
def boolFinSuccEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) × Bool where
  toFun c := (fun i => c i.castSucc, c (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv c := by funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by refine Prod.ext ?_ ?_ <;> simp

/-- **Noncommutative binomial expansion** as an ordered sum over sign assignments:
`(A + B)^n = Σ_{c : Fin n → Bool} ∏_k (if c k then A else B)`.  Proved by induction on `n`
peeling the last factor (the commutative `add_pow` is unavailable in a noncommutative ring).
**Note**: this is a specialization of the fully general `pow_sum_smul_eq_sum_smul_prod`
(NoncommPowerExpansion.lean) to the case `ι = Bool` (two operators via smul scalars
`1 • A` and `1 • B`). -/
theorem add_pow_eq_sum_ofFn {R : Type*} [Ring R] (A B : R) :
    ∀ n : ℕ, (A + B) ^ n
      = ∑ c : Fin n → Bool, (List.ofFn (fun k => if c k then A else B)).prod
  | 0 => by simp
  | (n + 1) => by
    have h : ∀ c' : Fin (n + 1) → Bool,
        (List.ofFn (fun k => if c' k then A else B)).prod
          = (List.ofFn (fun k => if (boolFinSuccEquiv n c').1 k then A else B)).prod
            * (if (boolFinSuccEquiv n c').2 then A else B) :=
      fun c' => by
        rw [List.ofFn_succ', List.prod_concat]; rfl
    rw [pow_succ, add_pow_eq_sum_ofFn A B n, Finset.sum_mul,
      Fintype.sum_equiv (boolFinSuccEquiv n)
        (fun c' : Fin (n + 1) → Bool => (List.ofFn (fun k => if c' k then A else B)).prod)
        (fun p : (Fin n → Bool) × Bool =>
          (List.ofFn (fun k => if p.1 k then A else B)).prod * (if p.2 then A else B)) h,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Fintype.sum_bool]
    exact mul_add _ A B

/-- The **block word** for a sign assignment `c : Fin n → Bool`: a length-`2n` balanced binary word
that concatenates the block `[+, −]` (`c k = true`) or `[−, +]` (`c k = false`) for each `k`. -/
def blockWord {n : ℕ} (c : Fin n → Bool) : List Bool :=
  (List.ofFn fun k => if c k then [true, false] else [false, true]).flatten

/-- A block word has length `2n`. -/
theorem blockWord_length {n : ℕ} (c : Fin n → Bool) : (blockWord c).length = 2 * n := by
  simp only [blockWord, List.length_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  simp only [Function.comp]
  rw [show (fun k => (if c k then [true, false] else [false, true]).length) = (fun _ => 2) from by
    funext k; split <;> rfl]
  simp [Finset.sum_const, mul_comm]

/-- A block word has exactly `n` `true` letters (it is balanced). -/
theorem blockWord_count_true {n : ℕ} (c : Fin n → Bool) : (blockWord c).count true = n := by
  simp only [blockWord, List.count_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  simp only [Function.comp]
  rw [show (fun k => (if c k then [true, false] else [false, true]).count true) = (fun _ => 1)
      from by funext k; split <;> rfl]
  simp

/-- The order-word product of a block word equals the ordered product of the block operators
`A = ô⁺ô⁻` (`c k = true`) or `B = ô⁻ô⁺` (`c k = false`). -/
theorem orderWordProd_blockWord (d L N : ℕ) [NeZero L] {n : ℕ} (c : Fin n → Bool) :
    orderWordProd d L N (blockWord c)
      = (List.ofFn (fun k => if c k
          then staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          else
            staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)).prod := by
  simp only [orderWordProd, blockWord, List.map_flatten, List.prod_flatten, List.map_ofFn]
  congr 1
  refine List.ext_getElem (by simp) (fun k h1 h2 => ?_)
  simp only [List.getElem_ofFn, Function.comp]
  split <;> simp [staggeredOrderDensityOpS]

/-- `p̂ⁿ` is the uniform `(½)ⁿ`-combination of the `2ⁿ` block-word products. -/
theorem staggeredPhatS_pow_eq (d L N n : ℕ) [NeZero L] :
    staggeredPhatS d L N ^ n
      = ((2 : ℂ)⁻¹) ^ n • ∑ c : Fin n → Bool, orderWordProd d L N (blockWord c) := by
  rw [staggeredPhatS, smul_pow, add_pow_eq_sum_ofFn]
  congr 1
  refine Finset.sum_congr rfl (fun c _ => (orderWordProd_blockWord d L N c).symm)

/-- The `true`-count of a binary word `List.ofFn s` equals the cardinality of the `true`-fiber of
`s` (so a `BalancedSigns` sequence yields a balanced word). -/
theorem count_true_ofFn {m : ℕ} (s : Fin m → Bool) :
    (List.ofFn s).count true = (Finset.univ.filter (fun i => s i = true)).card := by
  have h : ∀ {m : ℕ} (s : Fin m → Bool),
      (List.ofFn s).count true = ∑ i : Fin m, (if s i then 1 else 0) := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      rw [List.ofFn_succ, List.count_cons, ih (fun i => s i.succ), Fin.sum_univ_succ]
      have hif : (if (s 0 == true) then (1 : ℕ) else 0) = (if s 0 then 1 else 0) := by
        cases s 0 <;> rfl
      rw [hif]; ring
  rw [h s, Finset.card_filter]

/-- At `N = 0` (spin `0`) the per-volume order operator vanishes (the single-site ladder operators
are the `1×1` zero matrices). -/
theorem staggeredOrderDensityOpS_zero (d L : ℕ) [NeZero L] (b : Bool) :
    staggeredOrderDensityOpS d L 0 b = 0 := by
  have hp : spinSOpPlus 0 = 0 := by ext i j; fin_cases i; fin_cases j; simp [spinSOpPlus]
  have hm : spinSOpMinus 0 = 0 := by ext i j; fin_cases i; fin_cases j; simp [spinSOpMinus]
  have hos : ∀ (x : HypercubicTorus d L), (onSiteS x (0 : Matrix (Fin 1) (Fin 1) ℂ)
      : ManyBodyOpS (HypercubicTorus d L) 0) = 0 := by
    intro x; ext σ' σ; rw [onSiteS_apply]; simp
  unfold staggeredOrderDensityOpS staggeredRaisingOpS staggeredLoweringOpS spinSSiteOpPlus
    spinSSiteOpMinus
  cases b <;> simp [hp, hm, hos]

/-- **Tasaki Lemma 4.14 (order-operator algebra estimate), now a THEOREM.**  For any balanced sign
sequence `s` of length `2n` (`n > 0`), the `L²` operator norm of the difference between the ordered
product
`ô^{s₁} ⋯ ô^{s_{2n}}` and `p̂ⁿ` is bounded by `n² (o₀)^{2n−1} / V`, where `o₀ = 2S = N` and
`V = L^d` (eq. (4.2.34)):
`‖ô^{s₁} ⋯ ô^{s_{2n}} − p̂ⁿ‖ ≤ n² N^{2n−1} / L^d`.

Any balanced product rearranges to any other by `≤ n²` neighboring `±` exchanges, each costing
`≤ ‖[ô^+, ô^-]‖ ≤ o₀/V` (eq. (4.2.33)); the bound follows with `‖ô^{±}‖ ≤ o₀`.  The proof writes
`p̂ⁿ` as the uniform `(½)ⁿ`-combination of the `2ⁿ` balanced block words (`staggeredPhatS_pow_eq`),
turns the difference into an average of word differences, and bounds each by `n²·N^{2n−1}/V` through
the adjacent-swap telescoping (`orderWordProd_sub_balanced_manyBodyOperatorNormS_le`). -/
theorem staggered_balanced_order_product_norm_le {d L N n : ℕ} [NeZero L] (hn : 0 < n)
    (s : Fin (2 * n) → Bool) (hbal : BalancedSigns s) :
    manyBodyOperatorNormS (balancedOrderProductS d L N n s - staggeredPhatS d L N ^ n) ≤
      (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- N = 0: every per-volume order operator vanishes, so the difference is `0`.
    subst hN0
    have hbop : balancedOrderProductS d L 0 n s = 0 := by
      rw [balancedOrderProductS]
      refine List.prod_eq_zero ?_
      refine List.mem_ofFn.2 ⟨⟨0, by omega⟩, ?_⟩
      rw [staggeredOrderDensityOpS_zero]
    have hphat : staggeredPhatS d L 0 ^ n = 0 := by
      have h0 : staggeredPhatS d L 0 = 0 := by
        rw [staggeredPhatS]; simp [staggeredOrderDensityOpS_zero]
      rw [h0, zero_pow (by omega : n ≠ 0)]
    rw [hbop, hphat, sub_zero, manyBodyOperatorNormS_zero]
    positivity
  · -- 1 ≤ N: average the balanced-word swap bound over the `2ⁿ` block words.
    have hN1 : 1 ≤ N := hN
    have hbop : balancedOrderProductS d L N n s = orderWordProd d L N (List.ofFn s) := by
      rw [balancedOrderProductS, orderWordProd, List.map_ofFn]; rfl
    have hLs : (List.ofFn s).length = 2 * n := by rw [List.length_ofFn]
    have htrue : (List.ofFn s).count true = n := by rw [count_true_ofFn]; exact hbal
    have hcard : (Fintype.card (Fin n → Bool)) = 2 ^ n := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hconst : orderWordProd d L N (List.ofFn s)
        = ((2 : ℂ)⁻¹) ^ n • ∑ _c : Fin n → Bool, orderWordProd d L N (List.ofFn s) := by
      have hsum : (∑ _c : Fin n → Bool, orderWordProd d L N (List.ofFn s))
          = ((2 : ℂ) ^ n) • orderWordProd d L N (List.ofFn s) := by
        simp only [Finset.sum_const, Finset.card_univ, hcard,
          ← Nat.cast_smul_eq_nsmul (R := ℂ), Nat.cast_pow, Nat.cast_ofNat]
      rw [hsum, smul_smul, ← mul_pow]
      norm_num
    rw [hbop, staggeredPhatS_pow_eq, hconst, ← smul_sub, ← Finset.sum_sub_distrib,
      manyBodyOperatorNormS_smul]
    have hnorm2 : ‖((2 : ℂ)⁻¹) ^ n‖ = ((2 : ℝ)⁻¹) ^ n := by
      rw [norm_pow, norm_inv, Complex.norm_ofNat]
    rw [hnorm2]
    have hsum_le : manyBodyOperatorNormS
        (∑ c : Fin n → Bool,
          (orderWordProd d L N (List.ofFn s) - orderWordProd d L N (blockWord c)))
        ≤ (2 ^ n : ℝ) * ((n : ℝ) ^ 2 * ((N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d)) := by
      refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
      calc ∑ c : Fin n → Bool, manyBodyOperatorNormS
              (orderWordProd d L N (List.ofFn s) - orderWordProd d L N (blockWord c))
          ≤ ∑ _c : Fin n → Bool, (n : ℝ) ^ 2 * ((N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d) := by
            refine Finset.sum_le_sum (fun c _ => ?_)
            refine orderWordProd_sub_balanced_manyBodyOperatorNormS_le d L N hN1 ?_ hLs htrue
            exact binary_perm_of_count (by rw [hLs, blockWord_length])
              (by rw [htrue, blockWord_count_true])
        _ = (2 ^ n : ℝ) * ((n : ℝ) ^ 2 * ((N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d)) := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; push_cast; ring
    refine le_trans (mul_le_mul_of_nonneg_left hsum_le (by positivity)) (le_of_eq ?_)
    rw [mul_div_assoc]
    rw [show ((2 : ℝ)⁻¹) ^ n * ((2 ^ n : ℝ) * ((n : ℝ) ^ 2 * ((N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d)))
        = (((2 : ℝ)⁻¹) ^ n * (2 : ℝ) ^ n) * ((n : ℝ) ^ 2 * ((N : ℝ) ^ (2 * n - 1) / (L : ℝ) ^ d))
        from by ring, ← mul_pow]
    norm_num

open Filter in
/-- **Tasaki Lemma 4.15 (the order parameter as a `p̂`-ratio double limit), AXIOM.**  Tasaki
§4.2.2 eq. (4.2.38) (rendered p. 105) states the symmetry-breaking order parameter `m∗` as the
square-rooted iterated limit of the ground-state `p̂`-ratios,
`m∗ = lim_{n↑∞} liminf_{L↑∞} √(⟨p̂^{n+1}⟩ / ⟨p̂^n⟩)` (the `√` radical is present in the printed
equation; a `pdftotext` extraction of the PDF dropped it).  Squaring, this equivalently records
that the **bare (unrooted) ratio** has the iterated limit `(m∗)²`, i.e.
`(m∗)² = lim_{n↑∞} liminf_{L↑∞} ⟨p̂^{n+1}⟩ / ⟨p̂^n⟩` (the `n`-ratio is increasing and bounded, so
the outer limit exists; the inner is a `liminf` per footnote 31).  This is consistent with
`p̂ = (ô¹)² + (ô²)²` having density-squared dimension (`⟨p̂^n⟩ ≃ (m∗)^{2n}`, txt:5709–5710) and
with eq. (4.2.37) `⟨p̂^n⟩/⟨p̂^{n-1}⟩ ≥ 2 q₀` combined with eq. (4.2.39) `m∗ ≥ √(2 q₀)`.  We state
the sound `liminf`-lower direction of the squared form — for every `ε > 0`, for all large `n`,
eventually in (even) `L` the bare ratio exceeds `(m∗)² − ε` — which captures
`lim_n liminf_L ⟨p̂^{n+1}⟩/⟨p̂^n⟩ ≥ (m∗)²`.  The axiom also records the `U(1)`-optimal bound
`√(2 q₀) ≤ m∗` (eq. (4.2.39), the weaker `√2` companion of Theorem 4.11's `√3`).

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
        mStar ^ 2 - ε <
          expectationRatioRe (staggeredPhatS d L N ^ (n + 1)) (Φ L) /
            expectationRatioRe (staggeredPhatS d L N ^ n) (Φ L)) ∧
    Real.sqrt (2 * q₀) ≤ mStar

end LatticeSystem.Quantum
