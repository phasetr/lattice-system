/-
Tasaki §4.2.2 Theorem 4.8 (Tanaka symmetry-breaking state), crux sub-arc PR-A — the `±`-word
expansion basis, the scale-invariance bridge, and the two charge-selection rules.

The Tanaka tower is built from the `1`-axis order operator `ô^{(1)} = (ô⁺ + ô⁻)/2`
(`staggeredOrderOp1S`, Cartesian decomposition eqs. (4.2.30)/(4.2.31)).  To analyse the double
commutator `[(ô^{(1)})^k, [Ĥ, (ô^{(1)})^k]]` (eqs. (4.2.70)/(4.2.71)) one expands each power into a
sum of `±`-order words `ô^{s₁} ⋯ ô^{s_k}` (`orderWordProd`), by the noncommutative binomial theorem
`add_pow_eq_sum_ofFn` applied to `Ã := ô⁺ + ô⁻` (the volume factor `V/2 = L^d/2` is pulled out and
killed by Rayleigh-quotient scale invariance).  On a `Ŝ_tot^{(3)}`-singlet ground state `Φ`
(eq. (4.1.7)) every word carries a definite net magnetization charge `m(w)` (`mCharge`), so only
charge-neutral words survive in an expectation value — the selection rule underlying the binomial
cancellation `C(2M-2, M-1)/C(2M, M) = M/(2(2M-1))` at the heart of the crux.

This file provides only the *expansion basis* consumed by the later crux PRs (PR-B denominator lower
bound, PR-C telescoping/charge decomposition, PR-D assembly, PR-E capstone).  It touches none of the
crux core (the `Nat.choose` counting / Pascal ratio / telescoping).  All order-word leaf bounds are
word-generic and are reused verbatim, never copied for the `1`-axis operator.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §4.2.2, pp. 111–112,
eqs. (4.2.10), (4.2.30), (4.2.31), (4.2.67)–(4.2.71); Tanaka [62]/[66].
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46

namespace LatticeSystem.Quantum

open Matrix

/-! ### `±`-word expansion basis (eqs. (4.2.67)/(4.2.71) density side) -/

/-- The order-word product along `List.ofFn c` (`c : Fin K → Bool`) is the ordered product of the
per-index order densities `ô⁺` (`c k = true`) or `ô⁻` (`c k = false`): this is the single-letter
form of the block-word identity `orderWordProd_blockWord`. -/
theorem orderWordProd_ofFn (d L N K : ℕ) [NeZero L] (c : Fin K → Bool) :
    orderWordProd d L N (List.ofFn c)
      = (List.ofFn (fun k => if c k then staggeredOrderDensityOpS d L N true
          else staggeredOrderDensityOpS d L N false)).prod := by
  have hfun : (fun k => staggeredOrderDensityOpS d L N (c k))
      = (fun k => if c k then staggeredOrderDensityOpS d L N true
          else staggeredOrderDensityOpS d L N false) := by
    funext k; cases c k <;> rfl
  rw [orderWordProd, List.map_ofFn, Function.comp_def, hfun]

/-- **`±`-word expansion of `Ã^K`** (eq. (4.2.71), density side): the `K`-th power of the summed
order density `Ã = ô⁺ + ô⁻` is the sum of all `2^K` order words of length `K`,
`(ô⁺ + ô⁻)^K = Σ_{c : Fin K → Bool} ô^{s₁} ⋯ ô^{s_K}`.  Proved from the noncommutative binomial
theorem `add_pow_eq_sum_ofFn`. -/
theorem orderDensitySum_pow_eq_sum_words (d L N K : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ K
      = ∑ c : Fin K → Bool, orderWordProd d L N (List.ofFn c) := by
  rw [add_pow_eq_sum_ofFn]
  exact Finset.sum_congr rfl (fun c _ => (orderWordProd_ofFn d L N K c).symm)

/-! ### Scale-invariance bridge (eq. (4.2.70)): drop the `V/2` normalization -/

/-- The `1`-axis order operator is `(V/2)` times the summed order density,
`Ô_L^{(1)} = (L^d/2)·(ô⁺ + ô⁻)`: combine the Cartesian decompositions `Ô^± = Ô^{(1)} ± iÔ^{(2)}`
(so `Ô⁺ + Ô⁻ = 2 Ô^{(1)}`) with the per-volume rescalings `Ô^± = V ô^±` (eqs. (4.2.30)/(4.2.31)). -/
theorem staggeredOrderOp1S_eq_smul_orderDensitySum (d L N : ℕ) [NeZero L] :
    staggeredOrderOp1S (torusParitySublattice d L) N
      = ((L : ℂ) ^ d / 2)
        • (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) := by
  have h2 : (2 : ℂ) • staggeredOrderOp1S (torusParitySublattice d L) N
      = staggeredRaisingOpS (torusParitySublattice d L) N
        + staggeredLoweringOpS (torusParitySublattice d L) N := by
    rw [staggeredRaisingOpS_eq_cartesian, staggeredLoweringOpS_eq_cartesian]; module
  rw [staggeredRaisingOpS_eq_smul, staggeredLoweringOpS_eq_smul, ← smul_add] at h2
  have hunfold : staggeredOrderOp1S (torusParitySublattice d L) N
      = (2 : ℂ)⁻¹ • ((2 : ℂ) • staggeredOrderOp1S (torusParitySublattice d L) N) := by
    rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [hunfold, h2, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- **`±`-word expansion of `(Ô_L^{(1)})^k`** (eqs. (4.2.30)/(4.2.71)): the `k`-th power of the
`1`-axis order operator is `(L^d/2)^k` times the sum of all length-`k` order words. -/
theorem orderOp1S_pow_eq_smul_sum (d L N k : ℕ) [NeZero L] :
    (staggeredOrderOp1S (torusParitySublattice d L) N) ^ k
      = ((L : ℂ) ^ d / 2) ^ k • ∑ c : Fin k → Bool, orderWordProd d L N (List.ofFn c) := by
  rw [staggeredOrderOp1S_eq_smul_orderDensitySum, smul_pow, orderDensitySum_pow_eq_sum_words]

/-- **Scale-invariance bridge** (eq. (4.2.70)): the Rayleigh quotient of the Tanaka tower term
`(Ô_L^{(1)})^k Φ` equals that of the un-normalized density power `(ô⁺ + ô⁻)^k Φ`, because the two
differ by the nonzero scalar `(L^d/2)^k` and the Rayleigh quotient is scale invariant.  This lets
the crux work with `Ã = ô⁺ + ô⁻` (no volume factor). -/
theorem tanakaTowerTerm_expectationRatioRe_eq (d L N k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
        (tanakaTowerTerm (torusParitySublattice d L) N k Φ)
      = expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
          (((staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ) := by
  have hc : ((L : ℂ) ^ d / 2) ^ k ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L))) two_ne_zero)
  have hfac : tanakaTowerTerm (torusParitySublattice d L) N k Φ
      = ((L : ℂ) ^ d / 2) ^ k
        • (((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ) := by
    rw [tanakaTowerTerm, staggeredOrderOp1S_eq_smul_orderDensitySum, smul_pow, Matrix.smul_mulVec]
  simp only [expectationRatioRe]
  rw [hfac]
  exact rayleigh_smul_invariant (heisenbergHamiltonianS (torusNNCoupling d L) N) _ hc _

/-! ### Charge-selection rules on a singlet (eqs. (4.1.7)/(4.2.69)) -/

/-- **Leibniz rule for `Ŝ_tot^{(3)}`-charge**: if `A` commutes with `X` and `Y` up to the scalar
charges `a` and `b` (`[A, X] = a X`, `[A, Y] = b Y`), then it commutes with the product `X Y` up to
the summed charge, `[A, X Y] = (a + b) (X Y)`.  This is the derivation identity for the commutator
`[A, ·]`. -/
theorem commutator_smul_of_smul {n : Type*} [Fintype n]
    {A X Y : Matrix n n ℂ} {a b : ℂ} (hX : A * X - X * A = a • X) (hY : A * Y - Y * A = b • Y) :
    A * (X * Y) - (X * Y) * A = (a + b) • (X * Y) := by
  have hderiv : A * (X * Y) - (X * Y) * A = (A * X - X * A) * Y + X * (A * Y - Y * A) := by
    noncomm_ring
  rw [hderiv, hX, hY, smul_mul_assoc, mul_smul_comm, ← add_smul]

/-- **Operator word commutator** `[Ŝ_tot^{(3)}, ô^{w}] = m(w) · ô^{w}`: the ordered order-word
product shifts the total magnetization by its net charge `m(w)` (`mCharge`).  Proved by induction
peeling one letter and using the per-letter commutator `[Ŝ_tot^{(3)}, ô^b] = ε_b ô^b`. -/
theorem totalSpinSOp3_commutator_orderWordProd (d L N : ℕ) [NeZero L] (w : List Bool) :
    totalSpinSOp3 (HypercubicTorus d L) N * orderWordProd d L N w
        - orderWordProd d L N w * totalSpinSOp3 (HypercubicTorus d L) N
      = mCharge w • orderWordProd d L N w := by
  induction w with
  | nil =>
    rw [orderWordProd, List.map_nil, List.prod_nil, mCharge_nil, mul_one, one_mul, sub_self,
      zero_smul]
  | cons b t ih =>
    rw [orderWordProd_cons, mCharge_cons]
    exact commutator_smul_of_smul (totalSpinSOp3_commutator_orderDensity d L N b) ih

/-- **Charge-eigenvector vanishing**: if a Hermitian charge operator `S` annihilates `Φ`
(`S Φ = 0`) and commutes with `W` up to a nonzero scalar charge `c` (`[S, W] = c W`), then the
expectation `⟨Φ, W Φ⟩` vanishes.  Indeed `W Φ` is an `S`-eigenvector of eigenvalue `c`, and
Hermiticity moves `S` onto the annihilated bra, forcing `c·⟨Φ, W Φ⟩ = 0`. -/
private theorem dotProduct_eq_zero_of_commutator_smul {n : Type*} [Fintype n]
    (S : Matrix n n ℂ) (hS : S.IsHermitian) (Φ : n → ℂ) (hsing : S.mulVec Φ = 0)
    (W : Matrix n n ℂ) (c : ℂ) (hc : c ≠ 0) (hcomm : S * W - W * S = c • W) :
    (star Φ ⬝ᵥ W.mulVec Φ).re = 0 := by
  have hev : S.mulVec (W.mulVec Φ) = c • W.mulVec Φ := by
    have h := congrArg (fun M : Matrix n n ℂ => M.mulVec Φ) hcomm
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsing, Matrix.mulVec_zero, sub_zero] at h
    exact h
  have hA : star Φ ⬝ᵥ S.mulVec (W.mulVec Φ) = c * (star Φ ⬝ᵥ W.mulVec Φ) := by
    rw [hev, dotProduct_smul, smul_eq_mul]
  have hB : star Φ ⬝ᵥ S.mulVec (W.mulVec Φ) = 0 := by
    rw [star_dotProduct_mulVec_conjTranspose, hS.eq, hsing, star_zero, zero_dotProduct]
  have hzero : star Φ ⬝ᵥ W.mulVec Φ = 0 :=
    (mul_eq_zero.mp (hA.symm.trans hB)).resolve_left hc
  rw [hzero, Complex.zero_re]

/-- **Singlet charge-selection rule** (eqs. (4.1.7)/(4.2.69)): on a `Ŝ_tot^{(3)}`-singlet `Φ` the
expectation of a charged order word vanishes, `⟨Φ, ô^{w} Φ⟩ = 0` whenever `m(w) ≠ 0`.  Instance of
`dotProduct_eq_zero_of_commutator_smul` at the word commutator
`[Ŝ_tot^{(3)}, ô^{w}] = m(w) ô^{w}`. -/
theorem dotProduct_orderWord_singlet_eq_zero_of_charge_ne (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (w : List Bool) (hw : mCharge w ≠ 0) :
    (star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re = 0 :=
  dotProduct_eq_zero_of_commutator_smul _ (totalSpinSOp3_isHermitian (HypercubicTorus d L) N) Φ
    hsing _ _ hw (totalSpinSOp3_commutator_orderWordProd d L N w)

/-- **Cross-charge selection rule** (numerator, eq. (4.2.71)): for a charge-`γ` homogeneous middle
operator `G` (`[Ŝ_tot^{(3)}, G] = γ G`), the sandwiched expectation `⟨Φ, ô^{wₗ} G ô^{wᵣ} Φ⟩`
vanishes on a singlet `Φ` whenever the total charge `m(wₗ) + γ + m(wᵣ) ≠ 0`.  The sandwich is a
`Ŝ_tot^{(3)}`-eigenvector of eigenvalue `m(wₗ) + γ + m(wᵣ)` (word commutator on both sides, `hG` in
the middle), so `dotProduct_eq_zero_of_commutator_smul` applies. -/
theorem dotProduct_word_sandwich_eq_zero_of_charge_ne (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (wl wr : List Bool) (G : ManyBodyOpS (HypercubicTorus d L) N) (γ : ℂ)
    (hG : totalSpinSOp3 (HypercubicTorus d L) N * G - G * totalSpinSOp3 (HypercubicTorus d L) N
        = γ • G)
    (hcharge : mCharge wl + γ + mCharge wr ≠ 0) :
    (star Φ ⬝ᵥ (orderWordProd d L N wl * G * orderWordProd d L N wr).mulVec Φ).re = 0 := by
  have hcomm : totalSpinSOp3 (HypercubicTorus d L) N
        * (orderWordProd d L N wl * G * orderWordProd d L N wr)
        - (orderWordProd d L N wl * G * orderWordProd d L N wr)
          * totalSpinSOp3 (HypercubicTorus d L) N
      = (mCharge wl + γ + mCharge wr) • (orderWordProd d L N wl * G * orderWordProd d L N wr) :=
    commutator_smul_of_smul
      (commutator_smul_of_smul (totalSpinSOp3_commutator_orderWordProd d L N wl) hG)
      (totalSpinSOp3_commutator_orderWordProd d L N wr)
  exact dotProduct_eq_zero_of_commutator_smul _
    (totalSpinSOp3_isHermitian (HypercubicTorus d L) N) Φ hsing _ _ hcharge hcomm

end LatticeSystem.Quantum
