import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateSector
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaCapstone

/-!
# Tasaki §5.3 Theorem 5.3: off-diagonal matrix elements of the coherent tower states

Collapsing the coherent-state Rayleigh double sum `⟨Ξ_θ, Ô⁺ Ξ_θ⟩` (from
`becCoherentState_dotProduct_mulVec`)
of the `U(1)` symmetry-breaking states leaves only the *off-diagonal* matrix elements
`⟨Γ_{M'}, Ô⁺ Γ_M⟩` between normalized tower states.  This file evaluates those elements for the
raising operator `Ô⁺ = staggeredRaisingOpS`:

* `becOffDiagonal_ne_adjacent_eq_zero`: at half filling (`Ŝ³_tot Φ = 0`), `⟨Γ_{M'}, Ô⁺ Γ_M⟩ = 0`
  whenever `M' ≠ M + 1` — `Ô⁺ Γ_M` sits in the total-`Ŝ³` sector `M + 1` (raising increments the
  magnetization), orthogonal to `Γ_{M'}` in every other sector;
* `becOffDiagonal_eq_norm_ratio`: on the raising side (`M ≥ 0`, both tower states nonzero) the
  single surviving element is the **norm ratio** `⟨Γ_{M+1}, Ô⁺ Γ_M⟩ = √(D_{M+1}/D_M)` with
  `D_M = ‖(Ô⁺)^M Φ‖² = vecNormSqRe (towerState … M Φ)`, since there `Ô⁺ towerState M Φ = towerState
  (M+1) Φ` exactly, so `Ô⁺ Γ_M` is parallel to `Γ_{M+1}`.

These are the building blocks the downstream coherent-moment PR feeds into the Cesàro window average
`⟨Ξ_θ, Ô⁺ Ξ_θ⟩/L^d → m∗ e^{iθ}` (eq. (5.3.6)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eqs. (5.3.3)–(5.3.6), pp. 141–142 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix

open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Raising recursion of the tower states** (`M ≥ 0`): `Ô⁺ towerState M Φ = towerState (M+1) Φ`.
Both states are built with the raising operator, so applying one more `Ô⁺` advances the tower by one
step (`(Ô⁺)^{|M|+1} = (Ô⁺)^{|M+1|}`). -/
private theorem staggeredRaisingOpS_mulVec_towerState_of_nonneg (A : Λ → Bool) {M : ℤ}
    (hM : 0 ≤ M) {Φ : (Λ → Fin (N + 1)) → ℂ} :
    (staggeredRaisingOpS A N).mulVec (towerState A N M Φ) = towerState A N (M + 1) Φ := by
  have hnat : (M + 1).natAbs = M.natAbs + 1 := by
    have h1 : ((M + 1).natAbs : ℤ) = M + 1 := Int.natAbs_of_nonneg (by linarith)
    have h2 : (M.natAbs : ℤ) = M := Int.natAbs_of_nonneg hM
    omega
  unfold towerState
  rw [if_pos hM, if_pos (show (0 : ℤ) ≤ M + 1 by linarith), hnat, pow_succ',
    Matrix.mulVec_mulVec]

/-- **Lowering-branch form of the tower state** (`M ≤ 0`): `towerState M Φ = (Ô⁻)^{|M|} Φ`.  At
`M = 0` both branches collapse to `(·)^0 = 1`, so the lowering power agrees with the definition. -/
private theorem towerState_eq_loweringPow_of_nonpos (A : Λ → Bool) {M : ℤ} (hM : M ≤ 0)
    {Φ : (Λ → Fin (N + 1)) → ℂ} :
    towerState A N M Φ = ((staggeredLoweringOpS A N) ^ M.natAbs).mulVec Φ := by
  unfold towerState
  rcases eq_or_lt_of_le hM with h | h
  · subst h; simp
  · rw [if_neg (not_le.mpr h)]

/-- **Lowering recursion of the tower states** (`M ≤ 0`): `Ô⁻ towerState M Φ = towerState (M−1) Φ`
(mirror of `staggeredRaisingOpS_mulVec_towerState_of_nonneg`; `(Ô⁻)^{|M|+1} = (Ô⁻)^{|M−1|}`). -/
private theorem staggeredLoweringOpS_mulVec_towerState_of_nonpos (A : Λ → Bool) {M : ℤ}
    (hM : M ≤ 0) {Φ : (Λ → Fin (N + 1)) → ℂ} :
    (staggeredLoweringOpS A N).mulVec (towerState A N M Φ) = towerState A N (M - 1) Φ := by
  have hnat : (M - 1).natAbs = M.natAbs + 1 := by
    have h1 : (M.natAbs : ℤ) = -M := by
      rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by linarith)
    have h2 : ((M - 1).natAbs : ℤ) = -(M - 1) := by
      rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by linarith)
    omega
  rw [towerState_eq_loweringPow_of_nonpos A hM,
    towerState_eq_loweringPow_of_nonpos A (show M - 1 ≤ 0 by linarith), hnat, pow_succ',
    Matrix.mulVec_mulVec]

/-- **Sector orthogonality of the off-diagonal element** (Tasaki §5.3, eq. (5.3.3)): at half filling
(`Ŝ³_tot Φ = 0`), the raising off-diagonal element `⟨Γ_{M'}, Ô⁺ Γ_M⟩` vanishes unless `M' = M + 1`.
The vector `Ô⁺ Γ_M` is a `Ŝ³_tot`-eigenvector with eigenvalue `M + 1` (raising increments the
magnetization by one), while `Γ_{M'}` has eigenvalue `M'`; distinct real eigenvalues of the
Hermitian `Ŝ³_tot` are orthogonal. -/
theorem becOffDiagonal_ne_adjacent_eq_zero (A : Λ → Bool) {M M' : ℤ} (hne : M' ≠ M + 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (unitNormalize (towerState A N M' Φ)) ⬝ᵥ
      (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ)) = 0 := by
  have key : star (towerState A N M' Φ) ⬝ᵥ
      (staggeredRaisingOpS A N).mulVec (towerState A N M Φ) = 0 := by
    have ht : (totalSpinSOp3 Λ N).mulVec (towerState A N M Φ)
        = (M : ℂ) • towerState A N M Φ := towerState_totalSpin3_eigenvector A M hsing
    have ht' : (totalSpinSOp3 Λ N).mulVec (towerState A N M' Φ)
        = (M' : ℂ) • towerState A N M' Φ := towerState_totalSpin3_eigenvector A M' hsing
    have hw : (totalSpinSOp3 Λ N).mulVec
          ((staggeredRaisingOpS A N).mulVec (towerState A N M Φ))
        = ((M : ℂ) + 1) • (staggeredRaisingOpS A N).mulVec (towerState A N M Φ) :=
      totalSpinSOp3_mulVec_staggeredRaising_eigenvec A ht
    have hadj := star_mulVec_dotProduct (totalSpinSOp3 Λ N) (towerState A N M' Φ)
      ((staggeredRaisingOpS A N).mulVec (towerState A N M Φ))
    rw [ht', (totalSpinSOp3_isHermitian Λ N).eq, hw, star_smul, star_intCast,
      smul_dotProduct, smul_eq_mul, dotProduct_smul, smul_eq_mul] at hadj
    have hne'' : (M' : ℂ) ≠ (M : ℂ) + 1 := by
      rw [← Int.cast_one, ← Int.cast_add]; exact_mod_cast hne
    have hne' : (M' : ℂ) - ((M : ℂ) + 1) ≠ 0 := sub_ne_zero.mpr hne''
    have hzero : ((M' : ℂ) - ((M : ℂ) + 1)) *
        (star (towerState A N M' Φ) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (towerState A N M Φ)) = 0 := by
      rw [sub_mul, hadj, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left hne'
  unfold unitNormalize
  rw [star_smul_dotProduct_mulVec_smul, key, mul_zero]

/-- **Off-diagonal element as a norm ratio** (Tasaki §5.3, eqs. (5.3.3), (5.3.6)): on the raising
side (`M ≥ 0`, both tower states nonzero), the adjacent off-diagonal element is the real, positive
norm
ratio `⟨Γ_{M+1}, Ô⁺ Γ_M⟩ = √(D_{M+1}/D_M)`, `D_M = ‖(Ô⁺)^M Φ‖² = vecNormSqRe (towerState … M Φ)`.
Here `Ô⁺ towerState M Φ = towerState (M+1) Φ` exactly, so `Ô⁺ Γ_M` is parallel to `Γ_{M+1}` and the
sandwich reduces to the ratio of their norms. -/
theorem becOffDiagonal_eq_norm_ratio (A : Λ → Bool) {M : ℤ} (hM : 0 ≤ M)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht : towerState A N M Φ ≠ 0)
    (ht' : towerState A N (M + 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
      (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = ((Real.sqrt (vecNormSqRe (towerState A N (M + 1) Φ)
          / vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) := by
  have hrec : (staggeredRaisingOpS A N).mulVec (towerState A N M Φ) = towerState A N (M + 1) Φ :=
    staggeredRaisingOpS_mulVec_towerState_of_nonneg A hM
  have hna : 0 < vecNormSqRe (towerState A N M Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht)).1
  have hna' : 0 < vecNormSqRe (towerState A N (M + 1) Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hself : star (towerState A N (M + 1) Φ) ⬝ᵥ towerState A N (M + 1) Φ
      = ((vecNormSqRe (towerState A N (M + 1) Φ) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]
      exact ((Complex.le_def.mp (dotProduct_star_self_nonneg _)).2).symm
  have h1 : ((Real.sqrt (vecNormSqRe (towerState A N (M + 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna').ne'
  have h2 : ((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna).ne'
  unfold unitNormalize
  rw [star_smul_dotProduct_mulVec_smul, hrec, hself, Complex.star_def, map_inv₀,
    Complex.conj_ofReal, Real.sqrt_div hna'.le, Complex.ofReal_div,
    show ((vecNormSqRe (towerState A N (M + 1) Φ) : ℝ) : ℂ)
        = ((Real.sqrt (vecNormSqRe (towerState A N (M + 1) Φ)) : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hna'.le]]
  field_simp

/-- **Off-diagonal element as an inverse norm ratio on the lowering side** (Tasaki §5.3, eqs.
(5.3.3), (5.3.6); math-note §2② 2026-07-17 refinement): for `M ≤ −1` (both tower states nonzero) the
same `Ô⁺`-sandwiched adjacent element is the **inverse** ratio `⟨Γ_{M+1}, Ô⁺ Γ_M⟩ = √(D_M/D_{M+1})`,
`D_M = vecNormSqRe (towerState … M Φ)`.  Here the tower is built with `Ô⁻`, so `Ô⁺ Γ_M` is *not*
parallel to `Γ_{M+1}`; instead `(Ô⁺)ᴴ = Ô⁻` (`staggeredRaisingOpS_conjTranspose`) moves `Ô⁺` onto
the bra and the lowering recursion `Ô⁻ towerState (M+1) Φ = towerState M Φ` collapses it to
`‖Γ_M‖²`,
giving the inverse of the `M ≥ 0` ratio. -/
theorem becOffDiagonal_eq_norm_ratio_neg (A : Λ → Bool) {M : ℤ} (hM : M ≤ -1)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht : towerState A N M Φ ≠ 0)
    (ht' : towerState A N (M + 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
      (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = ((Real.sqrt (vecNormSqRe (towerState A N M Φ)
          / vecNormSqRe (towerState A N (M + 1) Φ)) : ℝ) : ℂ) := by
  have hrec : (staggeredLoweringOpS A N).mulVec (towerState A N (M + 1) Φ)
      = towerState A N M Φ := by
    have h := staggeredLoweringOpS_mulVec_towerState_of_nonpos A
      (show M + 1 ≤ 0 by linarith) (Φ := Φ)
    rwa [add_sub_cancel_right] at h
  have hadj : star (towerState A N (M + 1) Φ) ⬝ᵥ
        (staggeredRaisingOpS A N).mulVec (towerState A N M Φ)
      = star (towerState A N M Φ) ⬝ᵥ towerState A N M Φ := by
    have h := star_mulVec_dotProduct (staggeredLoweringOpS A N) (towerState A N (M + 1) Φ)
      (towerState A N M Φ)
    rw [staggeredLoweringOpS_conjTranspose, hrec] at h
    exact h.symm
  have hna : 0 < vecNormSqRe (towerState A N M Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht)).1
  have hna' : 0 < vecNormSqRe (towerState A N (M + 1) Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hself : star (towerState A N M Φ) ⬝ᵥ towerState A N M Φ
      = ((vecNormSqRe (towerState A N M Φ) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]
      exact ((Complex.le_def.mp (dotProduct_star_self_nonneg _)).2).symm
  have h1 : ((Real.sqrt (vecNormSqRe (towerState A N (M + 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna').ne'
  have h2 : ((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna).ne'
  unfold unitNormalize
  rw [star_smul_dotProduct_mulVec_smul, hadj, hself, Complex.star_def, map_inv₀,
    Complex.conj_ofReal, Real.sqrt_div hna.le, Complex.ofReal_div,
    show ((vecNormSqRe (towerState A N M Φ) : ℝ) : ℂ)
        = ((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hna.le]]
  field_simp

/-- **Sector orthogonality of the lowering off-diagonal element** (Tasaki §5.3, eq. (5.3.3); mirror
of `becOffDiagonal_ne_adjacent_eq_zero`): at half filling (`Ŝ³_tot Φ = 0`), the lowering
off-diagonal element `⟨Γ_{M'}, Ô⁻ Γ_M⟩` vanishes unless `M' = M − 1`.  The vector `Ô⁻ Γ_M` sits in
the
`Ŝ³_tot`-sector `M − 1` (lowering decrements the magnetization).  This is obtained from the raising
statement by adjoint reversal `(Ô⁻)ᴴ = Ô⁺` (`staggeredRaisingOpS_conjTranspose`): moving `Ô⁻` onto
the bra turns the element into the conjugate of `⟨Γ_M, Ô⁺ Γ_{M'}⟩`, which vanishes for `M ≠ M' + 1`,
i.e. `M' ≠ M − 1`. -/
theorem becOffDiagonal_lowering_ne_adjacent_eq_zero (A : Λ → Bool) {M M' : ℤ} (hne : M' ≠ M - 1)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (unitNormalize (towerState A N M' Φ)) ⬝ᵥ
      (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ)) = 0 := by
  have hne' : M ≠ M' + 1 := by omega
  rw [← staggeredRaisingOpS_conjTranspose A, ← star_mulVec_dotProduct, Matrix.star_dotProduct,
    becOffDiagonal_ne_adjacent_eq_zero A hne' hsing, star_zero]

/-- **Lowering off-diagonal element as a norm ratio on the lowering side** (Tasaki §5.3, eqs.
(5.3.3), (5.3.6); mirror of `becOffDiagonal_eq_norm_ratio`): for `M ≤ 0` (both tower states nonzero)
the adjacent lowering element is the real, positive norm ratio
`⟨Γ_{M−1}, Ô⁻ Γ_M⟩ = √(D_{M−1}/D_M)`, `D_M = vecNormSqRe (towerState … M Φ)`.  Here
`Ô⁻ towerState M Φ = towerState (M−1) Φ` exactly (lowering recursion), so `Ô⁻ Γ_M` is parallel to
`Γ_{M−1}` and the sandwich reduces to the ratio of their norms. -/
theorem becOffDiagonal_lowering_eq_norm_ratio (A : Λ → Bool) {M : ℤ} (hM : M ≤ 0)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht : towerState A N M Φ ≠ 0)
    (ht' : towerState A N (M - 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M - 1) Φ)) ⬝ᵥ
      (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = ((Real.sqrt (vecNormSqRe (towerState A N (M - 1) Φ)
          / vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) := by
  have hrec : (staggeredLoweringOpS A N).mulVec (towerState A N M Φ) = towerState A N (M - 1) Φ :=
    staggeredLoweringOpS_mulVec_towerState_of_nonpos A hM
  have hna : 0 < vecNormSqRe (towerState A N M Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht)).1
  have hna' : 0 < vecNormSqRe (towerState A N (M - 1) Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hself : star (towerState A N (M - 1) Φ) ⬝ᵥ towerState A N (M - 1) Φ
      = ((vecNormSqRe (towerState A N (M - 1) Φ) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]
      exact ((Complex.le_def.mp (dotProduct_star_self_nonneg _)).2).symm
  have h1 : ((Real.sqrt (vecNormSqRe (towerState A N (M - 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna').ne'
  have h2 : ((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna).ne'
  unfold unitNormalize
  rw [star_smul_dotProduct_mulVec_smul, hrec, hself, Complex.star_def, map_inv₀,
    Complex.conj_ofReal, Real.sqrt_div hna'.le, Complex.ofReal_div,
    show ((vecNormSqRe (towerState A N (M - 1) Φ) : ℝ) : ℂ)
        = ((Real.sqrt (vecNormSqRe (towerState A N (M - 1) Φ)) : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hna'.le]]
  field_simp

/-- **Lowering off-diagonal element as an inverse norm ratio on the raising side** (Tasaki §5.3,
eqs. (5.3.3), (5.3.6); mirror of `becOffDiagonal_eq_norm_ratio_neg`): for `M ≥ 1` (both tower states
nonzero) the same `Ô⁻`-sandwiched adjacent element is the **inverse** ratio
`⟨Γ_{M−1}, Ô⁻ Γ_M⟩ = √(D_M/D_{M−1})`, `D_M = vecNormSqRe (towerState … M Φ)`.  Here the tower is
built with `Ô⁺`, so `(Ô⁻)ᴴ = Ô⁺` (`staggeredRaisingOpS_conjTranspose`) moves `Ô⁻` onto the bra and
the raising recursion `Ô⁺ towerState (M−1) Φ = towerState M Φ` collapses it to `‖Γ_M‖²`, giving the
inverse of the `M ≤ 0` ratio. -/
theorem becOffDiagonal_lowering_eq_norm_ratio_pos (A : Λ → Bool) {M : ℤ} (hM : 1 ≤ M)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht : towerState A N M Φ ≠ 0)
    (ht' : towerState A N (M - 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M - 1) Φ)) ⬝ᵥ
      (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = ((Real.sqrt (vecNormSqRe (towerState A N M Φ)
          / vecNormSqRe (towerState A N (M - 1) Φ)) : ℝ) : ℂ) := by
  have hrec : (staggeredRaisingOpS A N).mulVec (towerState A N (M - 1) Φ)
      = towerState A N M Φ := by
    have h := staggeredRaisingOpS_mulVec_towerState_of_nonneg A
      (show (0 : ℤ) ≤ M - 1 by linarith) (Φ := Φ)
    rwa [show M - 1 + 1 = M from by ring] at h
  have hadj : star (towerState A N (M - 1) Φ) ⬝ᵥ
        (staggeredLoweringOpS A N).mulVec (towerState A N M Φ)
      = star (towerState A N M Φ) ⬝ᵥ towerState A N M Φ := by
    have h := star_mulVec_dotProduct (staggeredRaisingOpS A N) (towerState A N (M - 1) Φ)
      (towerState A N M Φ)
    rw [staggeredRaisingOpS_conjTranspose, hrec] at h
    exact h.symm
  have hna : 0 < vecNormSqRe (towerState A N M Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht)).1
  have hna' : 0 < vecNormSqRe (towerState A N (M - 1) Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hself : star (towerState A N M Φ) ⬝ᵥ towerState A N M Φ
      = ((vecNormSqRe (towerState A N M Φ) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]
      exact ((Complex.le_def.mp (dotProduct_star_self_nonneg _)).2).symm
  have h1 : ((Real.sqrt (vecNormSqRe (towerState A N (M - 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna').ne'
  have h2 : ((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hna).ne'
  unfold unitNormalize
  rw [star_smul_dotProduct_mulVec_smul, hadj, hself, Complex.star_def, map_inv₀,
    Complex.conj_ofReal, Real.sqrt_div hna.le, Complex.ofReal_div,
    show ((vecNormSqRe (towerState A N M Φ) : ℝ) : ℂ)
        = ((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hna.le]]
  field_simp

end LatticeSystem.Quantum
