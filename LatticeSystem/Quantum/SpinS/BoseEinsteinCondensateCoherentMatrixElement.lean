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

end LatticeSystem.Quantum
