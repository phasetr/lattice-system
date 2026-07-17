import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSectorWords
import LatticeSystem.Math.ComplexVectorKernel

/-!
# Tasaki §5.3 Theorem 5.3: total-`Ŝ³` sector structure of the coherent tower states

The `U(1)` coherent state `Ξ_θ` (eq. (5.3.5)) superposes the tower states `Γ_M` over the window.
Their expectation double sum `⟨Ξ_θ, O Ξ_θ⟩` (`becCoherentState_dotProduct_mulVec`) collapses because
the `Γ_M` live in distinct total-`Ŝ³` sectors and are therefore mutually orthogonal.  This file
supplies that sector structure at half filling (the singlet premise `Ŝ³_tot Φ = 0`):

* `towerState_totalSpin3_eigenvector`: `Ŝ³_tot (Ô^{sgn M})^{|M|} Φ = M (Ô^{sgn M})^{|M|} Φ`, i.e.
  the (unnormalized) tower state `towerState A N M Φ` is an eigenvector of `Ŝ³_tot` with eigenvalue
  `M` (raising increments, lowering decrements the total magnetization);
* `towerState_inner_eq_zero_of_ne`: distinct-`M` tower states are orthogonal (Hermitian `Ŝ³_tot`,
  distinct real eigenvalues);
* `towerState_unitNormalize_inner_eq_zero_of_ne`: the same orthogonality for the normalized
  `Γ_M = unitNormalize (towerState …)`, the form consumed by the `O = 1` diagonalization of the
  coherent-state double sum in the downstream moment PRs.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eqs. (5.3.3)–(5.3.5), pp. 141–142 (Koma–Tasaki [21]); the sector
commutators `[Ŝ³_tot, Ô^±] = ±Ô^±` reuse the §4.2 infrastructure.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Single-step and iterated magnetization shift -/

/-- **Single raising step**: if `Ŝ³_tot v = λ v` then `Ŝ³_tot (Ô⁺ v) = (λ + 1) (Ô⁺ v)` (the
staggered raising operator increments the total magnetization by one). -/
private theorem totalSpinSOp3_mulVec_staggeredRaising_eigenvec (A : Λ → Bool)
    {v : (Λ → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 Λ N).mulVec v = lam • v) :
    (totalSpinSOp3 Λ N).mulVec ((staggeredRaisingOpS A N).mulVec v)
      = (lam + 1) • (staggeredRaisingOpS A N).mulVec v := by
  have hcomm := totalSpinSOp3_commutator_staggeredRaisingOpS (N := N) A
  have key : totalSpinSOp3 Λ N * staggeredRaisingOpS A N =
      staggeredRaisingOpS A N * totalSpinSOp3 Λ N + staggeredRaisingOpS A N := by
    have hadd : totalSpinSOp3 Λ N * staggeredRaisingOpS A N =
        (totalSpinSOp3 Λ N * staggeredRaisingOpS A N -
          staggeredRaisingOpS A N * totalSpinSOp3 Λ N) +
          staggeredRaisingOpS A N * totalSpinSOp3 Λ N := by abel
    rw [hadd, hcomm]; abel
  rw [Matrix.mulVec_mulVec, key, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

/-- **Single lowering step**: if `Ŝ³_tot v = λ v` then `Ŝ³_tot (Ô⁻ v) = (λ − 1) (Ô⁻ v)` (the
staggered lowering operator decrements the total magnetization by one). -/
private theorem totalSpinSOp3_mulVec_staggeredLowering_eigenvec (A : Λ → Bool)
    {v : (Λ → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 Λ N).mulVec v = lam • v) :
    (totalSpinSOp3 Λ N).mulVec ((staggeredLoweringOpS A N).mulVec v)
      = (lam - 1) • (staggeredLoweringOpS A N).mulVec v := by
  have hcomm := totalSpinSOp3_commutator_staggeredLoweringOpS (N := N) A
  have key : totalSpinSOp3 Λ N * staggeredLoweringOpS A N =
      staggeredLoweringOpS A N * totalSpinSOp3 Λ N - staggeredLoweringOpS A N := by
    have hadd : totalSpinSOp3 Λ N * staggeredLoweringOpS A N =
        (totalSpinSOp3 Λ N * staggeredLoweringOpS A N -
          staggeredLoweringOpS A N * totalSpinSOp3 Λ N) +
          staggeredLoweringOpS A N * totalSpinSOp3 Λ N := by abel
    rw [hadd, hcomm]; abel
  rw [Matrix.mulVec_mulVec, key, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- **Iterated raising**: for a singlet `Φ` (`Ŝ³_tot Φ = 0`), `(Ô⁺)^m Φ` is an eigenvector of
`Ŝ³_tot` with eigenvalue `m` (each raising increments the magnetization by one). -/
private theorem totalSpinSOp3_mulVec_staggeredRaising_pow_eigenvec (A : Λ → Bool) (m : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (totalSpinSOp3 Λ N).mulVec (((staggeredRaisingOpS A N) ^ m).mulVec Φ)
      = (m : ℂ) • ((staggeredRaisingOpS A N) ^ m).mulVec Φ := by
  induction m with
  | zero => rw [pow_zero, Matrix.one_mulVec, hsing, Nat.cast_zero, zero_smul]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_staggeredRaising_eigenvec A ih,
      show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) from by push_cast; ring]

/-- **Iterated lowering**: for a singlet `Φ` (`Ŝ³_tot Φ = 0`), `(Ô⁻)^m Φ` is an eigenvector of
`Ŝ³_tot` with eigenvalue `−m` (each lowering decrements the magnetization by one). -/
private theorem totalSpinSOp3_mulVec_staggeredLowering_pow_eigenvec (A : Λ → Bool) (m : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (totalSpinSOp3 Λ N).mulVec (((staggeredLoweringOpS A N) ^ m).mulVec Φ)
      = (-(m : ℂ)) • ((staggeredLoweringOpS A N) ^ m).mulVec Φ := by
  induction m with
  | zero => rw [pow_zero, Matrix.one_mulVec, hsing, Nat.cast_zero, neg_zero, zero_smul]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_staggeredLowering_eigenvec A ih,
      show (-(k : ℂ) - 1) = (-((k + 1 : ℕ) : ℂ)) from by push_cast; ring]

/-! ### Tower states are `Ŝ³_tot` eigenvectors and mutually orthogonal -/

/-- **Sector eigenvalue of the tower state** (Tasaki §5.3, eq. (5.3.3)): for a singlet `Φ`
(`Ŝ³_tot Φ = 0`), the tower state `Γ_M = (Ô^{sgn M})^{|M|} Φ` is an eigenvector of `Ŝ³_tot` with
eigenvalue `M`.  Raising (`M ≥ 0`) contributes `+|M| = M`, lowering (`M < 0`) contributes
`−|M| = M`. -/
theorem towerState_totalSpin3_eigenvector (A : Λ → Bool) (M : ℤ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (totalSpinSOp3 Λ N).mulVec (towerState A N M Φ) = (M : ℂ) • towerState A N M Φ := by
  unfold towerState
  by_cases hM : 0 ≤ M
  · rw [if_pos hM, totalSpinSOp3_mulVec_staggeredRaising_pow_eigenvec A M.natAbs hsing,
      show ((M.natAbs : ℕ) : ℂ) = (M : ℂ) from by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hM]]
  · rw [if_neg hM, totalSpinSOp3_mulVec_staggeredLowering_pow_eigenvec A M.natAbs hsing,
      show (-((M.natAbs : ℕ) : ℂ)) = (M : ℂ) from by
        have hMlt : M < 0 := not_le.mp hM
        have h1 : ((M.natAbs : ℤ)) = -M := by
          rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by linarith)
        have h2 : ((M.natAbs : ℂ)) = -(M : ℂ) := by
          rw [← Int.cast_natCast, h1]; push_cast; ring
        rw [h2]; ring]

/-- **Sector orthogonality of the tower states** (Tasaki §5.3, eqs. (5.3.3)–(5.3.5)): for a singlet
`Φ` (`Ŝ³_tot Φ = 0`) and `M ≠ M'`, the tower states `Γ_M`, `Γ_{M'}` are orthogonal.  They are
eigenvectors of the Hermitian `Ŝ³_tot` with distinct real eigenvalues `M`, `M'`. -/
theorem towerState_inner_eq_zero_of_ne (A : Λ → Bool) {M M' : ℤ} (hMM' : M ≠ M')
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (towerState A N M' Φ) ⬝ᵥ towerState A N M Φ = 0 := by
  have hAu := towerState_totalSpin3_eigenvector A M hsing
  have hAv := towerState_totalSpin3_eigenvector A M' hsing
  set u := towerState A N M Φ
  set v := towerState A N M' Φ
  have hadj := star_mulVec_dotProduct (totalSpinSOp3 Λ N) v u
  rw [hAv, (totalSpinSOp3_isHermitian Λ N).eq, hAu, star_smul, star_intCast, smul_dotProduct,
    smul_eq_mul, dotProduct_smul, smul_eq_mul] at hadj
  have hne : (M' : ℂ) - (M : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (fun h => hMM' (Int.cast_injective h).symm)
  have hzero : ((M' : ℂ) - (M : ℂ)) * (star v ⬝ᵥ u) = 0 := by
    rw [sub_mul, hadj, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- **Normalized sector orthogonality**: the normalized tower states
`Γ_M = unitNormalize (towerState … M Φ)` are mutually orthogonal for distinct `M` (a scalar
multiple of `towerState_inner_eq_zero_of_ne`).  This is the `O = 1` diagonalization form
consumed by the coherent-state double-sum collapse of the downstream moment PRs. -/
theorem towerState_unitNormalize_inner_eq_zero_of_ne (A : Λ → Bool) {M M' : ℤ} (hMM' : M ≠ M')
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (unitNormalize (towerState A N M' Φ)) ⬝ᵥ unitNormalize (towerState A N M Φ) = 0 := by
  unfold unitNormalize
  rw [star_smul, smul_dotProduct, dotProduct_smul, towerState_inner_eq_zero_of_ne A hMM' hsing,
    smul_zero, smul_zero]

end LatticeSystem.Quantum
