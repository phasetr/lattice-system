import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSectorWords

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): foundational algebra (PR-1)

This file collects the Hamiltonian-independent algebraic groundwork for the discharge of the
Bose–Einstein-condensation tower theorem (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)).
It is the BEC counterpart of the Anderson-tower Theorem 4.6 foundations, adapted to the
chemical-potential XY Hamiltonian `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}` (eq. (5.3.2),
`xyChemicalPotentialHamiltonianS`).

The pieces proved here are:

* `xyChemicalPotentialHamiltonianS_isHermitian` — `Ĥ_μ` is Hermitian (real XY coupling and real
  chemical potential `μ` times the Hermitian `Ŝ_tot^{(3)}`), the self-adjointness prerequisite of
  the variational double-commutator engine.
* `totalSpinSOp3_commutator_towerPow` — the sector eigenvalue of the tower operator,
  `[Ŝ_tot^{(3)}, (Ô_L^{sgn M})^{|M|}] = M (Ô_L^{sgn M})^{|M|}` (§4-a of the design note):
  obtained by iterating the per-operator Cartan relations `[Ŝ_tot^{(3)}, Ô_L^±] = ±Ô_L^±`
  (`totalSpinSOp3_commutator_staggeredRaisingOpS`/`…LoweringOpS`) through the generic
  eigenoperator power law `commutator_pow_smul_eigen`.  This is the `−μ Ŝ_tot^{(3)}`
  chemical-potential
  contribution to the double commutator of the tower trial state.

The generic `rpow`–`sqrt` window bridge `L^{d/2} = √(L^d)` lives in
`LatticeSystem/Math/Analysis/RealRpowNatSqrt.lean` (`LatticeSystem.Math.Ldhalf_bridge`): a
source-independent real-analysis fact shared with the Anderson tower, not declared here.

These lemmas are consumed by the later PRs of the Theorem 5.2 arc (the double-commutator numerator
bound and the cubic energy assembly); they add no textbook content of their own.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eqs. (5.3.1)–(5.3.4), pp. 140–141 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Hermiticity of the chemical-potential XY Hamiltonian -/

/-- **The chemical-potential XY Hamiltonian is Hermitian.**  `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}`
(eq. (5.3.2)) is self-adjoint: the XY term `xyHamiltonianS` is the anisotropic Heisenberg
Hamiltonian at real coupling `torusNNCoupling` and real anisotropy/crystal-field `0`, and both
scalar factors (`2` and the real chemical potential `μ`) are self-adjoint, so the difference of
Hermitian operators is Hermitian.  This is the self-adjointness prerequisite for the variational
double-commutator gap bound of Theorem 5.2. -/
theorem xyChemicalPotentialHamiltonianS_isHermitian (d L : ℕ) [NeZero L] (μ : ℝ) :
    (xyChemicalPotentialHamiltonianS d L μ).IsHermitian := by
  unfold xyChemicalPotentialHamiltonianS xyHamiltonianS
  refine Matrix.IsHermitian.sub (Matrix.IsHermitian.smul ?_ ?_)
    (Matrix.IsHermitian.smul (totalSpinSOp3_isHermitian _ _) ?_)
  · refine anisotropicHeisenbergS_isHermitian_of_real (fun x y => ?_) ?_ ?_ 1
    · unfold torusNNCoupling; split <;> simp
    · simp
    · simp
  · simp [IsSelfAdjoint, star_ofNat]
  · simp [IsSelfAdjoint, Complex.conj_ofReal]

/-! ## Sector eigenvalue of the tower operator -/

/-- **Eigenoperator power commutator.**  If `A` is an eigenoperator of the adjoint action of `H`
with eigenvalue `c` (`[H, A] = c • A`), then `[H, Aⁿ] = (n c) • Aⁿ`: the adjoint eigenvalue
is additive under products.  Proved by induction on `n` via the Leibniz rule for the
commutator. -/
private theorem commutator_pow_smul_eigen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : Matrix ι ι ℂ) {c : ℂ} (h : H * A - A * H = c • A) (n : ℕ) :
    H * A ^ n - A ^ n * H = ((n : ℂ) * c) • A ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hleib : H * A ^ (k + 1) - A ^ (k + 1) * H
        = (H * A ^ k - A ^ k * H) * A + A ^ k * (H * A - A * H) := by
      rw [pow_succ]; noncomm_ring
    rw [hleib, ih, h]
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [← add_smul, ← pow_succ]
    congr 1
    push_cast; ring

/-- **Tower-operator sector eigenvalue**
`[Ŝ_tot^{(3)}, (Ô_L^{sgn M})^{|M|}] = M (Ô_L^{sgn M})^{|M|}`
(§4-a of the design note): applying the staggered raising order operator `Ô_L^+` raises the total
magnetization by one and the lowering operator `Ô_L^−` lowers it by one, so the `|M|`-fold tower
operator carries total-magnetization eigenvalue exactly `M` under the adjoint action of
`Ŝ_tot^{(3)}`.  The operator is exactly the one used by `towerState`, so this feeds the
`−μ Ŝ_tot^{(3)}` term of the tower double commutator. -/
theorem totalSpinSOp3_commutator_towerPow (A : Λ → Bool) (M : ℤ) :
    totalSpinSOp3 Λ N
        * (if 0 ≤ M then staggeredRaisingOpS A N else staggeredLoweringOpS A N) ^ M.natAbs
      - (if 0 ≤ M then staggeredRaisingOpS A N else staggeredLoweringOpS A N) ^ M.natAbs
        * totalSpinSOp3 Λ N
      = (M : ℂ)
        • (if 0 ≤ M then staggeredRaisingOpS A N else staggeredLoweringOpS A N) ^ M.natAbs := by
  by_cases hM : 0 ≤ M
  · rw [if_pos hM]
    rw [commutator_pow_smul_eigen (totalSpinSOp3 Λ N) (staggeredRaisingOpS A N)
      (by rw [one_smul]; exact totalSpinSOp3_commutator_staggeredRaisingOpS A) M.natAbs]
    congr 1
    rw [mul_one]
    have h1 : (M.natAbs : ℤ) = M := Int.natAbs_of_nonneg hM
    calc (M.natAbs : ℂ) = ((M.natAbs : ℤ) : ℂ) := by rw [Int.cast_natCast]
      _ = (M : ℂ) := by rw [h1]
  · rw [if_neg hM]
    rw [commutator_pow_smul_eigen (totalSpinSOp3 Λ N) (staggeredLoweringOpS A N)
      (by rw [neg_one_smul]; exact totalSpinSOp3_commutator_staggeredLoweringOpS A) M.natAbs]
    congr 1
    have h1 : (M.natAbs : ℤ) = -M := by omega
    calc (M.natAbs : ℂ) * (-1) = ((M.natAbs : ℤ) : ℂ) * (-1) := by rw [Int.cast_natCast]
      _ = ((-M : ℤ) : ℂ) * (-1) := by rw [h1]
      _ = (M : ℂ) := by push_cast; ring

end LatticeSystem.Quantum
