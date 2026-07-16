import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSectorWords

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): foundational algebra (PR-1)

This file collects the Hamiltonian-independent algebraic groundwork for the discharge of the
Bose–Einstein-condensation tower theorem (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)).  It is
the BEC counterpart of the Anderson-tower Theorem 4.6 foundations, adapted to the chemical-potential
XY Hamiltonian `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}` (eq. (5.3.2), `xyChemicalPotentialHamiltonianS`).

The pieces proved here are:

* `xyChemicalPotentialHamiltonianS_isHermitian` — `Ĥ_μ` is Hermitian (real XY coupling and real
  chemical potential `μ` times the Hermitian `Ŝ_tot^{(3)}`), the self-adjointness prerequisite of
  the variational double-commutator engine.
* `totalSpinSOp3_commutator_towerPow` — the sector eigenvalue of the tower operator,
  `[Ŝ_tot^{(3)}, (Ô_L^{sgn M})^{|M|}] = M (Ô_L^{sgn M})^{|M|}` (§4-a of the design note): obtained
  by iterating the per-operator Cartan relations `[Ŝ_tot^{(3)}, Ô_L^±] = ±Ô_L^±`
  (`totalSpinSOp3_commutator_staggeredRaisingOpS`/`…LoweringOpS`) through the generic eigenoperator
  power law `commutator_pow_smul_eigen`.  This is the `−μ Ŝ_tot^{(3)}` chemical-potential
  contribution to the double commutator of the tower trial state.
* `Ldhalf_bridge` — the real-analysis identity `L^{d/2} = √(L^d)` bridging the `rpow` window
  `|M| ≤ C₁ L^{d/2}` (eq. (5.3.4)) to the `√(L^d)` normalization used by the tower engine.

These are consumed by the later PRs of the Theorem 5.2 arc (the double-commutator numerator bound
and the cubic energy assembly); they add no textbook content of their own.

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

end LatticeSystem.Quantum
