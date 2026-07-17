import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSectorWords

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): foundational algebra (PR-1)

This file collects the Hamiltonian-independent algebraic groundwork for the discharge of the
Bose–Einstein-condensation tower theorem (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)).
It is the BEC counterpart of the Anderson-tower Theorem 4.6 foundations, adapted to the
chemical-potential XY Hamiltonian `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}` (eq. (5.3.2),
`xyChemicalPotentialHamiltonianS`).

The piece proved here is:

* `xyChemicalPotentialHamiltonianS_isHermitian` — `Ĥ_μ` is Hermitian (real XY coupling and real
  chemical potential `μ` times the Hermitian `Ŝ_tot^{(3)}`), the self-adjointness prerequisite of
  the variational double-commutator engine.

The generic `rpow`–`sqrt` window bridge `L^{d/2} = √(L^d)` lives in
`LatticeSystem/Math/Analysis/RealRpowNatSqrt.lean` (`LatticeSystem.Math.Ldhalf_bridge`): a
source-independent real-analysis fact shared with the Anderson tower, not declared here.

This lemma is consumed by the half-filling energy assembly of the Theorem 5.2 arc
(`BoseEinsteinCondensateTower.lean`, the variational-gap self-adjointness input); it adds no
textbook content of its own.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eqs. (5.3.1)–(5.3.4), pp. 140–141 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix

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
