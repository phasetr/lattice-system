import LatticeSystem.Quantum.SpinS.EvenLatticeBoxCard
import LatticeSystem.Quantum.SpinS.BoxLocalTranslationInvariant

/-!
# Tasaki §4.3.1: consequences for a physical ground state (Definition 4.19)

A **physical ground state** is a translation-invariant infinite-volume ground
state that is ergodic (Definition 4.19, `IsPhysicalGroundState`).  This module
collects, all **axiom-free**, the state-level consequences for such a state that
follow from the constructive local-algebra layer (#4645–#4652): the structural
accessors, the bond energy condition, the vanishing of the bulk-density
fluctuation (ergodicity), the box / shifted-box energy-density values, and the
even-sublattice half-filling of the bulk density.

This is a capstone of the §4.3.1 constructive infinite-volume layer; no new axiom
is introduced and no existing axiom is touched.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, Definitions 4.17–4.19, eqs. (4.3.4)–(4.3.6),
  pp. 112–115.
-/

namespace LatticeSystem.Quantum

open scoped Topology

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

namespace InfiniteSpinSystem.IsPhysicalGroundState

variable {S : InfiniteSpinSystem d A} {εGS : ℝ} {ω : WeakDual ℂ A}

/-- A translation-invariant infinite-volume ground state that is ergodic is a
physical ground state. -/
theorem of_isInfiniteVolumeGroundState_isErgodic
    (hgs : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω)
    (herg : InfiniteSpinSystem.IsErgodic S ω) :
    InfiniteSpinSystem.IsPhysicalGroundState S εGS ω :=
  ⟨hgs, herg⟩

/-- A physical ground state is an infinite-volume ground state. -/
theorem isInfiniteVolumeGroundState
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) :
    InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω :=
  hω.1

/-- A physical ground state is ergodic. -/
theorem isErgodic (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) :
    InfiniteSpinSystem.IsErgodic S ω :=
  hω.2

/-- A physical ground state is a state. -/
theorem isState (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) :
    LatticeSystem.Math.IsState ω :=
  hω.1.1

/-- A physical ground state is translation invariant. -/
theorem translationInvariant
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) :
    InfiniteSpinSystem.TranslationInvariant S ω :=
  hω.1.2.1

/-- The bond energy condition of a physical ground state:
`ω(Ŝ_x · Ŝ_y) = ε_GS` for every nearest-neighbor bond. -/
theorem spinDot_apply (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω)
    {x y : Fin d → ℤ} (hxy : InfiniteSpinSystem.bond x y) :
    ω (InfiniteSpinSystem.spinDot S x y) = (εGS : ℂ) :=
  hω.1.2.2 x y hxy

/-- The bulk-density fluctuation of a self-adjoint local observable vanishes in a
physical ground state (ergodicity). -/
theorem tendsto_bulkDensityFluctuation
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω)
    {a : A} (ha : a ∈ S.localAlg) (hsa : IsSelfAdjoint a) :
    Filter.Tendsto (fun n : ℕ =>
      InfiniteSpinSystem.bulkDensityFluctuation S ω a (n + 1))
      Filter.atTop (nhds 0) :=
  hω.isErgodic.tendsto_bulkDensityFluctuation ha hsa

/-- A physical ground state is exactly an infinite-volume ground state whose
bulk-density fluctuations all vanish. -/
theorem iff_isInfiniteVolumeGroundState_and_tendsto_bulkDensityFluctuation :
    InfiniteSpinSystem.IsPhysicalGroundState S εGS ω ↔
      InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω ∧
        ∀ a : A, a ∈ S.localAlg → IsSelfAdjoint a →
          Filter.Tendsto (fun n : ℕ =>
            InfiniteSpinSystem.bulkDensityFluctuation S ω a (n + 1))
            Filter.atTop (nhds 0) := by
  constructor
  · intro hω
    exact ⟨hω.isInfiniteVolumeGroundState,
      fun a ha hsa => hω.tendsto_bulkDensityFluctuation ha hsa⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1,
      InfiniteSpinSystem.isErgodic_iff_tendsto_bulkDensityFluctuation.mpr
        ⟨h1.1, h1.2.1, h2⟩⟩

/-- The box partial Hamiltonian expectation in a physical ground state:
`ω(Ĥ_{Λ_n}) = |B_n| · ε_GS`. -/
theorem boxLocalHamiltonian_apply
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (n : ℕ) :
    ω (boxLocalHamiltonian S n) = (boxBondCount d n : ℂ) * (εGS : ℂ) :=
  hω.isInfiniteVolumeGroundState.boxLocalHamiltonian_apply n

/-- The box-local energy density of a physical ground state equals `ε_GS`
(nonempty boxes). -/
theorem boxLocalHamiltonianEnergyDensity_eq
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω)
    {n : ℕ} (hB : 0 < boxBondCount d n) :
    boxLocalHamiltonianEnergyDensity S ω n = εGS :=
  hω.isInfiniteVolumeGroundState.boxLocalHamiltonianEnergyDensity_eq hB

/-- The box-local energy density of a physical ground state converges to `ε_GS`. -/
theorem hasBoxLocalHamiltonianEnergyDensity
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (hd : 0 < d) :
    HasBoxLocalHamiltonianEnergyDensity S ω εGS :=
  hω.isInfiniteVolumeGroundState.hasBoxLocalHamiltonianEnergyDensity hd

/-- The shifted box partial Hamiltonian expectation in a physical ground state
(any shift): `ω(Ĥ_{Λ_n + x}) = |B_n| · ε_GS`. -/
theorem translatedBoxLocalHamiltonian_apply
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (x : Fin d → ℤ) (n : ℕ) :
    ω (translatedBoxLocalHamiltonian S x n) = (boxBondCount d n : ℂ) * (εGS : ℂ) :=
  hω.isInfiniteVolumeGroundState.translatedBoxLocalHamiltonian_apply x n

/-- The shifted-box energy density of a physical ground state converges to `ε_GS`
(any shift). -/
theorem hasTranslatedBoxLocalHamiltonianEnergyDensity
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (hd : 0 < d) (x : Fin d → ℤ) :
    HasTranslatedBoxLocalHamiltonianEnergyDensity S ω x εGS :=
  hω.isInfiniteVolumeGroundState.hasTranslatedBoxLocalHamiltonianEnergyDensity hd x

/-- Even-sublattice half-filling in a physical ground state: `ω(Â_n / Lᵈ) = ½ ω(Â)`
(`d ≥ 1`, `n ≥ 1`). -/
theorem bulkDensity_apply_eq_half_mul
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (a : A) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    ω (InfiniteSpinSystem.bulkDensity S a n) = (1 / 2 : ℂ) * ω a :=
  hω.translationInvariant.bulkDensity_apply_eq_half_mul a hd hn

/-- Real first-moment half-filling in a physical ground state:
`Re ω(Â_n)/Lᵈ = ½ Re ω(Â)` (`d ≥ 1`, `n ≥ 1`). -/
theorem bulkDensityMean_eq_half_mul
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (a : A) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    InfiniteSpinSystem.bulkDensityMean S ω a n = (ω a).re / 2 :=
  hω.translationInvariant.bulkDensityMean_eq_half_mul a hd hn

end InfiniteSpinSystem.IsPhysicalGroundState

end LatticeSystem.Quantum
