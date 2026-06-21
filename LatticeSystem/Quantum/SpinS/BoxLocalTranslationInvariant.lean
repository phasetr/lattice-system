import LatticeSystem.Quantum.SpinS.BoxLocalEnergyDensity

/-!
# Tasaki §4.3.1: translation-invariant expectations of the local finite-box observables

This module records the **state-level consequences** of the translation
covariance built in `BoxLocalTranslation.lean`: for a translation-invariant state
`ω` of an `InfiniteSpinSystem` (Definition 4.17, eq. (4.3.3)), the expectation of
a bond / bulk / box observable is unchanged under an **even** translation, and the
translated finite-box Hamiltonian has the same expectation as the centered one.

For an *infinite-volume ground state* the bond energy condition is uniform over
**all** bonds (Definition 4.17), so the stronger statement holds for *every*
shift `x` (not only even ones): `ω(Ĥ_{Λ_n + x}) = |B_n|·ε_GS = ω(Ĥ_{Λ_n})`, and
the shifted-box energy density again equals `ε_GS` and converges to it.

Everything here is proved **axiom-free** from the translation covariance lemmas
and the ground-state bond condition; no new axiom is introduced and no existing
axiom is touched.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, Definition 4.17, eqs. (4.3.3)–(4.3.6),
  pp. 112–115; Appendix A.7, pp. 530–533.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice
open scoped Topology

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

namespace InfiniteSpinSystem.TranslationInvariant

/-- A translation-invariant state is unchanged by an even translation:
`ω(τ_x a) = ω(a)` for `x ∈ ℤᵈ_even`. -/
theorem transl_apply {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (a : A)
    {x : Fin d → ℤ} (hx : InfiniteSpinSystem.evenSite x) :
    ω (S.transl x a) = ω a :=
  hω a x hx

/-- Even-translation invariance of a bond spin–spin expectation:
`ω(Ŝ_{y+x} · Ŝ_{z+x}) = ω(Ŝ_y · Ŝ_z)` for `x ∈ ℤᵈ_even`. -/
theorem spinDot_add_right_apply {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω)
    {x : Fin d → ℤ} (hx : InfiniteSpinSystem.evenSite x) (y z : Fin d → ℤ) :
    ω (InfiniteSpinSystem.spinDot S (y + x) (z + x)) = ω (InfiniteSpinSystem.spinDot S y z) := by
  rw [← InfiniteSpinSystem.transl_spinDot]
  exact hω _ x hx

/-- Even-translation invariance of a bulk-operator expectation:
`ω((τ_x Â)_n) = ω(Â_n)` for `x ∈ ℤᵈ_even`. -/
theorem bulkOp_transl_apply {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω)
    {x : Fin d → ℤ} (hx : InfiniteSpinSystem.evenSite x) (a : A) (n : ℕ) :
    ω (InfiniteSpinSystem.bulkOp S (S.transl x a) n) = ω (InfiniteSpinSystem.bulkOp S a n) := by
  rw [← InfiniteSpinSystem.transl_bulkOp]
  exact hω _ x hx

/-- Even-translation invariance of the box-Hamiltonian expectation:
`ω(τ_x Ĥ_{Λ_n}) = ω(Ĥ_{Λ_n})` for `x ∈ ℤᵈ_even`. -/
theorem transl_boxLocalHamiltonian_apply {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω)
    {x : Fin d → ℤ} (hx : InfiniteSpinSystem.evenSite x) (n : ℕ) :
    ω (S.transl x (boxLocalHamiltonian S n)) = ω (boxLocalHamiltonian S n) :=
  hω _ x hx

/-- For a translation-invariant state and an **even** shift, the shifted box
Hamiltonian has the same expectation as the centered one:
`ω(Ĥ_{Λ_n + x}) = ω(Ĥ_{Λ_n})`. -/
theorem translatedBoxLocalHamiltonian_apply_eq {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω)
    {x : Fin d → ℤ} (hx : InfiniteSpinSystem.evenSite x) (n : ℕ) :
    ω (translatedBoxLocalHamiltonian S x n) = ω (boxLocalHamiltonian S n) := by
  rw [← transl_boxLocalHamiltonian]
  exact hω _ x hx

end InfiniteSpinSystem.TranslationInvariant

/-- The **shifted-box energy density** `ω(Ĥ_{Λ_n + x}) / |B_n|` of a state `ω`. -/
noncomputable def translatedBoxLocalHamiltonianEnergyDensity
    (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A) (x : Fin d → ℤ) (n : ℕ) : ℝ :=
  (ω (translatedBoxLocalHamiltonian S x n)).re / (boxBondCount d n : ℝ)

/-- **`ω` has shifted-box energy density `ε`** along `Λ_n + x`: the per-bond
shifted-box energy density converges to `ε`. -/
def HasTranslatedBoxLocalHamiltonianEnergyDensity
    (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A) (x : Fin d → ℤ) (ε : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => translatedBoxLocalHamiltonianEnergyDensity S ω x (n + 1))
    Filter.atTop (nhds ε)

namespace InfiniteSpinSystem.TranslationInvariant

/-- For a translation-invariant state and an even shift, the shifted-box energy
density equals the centered box-local energy density. -/
theorem translatedBoxLocalHamiltonianEnergyDensity_eq_boxLocal
    {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω)
    {x : Fin d → ℤ} (hx : InfiniteSpinSystem.evenSite x) (n : ℕ) :
    translatedBoxLocalHamiltonianEnergyDensity S ω x n =
      boxLocalHamiltonianEnergyDensity S ω n := by
  unfold translatedBoxLocalHamiltonianEnergyDensity boxLocalHamiltonianEnergyDensity
  rw [hω.translatedBoxLocalHamiltonian_apply_eq hx n]

end InfiniteSpinSystem.TranslationInvariant

namespace InfiniteSpinSystem.IsInfiniteVolumeGroundState

variable {S : InfiniteSpinSystem d A} {εGS : ℝ} {ω : WeakDual ℂ A}

/-- **The shifted box Hamiltonian expectation in a ground state** (any shift `x`):
since every bond carries the energy density, `ω(Ĥ_{Λ_n + x}) = |B_n| · ε_GS`. -/
theorem translatedBoxLocalHamiltonian_apply
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω) (x : Fin d → ℤ) (n : ℕ) :
    ω (translatedBoxLocalHamiltonian S x n) = (boxBondCount d n : ℂ) * (εGS : ℂ) := by
  have hbond : ∀ p ∈ boxOrderedBondPairs d n,
      ω (InfiniteSpinSystem.spinDot S ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x))
        = (εGS : ℂ) := by
    intro p hp
    have hadj : (hypercubicBoxGraph d n).Adj p.1 p.2 := mem_boxOrderedBondPairs.mp hp
    have hb0 : InfiniteSpinSystem.bond (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ) :=
      InfiniteSpinSystem.bond_iff_adj.mpr (hypercubicBoxGraph_adj.mp hadj)
    have hb : InfiniteSpinSystem.bond ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x) :=
      (InfiniteSpinSystem.bond_add_right_iff x (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ)).mpr hb0
    exact hω.2.2 _ _ hb
  have hsmul : ω (translatedBoxLocalHamiltonian S x n)
      = (1 / 2 : ℂ) * ω (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x)) := by
    change ω ((1 / 2 : ℂ) • ∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x))
      = (1 / 2 : ℂ) * ω (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x))
    have h := map_smulₛₗ ω (1 / 2 : ℂ)
      (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x))
    rw [RingHom.id_apply, smul_eq_mul] at h
    exact h
  rw [hsmul, map_sum, Finset.sum_congr rfl hbond, Finset.sum_const,
    boxOrderedBondPairs_card_eq_two_mul_boxBondCount]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- In a ground state the shifted box Hamiltonian has the same expectation as the
centered one (any shift): `ω(Ĥ_{Λ_n + x}) = ω(Ĥ_{Λ_n})`. -/
theorem translatedBoxLocalHamiltonian_apply_eq_boxLocal
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω) (x : Fin d → ℤ) (n : ℕ) :
    ω (translatedBoxLocalHamiltonian S x n) = ω (boxLocalHamiltonian S n) := by
  rw [hω.translatedBoxLocalHamiltonian_apply x n, hω.boxLocalHamiltonian_apply n]

/-- In a ground state the shifted-box energy density equals `ε_GS` (for nonempty
boxes, any shift). -/
theorem translatedBoxLocalHamiltonianEnergyDensity_eq
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω) (x : Fin d → ℤ)
    {n : ℕ} (hB : 0 < boxBondCount d n) :
    translatedBoxLocalHamiltonianEnergyDensity S ω x n = εGS := by
  have hbne : (boxBondCount d n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  unfold translatedBoxLocalHamiltonianEnergyDensity
  rw [hω.translatedBoxLocalHamiltonian_apply x n]
  have hb : (boxBondCount d n : ℂ) = ((boxBondCount d n : ℝ) : ℂ) := by push_cast; ring
  rw [hb, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

/-- In a ground state the shifted-box energy density converges to `ε_GS`
(any shift). -/
theorem hasTranslatedBoxLocalHamiltonianEnergyDensity (hd : 0 < d)
    (hω : InfiniteSpinSystem.IsInfiniteVolumeGroundState S εGS ω) (x : Fin d → ℤ) :
    HasTranslatedBoxLocalHamiltonianEnergyDensity S ω x εGS := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards with n
  exact (hω.translatedBoxLocalHamiltonianEnergyDensity_eq x
    (boxBondCount_pos d (n + 1) hd (Nat.succ_le_succ (Nat.zero_le n)))).symm

end InfiniteSpinSystem.IsInfiniteVolumeGroundState

end LatticeSystem.Quantum
