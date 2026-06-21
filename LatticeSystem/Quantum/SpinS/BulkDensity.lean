import LatticeSystem.Quantum.SpinS.BulkOperator

/-!
# Tasaki §4.3.1: the bulk density `Â_n / Lᵈ` and the ergodic fluctuation

Continuing the bulk-operator algebra (`BulkOperator.lean`), this module introduces
the **bulk density** `Â_n / Lᵈ` (`Lᵈ = (2n)ᵈ`, the volume of the box `Λ_n`), the
real first and second moments of its expectation, and the **density fluctuation**
of Tasaki eq. (4.3.6).  Definition 4.18 (ergodicity) is restated through these
named pieces (`isErgodic_iff_tendsto_bulkDensityFluctuation`), and the structural
accessors of an ergodic state are provided.

Everything is proved **axiom-free**; no new axiom is introduced and no existing
axiom is touched.  No closed form for `|Λ_n ∩ ℤᵈ_even|` is asserted (that is a
separate finite-combinatorics question).

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, Definition 4.18, eqs. (4.3.5)–(4.3.6),
  pp. 114–115; Appendix A.7, pp. 530–533.
-/

namespace LatticeSystem.Quantum

open scoped Topology

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

namespace InfiniteSpinSystem

/-- The real box-volume normalization `Lᵈ = (2n)ᵈ` of the bulk-density limits
(Tasaki eqs. (4.3.4)–(4.3.6)). -/
noncomputable def bulkVolume (d n : ℕ) : ℝ := (2 * (n : ℝ)) ^ d

/-- The tail volumes `(2(n+1))ᵈ` are positive (so the densities are well-defined
on the tail, avoiding the empty `n = 0` box). -/
theorem bulkVolume_succ_pos (d n : ℕ) : 0 < bulkVolume d (n + 1) := by
  refine pow_pos ?_ d
  positivity

/-- The real volume normalization equals the cardinality of the box `Λ_n`:
`|Λ_n| = (2n)ᵈ`. -/
theorem latticeBox_card_real (d n : ℕ) :
    ((latticeBox d n).card : ℝ) = bulkVolume d n := by
  rw [latticeBox_eq_hypercubicBox, LatticeSystem.Lattice.hypercubicBox_card, bulkVolume]
  push_cast
  ring

/-- The **bulk-density observable** `Â_n / (2n)ᵈ` (Tasaki §4.3.1). -/
noncomputable def bulkDensity (S : InfiniteSpinSystem d A) (a : A) (n : ℕ) : A :=
  ((bulkVolume d n : ℂ)⁻¹) • bulkOp S a n

/-- The bulk density annihilates `0`. -/
@[simp]
theorem bulkDensity_zero (S : InfiniteSpinSystem d A) (n : ℕ) :
    bulkDensity S (0 : A) n = 0 := by
  simp [bulkDensity]

/-- The bulk density is additive. -/
theorem bulkDensity_add (S : InfiniteSpinSystem d A) (a b : A) (n : ℕ) :
    bulkDensity S (a + b) n = bulkDensity S a n + bulkDensity S b n := by
  simp [bulkDensity, bulkOp_add, smul_add]

/-- The bulk density is `ℂ`-homogeneous. -/
theorem bulkDensity_smul (S : InfiniteSpinSystem d A) (c : ℂ) (a : A) (n : ℕ) :
    bulkDensity S (c • a) n = c • bulkDensity S a n := by
  rw [bulkDensity, bulkOp_smul, bulkDensity, smul_comm]

/-- The expectation of the bulk density in a state `ω`:
`ω(Â_n / Lᵈ) = Lᵈ⁻¹ · ω(Â_n)`. -/
theorem bulkDensity_apply (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A) (a : A) (n : ℕ) :
    ω (bulkDensity S a n) = ((bulkVolume d n : ℂ)⁻¹) * ω (bulkOp S a n) := by
  have h := map_smulₛₗ ω ((bulkVolume d n : ℂ)⁻¹) (bulkOp S a n)
  rw [RingHom.id_apply, smul_eq_mul] at h
  exact h

/-- The **real first moment** of the bulk density, `Re ω(Â_n) / Lᵈ` (Tasaki
eq. (4.3.6)). -/
noncomputable def bulkDensityMean (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A)
    (a : A) (n : ℕ) : ℝ :=
  (ω (bulkOp S a n)).re / bulkVolume d n

/-- The **real second moment** of the bulk density, `Re ω(Â_n²) / L^{2d}` (Tasaki
eq. (4.3.6)). -/
noncomputable def bulkDensitySecondMoment (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A)
    (a : A) (n : ℕ) : ℝ :=
  (ω ((bulkOp S a n) ^ 2)).re / (bulkVolume d n) ^ 2

/-- The **bulk-density fluctuation** `Re ω(Â_n²)/L^{2d} − (Re ω(Â_n)/Lᵈ)²`
(Tasaki eq. (4.3.6)); its vanishing in the infinite-volume limit is ergodicity. -/
noncomputable def bulkDensityFluctuation (S : InfiniteSpinSystem d A) (ω : WeakDual ℂ A)
    (a : A) (n : ℕ) : ℝ :=
  bulkDensitySecondMoment S ω a n - (bulkDensityMean S ω a n) ^ 2

namespace TranslationInvariant

/-- In a translation-invariant state the bulk-density expectation is the
even-box-cardinality ratio times the one-site expectation. -/
theorem bulkDensity_apply_eq_card_mul {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (a : A) (n : ℕ) :
    ω (bulkDensity S a n) =
      ((bulkVolume d n : ℂ)⁻¹) * (((evenLatticeBox d n).card : ℂ) * ω a) := by
  rw [bulkDensity_apply, hω.bulkOp_apply_eq_card_mul]

/-- Real first-moment form of the translation-invariant bulk-density value. -/
theorem bulkDensityMean_eq_card_mul {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (a : A) (n : ℕ) :
    bulkDensityMean S ω a n =
      (((evenLatticeBox d n).card : ℝ) * (ω a).re) / bulkVolume d n := by
  unfold bulkDensityMean
  rw [hω.bulkOp_apply_eq_card_mul]
  simp [Complex.mul_re]

end TranslationInvariant

/-- **Definition 4.18 restated** through the named density fluctuation: a
translation-invariant state is ergodic iff the bulk-density fluctuation of every
self-adjoint local observable vanishes in the infinite-volume limit. -/
theorem isErgodic_iff_tendsto_bulkDensityFluctuation
    {S : InfiniteSpinSystem d A} {ρ : WeakDual ℂ A} :
    IsErgodic S ρ ↔
      LatticeSystem.Math.IsState ρ ∧ InfiniteSpinSystem.TranslationInvariant S ρ ∧
        ∀ a : A, a ∈ S.localAlg → IsSelfAdjoint a →
          Filter.Tendsto (fun n : ℕ => bulkDensityFluctuation S ρ a (n + 1))
            Filter.atTop (nhds 0) := by
  unfold IsErgodic
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine forall_congr' fun a => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine Filter.tendsto_congr fun n => ?_
  unfold bulkDensityFluctuation bulkDensitySecondMoment bulkDensityMean bulkVolume
  push_cast
  ring

namespace IsErgodic

/-- An ergodic state is a state. -/
theorem isState {S : InfiniteSpinSystem d A} {ρ : WeakDual ℂ A} (hρ : IsErgodic S ρ) :
    LatticeSystem.Math.IsState ρ :=
  hρ.1

/-- An ergodic state is translation invariant. -/
theorem translationInvariant {S : InfiniteSpinSystem d A} {ρ : WeakDual ℂ A}
    (hρ : IsErgodic S ρ) :
    InfiniteSpinSystem.TranslationInvariant S ρ :=
  hρ.2.1

/-- The bulk-density fluctuation of a self-adjoint local observable vanishes in an
ergodic state. -/
theorem tendsto_bulkDensityFluctuation {S : InfiniteSpinSystem d A} {ρ : WeakDual ℂ A}
    (hρ : IsErgodic S ρ) {a : A} (ha : a ∈ S.localAlg) (hsa : IsSelfAdjoint a) :
    Filter.Tendsto (fun n : ℕ => bulkDensityFluctuation S ρ a (n + 1))
      Filter.atTop (nhds 0) :=
  (isErgodic_iff_tendsto_bulkDensityFluctuation.mp hρ).2.2 a ha hsa

end IsErgodic

end InfiniteSpinSystem

end LatticeSystem.Quantum
