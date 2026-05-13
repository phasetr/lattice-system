import LatticeSystem.Quantum.SpinS.SaturatedLadderLoweringInvariant
import LatticeSystem.Quantum.SpinS.SaturatedLadderRaisingInvariant

/-!
# Invariance of the saturated-ferromagnet joint eigenspace under
the Cartesian total-spin generators `Ŝ^{(1)}_tot`, `Ŝ^{(2)}_tot`,
`Ŝ^{(3)}_tot`

For `[Nonempty V]`, the saturated-ferromagnet joint
`(H, (Ŝ_{tot})²)`-eigenspace is invariant under all three Cartesian
components of the total spin operator. Combined with the ladder
invariances (PR #2770: `Ŝ^-_tot`; PR #2771: `Ŝ^+_tot`), this
establishes invariance under the full `su(2)` Lie algebra acting via
the total-spin generators, completing the operational identification
of the joint eigenspace with the `(2m_max + 1)`-dim irreducible
representation begun in Tasaki §2.4 Theorem 2.1 closure (PR #2768).

The proofs reduce each Cartesian-component invariance to the ladder
invariances of PRs #2770 / #2771 via the linear combinations
`Ŝ^{(1)}_tot = (1/2)(Ŝ^+_tot + Ŝ^-_tot)`,
`Ŝ^{(2)}_tot = (1/(2i))(Ŝ^+_tot − Ŝ^-_tot)`,
plus the closure of any submodule under addition and scalar
multiplication. The `Ŝ^{(3)}_tot` case is independent: each
ladder iterate is an `Ŝ^{(3)}_tot`-eigenvector (PR #887 +
`ladderIterateUp_mem_eigenspace`), so its image is a scalar multiple
still in `span(ladderIterateUp)`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `Ŝ^{(1)}_tot = (1/2) • (Ŝ^+_tot + Ŝ^-_tot)`: lifts the single-
site identity `spinSOp1 N = (1/2) • (spinSOpPlus N + spinSOpMinus N)`
through the sum-over-sites definitions of the totals. -/
theorem totalSpinSOp1_eq_one_half_smul_plus_add_minus
    (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) :
    (totalSpinSOp1 V N : ManyBodyOpS V N) =
      ((1 : ℂ) / 2) • (totalSpinSOpPlus V N + totalSpinSOpMinus V N) := by
  unfold totalSpinSOp1 totalSpinSOpPlus totalSpinSOpMinus
  have h_site : ∀ x : V, onSiteS x (spinSOp1 N) =
      ((1 : ℂ) / 2) • (onSiteS x (spinSOpPlus N) +
        onSiteS x (spinSOpMinus N)) := by
    intro x
    unfold spinSOp1
    rw [onSiteS_smul, onSiteS_add]
  simp_rw [h_site]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]

/-- `Ŝ^{(2)}_tot = (1/(2 i)) • (Ŝ^+_tot − Ŝ^-_tot)`: lifts the
single-site identity through the totals. -/
theorem totalSpinSOp2_eq_one_over_two_I_smul_plus_sub_minus
    (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) :
    (totalSpinSOp2 V N : ManyBodyOpS V N) =
      ((1 : ℂ) / (2 * Complex.I)) •
        (totalSpinSOpPlus V N - totalSpinSOpMinus V N) := by
  unfold totalSpinSOp2 totalSpinSOpPlus totalSpinSOpMinus
  have h_site : ∀ x : V, onSiteS x (spinSOp2 N) =
      ((1 : ℂ) / (2 * Complex.I)) •
        (onSiteS x (spinSOpPlus N) - onSiteS x (spinSOpMinus N)) := by
    intro x
    unfold spinSOp2
    rw [onSiteS_smul, onSiteS_sub]
  simp_rw [h_site]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib]

/-- **`Ŝ^{(1)}_tot` invariance** of the saturated-ferromagnet joint
eigenspace: reduces via
`Ŝ^{(1)}_tot = (1/2)(Ŝ^+_tot + Ŝ^-_tot)` to the ladder invariances
of PRs #2770 / #2771 plus submodule add/smul closure. -/
theorem saturatedFerromagnetJointEigenspace_totalSpinSOp1_invariant
    [Nonempty V] (J : V → V → ℂ) :
    Submodule.map (totalSpinSOp1 V N).mulVecLin
        (saturatedFerromagnetJointEigenspace (V := V) J N) ≤
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  rintro w ⟨v, hv, rfl⟩
  rw [Matrix.mulVecLin_apply,
      totalSpinSOp1_eq_one_half_smul_plus_add_minus,
      Matrix.smul_mulVec, Matrix.add_mulVec]
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.add_mem _ ?_ ?_
  · exact saturatedFerromagnetJointEigenspace_totalSpinSOpPlus_invariant
      (V := V) (N := N) J ⟨v, hv, by rw [Matrix.mulVecLin_apply]⟩
  · exact saturatedFerromagnetJointEigenspace_totalSpinSOpMinus_invariant
      (V := V) (N := N) J ⟨v, hv, by rw [Matrix.mulVecLin_apply]⟩

/-- **`Ŝ^{(2)}_tot` invariance** of the saturated-ferromagnet joint
eigenspace: reduces via
`Ŝ^{(2)}_tot = (1/(2 i))(Ŝ^+_tot − Ŝ^-_tot)` to the ladder
invariances. -/
theorem saturatedFerromagnetJointEigenspace_totalSpinSOp2_invariant
    [Nonempty V] (J : V → V → ℂ) :
    Submodule.map (totalSpinSOp2 V N).mulVecLin
        (saturatedFerromagnetJointEigenspace (V := V) J N) ≤
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  rintro w ⟨v, hv, rfl⟩
  rw [Matrix.mulVecLin_apply,
      totalSpinSOp2_eq_one_over_two_I_smul_plus_sub_minus,
      Matrix.smul_mulVec, Matrix.sub_mulVec]
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.sub_mem _ ?_ ?_
  · exact saturatedFerromagnetJointEigenspace_totalSpinSOpPlus_invariant
      (V := V) (N := N) J ⟨v, hv, by rw [Matrix.mulVecLin_apply]⟩
  · exact saturatedFerromagnetJointEigenspace_totalSpinSOpMinus_invariant
      (V := V) (N := N) J ⟨v, hv, by rw [Matrix.mulVecLin_apply]⟩

/-- **`Ŝ^{(3)}_tot` invariance** of the saturated-ferromagnet joint
eigenspace: each ladder iterate is an `Ŝ^{(3)}_tot`-eigenvector
(`ladderIterateUp_mem_eigenspace`), so its image under `Ŝ^{(3)}_tot`
is a scalar multiple still in `span(ladderIterateUp) = joint J N`
(PR #2768). -/
theorem saturatedFerromagnetJointEigenspace_totalSpinSOp3_invariant
    [Nonempty V] (J : V → V → ℂ) :
    Submodule.map (totalSpinSOp3 V N).mulVecLin
        (saturatedFerromagnetJointEigenspace (V := V) J N) ≤
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  rw [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp J,
      Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro w ⟨_, ⟨k, rfl⟩, rfl⟩
  rw [Matrix.mulVecLin_apply]
  have h := ladderIterateUp_mem_eigenspace (V := V) (N := N) k
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end LatticeSystem.Quantum
