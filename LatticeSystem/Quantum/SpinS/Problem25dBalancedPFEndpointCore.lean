import LatticeSystem.Quantum.SpinS.Problem25dBalancedSectorWitness

/-!
# Problem 2.5.d balanced PF endpoint: non-normalized phase bridge (foundation)

Foundational layer extracted from `Problem25dBalancedPFEndpoint.lean` for build speed.  This file
proves the non-normalized phase bridge: a unit-modulus phase exists for a unitary fixing a vector up
to scaling, refined to the one-dimensional commuting-eigenspace case.

The balanced PF endpoint correlation positivity is kept in the capstone module
`Problem25dBalancedPFEndpoint.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Non-normalized phase bridge -/

omit [DecidableEq V] in
/-- If a unitary matrix maps a non-zero vector to `c • Φ`, then the scalar has
unit modulus.  Unlike `phase_unit_of_unitary_mulVec_eq_smul`, this version does
not require normalizing `Φ`. -/
theorem phase_unit_of_unitary_mulVec_eq_smul_of_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} {Φ : n → ℂ} {c : ℂ}
    (hUunit : U.conjTranspose * U = 1)
    (hΦ_ne : Φ ≠ 0)
    (hphase : U.mulVec Φ = c • Φ) :
    star c * c = 1 := by
  have hpres :
      dotProduct (star (U.mulVec Φ)) (U.mulVec Φ) = dotProduct (star Φ) Φ := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      (dotProduct_star_conjTranspose_mulVec_self
        (U := U.conjTranspose)
        (by simpa [Matrix.conjTranspose_conjTranspose] using hUunit) Φ)
  have hscale :
      dotProduct (star (U.mulVec Φ)) (U.mulVec Φ) =
        (star c * c) * dotProduct (star Φ) Φ := by
    rw [hphase, star_smul, smul_dotProduct, dotProduct_smul]
    simp [smul_eq_mul, mul_assoc]
  have hmain : (star c * c) * dotProduct (star Φ) Φ = dotProduct (star Φ) Φ := by
    rw [← hscale, hpres]
  have hnorm_ne : dotProduct (star Φ) Φ ≠ 0 := by
    have hself :
        dotProduct (star Φ) Φ = ((∑ i, Complex.normSq (Φ i) : ℝ) : ℂ) := by
      rw [dotProduct, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    have hsome : ∃ i, Φ i ≠ 0 := by
      by_contra h
      apply hΦ_ne
      funext i
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hsome
    have hsum_pos : 0 < ∑ j, Complex.normSq (Φ j) :=
      Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
        ⟨i, Finset.mem_univ i, lt_of_le_of_ne (Complex.normSq_nonneg _)
          (Ne.symm (by simpa [Complex.normSq_eq_zero] using hi))⟩
    rw [hself]
    exact Complex.ofReal_ne_zero.mpr hsum_pos.ne'
  have hmain' :
      (star c * c) * dotProduct (star Φ) Φ =
        1 * dotProduct (star Φ) Φ := by
    simpa using hmain
  exact mul_right_cancel₀ hnorm_ne hmain'

omit [DecidableEq V] in
/-- Combined one-dimensional eigenspace and non-normalized unitary phase bridge:
a non-zero eigenvector in a `finrank ≤ 1` eigenspace is fixed up to a
unit-modulus phase by any unitary symmetry commuting with the Hamiltonian. -/
theorem exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute_of_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {H U : Matrix n n ℂ} {μ : ℂ} {Φ : n → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin' H) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦ : H.mulVec Φ = μ • Φ)
    (hcomm : H * U = U * H)
    (hUunit : U.conjTranspose * U = 1) :
    ∃ c : ℂ, U.mulVec Φ = c • Φ ∧ star c * c = 1 := by
  obtain ⟨c, hc⟩ :=
    mulVec_eq_smul_of_finrank_eigenspace_le_one_of_commute
      huniq hΦ_ne hΦ hcomm
  exact ⟨c, hc, phase_unit_of_unitary_mulVec_eq_smul_of_ne_zero hUunit hΦ_ne hc⟩

end LatticeSystem.Quantum
