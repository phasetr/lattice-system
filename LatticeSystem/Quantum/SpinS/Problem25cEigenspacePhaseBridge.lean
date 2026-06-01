import LatticeSystem.Quantum.SpinS.RayleighUnitarySimilarity
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Tasaki Problem 2.5.c: one-dimensional eigenspace phase bridge

This module supplies the abstract linear-algebra input needed after
`Problem25cPhaseInvariantAxisInput.lean`.  If a Hamiltonian eigenspace has
`finrank ≤ 1`, then any commuting symmetry maps a non-zero eigenvector to a
scalar multiple of itself.  If the symmetry is unitary and the eigenvector is
normalized, the scalar has unit modulus.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.c, p. 43, and the Theorem 2.4 symmetry context,
pp. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A vector in a one-dimensional eigenspace spans the image of every commuting
operator: if `H` has `finrank ≤ 1` at eigenvalue `μ`, `Φ` is a non-zero
`μ`-eigenvector, and `U` commutes with `H`, then `UΦ` is a scalar multiple of
`Φ`. -/
theorem mulVec_eq_smul_of_finrank_eigenspace_le_one_of_commute
    {H U : Matrix n n ℂ} {μ : ℂ} {Φ : n → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin' H) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦ : H.mulVec Φ = μ • Φ)
    (hcomm : H * U = U * H) :
    ∃ c : ℂ, U.mulVec Φ = c • Φ := by
  set E := End.eigenspace (Matrix.toLin' H) μ with hEdef
  have hΦ_in : Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hΦ
  have hUΦ_in : U.mulVec Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_smul]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp huniq
  obtain ⟨a, ha⟩ := hv ⟨Φ, hΦ_in⟩
  obtain ⟨b, hb⟩ := hv ⟨U.mulVec Φ, hUΦ_in⟩
  have ha' : a • (v : n → ℂ) = Φ := by
    have h := congrArg ((↑) : ↥E → n → ℂ) ha
    simpa using h
  have hb' : b • (v : n → ℂ) = U.mulVec Φ := by
    have h := congrArg ((↑) : ↥E → n → ℂ) hb
    simpa using h
  have ha_ne : a ≠ 0 := by
    intro h0
    apply hΦ_ne
    rw [← ha', h0, zero_smul]
  refine ⟨b * a⁻¹, ?_⟩
  rw [← hb', ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]

/-- If a unitary matrix maps a normalized vector to `c • Φ`, then the scalar
has unit modulus, written as `star c * c = 1`. -/
theorem phase_unit_of_unitary_mulVec_eq_smul
    {U : Matrix n n ℂ} {Φ : n → ℂ} {c : ℂ}
    (hUunit : U.conjTranspose * U = 1)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
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
  rw [hΦnorm, mul_one] at hmain
  exact hmain

/-- Combined one-dimensional eigenspace and unitary phase bridge: a normalized
non-zero eigenvector in a `finrank ≤ 1` eigenspace is fixed up to a unit-modulus
phase by any unitary symmetry commuting with the Hamiltonian. -/
theorem exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute
    {H U : Matrix n n ℂ} {μ : ℂ} {Φ : n → ℂ}
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin' H) μ) ≤ 1)
    (hΦ_ne : Φ ≠ 0)
    (hΦnorm : dotProduct (star Φ) Φ = 1)
    (hΦ : H.mulVec Φ = μ • Φ)
    (hcomm : H * U = U * H)
    (hUunit : U.conjTranspose * U = 1) :
    ∃ c : ℂ, U.mulVec Φ = c • Φ ∧ star c * c = 1 := by
  obtain ⟨c, hc⟩ :=
    mulVec_eq_smul_of_finrank_eigenspace_le_one_of_commute
      huniq hΦ_ne hΦ hcomm
  exact ⟨c, hc, phase_unit_of_unitary_mulVec_eq_smul hUunit hΦnorm hc⟩

end LatticeSystem.Quantum
