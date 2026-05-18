import Mathlib.Data.Nat.Lattice
import LatticeSystem.Quantum.SpinS.CasimirRearrangement
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding

/-!
# Tasaki §2.5 Theorem 2.3 — Casimir ladder obstructions

This module contains the total-Casimir consequences used in the
Tasaki §2.5 Theorem 2.3 adjacent-sector ladder argument. They say
that a vanished total lowering or raising move forces the corresponding
SU(2) endpoint Casimir value, and package the contrapositive as
non-vanishing criteria.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Ladder-kernel Casimir consequences -/

/-- **Tasaki §2.5 Theorem 2.3 ladder-kernel Casimir consequence,
lowering direction**: if a vector in the `Ŝ_tot^(3)` eigenspace of
eigenvalue `m` is killed by `Ŝ^-_tot`, then it is a total-Casimir
eigenvector with eigenvalue `m * (m - 1)`.

This is the SU(2) obstruction behind the remaining Theorem 2.3
adjacent-sector step: a failed lowering move forces the source vector
to be a lowest-weight vector for the total-spin representation. -/
theorem tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpMinus_eq_zero_of_mem_magSubspaceS
    {N : ℕ} {m : ℂ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ magSubspaceS V N m)
    (hker : (totalSpinSOpMinus V N).mulVec Ψ = 0) :
    (totalSpinSSquared V N).mulVec Ψ = (m * (m - 1)) • Ψ := by
  rw [mem_magSubspaceS_iff] at hΨ
  have hRearr :=
    totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z
      (V := V) (N := N)
  have hLHS :
      ((totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N).mulVec Ψ =
        0 := by
    rw [← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  have hzero :
      ((totalSpinSSquared V N - totalSpinSOp3 V N * totalSpinSOp3 V N +
          totalSpinSOp3 V N : ManyBodyOpS V N).mulVec Ψ) = 0 := by
    rw [← hRearr]
    exact hLHS
  rw [Matrix.add_mulVec, Matrix.sub_mulVec] at hzero
  have h_sq :
      ((totalSpinSOp3 V N * totalSpinSOp3 V N : ManyBodyOpS V N).mulVec Ψ) =
        (m * m) • Ψ := by
    rw [← Matrix.mulVec_mulVec, hΨ, Matrix.mulVec_smul, hΨ, smul_smul]
  rw [h_sq, hΨ] at hzero
  have hmove :
      (totalSpinSSquared V N).mulVec Ψ = (m * m) • Ψ - m • Ψ := by
    calc
      (totalSpinSSquared V N).mulVec Ψ =
          ((totalSpinSSquared V N).mulVec Ψ - (m * m) • Ψ + m • Ψ) +
              (m * m) • Ψ - m • Ψ := by abel
      _ = 0 + (m * m) • Ψ - m • Ψ := by rw [hzero]
      _ = (m * m) • Ψ - m • Ψ := by simp
  rw [hmove, ← sub_smul]
  congr 1
  ring

/-- **Tasaki §2.5 Theorem 2.3 ladder-kernel Casimir consequence,
raising direction**: if a vector in the `Ŝ_tot^(3)` eigenspace of
eigenvalue `m` is killed by `Ŝ^+_tot`, then it is a total-Casimir
eigenvector with eigenvalue `m * (m + 1)`.

This is the raising-direction companion to the lowering kernel
obstruction, using the `Ŝ^-_tot Ŝ^+_tot` Casimir rearrangement. -/
theorem tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpPlus_eq_zero_of_mem_magSubspaceS
    {N : ℕ} {m : ℂ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ magSubspaceS V N m)
    (hker : (totalSpinSOpPlus V N).mulVec Ψ = 0) :
    (totalSpinSSquared V N).mulVec Ψ = (m * (m + 1)) • Ψ := by
  rw [mem_magSubspaceS_iff] at hΨ
  have hRearr :=
    totalSpinSOpMinus_mul_totalSpinSOpPlus_eq_casimir_minus_z_sq_sub_z
      (V := V) (N := N)
  have hLHS :
      ((totalSpinSOpMinus V N : ManyBodyOpS V N) * totalSpinSOpPlus V N).mulVec Ψ =
        0 := by
    rw [← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  have hzero :
      ((totalSpinSSquared V N - totalSpinSOp3 V N * totalSpinSOp3 V N -
          totalSpinSOp3 V N : ManyBodyOpS V N).mulVec Ψ) = 0 := by
    rw [← hRearr]
    exact hLHS
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec] at hzero
  have h_sq :
      ((totalSpinSOp3 V N * totalSpinSOp3 V N : ManyBodyOpS V N).mulVec Ψ) =
        (m * m) • Ψ := by
    rw [← Matrix.mulVec_mulVec, hΨ, Matrix.mulVec_smul, hΨ, smul_smul]
  rw [h_sq, hΨ] at hzero
  have hmove :
      (totalSpinSSquared V N).mulVec Ψ = (m * m) • Ψ + m • Ψ := by
    calc
      (totalSpinSSquared V N).mulVec Ψ =
          ((totalSpinSSquared V N).mulVec Ψ - (m * m) • Ψ - m • Ψ) +
              (m * m) • Ψ + m • Ψ := by abel
      _ = 0 + (m * m) • Ψ + m • Ψ := by rw [hzero]
      _ = (m * m) • Ψ + m • Ψ := by simp
  rw [hmove, ← add_smul]
  congr 1
  ring

/-- **Tasaki §2.5 Theorem 2.3 Casimir-based ladder non-vanishing,
lowering direction**: if a non-zero vector in the `Ŝ_tot^(3)`
eigenspace of value `m` has total-Casimir eigenvalue `γ ≠ m * (m - 1)`,
then its `Ŝ^-_tot` image is non-zero.

This is the contrapositive use of
`tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpMinus_eq_zero_of_mem_magSubspaceS`:
away from the forced kernel Casimir value, the lowering step cannot
vanish. -/
theorem tasaki23_totalSpinSOpMinus_mulVec_ne_zero_of_casimir_ne_kernel_value
    {N : ℕ} {m γ : ℂ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_mag : Ψ ∈ magSubspaceS V N m)
    (hΨ_cas : (totalSpinSSquared V N).mulVec Ψ = γ • Ψ)
    (hγ_ne : γ ≠ m * (m - 1))
    (hΨ_ne : Ψ ≠ 0) :
    (totalSpinSOpMinus V N).mulVec Ψ ≠ 0 := by
  intro hker
  have hforced :
      (totalSpinSSquared V N).mulVec Ψ = (m * (m - 1)) • Ψ :=
    tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpMinus_eq_zero_of_mem_magSubspaceS
      hΨ_mag hker
  have hzero : (γ - m * (m - 1)) • Ψ = 0 := by
    calc
      (γ - m * (m - 1)) • Ψ = γ • Ψ - (m * (m - 1)) • Ψ := by
        rw [sub_smul]
      _ = 0 := by
        rw [← hΨ_cas, ← hforced, sub_self]
  rcases smul_eq_zero.mp hzero with hscalar | hvec
  · exact hγ_ne (sub_eq_zero.mp hscalar)
  · exact hΨ_ne hvec

/-- **Tasaki §2.5 Theorem 2.3 Casimir-based ladder non-vanishing,
raising direction**: if a non-zero vector in the `Ŝ_tot^(3)`
eigenspace of value `m` has total-Casimir eigenvalue `γ ≠ m * (m + 1)`,
then its `Ŝ^+_tot` image is non-zero.

This is the raising companion to
`tasaki23_totalSpinSOpMinus_mulVec_ne_zero_of_casimir_ne_kernel_value`. -/
theorem tasaki23_totalSpinSOpPlus_mulVec_ne_zero_of_casimir_ne_kernel_value
    {N : ℕ} {m γ : ℂ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_mag : Ψ ∈ magSubspaceS V N m)
    (hΨ_cas : (totalSpinSSquared V N).mulVec Ψ = γ • Ψ)
    (hγ_ne : γ ≠ m * (m + 1))
    (hΨ_ne : Ψ ≠ 0) :
    (totalSpinSOpPlus V N).mulVec Ψ ≠ 0 := by
  intro hker
  have hforced :
      (totalSpinSSquared V N).mulVec Ψ = (m * (m + 1)) • Ψ :=
    tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpPlus_eq_zero_of_mem_magSubspaceS
      hΨ_mag hker
  have hzero : (γ - m * (m + 1)) • Ψ = 0 := by
    calc
      (γ - m * (m + 1)) • Ψ = γ • Ψ - (m * (m + 1)) • Ψ := by
        rw [sub_smul]
      _ = 0 := by
        rw [← hΨ_cas, ← hforced, sub_self]
  rcases smul_eq_zero.mp hzero with hscalar | hvec
  · exact hγ_ne (sub_eq_zero.mp hscalar)
  · exact hΨ_ne hvec

end LatticeSystem.Quantum
