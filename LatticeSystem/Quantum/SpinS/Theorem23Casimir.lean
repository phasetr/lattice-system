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

/-! ## Sector-embedded Casimir non-vanishing -/

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded Casimir non-vanishing,
lowering direction**: if a zero-extended `magSumS = M` sector vector is
a total-Casimir eigenvector at a value different from the lowering
kernel value for that sector magnetization, then its total-lowering
image is non-zero.

This packages
`tasaki23_totalSpinSOpMinus_mulVec_ne_zero_of_casimir_ne_kernel_value`
with `magSectorEmbedding_mem_magSubspaceS`, so the criterion applies
directly to sector vectors used in the adjacent-sector chain. -/
theorem tasaki23_totalSpinSOpMinus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
    {N M : ℕ} {γ : ℂ} {Φ : magConfigS V N M → ℂ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        γ • magSectorEmbedding Φ)
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)))
    (hΦ_ne : magSectorEmbedding Φ ≠ 0) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 := by
  exact
    tasaki23_totalSpinSOpMinus_mulVec_ne_zero_of_casimir_ne_kernel_value
      (magSectorEmbedding_mem_magSubspaceS (V := V) (N := N) (M := M) Φ)
      hΦ_cas hγ_ne hΦ_ne

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded Casimir non-vanishing,
raising direction**: if a zero-extended `magSumS = M` sector vector is
a total-Casimir eigenvector at a value different from the raising
kernel value for that sector magnetization, then its total-raising
image is non-zero.

This is the raising companion to
`tasaki23_totalSpinSOpMinus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value`. -/
theorem tasaki23_totalSpinSOpPlus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
    {N M : ℕ} {γ : ℂ} {Φ : magConfigS V N M → ℂ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        γ • magSectorEmbedding Φ)
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) + 1)))
    (hΦ_ne : magSectorEmbedding Φ ≠ 0) :
    (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 := by
  exact
    tasaki23_totalSpinSOpPlus_mulVec_ne_zero_of_casimir_ne_kernel_value
      (magSectorEmbedding_mem_magSubspaceS (V := V) (N := N) (M := M) Φ)
      hΦ_cas hγ_ne hΦ_ne

/-! ## Marshall-positive sector vectors -/

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 Marshall-positive sector vector
non-vanishing**: the zero-extension of a sector vector with strictly
positive Marshall coefficients is non-zero.

This supplies the non-zero vector hypothesis needed to apply the
sector-embedded Casimir ladder non-vanishing criteria to the
Theorem 2.2 sector ground-state vector. -/
theorem tasaki23_marshallPositive_magSectorEmbedding_ne_zero
    (A : V → Bool) {N M : ℕ} [Nonempty (magConfigS V N M)]
    {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ τ, 0 < v τ) :
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ≠ 0 := by
  intro hzero
  let τ : magConfigS V N M := Classical.choice inferInstance
  have happly := congrFun hzero τ.1
  rw [magSectorEmbedding_apply_subtype] at happly
  have hpos :
      0 <
        (marshallSignS A τ.1).re *
          ((marshallSignS A τ.1).re * v τ) := by
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos τ
  have hreal_ne : (marshallSignS A τ.1).re * v τ ≠ 0 := by
    intro hreal_zero
    have hprod_zero :
        (marshallSignS A τ.1).re *
          ((marshallSignS A τ.1).re * v τ) = 0 := by
      rw [hreal_zero, mul_zero]
    exact (ne_of_gt hpos) hprod_zero
  exact (Complex.ofReal_ne_zero.mpr hreal_ne) happly

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 Marshall-positive sector Casimir
non-vanishing, lowering direction**: a Marshall-positive sector vector
with a non-endpoint total-Casimir eigenvalue has non-zero total-lowering
image after zero-extension.

This is the lowering sector-embedded Casimir criterion with the
non-zero hypothesis discharged from strict Marshall positivity. -/
theorem tasaki23_totalSpinSOpMinus_mulVec_marshallPositive_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
    (A : V → Bool) {N M : ℕ} [Nonempty (magConfigS V N M)]
    {γ : ℂ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)))
    (hv_pos : ∀ τ, 0 < v τ) :
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 := by
  exact
    tasaki23_totalSpinSOpMinus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
      hΦ_cas hγ_ne (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 Marshall-positive sector Casimir
non-vanishing, raising direction**: a Marshall-positive sector vector
with a non-endpoint total-Casimir eigenvalue has non-zero total-raising
image after zero-extension.

This is the raising companion to
`tasaki23_totalSpinSOpMinus_mulVec_marshallPositive_magSectorEmbedding_ne_zero`
`_of_casimir_ne_kernel_value`. -/
theorem tasaki23_totalSpinSOpPlus_mulVec_marshallPositive_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
    (A : V → Bool) {N M : ℕ} [Nonempty (magConfigS V N M)]
    {γ : ℂ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) + 1)))
    (hv_pos : ∀ τ, 0 < v τ) :
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 := by
  exact
    tasaki23_totalSpinSOpPlus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
      hΦ_cas hγ_ne (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)

end LatticeSystem.Quantum
