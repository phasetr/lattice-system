import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Eigenvalue of a commuting involution on a one-dimensional eigenspace

Generic finite-dimensional linear-algebra infrastructure shared by Tasaki §2.5 Theorem 2.4
(`Theorem24ZeroMagnetizationFromUniqueness`) and §4.1 Theorem 4.2 (the susceptibility sum rule's
first-order vanishing, issue #4777).

If a matrix `H` has a `μ`-eigenspace of `finrank ≤ 1` (a unique ground state, up to scale), then a
non-zero eigenvector `Φ` spans that eigenspace; any operator `Θ` commuting with `H` preserves the
eigenspace, so `Θ Φ` is again a scalar multiple of `Φ`.  When `Θ` is an involution (`Θ² = 1`) that
scalar `δ` satisfies `δ² = 1` (`Θ` acts as `±1` on the ground state).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020, §2.5
Theorem 2.4 (p. 43–44) and §4.1 Theorem 4.2 (pp. 84–86).
-/

namespace LatticeSystem.Math

open Matrix Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **A member of a `finrank ≤ 1` submodule is a scalar multiple of any non-zero member.**  From the
generator `v` of the (at most one-dimensional) space, both `Φ` and `w` are scalar multiples of `v`,
so `w = c • Φ` with `c = (coefficient of w) · (coefficient of Φ)⁻¹`. -/
theorem exists_smul_of_mem_finrank_le_one {E : Submodule ℂ (ι → ℂ)} [Module.Finite ℂ ↥E]
    (hE : finrank ℂ E ≤ 1) {Φ : ι → ℂ} (hΦmem : Φ ∈ E) (hΦne : Φ ≠ 0)
    {w : ι → ℂ} (hwmem : w ∈ E) : ∃ c : ℂ, w = c • Φ := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hE
  obtain ⟨a, ha⟩ := hv ⟨Φ, hΦmem⟩
  obtain ⟨b, hb⟩ := hv ⟨w, hwmem⟩
  have ha' : a • (v : ι → ℂ) = Φ := by
    have h := congrArg ((↑) : ↥E → ι → ℂ) ha; simpa using h
  have hb' : b • (v : ι → ℂ) = w := by
    have h := congrArg ((↑) : ↥E → ι → ℂ) hb; simpa using h
  have ha_ne : a ≠ 0 := fun h0 => hΦne (by rw [← ha', h0, zero_smul])
  exact ⟨b * a⁻¹, by rw [← hb', ← ha', smul_smul, mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]⟩

/-- **A commuting involution acts as `±1` on a unique ground state.**  If the `μ`-eigenspace of `H`
has `finrank ≤ 1`, `Φ ≠ 0` is a `μ`-eigenvector, and `Θ` commutes with `H` (`H Θ = Θ H`) and is
an involution (`Θ² = 1`), then `Θ Φ = δ • Φ` for a scalar `δ` with `δ² = 1`.  `Θ Φ` lies in the
eigenspace (commutation), so is a multiple of `Φ` (uniqueness), and `Θ² Φ = Φ` forces `δ² = 1`. -/
theorem exists_involution_eigenvalue_of_unique_eigenspace (H Θ : Matrix ι ι ℂ) (μ : ℂ)
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin' H) μ) ≤ 1)
    {Φ : ι → ℂ} (hΦ_ne : Φ ≠ 0) (hΦ : H.mulVec Φ = μ • Φ)
    (hcomm : H * Θ = Θ * H) (hinv : Θ * Θ = 1) :
    ∃ δ : ℂ, Θ.mulVec Φ = δ • Φ ∧ δ ^ 2 = 1 := by
  set E := End.eigenspace (Matrix.toLin' H) μ with hEdef
  have hΦ_in : Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΦ
  have hΘΦ_in : Θ.mulVec Φ ∈ E := by
    rw [hEdef, End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcomm,
      ← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_smul]
  obtain ⟨δ, hΘΦ_eq⟩ := exists_smul_of_mem_finrank_le_one huniq hΦ_in hΦ_ne hΘΦ_in
  refine ⟨δ, hΘΦ_eq, ?_⟩
  -- `Θ² Φ = Φ` gives `δ² • Φ = Φ`, hence `δ² = 1` (as `Φ ≠ 0`).
  have hΘ2 : Θ.mulVec (Θ.mulVec Φ) = Φ := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hδ2 : δ ^ 2 • Φ = Φ := by
    have h := hΘ2
    rw [hΘΦ_eq, Matrix.mulVec_smul, hΘΦ_eq, smul_smul, ← sq] at h; exact h
  by_contra hne
  have hsub : (δ ^ 2 - 1) • Φ = 0 := by rw [sub_smul, hδ2, one_smul, sub_self]
  exact hΦ_ne ((smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne))

end LatticeSystem.Math
