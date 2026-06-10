import LatticeSystem.Math.AngularMomentum.Multiplet
import LatticeSystem.Math.CommutingHermitianEigenvector
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Tasaki Appendix A.3.2: every level has a spin-0 or spin-1/2 representative (Theorem A.17)

Tasaki's Theorem A.17, "used repeatedly in the present book": for an `su(2)`-invariant Hamiltonian
`Ĥ`, every energy eigenvalue `E` admits a corresponding eigenstate `|Φ⟩` with either
`Ĵ⁽³⁾|Φ⟩ = 0` or `Ĵ⁽³⁾|Φ⟩ = (1/2)|Φ⟩`.  In words, to find all energy eigenvalues one only needs to
look at the `Ĵ⁽³⁾ = 0` and `Ĵ⁽³⁾ = 1/2` sectors.

It is a corollary of the multiplet degeneracy (Theorem A.16): starting from a joint
energy/`Ĵ²`/`Ĵ⁽³⁾` eigenstate of spin `J = n/2` (Theorem A.13), the multiplet contains a state at
the magnetic number `M = J − ⌊J⌋ ∈ {0, 1/2}` — explicitly `M = 0` when `2J` is even and `M = 1/2`
when `2J` is odd, obtained from Theorem A.16 with `k = ⌊J⌋`.  The remaining ingredient is the
*existence* of a simultaneous eigenstate of the commuting self-adjoint family `Ĥ, Ĵ², Ĵ⁽³⁾` inside
the `E`-eigenspace; this is now **proved** (`exists_joint_su2_energy_eigenstate`) from the generic
simultaneous diagonalization of two commuting Hermitian operators on an invariant subspace
(`exists_common_eigenvector_of_isHermitian_commute`, `Math/CommutingHermitianEigenvector.lean`),
using that the Casimir `Ĵ²` is positive semidefinite and commutes with `Ĵ³` and `Ĥ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.3.2, Theorem A.17, p. 473.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d] (H J1 J2 J3 : Matrix d d ℂ)

/-- **Simultaneous diagonalization of the commuting self-adjoint family `Ĥ, Ĵ², Ĵ⁽³⁾`.**
For self-adjoint `Ĥ` and angular-momentum components `Ĵ⁽ᵅ⁾` (`su(2)` relations, each commuting with
`Ĥ`), any energy eigenvector `v ≠ 0` (`Ĥ v = E v`) has, inside the same `E`-eigenspace, a nonzero
*joint* eigenstate `Φ` of `Ĵ²` and `Ĵ⁽³⁾`: there are reals `J ≥ 0` and `M` with
`Ĵ² Φ = J(J+1) Φ`, `Ĵ⁽³⁾ Φ = M Φ` and `Ĥ Φ = E Φ`.

Discharged from `exists_common_eigenvector_of_isHermitian_commute`: the Casimir `Ĵ² = J1²+J2²+J3²`
is positive semidefinite (a sum `∑ JαᴴJα`) and commutes with both `Ĵ³` (from the su(2) relations)
and `Ĥ` (from `[Ĥ, Ĵ⁽ᵅ⁾]=0`), so `Ĵ²` and `Ĵ³` are commuting Hermitian operators preserving the
`Ĥ = E` eigenspace `W` (nonzero, witnessed by `v`); they have a common eigenvector `Φ ∈ W` with real
eigenvalues `a ≥ 0` (PSD) and `M`, and `a = J(J+1)` for `J = (√(1+4a)-1)/2 ≥ 0`. -/
theorem exists_joint_su2_energy_eigenstate {d : Type*} [Fintype d]
    (H J1 J2 J3 : Matrix d d ℂ) (_hH : H.IsHermitian) (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h3 : J3.IsHermitian) (hcH1 : H * J1 = J1 * H) (hcH2 : H * J2 = J2 * H) (hcH3 : H * J3 = J3 * H)
    (_h12 : J1 * J2 - J2 * J1 = Complex.I • J3) (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) {E : ℂ} {v : d → ℂ} (hv : v ≠ 0)
    (hEv : H.mulVec v = E • v) :
    ∃ (Φ : d → ℂ) (Jr M : ℝ), Φ ≠ 0 ∧ 0 ≤ Jr ∧
      (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ ∧
      J3.mulVec Φ = (M : ℂ) • Φ ∧ H.mulVec Φ = E • Φ := by
  classical
  -- `Ĵ² = J1²+J2²+J3²` is positive semidefinite (a sum of `JαᴴJα`), hence Hermitian.
  have hJsqPSD : (J1 * J1 + J2 * J2 + J3 * J3).PosSemidef := by
    have e : J1 * J1 + J2 * J2 + J3 * J3 =
        J1.conjTranspose * J1 + (J2.conjTranspose * J2 + J3.conjTranspose * J3) := by
      rw [h1, h2, h3]; abel
    rw [e]
    exact (Matrix.posSemidef_conjTranspose_mul_self J1).add
      ((Matrix.posSemidef_conjTranspose_mul_self J2).add
        (Matrix.posSemidef_conjTranspose_mul_self J3))
  -- `Ĵ³ ↦ J1*J3 = J3*J1 - i J2` and `J2*J3 = J3*J2 + i J1`.
  have k31 : J1 * J3 = J3 * J1 - Complex.I • J2 := by
    have h := h31; rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have k23 : J2 * J3 = J3 * J2 + Complex.I • J1 := by
    rw [add_comm]; exact sub_eq_iff_eq_add.mp h23
  -- `Ĵ²` commutes with `Ĵ³` (Casimir).
  have P1 : J1 * J1 * J3 = J3 * J1 * J1 - Complex.I • (J2 * J1) - Complex.I • (J1 * J2) := by
    rw [mul_assoc, k31, mul_sub, mul_smul_comm, ← mul_assoc, k31, sub_mul, smul_mul_assoc]
  have P2 : J2 * J2 * J3 = J3 * J2 * J2 + Complex.I • (J1 * J2) + Complex.I • (J2 * J1) := by
    rw [mul_assoc, k23, mul_add, mul_smul_comm, ← mul_assoc, k23, add_mul, smul_mul_assoc]
  have hcomm3 : (J1 * J1 + J2 * J2 + J3 * J3) * J3 = J3 * (J1 * J1 + J2 * J2 + J3 * J3) :=
    calc (J1 * J1 + J2 * J2 + J3 * J3) * J3
        = J1 * J1 * J3 + J2 * J2 * J3 + J3 * J3 * J3 := by noncomm_ring
      _ = (J3 * J1 * J1 - Complex.I • (J2 * J1) - Complex.I • (J1 * J2))
            + (J3 * J2 * J2 + Complex.I • (J1 * J2) + Complex.I • (J2 * J1))
            + J3 * J3 * J3 := by rw [P1, P2]
      _ = J3 * J1 * J1 + J3 * J2 * J2 + J3 * J3 * J3 := by abel
      _ = J3 * (J1 * J1 + J2 * J2 + J3 * J3) := by noncomm_ring
  -- `Ĵ²` commutes with `Ĥ`.
  have c1 : J1 * J1 * H = H * (J1 * J1) := by
    rw [mul_assoc, ← hcH1, ← mul_assoc, ← hcH1, mul_assoc]
  have c2 : J2 * J2 * H = H * (J2 * J2) := by
    rw [mul_assoc, ← hcH2, ← mul_assoc, ← hcH2, mul_assoc]
  have c3 : J3 * J3 * H = H * (J3 * J3) := by
    rw [mul_assoc, ← hcH3, ← mul_assoc, ← hcH3, mul_assoc]
  have hcommH : (J1 * J1 + J2 * J2 + J3 * J3) * H = H * (J1 * J1 + J2 * J2 + J3 * J3) :=
    calc (J1 * J1 + J2 * J2 + J3 * J3) * H
        = J1 * J1 * H + J2 * J2 * H + J3 * J3 * H := by noncomm_ring
      _ = H * (J1 * J1) + H * (J2 * J2) + H * (J3 * J3) := by rw [c1, c2, c3]
      _ = H * (J1 * J1 + J2 * J2 + J3 * J3) := by noncomm_ring
  -- Work in `EuclideanSpace`; `W` = the `Ĥ = E` eigenspace.
  set W : Submodule ℂ (EuclideanSpace ℂ d) :=
    Module.End.eigenspace (Matrix.toEuclideanLin H) E with hW_def
  have hvW : (WithLp.toLp 2 v : EuclideanSpace ℂ d) ∈ W := by
    rw [hW_def, Module.End.mem_eigenspace_iff]
    apply WithLp.ofLp_injective (p := 2) (V := d → ℂ)
    change Matrix.mulVec H v = E • v
    exact hEv
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv (by simpa using congrArg (WithLp.ofLp) hvW)
  -- `Ĵ²` and `Ĵ³` preserve `W` (they commute with `Ĥ`).
  have preserve : ∀ (B : Matrix d d ℂ), B * H = H * B →
      ∀ w ∈ W, Matrix.toEuclideanLin B w ∈ W := by
    intro B hBH w hw
    rw [hW_def, Module.End.mem_eigenspace_iff] at hw ⊢
    apply WithLp.ofLp_injective (p := 2) (V := d → ℂ)
    have hwofLp : Matrix.mulVec H (WithLp.ofLp w) = E • WithLp.ofLp w := by
      have := congrArg WithLp.ofLp hw; simpa using this
    change Matrix.mulVec H (Matrix.mulVec B (WithLp.ofLp w))
      = E • Matrix.mulVec B (WithLp.ofLp w)
    rw [Matrix.mulVec_mulVec, ← hBH, ← Matrix.mulVec_mulVec, hwofLp, Matrix.mulVec_smul]
  have hWA := preserve _ hcommH
  have hWB := preserve _ hcH3.symm
  -- Common eigenvector of `Ĵ²` and `Ĵ³` inside `W`.
  obtain ⟨Φe, a, b, hΦmem, hΦne, hΦa, hΦb⟩ :=
    LatticeSystem.Math.Matrix.exists_common_eigenvector_of_isHermitian_commute
      hJsqPSD.1 h3 hcomm3 hWne hWA hWB
  -- `a ≥ 0` (the Casimir is positive).
  have hApos : (Matrix.toEuclideanLin (J1 * J1 + J2 * J2 + J3 * J3)).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hJsqPSD
  have ha : 0 ≤ a := LatticeSystem.Math.isPositive_eigenvalue_nonneg hApos hΦne hΦa
  -- `a = Jr (Jr+1)` with `Jr = (√(1+4a) - 1)/2 ≥ 0`.
  set Jr : ℝ := (Real.sqrt (1 + 4 * a) - 1) / 2 with hJr_def
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + 4 * a) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (1 + 4 * a) := Real.sqrt_le_sqrt (by linarith)
    simpa using h1
  have hJr_nonneg : 0 ≤ Jr := by rw [hJr_def]; linarith [hsqrt1]
  have hJr_eq : Jr * (Jr + 1) = a := by
    have hs : Real.sqrt (1 + 4 * a) ^ 2 = 1 + 4 * a := Real.sq_sqrt (by linarith)
    rw [hJr_def]; nlinarith [hs]
  -- Transport everything back to `d → ℂ`.
  refine ⟨WithLp.ofLp Φe, Jr, b, ?_, hJr_nonneg, ?_, ?_, ?_⟩
  · intro hΦ0
    exact hΦne (by simpa using hΦ0)
  · rw [show ((Jr * (Jr + 1) : ℝ) : ℂ) = (a : ℂ) by rw [hJr_eq]]
    exact congrArg WithLp.ofLp hΦa
  · exact congrArg WithLp.ofLp hΦb
  · rw [hW_def, Module.End.mem_eigenspace_iff] at hΦmem
    exact congrArg WithLp.ofLp hΦmem

omit [DecidableEq d] in
/-- **Tasaki Theorem A.17 (spin-0 / spin-1/2 sector suffices).**  For an `su(2)`-invariant
self-adjoint `Ĥ` (each `Ĵ⁽ᵅ⁾` self-adjoint, `su(2)` relations, `[Ĥ, Ĵ⁽ᵅ⁾] = 0`), every energy
eigenvalue `E` (witnessed by some `v ≠ 0`, `Ĥ v = E v`) has a corresponding eigenstate `Φ ≠ 0`
(`Ĥ Φ = E Φ`) with either `Ĵ⁽³⁾ Φ = 0` or `Ĵ⁽³⁾ Φ = (1/2) Φ`.  From a joint eigenstate of spin
`J = n/2` (Theorem A.13) the multiplet (Theorem A.16) contains the magnetic number `M = J − ⌊J⌋`,
which is `0` for even `n` and `1/2` for odd `n` (take `k = ⌊J⌋`). -/
theorem ham_eigenstate_spin_zero_or_half (hH : H.IsHermitian) (h1 : J1.IsHermitian)
    (h2 : J2.IsHermitian) (h3 : J3.IsHermitian) (hcH1 : H * J1 = J1 * H) (hcH2 : H * J2 = J2 * H)
    (hcH3 : H * J3 = J3 * H) (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1) (h31 : J3 * J1 - J1 * J3 = Complex.I • J2)
    {E : ℂ} {v : d → ℂ} (hv : v ≠ 0) (hEv : H.mulVec v = E • v) :
    ∃ Φ : d → ℂ, Φ ≠ 0 ∧ H.mulVec Φ = E • Φ ∧
      (J3.mulVec Φ = 0 ∨ J3.mulVec Φ = ((1 / 2 : ℝ) : ℂ) • Φ) := by
  -- Joint `Ĥ`/`Ĵ²`/`Ĵ⁽³⁾` eigenstate in the `E`-eigenspace (simultaneous diagonalization).
  obtain ⟨Φ0, Jr, M, hΦ0, hJr, hsq, h3eq, hHΦ⟩ :=
    exists_joint_su2_energy_eigenstate H J1 J2 J3 hH h1 h2 h3 hcH1 hcH2 hcH3 h12 h23 h31 hv hEv
  -- `J = n/2` (Theorem A.13).
  obtain ⟨n, hn⟩ := angMom_J_eq_half_nat J1 J2 J3 h1 h2 h12 h23 h31 hΦ0 hJr hsq h3eq
  have hmult := ham_su2_multiplet H J1 J2 J3 hcH1 hcH2 hcH3 h1 h2 h12 h23 h31 hΦ0 hJr hsq h3eq hHΦ
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `n = m + m` even ⇒ `J = m` ⇒ companion at `M = 0`.
    have hJrm : Jr = (m : ℝ) := by rw [hn, hm]; push_cast; ring
    obtain ⟨Ψ, hΨ, _, h3Ψ, hHΨ⟩ := hmult m (by rw [hJrm]; linarith)
    refine ⟨Ψ, hΨ, hHΨ, Or.inl ?_⟩
    rw [h3Ψ, show ((Jr - (m : ℝ) : ℝ) : ℂ) = 0 by rw [hJrm]; push_cast; ring, zero_smul]
  · -- `n = 2m + 1` odd ⇒ `J = m + 1/2` ⇒ companion at `M = 1/2`.
    have hJrm : Jr = (m : ℝ) + 1 / 2 := by rw [hn, hm]; push_cast; ring
    obtain ⟨Ψ, hΨ, _, h3Ψ, hHΨ⟩ := hmult m (by rw [hJrm]; linarith)
    refine ⟨Ψ, hΨ, hHΨ, Or.inr ?_⟩
    rw [h3Ψ, show ((Jr - (m : ℝ) : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) by rw [hJrm]; push_cast; ring]

end LatticeSystem.Math
