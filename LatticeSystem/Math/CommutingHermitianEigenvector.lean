import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Common eigenvector of two commuting self-adjoint operators

On a finite-dimensional complex inner product space, two commuting self-adjoint operators
`A`, `B` and a nonzero subspace `W` invariant under both admit a nonzero **common
eigenvector** inside `W`, with *real* eigenvalues.  This is the elementary finite-dimensional
core of simultaneous diagonalization of a commuting family of Hermitian operators.

The argument is the standard one: over the algebraically closed field `ℂ`, `A` restricted to
the finite-dimensional `W` has an eigenvalue `α` (`Module.End.exists_eigenvalue`); `α` is real
because `A` is self-adjoint (`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`).  Since `B`
commutes with `A` and preserves `W`, it preserves the (nonzero) `α`-eigenspace `S = W ⊓
eigenspace A α`; `B` restricted to `S` has a real eigenvalue `β` with eigenvector `Φ ∈ S`, a
common eigenvector of `A` and `B`.

This is used to discharge Tasaki's Theorem A.17 (`exists_joint_su2_energy_eigenstate`).
-/

open Module Module.End
open scoped ComplexOrder

namespace LatticeSystem.Math

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- An eigenvalue of a self-adjoint operator (witnessed by a nonzero eigenvector) is real: it
equals the complex cast of its real part. -/
theorem isSymmetric_eigenvalue_eq_ofReal {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (hAv : A v = μ • v) : ((μ.re : ℝ) : ℂ) = μ := by
  have hμ : Module.End.HasEigenvalue A μ :=
    hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr hAv, hv⟩
  have hconj := hA.conj_eigenvalue_eq_self hμ
  rwa [Complex.conj_eq_iff_re] at hconj

/-- **Common eigenvector of two commuting self-adjoint operators on an invariant subspace.**
On a finite-dimensional complex inner product space, if `A`, `B` are self-adjoint, commute, and
both preserve a nonzero subspace `W`, then `W` contains a nonzero vector `Φ` that is a
simultaneous eigenvector of `A` and `B` with real eigenvalues `a`, `b`. -/
theorem exists_common_eigenvector_of_isSymmetric_comm {A B : E →ₗ[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : A ∘ₗ B = B ∘ₗ A)
    {W : Submodule ℂ E} (hW : W ≠ ⊥)
    (hWA : ∀ v ∈ W, A v ∈ W) (hWB : ∀ v ∈ W, B v ∈ W) :
    ∃ (Φ : E) (a b : ℝ), Φ ∈ W ∧ Φ ≠ 0 ∧ A Φ = (a : ℂ) • Φ ∧ B Φ = (b : ℂ) • Φ := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  -- An eigenvalue `α` of `A` restricted to `W`, with eigenvector `u ∈ W`.
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (LinearMap.restrict A hWA)
  obtain ⟨u, hu_mem, hu_ne⟩ := hα.exists_hasEigenvector
  have hAu : A (u : E) = α • (u : E) := by
    have h := mem_eigenspace_iff.mp hu_mem
    have h2 := congrArg (fun w : W => (w : E)) h
    simpa [LinearMap.restrict_apply] using h2
  have hu_ne_E : (u : E) ≠ 0 := fun h => hu_ne (Submodule.coe_eq_zero.mp h)
  have hα_re : ((α.re : ℝ) : ℂ) = α := isSymmetric_eigenvalue_eq_ofReal hA hu_ne_E hAu
  -- The `α`-eigenspace of `A` inside `W` is nonzero and `B`-invariant.
  set S : Submodule ℂ E := W ⊓ Module.End.eigenspace A α with hS
  have huS : (u : E) ∈ S := ⟨u.2, mem_eigenspace_iff.mpr hAu⟩
  have hS_ne : S ≠ ⊥ := by
    intro h; rw [h, Submodule.mem_bot] at huS; exact hu_ne_E huS
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS_ne
  have hSB : ∀ w ∈ S, B w ∈ S := by
    intro w hw
    refine Submodule.mem_inf.mpr ⟨hWB w hw.1, ?_⟩
    rw [mem_eigenspace_iff]
    have hAw : A w = α • w := mem_eigenspace_iff.mp hw.2
    have hcomm : A (B w) = B (A w) := by
      have hc := LinearMap.congr_fun hAB w
      simpa only [LinearMap.comp_apply] using hc
    rw [hcomm, hAw, map_smul]
  -- An eigenvalue `β` of `B` restricted to `S`, with eigenvector `Φ ∈ S`.
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict B hSB)
  obtain ⟨φ, hφ_mem, hφ_ne⟩ := hβ.exists_hasEigenvector
  have hBφ : B (φ : E) = β • (φ : E) := by
    have h := mem_eigenspace_iff.mp hφ_mem
    have h2 := congrArg (fun w : S => (w : E)) h
    simpa [LinearMap.restrict_apply] using h2
  have hφ_ne_E : (φ : E) ≠ 0 := fun h => hφ_ne (Submodule.coe_eq_zero.mp h)
  have hβ_re : ((β.re : ℝ) : ℂ) = β := isSymmetric_eigenvalue_eq_ofReal hB hφ_ne_E hBφ
  have hφ_S : (φ : E) ∈ S := φ.2
  have hAφ : A (φ : E) = α • (φ : E) := mem_eigenspace_iff.mp hφ_S.2
  refine ⟨(φ : E), α.re, β.re, hφ_S.1, hφ_ne_E, ?_, ?_⟩
  · rw [hα_re]; exact hAφ
  · rw [hβ_re]; exact hBφ

omit [FiniteDimensional ℂ E] in
/-- A real eigenvalue of a positive operator is nonnegative. -/
theorem isPositive_eigenvalue_nonneg {A : E →ₗ[ℂ] E} (hA : A.IsPositive)
    {a : ℝ} {Φ : E} (hΦ : Φ ≠ 0) (hAΦ : A Φ = (a : ℂ) • Φ) : 0 ≤ a := by
  have h := hA.re_inner_nonneg_right Φ
  rw [hAΦ, inner_smul_right] at h
  have hre : RCLike.re ((a : ℂ) * inner ℂ Φ Φ) = a * ‖Φ‖ ^ 2 := by
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  rw [hre] at h
  have hn : (0 : ℝ) < ‖Φ‖ ^ 2 := by
    have : ‖Φ‖ ≠ 0 := norm_ne_zero_iff.mpr hΦ
    positivity
  exact (mul_nonneg_iff_of_pos_right hn).mp h

/-- **Matrix form: common eigenvector of two commuting Hermitian matrices on an invariant
subspace.**  For Hermitian `A`, `B` with `A * B = B * A`, both preserving a nonzero subspace `W`
of `EuclideanSpace ℂ d`, there is a nonzero common eigenvector `Φ ∈ W` with real eigenvalues. -/
theorem Matrix.exists_common_eigenvector_of_isHermitian_commute {d : Type*} [Fintype d]
    [DecidableEq d] {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A * B = B * A) {W : Submodule ℂ (EuclideanSpace ℂ d)} (hW : W ≠ ⊥)
    (hWA : ∀ v ∈ W, Matrix.toEuclideanLin A v ∈ W)
    (hWB : ∀ v ∈ W, Matrix.toEuclideanLin B v ∈ W) :
    ∃ (Φ : EuclideanSpace ℂ d) (a b : ℝ), Φ ∈ W ∧ Φ ≠ 0 ∧
      Matrix.toEuclideanLin A Φ = (a : ℂ) • Φ ∧ Matrix.toEuclideanLin B Φ = (b : ℂ) • Φ := by
  refine exists_common_eigenvector_of_isSymmetric_comm
    (Matrix.isHermitian_iff_isSymmetric.mp hA) (Matrix.isHermitian_iff_isSymmetric.mp hB)
    ?_ hW hWA hWB
  ext x i
  change Matrix.mulVec A (Matrix.mulVec B (WithLp.ofLp x)) i
    = Matrix.mulVec B (Matrix.mulVec A (WithLp.ofLp x)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB]

/-- **Matrix real-eigenvalue extraction.** A Hermitian matrix `A` over `ℂ` with a nonzero
eigenvector `v` (in `mulVec` form `A *ᵥ v = c • v`) has a real eigenvalue: `c` is the complex cast
of some real `μ` (namely `c.re`).  Bridged to `Matrix.toEuclideanLin` via
`Matrix.isHermitian_iff_isSymmetric` and `isSymmetric_eigenvalue_eq_ofReal`.  This is the reusable
matrix form of the self-adjoint real-spectrum fact (avoiding a private `dotProduct`-based
reimplementation). -/
theorem isHermitian_mulVec_eigenvalue_eq_ofReal {d : Type*} [Fintype d]
    {A : Matrix d d ℂ} (hA : A.IsHermitian) {c : ℂ} {v : d → ℂ}
    (hv : v ≠ 0) (hAv : A.mulVec v = c • v) : ∃ μ : ℝ, (μ : ℂ) = c := by
  classical
  refine ⟨c.re, ?_⟩
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
  have hvne : (WithLp.toLp 2 v : EuclideanSpace ℂ d) ≠ 0 := by
    rw [ne_eq, WithLp.toLp_eq_zero]; exact hv
  have hAv' : Matrix.toEuclideanLin A (WithLp.toLp 2 v) = c • (WithLp.toLp 2 v) := by
    have h1 : Matrix.toEuclideanLin A (WithLp.toLp 2 v) = WithLp.toLp 2 (A.mulVec v) := by
      rw [show Matrix.toEuclideanLin A = Matrix.toLpLin 2 2 A from rfl, Matrix.toLpLin_toLp,
        Matrix.toLin'_apply]
    rw [h1, hAv, WithLp.toLp_smul]
  exact isSymmetric_eigenvalue_eq_ofReal hsym hvne hAv'

/-- **Matrix nonnegative-eigenvalue extraction.**  A positive semidefinite matrix `A` over `ℂ`
with a nonzero real eigenvector `v` (`A *ᵥ v = c • v`, `c : ℝ`) has a nonnegative eigenvalue
`0 ≤ c`, because the quadratic form `star v ⬝ᵥ (A *ᵥ v) = c · ‖v‖²` is `≥ 0` and `‖v‖² > 0`. -/
theorem Matrix.posSemidef_mulVec_eigenvalue_nonneg {d : Type*} [Fintype d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) {v : d → ℂ} {c : ℝ}
    (hv : v ≠ 0) (hAv : A.mulVec v = (c : ℂ) • v) : 0 ≤ c := by
  classical
  have hquad : (0 : ℂ) ≤ dotProduct (star v) (A.mulVec v) := hA.dotProduct_mulVec_nonneg v
  have hnorm : dotProduct (star v) v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by rw [Complex.normSq_eq_conj_mul_self])
  have hpos : 0 < (∑ i, Complex.normSq (v i) : ℝ) := by
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
    rw [Pi.zero_apply] at hi₀
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      ⟨i₀, Finset.mem_univ _, Complex.normSq_pos.mpr hi₀⟩
  rw [hAv, dotProduct_smul, smul_eq_mul, hnorm] at hquad
  rw [show (c : ℂ) * ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)
      = ((c * (∑ i, Complex.normSq (v i)) : ℝ) : ℂ) by push_cast; ring] at hquad
  have hcs : 0 ≤ c * (∑ i, Complex.normSq (v i) : ℝ) := by
    rwa [← Complex.ofReal_zero, Complex.real_le_real] at hquad
  exact le_of_mul_le_mul_right (by rw [zero_mul]; exact hcs) hpos

end LatticeSystem.Math
