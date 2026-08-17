import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Low-energy eigenvector inside an invariant submodule

Generic finite-dimensional linear algebra: if a Hermitian matrix `H` preserves a submodule `p` of
`n → ℂ`, then `p` contains an eigenvector of `H` whose (real) eigenvalue is at most the Rayleigh
quotient of any unit vector of `p`.  Restricting the extraction to `p` is what distinguishes this
statement from ambient minimisation: three ambient minimisations may all return the *same*
eigenvector, whereas three pairwise-orthogonal invariant submodules return three independent ones.

The proof restricts `Matrix.toEuclideanLin H` to the sector, minimises `reApplyInnerSelf` on the
sphere through the given unit vector, and reads off the eigenvector from
`IsSelfAdjoint.hasEigenvector_of_isLocalExtrOn`, whose eigenvalue is the Rayleigh quotient at the
minimiser.  No infimum over the punctured space is formed, so no `BddBelow` side condition arises.
-/

namespace LatticeSystem.Math

open Matrix Metric LatticeSystem.Quantum

variable {n : Type*} [Fintype n]

/-- The transport of a submodule of `n → ℂ` to the `L²` space `EuclideanSpace ℂ n`, along the
canonical linear equivalence.  Membership is definitionally `WithLp.ofLp v ∈ p`. -/
private noncomputable def euclideanSector (p : Submodule ℂ (n → ℂ)) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  p.comap (WithLp.linearEquiv 2 ℂ (n → ℂ)).toLinearMap

/-- Membership in the transported sector is membership of the underlying vector. -/
private theorem mem_euclideanSector {p : Submodule ℂ (n → ℂ)} {v : EuclideanSpace ℂ n} :
    v ∈ euclideanSector p ↔ WithLp.ofLp v ∈ p := Iff.rfl

/-- **A Hermitian matrix has, inside any invariant submodule, an eigenvector whose eigenvalue is at
most the Rayleigh quotient of any prescribed nonzero vector of that submodule.**  Combined with the
`Z₂ × Z₂` character sectors this delivers three *independent* low-lying eigenvectors, which a plain
ambient variational extraction cannot guarantee.  The bound is stated for the scale-invariant
Rayleigh quotient, so no normalisation of the trial vector is required. -/
theorem exists_sector_eigenvector_energy_le_rayleigh
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (p : Submodule ℂ (n → ℂ))
    (hInv : ∀ v ∈ p, H.mulVec v ∈ p)
    {Gamma : n → ℂ} (hGammaMem : Gamma ∈ p) (hGammaNe : Gamma ≠ 0) :
    ∃ E : ℝ, ∃ Psi : n → ℂ,
      Psi ∈ p ∧ Psi ≠ 0 ∧
      H.mulVec Psi = (E : ℂ) • Psi ∧
      E ≤ rayleighOnVec H Gamma / (star Gamma ⬝ᵥ Gamma).re := by
  classical
  haveI : ProperSpace (EuclideanSpace ℂ n) :=
    FiniteDimensional.proper_rclike ℂ (EuclideanSpace ℂ n)
  set q : Submodule ℂ (EuclideanSpace ℂ n) := euclideanSector p with hqdef
  have hqInv : ∀ v ∈ q, Matrix.toEuclideanLin H v ∈ q := fun v hv =>
    (mem_euclideanSector).mpr
      (by
        rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
        exact hInv _ ((mem_euclideanSector).mp hv))
  have hsym : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hH
  have hres := hsym.restrict_invariant hqInv
  -- The adjoint/star structure on `↥q →L[ℂ] ↥q` needs completeness at the `NormedAddCommGroup`
  -- instance path, which is only definitionally (not syntactically) the one instance search finds.
  haveI : @CompleteSpace (↥q)
      (@PseudoMetricSpace.toUniformSpace (↥q)
        (@SeminormedAddCommGroup.toPseudoMetricSpace (↥q)
          (@NormedAddCommGroup.toSeminormedAddCommGroup (↥q)
            (Submodule.normedAddCommGroup q)))) := inferInstanceAs (CompleteSpace q)
  set T := hres.toSelfAdjoint with hTdef
  set G : q := ⟨WithLp.toLp 2 Gamma, hGammaMem⟩ with hGdef
  have hGne : G ≠ 0 := by
    intro h
    exact hGammaNe (WithLp.toLp_injective 2 (congrArg Subtype.val h))
  have hGpos : 0 < ‖G‖ := norm_pos_iff.mpr hGne
  have hGsq : ‖G‖ ^ 2 = (star Gamma ⬝ᵥ Gamma).re := by
    have h := @norm_sq_eq_re_inner ℂ q _ _ _ G
    rw [h, Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct, hGdef]
    change ((Gamma ⬝ᵥ star Gamma).re : ℝ) = (star Gamma ⬝ᵥ Gamma).re
    rw [dotProduct_comm, Matrix.star_dotProduct, Complex.star_def, Complex.conj_re]
  have hcompact : IsCompact (sphere (0 : q) ‖G‖) := isCompact_sphere _ _
  have hne : (sphere (0 : q) ‖G‖).Nonempty := ⟨G, mem_sphere_zero_iff_norm.mpr rfl⟩
  obtain ⟨x₀, hx₀mem, hmin⟩ :=
    hcompact.exists_isMinOn hne (T.val.reApplyInnerSelf_continuous).continuousOn
  have hx₀norm : ‖x₀‖ = ‖G‖ := mem_sphere_zero_iff_norm.mp hx₀mem
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx₀norm
    exact hGpos.ne hx₀norm
  have hextr : IsMinOn T.val.reApplyInnerSelf (sphere (0 : q) ‖x₀‖) x₀ := by
    rw [hx₀norm]; exact hmin
  have hev := T.prop.hasEigenvector_of_isLocalExtrOn hx₀ne (Or.inl hextr.localize)
  refine ⟨T.val.rayleighQuotient x₀, WithLp.ofLp (x₀ : EuclideanSpace ℂ n), x₀.2, ?_, ?_, ?_⟩
  · intro h
    exact hx₀ne (Subtype.ext (WithLp.ofLp_injective 2 (by simpa using h)))
  · have heig : (T.val x₀ : q) = ((T.val.rayleighQuotient x₀ : ℝ) : ℂ) • x₀ :=
      Module.End.mem_eigenspace_iff.mp hev.1
    have hcoe : ((T.val x₀ : q) : EuclideanSpace ℂ n)
        = Matrix.toEuclideanLin H (x₀ : EuclideanSpace ℂ n) := rfl
    have hlift := congrArg (fun z : q => WithLp.ofLp (z : EuclideanSpace ℂ n)) heig
    simpa [hcoe, Matrix.ofLp_toLpLin, Matrix.toLin'_apply] using hlift
  · have hGsphere : G ∈ sphere (0 : q) ‖G‖ := mem_sphere_zero_iff_norm.mpr rfl
    have hle : T.val.reApplyInnerSelf x₀ ≤ T.val.reApplyInnerSelf G := hmin hGsphere
    have hray : T.val.rayleighQuotient x₀
        = T.val.reApplyInnerSelf x₀ / (star Gamma ⬝ᵥ Gamma).re := by
      rw [ContinuousLinearMap.rayleighQuotient, hx₀norm, hGsq]
    have hGray : T.val.reApplyInnerSelf G = rayleighOnVec H Gamma := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      have hcoe : ((T.val G : q) : EuclideanSpace ℂ n)
          = Matrix.toEuclideanLin H (G : EuclideanSpace ℂ n) := rfl
      rw [Submodule.coe_inner, hcoe, EuclideanSpace.inner_eq_star_dotProduct,
        Matrix.ofLp_toLpLin, Matrix.toLin'_apply, hGdef, rayleighOnVec]
      change (Gamma ⬝ᵥ star (H.mulVec Gamma)).re = (star Gamma ⬝ᵥ H.mulVec Gamma).re
      rw [dotProduct_comm, Matrix.star_dotProduct, Complex.star_def, Complex.conj_re]
    rw [hray, ← hGray]
    have hpos : 0 < (star Gamma ⬝ᵥ Gamma).re := by
      rw [← hGsq]; positivity
    exact (div_le_div_iff_of_pos_right hpos).mpr hle

end LatticeSystem.Math
