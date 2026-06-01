import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Eigenvectors in invariant submodules

This module packages a small finite-dimensional linear-algebra bridge used by
the Tasaki §2.5 Problem 2.5.a single-cluster sector-decomposition route.

If a non-zero submodule is invariant under an endomorphism over an algebraically
closed field, then restricting the endomorphism to that submodule gives a
non-zero finite-dimensional endomorphism, hence an eigenvector.  Forgetting the
subtype gives an eigenvector of the original endomorphism which still lies in
the submodule.
-/

namespace LatticeSystem.Math

open Module

variable {K E : Type*} [Field K] [IsAlgClosed K]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- **Eigenvector in a non-zero invariant submodule**: if `p` is a non-zero
submodule invariant under `f`, then `f` has a non-zero eigenvector lying in
`p`.

The invariant-submodule hypothesis is written as `p ≤ p.comap f`, i.e. every
`x ∈ p` satisfies `f x ∈ p`. -/
theorem exists_eigenvector_in_invariant_submodule
    (f : Module.End K E) (p : Submodule K E)
    (hp : p ≤ p.comap f)
    (hne : p ≠ ⊥) :
    ∃ μ : K, ∃ v : E, v ∈ p ∧ v ≠ 0 ∧ f v = μ • v := by
  obtain ⟨x, hx_mem, hx_ne⟩ : ∃ x : E, x ∈ p ∧ x ≠ 0 := by
    by_contra h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    by_contra hx_ne
    exact h ⟨x, hx, hx_ne⟩
  haveI : Nontrivial p := by
    exact ⟨⟨⟨x, hx_mem⟩, 0, by
      intro hzero
      exact hx_ne (congrArg Subtype.val hzero)⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict f hp)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff] at hw
  obtain ⟨hw_mem, hw_ne⟩ := hw
  refine ⟨μ, w, w.property, ?_, ?_⟩
  · intro hzero
    exact hw_ne (Subtype.ext hzero)
  · have happ := (Module.End.mem_eigenspace_iff).mp hw_mem
    have hsub : (LinearMap.restrict f hp) w = μ • w := happ
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val hsub

end LatticeSystem.Math
