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

/-- **Joint eigenvector in a non-zero invariant submodule**: if a non-zero
submodule is invariant under two commuting endomorphisms, then it contains a
non-zero simultaneous eigenvector for both endomorphisms. -/
theorem exists_joint_eigenvector_in_invariant_submodule
    (f g : Module.End K E) (p : Submodule K E)
    (hf : p ≤ p.comap f)
    (hg : p ≤ p.comap g)
    (hcomm : Commute f g)
    (hne : p ≠ ⊥) :
    ∃ lam μ : K, ∃ v : E, v ∈ p ∧ v ≠ 0 ∧ f v = lam • v ∧ g v = μ • v := by
  obtain ⟨lam, w, hw_mem, hw_ne, hw_f⟩ :=
    exists_eigenvector_in_invariant_submodule f p hf hne
  let q : Submodule K E := p ⊓ Module.End.eigenspace f lam
  have hw_q : w ∈ q := by
    refine ⟨hw_mem, ?_⟩
    exact (Module.End.mem_eigenspace_iff).mpr hw_f
  have hq_ne : q ≠ ⊥ := by
    intro hq
    have hw_zero : w = 0 := by
      have : w ∈ (⊥ : Submodule K E) := by
        simpa [hq] using hw_q
      simpa using this
    exact hw_ne hw_zero
  have hgq : q ≤ q.comap g := by
    intro x hx
    obtain ⟨hx_p, hx_eig⟩ := hx
    refine ⟨hg hx_p, ?_⟩
    have hx_eig_eq : f x = lam • x :=
      (Module.End.mem_eigenspace_iff).mp hx_eig
    exact (Module.End.mem_eigenspace_iff).mpr <| by
      calc
        f (g x) = (f * g) x := rfl
        _ = (g * f) x := by rw [hcomm.eq]
        _ = g (f x) := rfl
        _ = g (lam • x) := by rw [hx_eig_eq]
        _ = lam • g x := by rw [map_smul]
  obtain ⟨μ, v, hv_q, hv_ne, hv_g⟩ :=
    exists_eigenvector_in_invariant_submodule g q hgq hq_ne
  obtain ⟨hv_p, hv_f_mem⟩ := hv_q
  have hv_f : f v = lam • v := by
    exact (Module.End.mem_eigenspace_iff).mp hv_f_mem
  exact ⟨lam, μ, v, hv_p, hv_ne, hv_f, hv_g⟩

end LatticeSystem.Math
