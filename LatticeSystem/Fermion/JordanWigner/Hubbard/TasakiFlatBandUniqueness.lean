import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPeel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSubspaces

/-!
# Tasaki §11.3.1: `BKernel ⊆ AlphaFock` (the flat-band uniqueness inclusion)

Combining the dual-annihilator occupation projector with the rotated occupation basis: a vector in
the `b̂`-kernel has no β-occupation in its basis expansion (each `d_{u,σ}` annihilates it,
so `b̂†_{u,σ} d_{u,σ}` kills it, forcing the β-occupied coordinates to vanish by basis
independence), hence lies in the span of the β-free occupation monomials, which is the α-Fock
subspace.  This is the hard inclusion of Tasaki's flat-band uniqueness (Theorem 11.11).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **The dual annihilator kills every `b̂`-kernel vector** (it is a linear combination of the
`b̂_{v,σ}`, each of which annihilates the vector). -/
theorem flatBandDualBAnnihilation_mulVec_eq_zero_of_mem_BKernel (u : Fin (K + 1)) (σ : Fin 2)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hv : v ∈ flatBandBKernelSubmodule K ν) :
    (flatBandDualBAnnihilation K ν u σ).mulVec v = 0 := by
  rw [flatBandDualBAnnihilation, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [Matrix.smul_mulVec, (mem_flatBandBKernelSubmodule_iff K ν).mp hv w σ, smul_zero]

/-- The occupation basis vectors are the occupation monomials. -/
theorem flatBandOccBasis_apply (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    flatBandOccBasis K ν f = occMonomial K ν f :=
  congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) f

/-- **A `b̂`-kernel vector has no β-occupied coordinate.**  Applying the projector
`b̂†_{u,σ} d_{u,σ}` (which kills `v` since `d_{u,σ} v = 0`) and reading off the occupation-basis
coordinate of any config `g` with the β-mode `(inr u, σ)` occupied gives `0`. -/
theorem flatBandOccBasis_repr_eq_zero_of_mem_BKernel (u : Fin (K + 1)) (σ : Fin 2)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hv : v ∈ flatBandBKernelSubmodule K ν)
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2} (hg : (Sum.inr u, σ) ∈ occFinset g) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  have hPv : (flatBandBCreation K ν u σ).mulVec
      ((flatBandDualBAnnihilation K ν u σ).mulVec v) = 0 := by
    rw [flatBandDualBAnnihilation_mulVec_eq_zero_of_mem_BKernel u σ hv, Matrix.mulVec_zero]
  have hsum : (flatBandBCreation K ν u σ).mulVec ((flatBandDualBAnnihilation K ν u σ).mulVec v)
      = ∑ f, (flatBandOccBasis K ν).repr v f •
          (if (Sum.inr u, σ) ∈ occFinset f then occMonomial K ν f else 0) := by
    conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
    simp only [flatBandOccBasis_apply, Matrix.mulVec_sum, Matrix.mulVec_smul,
      flatBandBCreation_dual_mulVec_occMonomial]
  rw [hsum] at hPv
  have hLI : ∑ f, (if (Sum.inr u, σ) ∈ occFinset f then (flatBandOccBasis K ν).repr v f else 0) •
      flatBandOccBasis K ν f = 0 := by
    rw [← hPv]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [flatBandOccBasis_apply]
    split_ifs <;> simp
  have hcoeff := Fintype.linearIndependent_iff.mp (flatBandOccBasis K ν).linearIndependent _ hLI g
  simpa [if_pos hg] using hcoeff

/-- Prepending an `α`-creation to an `α`-Slater state extends its mode list. -/
theorem flatBandACreation_mulVec_alphaSlaterState (p : Fin (K + 1)) (σ : Fin 2)
    (qs : List (Fin (K + 1) × Fin 2)) :
    (flatBandACreation K ν p σ).mulVec (flatBandAlphaSlaterState K ν qs)
      = flatBandAlphaSlaterState K ν ((p, σ) :: qs) := by
  unfold flatBandAlphaSlaterState
  rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]

/-- The `α`-Fock subspace is invariant under every `α`-creation `â†_{p,σ}`. -/
theorem flatBandACreation_mulVec_alphaFock_mem (p : Fin (K + 1)) (σ : Fin 2)
    {w : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hw : w ∈ flatBandAlphaFockSubmodule K ν) :
    (flatBandACreation K ν p σ).mulVec w ∈ flatBandAlphaFockSubmodule K ν := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨qs, rfl⟩
    rw [flatBandACreation_mulVec_alphaSlaterState]
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

/-- The vacuum lies in the `α`-Fock subspace (the empty `α`-Slater state). -/
theorem fermionMultiVacuum_mem_alphaFock :
    fermionMultiVacuum (2 * (2 * K + 1) + 1) ∈ flatBandAlphaFockSubmodule K ν := by
  have h0 : flatBandAlphaSlaterState K ν [] = fermionMultiVacuum (2 * (2 * K + 1) + 1) := by
    simp [flatBandAlphaSlaterState]
  rw [← h0]
  exact Submodule.subset_span ⟨[], rfl⟩

/-- **A β-free occupation monomial lies in the `α`-Fock subspace.**  Its creations are all
`α`-creations, under which `α`-Fock is invariant (with the vacuum inside). -/
theorem occMonomial_mem_alphaFock_of_betaFree
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    (hf : ∀ u σ, (Sum.inr u, σ) ∉ occFinset f) :
    occMonomial K ν f ∈ flatBandAlphaFockSubmodule K ν := by
  rw [occMonomial, flatBandModeMonomial]
  refine LatticeSystem.Math.listProd_mulVec_mem (fun M hM w hwmem => ?_)
    fermionMultiVacuum_mem_alphaFock
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hM
  obtain ⟨q1, q2⟩ := q
  rcases q1 with p | u
  · rw [show flatBandModeCreation K q2 (flatBandBasis K ν (Sum.inl p)) = flatBandACreation K ν p q2
        from by rw [flatBandModeCreation_basis, Sum.elim_inl]]
    exact flatBandACreation_mulVec_alphaFock_mem p q2 hwmem
  · exact absurd (Finset.mem_toList.mp hq) (hf u q2)

/-- **Tasaki §11.3.1 flat-band uniqueness inclusion: `BKernel ⊆ AlphaFock`.**  Expand a `b̂`-kernel
vector in the occupation basis; its β-occupied coordinates vanish, so it is a combination of β-free
occupation monomials, each in the `α`-Fock subspace. -/
theorem flatBandBKernelSubmodule_le_alphaFockSubmodule (K : ℕ) (ν : ℝ) :
    flatBandBKernelSubmodule K ν ≤ flatBandAlphaFockSubmodule K ν := by
  intro v hv
  rw [← (flatBandOccBasis K ν).sum_repr v]
  refine Submodule.sum_mem _ (fun f _ => ?_)
  rw [flatBandOccBasis_apply]
  by_cases hf : ∀ u σ, (Sum.inr u, σ) ∉ occFinset f
  · exact Submodule.smul_mem _ _ (occMonomial_mem_alphaFock_of_betaFree f hf)
  · simp only [not_forall, not_not] at hf
    obtain ⟨u, σ, hocc⟩ := hf
    rw [flatBandOccBasis_repr_eq_zero_of_mem_BKernel u σ hv hocc, zero_smul]
    exact Submodule.zero_mem _

end LatticeSystem.Fermion
