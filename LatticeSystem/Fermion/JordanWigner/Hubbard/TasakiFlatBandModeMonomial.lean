import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeCreation
import LatticeSystem.Math.ListProdMulVec

/-!
# Tasaki §11.3.1: the rotated-basis Fock monomials span (towards Theorem 11.11 uniqueness)

The `{α} ∪ {β}` single-particle basis (`flatBandBasis`) lifts to a many-body **rotated occupation
basis**: ordered products of mode-creations `Ĉ†_σ(basis i)` on the vacuum.  We define the span
`flatBandModeFockSubmodule` of these monomials and prove it is invariant under every *site* creation
`ĉ†_{x,σ}` (because a site creation is a finite linear combination of the `â†`/`b̂†`, each of which
prepends one mode to a monomial).  Since any standard computational basis vector is an ordered
product of site creations on the vacuum, the span is the whole space — the Fock factorisation
foundation for `flatBandBKernelSubmodule ⊆ flatBandAlphaFockSubmodule`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Lemma 11.10.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

/-- A **rotated-basis Fock monomial**: the ordered product of mode-creations
`Ĉ†_{σ}(flatBandBasis i)` (for `(i, σ)` ranging over the list `qs`) applied to the vacuum. -/
noncomputable def flatBandModeMonomial (K : ℕ) (ν : ℝ)
    (qs : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  ((qs.map (fun q => flatBandModeCreation K q.2 (flatBandBasis K ν q.1))).prod).mulVec
    (fermionMultiVacuum (2 * (2 * K + 1) + 1))

/-- The span of all rotated-basis Fock monomials. -/
noncomputable def flatBandModeFockSubmodule (K : ℕ) (ν : ℝ) :
    Submodule ℂ ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ (Set.range (flatBandModeMonomial K ν))

variable {K : ℕ} {ν : ℝ}

/-- Every rotated-basis Fock monomial lies in the span. -/
theorem flatBandModeMonomial_mem (qs : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    flatBandModeMonomial K ν qs ∈ flatBandModeFockSubmodule K ν :=
  Submodule.subset_span ⟨qs, rfl⟩

/-- Prepending a mode-creation to a monomial conses `(i, σ)` onto its list. -/
theorem flatBandModeCreation_mulVec_monomial (i : Fin (K + 1) ⊕ Fin (K + 1)) (σ : Fin 2)
    (qs : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    (flatBandModeCreation K σ (flatBandBasis K ν i)).mulVec (flatBandModeMonomial K ν qs)
      = flatBandModeMonomial K ν ((i, σ) :: qs) := by
  unfold flatBandModeMonomial
  rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]

/-- The span is invariant under each mode-creation `Ĉ†_σ(basis i)`. -/
theorem flatBandModeCreation_basis_mulVec_mem (i : Fin (K + 1) ⊕ Fin (K + 1)) (σ : Fin 2)
    {w : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hw : w ∈ flatBandModeFockSubmodule K ν) :
    (flatBandModeCreation K σ (flatBandBasis K ν i)).mulVec w ∈ flatBandModeFockSubmodule K ν := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨qs, rfl⟩
    rw [flatBandModeCreation_mulVec_monomial]
    exact flatBandModeMonomial_mem _
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

/-- The span is invariant under every *site* creation `ĉ†_{x,σ}`, because the site creation is the
`flatBandBasis`-expansion combination `∑_i (repr) i • Ĉ†_σ(basis i)` of the mode-creations. -/
theorem fermionMultiCreation_spinful_mulVec_mem (x : Fin (2 * K + 2)) (σ : Fin 2)
    {w : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hw : w ∈ flatBandModeFockSubmodule K ν) :
    (fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)).mulVec w
      ∈ flatBandModeFockSubmodule K ν := by
  rw [← flatBandModeCreation_single K σ x]
  have hrepr : flatBandModeCreation K σ (Pi.single x 1)
      = ∑ i, (flatBandBasis K ν).repr (Pi.single x 1) i •
          flatBandModeCreation K σ (flatBandBasis K ν i) := by
    conv_lhs => rw [← (flatBandBasis K ν).sum_repr (Pi.single x (1 : ℂ))]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  rw [hrepr, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (flatBandModeCreation_basis_mulVec_mem i σ hw)

end LatticeSystem.Fermion
