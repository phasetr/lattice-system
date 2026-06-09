import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeReorder
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Tasaki §11.3.1: the rotated occupation basis (towards `BKernel ⊆ AlphaFock`)

Indexing the rotated Fock monomials by occupation configs of the modes
`ι = (Fin(K+1) ⊕ Fin(K+1)) × Fin 2` (card `4K+4`), we obtain `occMonomial f` = the product of the
occupied mode creations on the vacuum.  These span the whole space (the span is invariant under
every site creation and contains the vacuum, so it contains every `basisVec`), and there are
`2^(4K+4) = finrank V` of them, so they form a **basis** of `V`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- The occupied-mode finset of an occupation config. -/
def occFinset (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    Finset ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2) :=
  Finset.univ.filter (fun q => f q = 1)

/-- A **rotated occupation monomial**: the product of the occupied mode creations on the vacuum. -/
noncomputable def occMonomial (K : ℕ) (ν : ℝ)
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  flatBandModeMonomial K ν (occFinset f).toList

/-- `occMonomial f` lies in the rotated-monomial span. -/
theorem occMonomial_mem (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    occMonomial K ν f ∈ flatBandModeFockSubmodule K ν :=
  flatBandModeMonomial_mem _

/-- Setting mode `q` to occupied inserts it into the occupied finset. -/
theorem occFinset_update_one (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2)
    {q : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2} :
    occFinset (Function.update f q 1) = insert q (occFinset f) := by
  ext q'
  simp only [occFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Function.update_apply]
  by_cases h : q' = q <;> simp [h]

/-- **The span is invariant under each mode creation `Ĉ†_σ(basis i)`** (occupation form): prepending
`(i, σ)` either repeats an occupied mode (giving `0`) or extends the occupation (giving a scalar
multiple of the extended `occMonomial`, by the reorder lemma). -/
theorem flatBandModeCreation_basis_mulVec_occMonomial_mem
    (i : Fin (K + 1) ⊕ Fin (K + 1)) (σ : Fin 2)
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    (flatBandModeCreation K σ (flatBandBasis K ν i)).mulVec (occMonomial K ν f)
      ∈ flatBandModeFockSubmodule K ν := by
  rw [occMonomial, flatBandModeCreation_mulVec_monomial i σ]
  by_cases h : (i, σ) ∈ occFinset f
  · rw [flatBandModeMonomial_cons_mem_eq_zero (i, σ) _ (Finset.mem_toList.mpr h)]
    exact Submodule.zero_mem _
  · have hperm : ((i, σ) :: (occFinset f).toList).Perm
        (occFinset (Function.update f (i, σ) 1)).toList := by
      rw [occFinset_update_one f]
      exact (Finset.toList_insert h).symm
    obtain ⟨z, hz⟩ := flatBandModeMonomial_perm (K := K) (ν := ν) hperm
    rw [hz]
    exact Submodule.smul_mem _ _ (occMonomial_mem _)

/-- A list-monomial with a repeated mode vanishes. -/
theorem flatBandModeMonomial_eq_zero_of_not_nodup
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) (hl : ¬ l.Nodup) :
    flatBandModeMonomial K ν l = 0 := by
  induction l with
  | nil => exact absurd List.nodup_nil hl
  | cons a l' ih =>
    by_cases ha : a ∈ l'
    · exact flatBandModeMonomial_cons_mem_eq_zero a l' ha
    · have hl' : ¬ l'.Nodup := fun h => hl (List.nodup_cons.mpr ⟨ha, h⟩)
      rw [← flatBandModeCreation_mulVec_monomial a.1 a.2, ih hl', Matrix.mulVec_zero]

/-- Every rotated list-monomial lies in the span of the occupation monomials (reorder to the sorted
occupied list, or vanish on a repeat). -/
theorem flatBandModeMonomial_mem_span_occMonomial
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    flatBandModeMonomial K ν l ∈ Submodule.span ℂ (Set.range (occMonomial K ν)) := by
  by_cases hl : l.Nodup
  · have hocc : occFinset (fun q => if q ∈ l.toFinset then 1 else 0) = l.toFinset := by
      ext q
      simp only [occFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : q ∈ l.toFinset <;> simp [h]
    have hperm : l.Perm (occFinset (fun q => if q ∈ l.toFinset then 1 else 0)).toList := by
      rw [hocc]
      exact (List.toFinset_toList hl).symm
    obtain ⟨z, hz⟩ := flatBandModeMonomial_perm (K := K) (ν := ν) hperm
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [flatBandModeMonomial_eq_zero_of_not_nodup l hl]
    exact Submodule.zero_mem _

/-- **The occupation monomials span the whole space.** -/
theorem span_range_occMonomial_eq_top :
    Submodule.span ℂ (Set.range (occMonomial K ν)) = ⊤ := by
  rw [eq_top_iff, ← flatBandModeFockSubmodule_eq_top (K := K) (ν := ν),
    flatBandModeFockSubmodule, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact flatBandModeMonomial_mem_span_occMonomial l

/-- **The rotated occupation basis of the many-body space** (Tasaki §11.3.1, Lemma 11.10 lifted to
the many-body level): the `occMonomial` family, indexed by occupation configs of the `4K+4` rotated
modes, is a basis of `V` (it spans `⊤` and there are `2^(4K+4) = finrank V` of them). -/
noncomputable def flatBandOccBasis (K : ℕ) (ν : ℝ) :
    Module.Basis ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) ℂ
      ((Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :=
  basisOfTopLeSpanOfCardEqFinrank (occMonomial K ν)
    (top_le_iff.mpr span_range_occMonomial_eq_top)
    (by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_prod,
        Fintype.card_sum, Fintype.card_fin]
      congr 1
      ring)

end LatticeSystem.Fermion
