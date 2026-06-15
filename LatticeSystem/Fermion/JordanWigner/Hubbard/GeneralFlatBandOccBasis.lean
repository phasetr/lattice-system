import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandModeMonomial
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# General flat-band occupation basis (Tasaki §11.3.4, toward eq. (11.3.46))

The general-basis Fock monomials (`GeneralFlatBandModeMonomial.lean`) are reordered into a canonical
(occupation-config) form, giving a **basis** of the many-body space indexed by occupation
configurations of the `2(M+1)` mode-spin slots.  This is the general-basis analogue of
`TasakiFlatBandOccBasis.lean` / `ModeReorder.lean`, valid for any single-particle basis `e`; it is
instantiated at the spectral eigenbasis of the hopping matrix `T` in the eq. (11.3.46) Fock-spanning
step.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.46).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- Swapping the first two factors of a general-basis Fock monomial negates it (the two leading
creations anticommute). -/
theorem generalModeMonomial_swap (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (x y : Fin (M + 1) × Fin 2) (l : List (Fin (M + 1) × Fin 2)) :
    generalModeMonomial e (y :: x :: l) = -generalModeMonomial e (x :: y :: l) := by
  unfold generalModeMonomial
  simp only [List.map_cons, List.prod_cons]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    eq_neg_of_add_eq_zero_left
      (spinfulFromVector_creation_creation_anticomm M (e y.1) (e x.1) y.2 x.2),
    Matrix.neg_mul, Matrix.neg_mulVec]

/-- **Reordering a general-basis Fock monomial scales it.**  Permuting the creation list multiplies
the monomial by a nonzero (sign) scalar — enough for the spanning/basis argument. -/
theorem generalModeMonomial_perm (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    {l l' : List (Fin (M + 1) × Fin 2)} (h : l.Perm l') :
    ∃ z : ℂ, z ≠ 0 ∧ generalModeMonomial e l = z • generalModeMonomial e l' := by
  induction h with
  | nil => exact ⟨1, one_ne_zero, by rw [one_smul]⟩
  | cons x _ ih =>
    obtain ⟨z, hz0, hz⟩ := ih
    refine ⟨z, hz0, ?_⟩
    rw [← spinfulCreation_mulVec_generalModeMonomial e x.1 x.2, hz, Matrix.mulVec_smul,
      spinfulCreation_mulVec_generalModeMonomial e x.1 x.2]
  | swap x y l =>
    exact ⟨-1, neg_ne_zero.mpr one_ne_zero, by rw [generalModeMonomial_swap, neg_one_smul]⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁0, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂0, hz₂⟩ := ih₂
    exact ⟨z₁ * z₂, mul_ne_zero hz₁0 hz₂0, by rw [hz₁, hz₂, smul_smul]⟩

/-- The square of a mode creation vanishes (`(Ĉ†_σ(e i))² = 0`). -/
theorem generalModeCreation_sq (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (i : Fin (M + 1)) (σ : Fin 2) :
    spinfulCreationFromVector M (e i) σ * spinfulCreationFromVector M (e i) σ = 0 :=
  spinfulCreationFromVector_sq M (e i) σ

/-- **Prepending an already-present mode to a monomial kills it.** -/
theorem generalModeMonomial_cons_mem_eq_zero
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (q : Fin (M + 1) × Fin 2)
    (l : List (Fin (M + 1) × Fin 2)) (hq : q ∈ l) :
    generalModeMonomial e (q :: l) = 0 := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hq
  obtain ⟨z, _, hz⟩ := generalModeMonomial_perm e (List.perm_middle.cons q)
  rw [hz]
  have : generalModeMonomial e (q :: q :: (s ++ t)) = 0 := by
    unfold generalModeMonomial
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mul_assoc, generalModeCreation_sq, Matrix.zero_mul, Matrix.zero_mulVec]
  rw [this, smul_zero]

/-- The occupied-mode finset of an occupation config. -/
def generalOccFinset (f : Fin (M + 1) × Fin 2 → Fin 2) : Finset (Fin (M + 1) × Fin 2) :=
  Finset.univ.filter (fun q => f q = 1)

/-- A **general occupation monomial**: the product of the occupied mode creations on the vacuum. -/
noncomputable def generalOccMonomial (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (f : Fin (M + 1) × Fin 2 → Fin 2) : (Fin (2 * M + 2) → Fin 2) → ℂ :=
  generalModeMonomial e (generalOccFinset f).toList

/-- `generalOccMonomial f` lies in the monomial span. -/
theorem generalOccMonomial_mem (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (f : Fin (M + 1) × Fin 2 → Fin 2) :
    generalOccMonomial e f ∈ generalModeFockSubmodule e :=
  generalModeMonomial_mem _ _

/-- Setting mode `q` to occupied inserts it into the occupied finset. -/
theorem generalOccFinset_update_one (f : Fin (M + 1) × Fin 2 → Fin 2)
    {q : Fin (M + 1) × Fin 2} :
    generalOccFinset (Function.update f q 1) = insert q (generalOccFinset f) := by
  ext q'
  simp only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Function.update_apply]
  by_cases h : q' = q <;> simp [h]

/-- A list-monomial with a repeated mode vanishes. -/
theorem generalModeMonomial_eq_zero_of_not_nodup
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (l : List (Fin (M + 1) × Fin 2))
    (hl : ¬ l.Nodup) :
    generalModeMonomial e l = 0 := by
  induction l with
  | nil => exact absurd List.nodup_nil hl
  | cons a l' ih =>
    by_cases ha : a ∈ l'
    · exact generalModeMonomial_cons_mem_eq_zero e a l' ha
    · have hl' : ¬ l'.Nodup := fun h => hl (List.nodup_cons.mpr ⟨ha, h⟩)
      rw [← spinfulCreation_mulVec_generalModeMonomial e a.1 a.2, ih hl', Matrix.mulVec_zero]

/-- Every general-basis list-monomial lies in the span of the occupation monomials. -/
theorem generalModeMonomial_mem_span_occMonomial
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (l : List (Fin (M + 1) × Fin 2)) :
    generalModeMonomial e l ∈ Submodule.span ℂ (Set.range (generalOccMonomial e)) := by
  by_cases hl : l.Nodup
  · have hocc : generalOccFinset (fun q => if q ∈ l.toFinset then 1 else 0) = l.toFinset := by
      ext q
      simp only [generalOccFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : q ∈ l.toFinset <;> simp [h]
    have hperm : l.Perm (generalOccFinset (fun q => if q ∈ l.toFinset then 1 else 0)).toList := by
      rw [hocc]
      exact (List.toFinset_toList hl).symm
    obtain ⟨z, _, hz⟩ := generalModeMonomial_perm e hperm
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [generalModeMonomial_eq_zero_of_not_nodup e l hl]
    exact Submodule.zero_mem _

/-- **The occupation monomials span the whole space.** -/
theorem span_range_generalOccMonomial_eq_top
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) :
    Submodule.span ℂ (Set.range (generalOccMonomial e)) = ⊤ := by
  rw [eq_top_iff, ← generalModeFockSubmodule_eq_top (e := e), generalModeFockSubmodule,
    Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact generalModeMonomial_mem_span_occMonomial e l

/-- **The general occupation basis of the many-body space** (Tasaki §11.3.4): the
`generalOccMonomial` family, indexed by occupation configs of the `2(M+1)` mode-spin slots, is a
basis of the full Fock space (it spans `⊤` and there are `2^(2(M+1)) = finrank` of them). -/
noncomputable def generalOccBasis (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) :
    Module.Basis (Fin (M + 1) × Fin 2 → Fin 2) ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  basisOfTopLeSpanOfCardEqFinrank (generalOccMonomial e)
    (top_le_iff.mpr (span_range_generalOccMonomial_eq_top e))
    (by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_prod,
        Fintype.card_fin]
      ring)

end LatticeSystem.Fermion
