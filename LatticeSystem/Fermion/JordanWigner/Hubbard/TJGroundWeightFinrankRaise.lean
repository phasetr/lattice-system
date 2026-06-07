import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightFinrank

/-!
# Tasaki 11.5: weight-space finrank non-increasing toward `Ŝ³ = ½` from below (Prop 11.24 E5b)

The `Ŝ⁺` mirror of `TJGroundWeightFinrank`: for the ground subspace `G`, the raising operator `Ŝ⁺`
maps the `Ŝ³ = sz` weight space of `G` injectively into `Ŝ³ = sz+1` whenever `sz < 0` (raising is
injective on negative weights).  Hence `finrank (G ⊓ Ŝ³=sz) ≤ finrank (G ⊓ Ŝ³=sz+1)` for `sz < 0`,
so iterating from below bounds every negative-weight space by the `Ŝ³ = ½` block (`≤ 1`, E3a) —
completing the route to `finrank G ≤ Ne+1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- `Ŝ⁺` preserves the ground subspace `G`. -/
theorem fermionTotalSpinPlus_mulVec_mem_groundSubmodule (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne) :
    (fermionTotalSpinPlus N).mulVec v ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne := by
  rw [groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply] at hv ⊢
  obtain ⟨⟨hH, hNn⟩, hhc⟩ := hv
  refine ⟨⟨?_, ?_⟩, fermionTotalSpinPlus_mulVec_mem_hardcore N hhc⟩
  · have hcomm : Commute (tJHamiltonian N G τ J) (fermionTotalSpinPlus N) :=
      (fermionTotalSpinPlus_commute_tJHamiltonian N G τ J).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
  · have hcomm : Commute (fermionTotalNumber (2 * N + 1)) (fermionTotalSpinPlus N) :=
      (fermionTotalSpinPlus_commute_fermionTotalNumber N).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hNn, Matrix.mulVec_smul]

/-- `Ŝ⁺` raises the `Ŝ³` weight by one: `Ŝ³ v = sz v ⟹ Ŝ³ (Ŝ⁺ v) = (sz+1) (Ŝ⁺ v)`. -/
theorem fermionTotalSpinZ_mulVec_fermionTotalSpinPlus_mulVec (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (sz : ℝ)
    (hv : (fermionTotalSpinZ N).mulVec v = ((sz : ℝ) : ℂ) • v) :
    (fermionTotalSpinZ N).mulVec ((fermionTotalSpinPlus N).mulVec v) =
      ((sz + 1 : ℝ) : ℂ) • ((fermionTotalSpinPlus N).mulVec v) := by
  have hcomm : fermionTotalSpinZ N * fermionTotalSpinPlus N =
      fermionTotalSpinPlus N * fermionTotalSpinZ N + fermionTotalSpinPlus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinPlus N
    rwa [sub_eq_iff_eq_add'] at h
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]
  rw [show (((sz + 1 : ℝ)) : ℂ) = (((sz : ℝ)) : ℂ) + 1 by push_cast; ring, add_smul, one_smul]

/-- **Weight-space finrank from below.**  For `sz < 0`,
`finrank (G ⊓ Ŝ³=sz) ≤ finrank (G ⊓ Ŝ³=sz+1)`. -/
theorem tJ_ground_weight_finrank_le_of_spinZ_neg (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) (sz : ℝ) (hsz : sz < 0) :
    finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz : ℝ)) : ℂ)) ≤
      finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz + 1 : ℝ)) : ℂ)) := by
  set Glo := groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz : ℝ)) : ℂ) with hGlo
  set Ghi := groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz + 1 : ℝ)) : ℂ) with hGhi
  have hweight : ∀ w : ↥Glo,
      (fermionTotalSpinZ N).mulVec w.val = ((sz : ℝ) : ℂ) • w.val := by
    intro w
    have hw : w.val ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz : ℝ)) : ℂ) := w.property
    have := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hw).2
    rwa [Matrix.mulVecLin_apply] at this
  have hmem : ∀ w : ↥Glo, ((fermionTotalSpinPlus N).mulVecLin.comp Glo.subtype) w ∈ Ghi := by
    intro w
    have hw : w.val ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz : ℝ)) : ℂ) := w.property
    have hwG := (Submodule.mem_inf.mp hw).1
    change (fermionTotalSpinPlus N).mulVec w.val ∈ Ghi
    rw [hGhi, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact ⟨fermionTotalSpinPlus_mulVec_mem_groundSubmodule N Ne G τ J hwG,
      fermionTotalSpinZ_mulVec_fermionTotalSpinPlus_mulVec N sz (hweight w)⟩
  refine LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict Ghi ((fermionTotalSpinPlus N).mulVecLin.comp Glo.subtype) hmem) ?_
  intro w w' hww'
  have hval : (fermionTotalSpinPlus N).mulVec w.val = (fermionTotalSpinPlus N).mulVec w'.val := by
    have := congrArg Subtype.val hww'
    simpa [LinearMap.codRestrict, LinearMap.comp_apply, Matrix.mulVecLin_apply] using this
  have hdiff : (fermionTotalSpinPlus N).mulVec (w.val - w'.val) = 0 := by
    rw [Matrix.mulVec_sub, hval, sub_self]
  have hdsz : (fermionTotalSpinZ N).mulVec (w.val - w'.val) =
      ((sz : ℝ) : ℂ) • (w.val - w'.val) := by
    rw [Matrix.mulVec_sub, hweight w, hweight w', smul_sub]
  by_contra hne
  have hd0 : w.val - w'.val ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.mp h))
  exact fermionTotalSpinPlus_mulVec_ne_zero_of_spinZ_neg N (w.val - w'.val) sz hdsz hsz hd0 hdiff

end LatticeSystem.Fermion
