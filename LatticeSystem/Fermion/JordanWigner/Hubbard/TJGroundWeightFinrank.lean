import LatticeSystem.Fermion.JordanWigner.Hubbard.TJLadderInjective
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundDegeneracyLower

/-!
# Tasaki 11.5: weight-space finrank is non-increasing toward `Ŝ³ = ½` (Prop 11.24 E5b step)

For the ground subspace `G = groundSubmoduleAtFilling Ĥ_tJ Ne`, the lowering operator `Ŝ⁻` maps the
`Ŝ³ = sz+1` weight space of `G` injectively into the `Ŝ³ = sz` weight space whenever `sz ≥ 0` (since
`sz+1 > 0`, by the ladder injectivity).  Hence the weight-space dimension is non-increasing as `Ŝ³`
decreases toward `½`:
`finrank (G ⊓ Ŝ³=sz+1) ≤ finrank (G ⊓ Ŝ³=sz)`.

Iterating down to `Ŝ³ = ½` (and up from below via `Ŝ⁺`) bounds every weight space by the `Ŝ³ = ½`
block, which is `≤ 1` (E3a) — the route to the degeneracy upper bound `finrank G ≤ Ne+1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- `Ŝ⁻` preserves the ground subspace `G` (it commutes with `Ĥ_tJ` and `N̂` and keeps the hard-core
subspace). -/
theorem fermionTotalSpinMinus_mulVec_mem_groundSubmodule (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne) :
    (fermionTotalSpinMinus N).mulVec v ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne := by
  rw [groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply] at hv ⊢
  obtain ⟨⟨hH, hNn⟩, hhc⟩ := hv
  refine ⟨⟨?_, ?_⟩, fermionTotalSpinMinus_mulVec_mem_hardcore N hhc⟩
  · have hcomm : Commute (tJHamiltonian N G τ J) (fermionTotalSpinMinus N) :=
      (fermionTotalSpinMinus_commute_tJHamiltonian N G τ J).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
  · have hcomm : Commute (fermionTotalNumber (2 * N + 1)) (fermionTotalSpinMinus N) :=
      (fermionTotalSpinMinus_commute_fermionTotalNumber N).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hNn, Matrix.mulVec_smul]

/-- `Ŝ⁻` lowers the `Ŝ³` weight by one: `Ŝ³ v = (sz+1) v ⟹ Ŝ³ (Ŝ⁻ v) = sz (Ŝ⁻ v)`. -/
theorem fermionTotalSpinZ_mulVec_fermionTotalSpinMinus_mulVec (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (sz : ℝ)
    (hv : (fermionTotalSpinZ N).mulVec v = ((sz + 1 : ℝ) : ℂ) • v) :
    (fermionTotalSpinZ N).mulVec ((fermionTotalSpinMinus N).mulVec v) =
      ((sz : ℝ) : ℂ) • ((fermionTotalSpinMinus N).mulVec v) := by
  have hcomm : fermionTotalSpinZ N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinZ N - fermionTotalSpinMinus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
    linear_combination (norm := noncomm_ring) h
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]
  rw [show (((sz : ℝ) : ℂ)) = (((sz + 1 : ℝ)) : ℂ) - 1 by push_cast; ring, sub_smul, one_smul]

/-- **Weight-space finrank is non-increasing toward `½`.**  For `sz ≥ 0`,
`finrank (G ⊓ Ŝ³=sz+1) ≤ finrank (G ⊓ Ŝ³=sz)`. -/
theorem tJ_ground_weight_finrank_le_succ (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) (sz : ℝ) (hsz : 0 ≤ sz) :
    finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz + 1 : ℝ)) : ℂ)) ≤
      finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz : ℝ)) : ℂ)) := by
  set Ghi := groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz + 1 : ℝ)) : ℂ) with hGhi
  set Glo := groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz : ℝ)) : ℂ) with hGlo
  have hweight : ∀ w : ↥Ghi,
      (fermionTotalSpinZ N).mulVec w.val = ((sz + 1 : ℝ) : ℂ) • w.val := by
    intro w
    have hw : w.val ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz + 1 : ℝ)) : ℂ) := w.property
    have := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hw).2
    rwa [Matrix.mulVecLin_apply] at this
  have hmem : ∀ w : ↥Ghi, ((fermionTotalSpinMinus N).mulVecLin.comp Ghi.subtype) w ∈ Glo := by
    intro w
    have hw : w.val ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((sz + 1 : ℝ)) : ℂ) := w.property
    have hwG := (Submodule.mem_inf.mp hw).1
    change (fermionTotalSpinMinus N).mulVec w.val ∈ Glo
    rw [hGlo, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact ⟨fermionTotalSpinMinus_mulVec_mem_groundSubmodule N Ne G τ J hwG,
      fermionTotalSpinZ_mulVec_fermionTotalSpinMinus_mulVec N sz (hweight w)⟩
  refine LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.codRestrict Glo ((fermionTotalSpinMinus N).mulVecLin.comp Ghi.subtype) hmem) ?_
  intro w w' hww'
  have hval : (fermionTotalSpinMinus N).mulVec w.val = (fermionTotalSpinMinus N).mulVec w'.val := by
    have := congrArg Subtype.val hww'
    simpa [LinearMap.codRestrict, LinearMap.comp_apply, Matrix.mulVecLin_apply] using this
  have hdiff : (fermionTotalSpinMinus N).mulVec (w.val - w'.val) = 0 := by
    rw [Matrix.mulVec_sub, hval, sub_self]
  have hdsz : (fermionTotalSpinZ N).mulVec (w.val - w'.val) =
      ((sz + 1 : ℝ) : ℂ) • (w.val - w'.val) := by
    rw [Matrix.mulVec_sub, hweight w, hweight w', smul_sub]
  by_contra hne
  have hd0 : w.val - w'.val ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.mp h))
  exact fermionTotalSpinMinus_mulVec_ne_zero_of_spinZ_pos N (w.val - w'.val) (sz + 1) hdsz
    (by linarith) hd0 hdiff

end LatticeSystem.Fermion
