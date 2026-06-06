import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingCompress
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorReduction
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity

/-!
# Tasaki 11.5: the spin operators preserve the filling space `W` (Prop 11.24 PR-E2 ≥)

For the `W`-restricted A.17 we apply the matrix A.17 axiom at the filling index to the compressions
of `Ĥ_tJ` and the three Cartesian total-spin components `Ŝ⁽¹⁾,Ŝ⁽²⁾,Ŝ⁽³⁾`.  This requires that each
of these operators **preserves** `W = (N̂ = Ne) ∩ H^hc` (so the compression homomorphism applies and
the compressed operators inherit the su(2)/Hermitian/commute relations).

An operator commuting with both `N̂` and the hard-core projection `P̂hc` preserves `W`
(`preservesTJFillingW_of_commute`).  `Ŝ⁽³⁾`, `Ŝ⁺`, `Ŝ⁻` each do; `Ŝ⁽¹⁾ = ½(Ŝ⁺+Ŝ⁻)` and
`Ŝ⁽²⁾ = −(i/2)(Ŝ⁺−Ŝ⁻)` follow by the submodule closure of `PreservesTJFillingW`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- An operator commuting with `N̂` and the hard-core projection preserves `W`. -/
theorem preservesTJFillingW_of_commute (Ne : ℕ) {B : ManyBodyOp (Fin (2 * N + 2))}
    (hN : Commute B (fermionTotalNumber (2 * N + 1)))
    (hP : Commute B (hubbardHardcoreProjection N)) :
    PreservesTJFillingW N Ne B := by
  intro v hv
  rw [mem_tJFillingWSubmodule_iff] at hv ⊢
  obtain ⟨hvN, hvhc⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, ← hN.eq, ← Matrix.mulVec_mulVec, hvN, Matrix.mulVec_smul]
  · have hself : (hubbardHardcoreProjection N).mulVec (B.mulVec v) = B.mulVec v := by
      rw [Matrix.mulVec_mulVec, ← hP.eq, ← Matrix.mulVec_mulVec,
        hubbardHardcoreProjection_mulVec_eq_self_of_mem N hvhc]
    rw [← hself]
    exact hubbardHardcoreProjection_mulVec_mem N _

/-- `PreservesTJFillingW` is closed under scalar multiplication (`W` is a submodule). -/
theorem preservesTJFillingW_smul (Ne : ℕ) {B : ManyBodyOp (Fin (2 * N + 2))}
    (h : PreservesTJFillingW N Ne B) (c : ℂ) : PreservesTJFillingW N Ne (c • B) := by
  intro v hv
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ c (h v hv)

/-- `PreservesTJFillingW` is closed under addition. -/
theorem preservesTJFillingW_add (Ne : ℕ) {B₁ B₂ : ManyBodyOp (Fin (2 * N + 2))}
    (h₁ : PreservesTJFillingW N Ne B₁) (h₂ : PreservesTJFillingW N Ne B₂) :
    PreservesTJFillingW N Ne (B₁ + B₂) := by
  intro v hv
  rw [Matrix.add_mulVec]
  exact Submodule.add_mem _ (h₁ v hv) (h₂ v hv)

/-- `PreservesTJFillingW` is closed under subtraction. -/
theorem preservesTJFillingW_sub (Ne : ℕ) {B₁ B₂ : ManyBodyOp (Fin (2 * N + 2))}
    (h₁ : PreservesTJFillingW N Ne B₁) (h₂ : PreservesTJFillingW N Ne B₂) :
    PreservesTJFillingW N Ne (B₁ - B₂) := by
  intro v hv
  rw [Matrix.sub_mulVec]
  exact Submodule.sub_mem _ (h₁ v hv) (h₂ v hv)

/-- `Ŝ⁺_tot` commutes with `N̂` (number-conserving per-site hops). -/
theorem fermionTotalSpinPlus_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinPlus N) (fermionTotalNumber (2 * N + 1)) := by
  rw [fermionTotalSpinPlus_eq_sum_siteSpinPlus]
  exact Commute.sum_left _ _ _
    (fun i _ => (fermionTotalNumber_commute_fermionSiteSpinPlus i).symm)

/-- `Ŝ⁽³⁾_tot` preserves `W`. -/
theorem preservesTJFillingW_fermionTotalSpinZ (Ne : ℕ) :
    PreservesTJFillingW N Ne (fermionTotalSpinZ N) :=
  preservesTJFillingW_of_commute Ne (fermionTotalSpinZ_commute_fermionTotalNumber N)
    (fermionTotalSpinZ_commute_hubbardHardcoreProjection N)

/-- `Ŝ⁺_tot` preserves `W`. -/
theorem preservesTJFillingW_fermionTotalSpinPlus (Ne : ℕ) :
    PreservesTJFillingW N Ne (fermionTotalSpinPlus N) :=
  preservesTJFillingW_of_commute Ne (fermionTotalSpinPlus_commute_fermionTotalNumber N)
    (fermionTotalSpinPlus_commute_hubbardHardcoreProjection N)

/-- `Ŝ⁻_tot` preserves `W`. -/
theorem preservesTJFillingW_fermionTotalSpinMinus (Ne : ℕ) :
    PreservesTJFillingW N Ne (fermionTotalSpinMinus N) :=
  preservesTJFillingW_of_commute Ne (fermionTotalSpinMinus_commute_fermionTotalNumber N)
    (fermionTotalSpinMinus_commute_hubbardHardcoreProjection N)

/-- `Ŝ⁽¹⁾_tot = ½(Ŝ⁺+Ŝ⁻)` preserves `W`. -/
theorem preservesTJFillingW_tJTotalSpinOne (Ne : ℕ) :
    PreservesTJFillingW N Ne (tJTotalSpinOne N) := by
  unfold tJTotalSpinOne
  exact preservesTJFillingW_smul Ne (preservesTJFillingW_add Ne
    (preservesTJFillingW_fermionTotalSpinPlus Ne) (preservesTJFillingW_fermionTotalSpinMinus Ne)) _

/-- `Ŝ⁽²⁾_tot = −(i/2)(Ŝ⁺−Ŝ⁻)` preserves `W`. -/
theorem preservesTJFillingW_tJTotalSpinTwo (Ne : ℕ) :
    PreservesTJFillingW N Ne (tJTotalSpinTwo N) := by
  unfold tJTotalSpinTwo
  exact preservesTJFillingW_smul Ne (preservesTJFillingW_sub Ne
    (preservesTJFillingW_fermionTotalSpinPlus Ne) (preservesTJFillingW_fermionTotalSpinMinus Ne)) _

end LatticeSystem.Fermion
