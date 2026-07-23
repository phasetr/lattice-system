import LatticeSystem.Quantum.SpinS.SpinThreeHalfBondProjection
import LatticeSystem.Quantum.SpinS.TwoSiteSliceS

/-!
# Embedding the local spin-three-half AKLT bond certificate

This module transports the certified local maximal-spin projector to an
arbitrary ordered pair of distinct sites and characterizes its global kernel
through two-site coefficient slices.
-/

namespace LatticeSystem.Quantum

open Matrix
open AKLTExactCertificateSector234Sequential

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The block embedding transports an ordered finite matrix product. -/
private theorem onEmbS_list_prod {m N : ℕ}
    (ι : Fin m → Λ) (hι : Function.Injective ι)
    (l : List
      (Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ)) :
    onEmbS ι l.prod = (l.map fun A => onEmbS ι A).prod := by
  induction l with
  | nil =>
      simpa only [List.prod_nil, List.map_nil] using
        (onEmbS_one (N := N) ι)
  | cons A l ih =>
      rw [List.prod_cons, ← onEmbS_mul hι, ih, List.map_cons,
        List.prod_cons]

/-- The block embedding transports matrix negation. -/
private theorem onEmbS_neg {m N : ℕ} (ι : Fin m → Λ)
    (A : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) :
    onEmbS ι (-A) = -onEmbS ι A := by
  simpa only [neg_one_smul] using onEmbS_smul ι (-1 : ℂ) A

/-- The arbitrary-bond spin-three projector is the block embedding of the
certified local `P₃` matrix. -/
theorem bondMaxSpinProjectionS_three_eq_onEmbS
    {x y : Λ} (hxy : x ≠ y) :
    bondMaxSpinProjectionS x y 3 =
      onEmbS ![x, y] spinThreeHalfBondMaxProjection := by
  rw [spinThreeHalfBondMaxProjection, bondMaxSpinProjectionS,
    bondMaxSpinProjectionS,
    onEmbS_list_prod ![x, y] (injective_bondEmb hxy)]
  apply congrArg List.prod
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, bondCasimirS, sub_eq_add_neg,
    onEmbS_add, onEmbS_smul, onEmbS_neg, onEmbS_one,
    spinSDot_eq_onEmbS hxy 3]

/-- The arbitrary-bond spin-three projector annihilates a many-body vector
exactly when every two-site slice belongs to the certified local VBS bond
subspace. -/
theorem bondMaxSpinProjectionS_three_mulVec_eq_zero_iff_slices
    {x y : Λ} (hxy : x ≠ y) (Φ : (Λ → Fin 4) → ℂ) :
    (bondMaxSpinProjectionS x y 3).mulVec Φ = 0 ↔
      ∀ τ : Λ → Fin 4,
        twoSiteSliceS x y Φ τ ∈
          spinThreeHalfVBSBondSubspace := by
  rw [bondMaxSpinProjectionS_three_eq_onEmbS hxy,
    onEmbS_mulVec_eq_zero_iff_twoSiteSlices hxy]
  apply forall_congr'
  intro τ
  change
    twoSiteSliceS x y Φ τ ∈
        LinearMap.ker (Matrix.mulVecLin
          spinThreeHalfBondMaxProjection) ↔
      twoSiteSliceS x y Φ τ ∈
        spinThreeHalfVBSBondSubspace
  rw [spinThreeHalfBondLocal_ker_eq_vbsBondSubspace]

end LatticeSystem.Quantum
