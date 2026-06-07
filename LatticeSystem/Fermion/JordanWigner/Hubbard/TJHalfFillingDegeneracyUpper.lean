import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingUpCount
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tasaki 11.5.3: half-filling ground degeneracy upper bound (Theorem 11.26 PR3i-3c)

The half-filling ground amplitudes are constant on each up-count class
(`tJ_ground_amplitude_eq_of_same_upCount`, PR3i-3b), and a ground state is determined by its
amplitudes (`tJ_filling_completeness`).  Evaluating a ground state at one representative per
up-count class is therefore an injective linear map `G ↪ (Fin (N+2) → ℂ)`, so:

* `tJ_halfFilling_groundSubmodule_finrank_le` — `finrank G ≤ N+2`.

Paired with the SU(2)-tower lower bound (`tJ_halfFilling_groundSubmodule_finrank_ge`, #4326) this
pins `finrank G = N+2` — the dimension half of the half-filling case of Theorem 11.26.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- The number of sites with index `< m` (for `m ≤ N+1`) is exactly `m`. -/
theorem tJ_card_val_lt (m : ℕ) (hm : m ≤ N + 1) :
    (Finset.univ.filter (fun k : Fin (N + 1) => k.val < m)).card = m := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if i < m then (1 : ℕ) else 0),
    ← Finset.card_filter,
    show (Finset.range (N + 1)).filter (· < m) = Finset.range m by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega,
    Finset.card_range]

/-- A representative half-filling config with exactly `j` up-spins: the first `j` sites are up. -/
def tJUpCountRep (j : Fin (N + 2)) : TJFillingSector N (N + 1) :=
  ⟨fun k => if k.val < j.val then 1 else 2, by
    refine tJ_upDownCount_of_full _ (fun k => ?_)
    by_cases h : k.val < j.val <;> simp [h]⟩

/-- The representative has the prescribed up-count. -/
theorem tJUpCountRep_upCount (j : Fin (N + 2)) :
    (Finset.univ.filter (fun k => (tJUpCountRep j).val k = 1)).card = j.val := by
  have hfe : (Finset.univ.filter (fun k : Fin (N + 1) => (tJUpCountRep j).val k = 1))
      = Finset.univ.filter (fun k => k.val < j.val) := by
    apply Finset.filter_congr
    intro k _
    by_cases h : k.val < j.val <;> simp [tJUpCountRep, h]
  rw [hfe]
  exact tJ_card_val_lt j.val (by omega)

/-- **Half-filling ground degeneracy upper bound.**  The d=1 ferromagnetic t-J ground subspace at
half filling has dimension at most `N+2`: a ground state is determined by its amplitudes, which are
constant on each of the `N+2` up-count classes, so evaluating at one representative per class is an
injective linear map into `Fin (N+2) → ℂ`. -/
theorem tJ_halfFilling_groundSubmodule_finrank_le (hpos : 0 < N) (τ J : ℝ) (hJ : 0 < J) :
    finrank ℂ
      ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1)) ≤ N + 2 := by
  classical
  set G := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1) with hG
  -- evaluation at the up-count representatives
  let proj : ↥G →ₗ[ℂ] (Fin (N + 2) → ℂ) :=
    { toFun := fun v j => (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (tJConfigOf N (tJUpCountRep j).val)
      map_add' := fun a b => by funext j; simp
      map_smul' := fun c a => by funext j; simp }
  have hinj : Function.Injective proj := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv0
    have hv0' : ∀ j : Fin (N + 2),
        (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (tJConfigOf N (tJUpCountRep j).val) = 0 :=
      fun j => congrFun (by simpa [proj] using hv0) j
    apply Subtype.ext
    have hhc : (v : (Fin (2 * N + 2) → Fin 2) → ℂ) ∈ hubbardHardcoreSubspace N := v.2.2
    have hN : (fermionTotalNumber (2 * N + 1)).mulVec (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
        = ((N + 1 : ℕ) : ℂ) • (v : (Fin (2 * N + 2) → Fin 2) → ℂ) := by
      have := v.2.1.2
      rwa [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at this
    rw [tJ_filling_completeness (N + 1) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) hhc hN,
      tJFillingExpansion]
    refine Finset.sum_eq_zero fun t _ => ?_
    -- the coefficient vanishes: equal up-count to a representative whose value is `0`
    have hcoeff : tJFillingExpansionCoeff N (N + 1) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) t
        = (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (tJConfigOf N t.val) := by
      rw [tJFillingExpansionCoeff, basisVec_sum_mul]
    set j : Fin (N + 2) :=
      ⟨(Finset.univ.filter (fun k => t.val k = 1)).card, by
        have := tJFillingSector_full t
        have h := t.2; omega⟩ with hj
    have hsame : (Finset.univ.filter (fun k => t.val k = 1)).card
        = (Finset.univ.filter (fun k => (tJUpCountRep j).val k = 1)).card := by
      rw [tJUpCountRep_upCount j]
    have : (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (tJConfigOf N t.val) = 0 := by
      rw [tJ_ground_amplitude_eq_of_same_upCount hpos τ J hJ v.2 t (tJUpCountRep j) hsame,
        hv0' j]
    rw [hcoeff, this, zero_smul]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle

end LatticeSystem.Fermion
