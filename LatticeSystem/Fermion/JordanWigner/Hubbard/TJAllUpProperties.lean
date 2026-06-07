import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAllUpGround

/-!
# Tasaki 11.5.3: number / hard-core / nonzero facts for the all-up state (Theorem 11.26 PR3g)

Filling-sector facts about the half-filling maximal-spin reference `|↑…↑⟩`, the inputs to
the half-filling ground energy and the SU(2) lower bound:

* `hubbardAllUpState_ne_zero` — `|↑…↑⟩ ≠ 0`;
* `hubbardAllUpState_mem_hardcore` — `|↑…↑⟩ ∈ H_hc`;
* `fermionTotalNumber_mulVec_allUpState` — `N̂ |↑…↑⟩ = (N+1) |↑…↑⟩` (the `N+1`-electron state).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- `|↑…↑⟩ ≠ 0`. -/
theorem hubbardAllUpState_ne_zero (N : ℕ) : hubbardAllUpState N ≠ 0 := by
  rw [hubbardAllUpState_eq_tJConfigOf]
  intro h
  have hd := congrFun h (tJConfigOf N (fun _ => 1))
  rw [basisVec_self, Pi.zero_apply] at hd
  exact one_ne_zero hd

/-- `|↑…↑⟩ ∈ H_hc`: the all-up configuration is hard-core (one electron per site). -/
theorem hubbardAllUpState_mem_hardcore (N : ℕ) :
    hubbardAllUpState N ∈ hubbardHardcoreSubspace N := by
  rw [hubbardAllUpState_eq_tJConfigOf]
  exact tJConfigOf_mem_hardcore N _

/-- `N̂ |↑…↑⟩ = (N+1) |↑…↑⟩`: the all-up state has `N+1` electrons (one per site). -/
theorem fermionTotalNumber_mulVec_allUpState (N : ℕ) :
    (fermionTotalNumber (2 * N + 1)).mulVec (hubbardAllUpState N) =
      ((N + 1 : ℕ) : ℂ) • hubbardAllUpState N := by
  rw [hubbardAllUpState_eq_tJConfigOf]
  refine fermionTotalNumber_mulVec_tJConfigOf_eq N (fun _ => 1) (N + 1) ?_
  have h1 : (Finset.univ.filter (fun k : Fin (N + 1) => (fun _ => (1 : Fin 3)) k = 1)) =
      Finset.univ := by simp
  have h2 : (Finset.univ.filter (fun k : Fin (N + 1) => (fun _ => (1 : Fin 3)) k = 2)) = ∅ := by
    simp
  rw [h1, h2, Finset.card_univ, Fintype.card_fin, Finset.card_empty, add_zero]

end LatticeSystem.Fermion
