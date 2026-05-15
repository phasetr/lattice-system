import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.BipartiteToyGroundStateSaturated
import LatticeSystem.Quantum.SpinS.AllAlignedStateMemBipartiteToyGSSaturated

/-!
# Néel state coincides with all-aligned state at saturated edges

At a saturated edge `|¬A| = 0` (every vertex has `A x = true`), the
Néel configuration `neelConfigOfS A N = fun x => if A x then 0 else
Fin.last N` collapses to the constant `fun _ => 0`, hence

  `Φ_Néel(A, N) = basisVecS (fun _ => 0) = allAlignedStateS Λ N 0`.

Similarly at `|A| = 0`, `Φ_Néel(A, N) = allAlignedStateS Λ N (Fin.last N)`.

This identification immediately gives **Néel ∈ predicted GS
subspace at saturated** by applying PRs #2782/#2820's all-aligned
witnesses.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

omit [DecidableEq Λ] in
/-- **Néel-config = all-zero-config at `|¬A| = 0`**:
`neelConfigOfS A N = fun _ => 0`. -/
theorem neelConfigOfS_eq_const_zero_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    neelConfigOfS A N = (fun _ : Λ => (0 : Fin (N + 1))) := by
  funext x
  unfold neelConfigOfS
  -- |¬A| = 0 means no x has !A x = true, hence all x have A x = true.
  have hfilter_empty :
      Finset.univ.filter (fun x : Λ => (! A x) = true) = ∅ :=
    Finset.card_eq_zero.mp h
  have hAx : A x = true := by
    by_contra hne
    have hAxF : A x = false := by rcases A x with _ | _ <;> simp_all
    have hnotA : (! A x) = true := by rw [hAxF]; rfl
    have hxmem : x ∈ Finset.univ.filter (fun x : Λ => (! A x) = true) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ x, hnotA⟩
    rw [hfilter_empty] at hxmem
    exact absurd hxmem (Finset.notMem_empty x)
  rw [if_pos hAx]

/-- **Néel state = all-aligned-up state at `|¬A| = 0`**:
`neelStateOfS A N = allAlignedStateS Λ N 0`. -/
theorem neelStateOfS_eq_allAlignedStateS_zero_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    neelStateOfS A N = (allAlignedStateS Λ N (0 : Fin (N + 1)) :
        (Λ → Fin (N + 1)) → ℂ) := by
  unfold neelStateOfS allAlignedStateS allAlignedConfigS
  rw [neelConfigOfS_eq_const_zero_of_cardNotA_zero A N h]

/-- **Néel ∈ predicted GS subspace at `|¬A| = 0`** (saturated edge):
direct from Néel = all-up state (above) + PR #2782's all-up
witness. -/
theorem neelStateOfS_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    [Nonempty Λ]
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    neelStateOfS A N ∈ bipartiteToyGroundStateSubspacePredicted A N := by
  rw [neelStateOfS_eq_allAlignedStateS_zero_of_cardNotA_zero A N h]
  exact allAlignedStateS_zero_mem_bipartiteToyGroundStateSubspacePredicted_of_cardNotA_zero
    A h

end LatticeSystem.Quantum
