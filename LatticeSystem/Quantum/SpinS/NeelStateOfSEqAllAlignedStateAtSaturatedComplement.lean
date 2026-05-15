import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Néel state coincides with all-down state at saturated complement edge

At the saturated complement edge `|A| = 0` (every vertex has
`A x = false`), the Néel configuration
`neelConfigOfS A N = fun x => if A x then 0 else Fin.last N`
collapses to the constant `fun _ => Fin.last N`, hence

  `Φ_Néel(A, N) = basisVecS (fun _ => Fin.last N)
                = allAlignedStateS Λ N (Fin.last N)`.

Companion of PR #2914 (the `|¬A| = 0` case where Néel = all-up).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

omit [DecidableEq Λ] in
/-- **Néel-config = all-`last`-config at `|A| = 0`**:
`neelConfigOfS A N = fun _ => Fin.last N`. -/
theorem neelConfigOfS_eq_const_last_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    neelConfigOfS A N = (fun _ : Λ => Fin.last N) := by
  funext x
  unfold neelConfigOfS
  have hfilter_empty :
      Finset.univ.filter (fun x : Λ => A x = true) = ∅ :=
    Finset.card_eq_zero.mp h
  have hAx : A x = false := by
    by_contra hne
    have hAxT : A x = true := by rcases A x with _ | _ <;> simp_all
    have hxmem : x ∈ Finset.univ.filter (fun x : Λ => A x = true) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ x, hAxT⟩
    rw [hfilter_empty] at hxmem
    exact absurd hxmem (Finset.notMem_empty x)
  rw [if_neg (by rw [hAx]; decide : ¬ A x = true)]

/-- **Néel state = all-aligned-down state at `|A| = 0`**:
`neelStateOfS A N = allAlignedStateS Λ N (Fin.last N)`. -/
theorem neelStateOfS_eq_allAlignedStateS_last_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    neelStateOfS A N = (allAlignedStateS Λ N (Fin.last N) :
        (Λ → Fin (N + 1)) → ℂ) := by
  unfold neelStateOfS allAlignedStateS allAlignedConfigS
  rw [neelConfigOfS_eq_const_last_of_cardA_zero A N h]

end LatticeSystem.Quantum
