import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopNN

/-!
# Tasaki 11.5: the backward (leftward) nearest-neighbour hop (Prop 11.24 PR-B7-3b)

The cyclic kinetic operator `K = Σ_σ Σ_i Σ_j (adj i j) ĉ†_{iσ}ĉ_{jσ}` contains, for each oriented
adjacent pair, both the *rightward* hop `ĉ†_{(a+1)σ}ĉ_{aσ}` (`tJ_uphop_nn_mulVec` etc.) and the
*leftward* hop `ĉ†_{aσ}ĉ_{(a+1)σ}`.  This file computes the leftward nearest-neighbour hop action and
matrix element, which are again **sign-free** (`+1`): the single intervening Jordan–Wigner mode is
empty, so the backward sign parity (`jwSign_mul_jwSign_update_backward`) collapses to `0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Leftward NN up-hop is sign-free.**  For `b.val = a.val + 1`, source `b` ↑, target `a` empty,
`ĉ†_{a↑}ĉ_{b↑} |Φ_s⟩ = |Φ_{tJSiteHop s b a}⟩` (the electron hops from `b` down to `a`). -/
theorem tJ_uphop_backward_nn_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s b = 1) (hsa : s a = 0) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N a 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 0)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s b a)) := by
  have hqp : (spinfulIndex N a 0).val < (spinfulIndex N b 0).val := by
    simp only [spinfulIndex]; omega
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hpne : spinfulIndex N a 0 ≠ spinfulIndex N b 0 := fun h =>
    hne ((spinfulIndex_eq_iff N a b 0 0).mp h).1
  have hcq : tJConfigOf N s (spinfulIndex N b 0) = 1 := by rw [tJConfigOf_apply_up, if_pos ha]
  have hcpz : tJConfigOf N s (spinfulIndex N a 0) = 0 := by
    rw [tJConfigOf_apply_up, if_neg (by rw [hsa]; decide)]
  have hcp : (Function.update (tJConfigOf N s) (spinfulIndex N b 0) 0) (spinfulIndex N a 0) = 0 := by
    rw [Function.update_of_ne hpne, hcpz]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec, if_pos ⟨hcq, hcp⟩,
    jwSign_mul_jwSign_update_backward (2 * N + 1) (spinfulIndex N b 0) (spinfulIndex N a 0)
      (tJConfigOf N s) hqp hcpz, tJConfigOf_tJSiteHop_up N s b a ha hsa]
  have hsum : (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k =>
      (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
      (tJConfigOf N s k).val) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, spinfulIndex] at hk
    have hkeq : k = spinfulIndex N a 1 := Fin.ext (by simp only [spinfulIndex]; omega)
    rw [hkeq, tJConfigOf_apply_down, if_neg (by rw [hsa]; decide)]
    rfl
  rw [hsum, pow_zero, one_smul]

/-- **Leftward NN down-hop is sign-free.**  For `b.val = a.val + 1`, source `b` ↓, target `a` empty,
`ĉ†_{a↓}ĉ_{b↓} |Φ_s⟩ = |Φ_{tJSiteHop s b a}⟩`. -/
theorem tJ_downhop_backward_nn_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s b = 2) (hsa : s a = 0) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N a 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 1)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s b a)) := by
  have hqp : (spinfulIndex N a 1).val < (spinfulIndex N b 1).val := by
    simp only [spinfulIndex]; omega
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hpne : spinfulIndex N a 1 ≠ spinfulIndex N b 1 := fun h =>
    hne ((spinfulIndex_eq_iff N a b 1 1).mp h).1
  have hcq : tJConfigOf N s (spinfulIndex N b 1) = 1 := by rw [tJConfigOf_apply_down, if_pos ha]
  have hcpz : tJConfigOf N s (spinfulIndex N a 1) = 0 := by
    rw [tJConfigOf_apply_down, if_neg (by rw [hsa]; decide)]
  have hcp : (Function.update (tJConfigOf N s) (spinfulIndex N b 1) 0) (spinfulIndex N a 1) = 0 := by
    rw [Function.update_of_ne hpne, hcpz]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec, if_pos ⟨hcq, hcp⟩,
    jwSign_mul_jwSign_update_backward (2 * N + 1) (spinfulIndex N b 1) (spinfulIndex N a 1)
      (tJConfigOf N s) hqp hcpz, tJConfigOf_tJSiteHop_down N s b a ha hsa]
  have hsum : (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k =>
      (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
      (tJConfigOf N s k).val) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, spinfulIndex] at hk
    have hkeq : k = spinfulIndex N b 0 := Fin.ext (by simp only [spinfulIndex]; omega)
    rw [hkeq, tJConfigOf_apply_up, if_neg (by rw [ha]; decide)]
    rfl
  rw [hsum, pow_zero, one_smul]

/-- **Leftward NN up-hop matrix element.**  `⟨Φ_{s'} | ĉ†_{a↑}ĉ_{b↑} | Φ_s⟩ = [s' = tJSiteHop s b a]`. -/
theorem tJ_uphop_backward_nn_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s b = 1) (hsa : s a = 0) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N a 0) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 0)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s b a then 1 else 0 := by
  rw [tJ_uphop_backward_nn_mulVec N s a b hb ha hsa]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s b a)

/-- **Leftward NN down-hop matrix element.** -/
theorem tJ_downhop_backward_nn_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (a b : Fin (N + 1)) (hb : b.val = a.val + 1) (ha : s b = 2) (hsa : s a = 0) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N a 1) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N b 1)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSiteHop s b a then 1 else 0 := by
  rw [tJ_downhop_backward_nn_mulVec N s a b hb ha hsa]
  exact tJConfigOf_basisVec_inner N s' (tJSiteHop s b a)

end LatticeSystem.Fermion
