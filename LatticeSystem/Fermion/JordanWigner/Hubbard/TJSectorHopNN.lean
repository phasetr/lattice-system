import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopAction

/-!
# Tasaki 11.5: the nearest-neighbour hop is sign-free on the t-J sector basis (Prop 11.24 PR3c-5)

For a forward *nearest-neighbour* hop `a → b` with `b.val = a.val + 1` (a non-wrap bond of the d=1
chain/cycle), the single Jordan–Wigner mode strictly between the source and target orbitals is the
*opposite-orbital* of one of the two sites, which the hop conditions force to be empty.  Hence the
strictly-between occupation is `0` and the hop matrix element is `+1`:

  `ĉ†_{bσ}ĉ_{aσ} |Φ_s⟩ = |Φ_{tJSiteHop s a b}⟩`   (no sign).

This is the sign-freeness of the d=1 t-J hopping on non-wrap bonds; the wrap bond `N ↔ 0` (sign
`(-1)^(Ne-1) = +1` for odd `Ne`) is handled separately.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Nearest-neighbour up-hop is sign-free.**  For `b.val = a.val + 1`, source `a` ↑, target `b`
empty, the single intervening mode is the down-orbital of `a` (empty since `a` is ↑), so
`ĉ†_{b↑}ĉ_{a↑} |Φ_s⟩ = |Φ_{tJSiteHop s a b}⟩`. -/
theorem tJ_uphop_nn_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s a = 1) (hsb : s b = 0) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N b 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 0)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s a b)) := by
  have hab : a.val < b.val := by omega
  rw [tJ_uphop_forward_mulVec N s a b hab ha hsb]
  have hsum : (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k =>
      (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
      (tJConfigOf N s k).val) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, spinfulIndex] at hk
    have hkeq : k = spinfulIndex N a 1 := Fin.ext (by simp only [spinfulIndex]; omega)
    rw [hkeq, tJConfigOf_apply_down, if_neg (by rw [ha]; decide)]
    rfl
  rw [hsum, pow_zero, one_smul]

/-- **Nearest-neighbour down-hop is sign-free.**  For `b.val = a.val + 1`, source `a` ↓, target `b`
empty, the single intervening mode is the up-orbital of `b` (empty since `b` is empty), so
`ĉ†_{b↓}ĉ_{a↓} |Φ_s⟩ = |Φ_{tJSiteHop s a b}⟩`. -/
theorem tJ_downhop_nn_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hb : b.val = a.val + 1) (ha : s a = 2) (hsb : s b = 0) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N b 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 1)).mulVec
        (basisVec (tJConfigOf N s))
      = basisVec (tJConfigOf N (tJSiteHop s a b)) := by
  have hab : a.val < b.val := by omega
  rw [tJ_downhop_forward_mulVec N s a b hab ha hsb]
  have hsum : (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k =>
      (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
      (tJConfigOf N s k).val) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, spinfulIndex] at hk
    have hkeq : k = spinfulIndex N b 0 := Fin.ext (by simp only [spinfulIndex]; omega)
    rw [hkeq, tJConfigOf_apply_up, if_neg (by rw [hsb]; decide)]
    rfl
  rw [hsum, pow_zero, one_smul]

end LatticeSystem.Fermion
