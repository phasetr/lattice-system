import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopConfig
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopSignBetween

/-!
# Tasaki 11.5: the forward-hop matrix element on the t-J sector basis (Prop 11.24 PR3c-4)

Composing the operator-level single-hop action (`HopBasisVec.lean`), the config identity
(`TJSectorHopConfig.lean`), and the forward-hop sign parity (`HopSignBetween.lean`), this file
computes the action of a single same-spin hopping term `ĉ†_{bσ}ĉ_{aσ}` on a t-J sector basis state
for a *forward* allowed hop (`a.val < b.val`, source occupied with spin σ, target empty):

  `ĉ†_{bσ}ĉ_{aσ} |Φ_s⟩ = (-1)^(#occupied modes strictly between (a,σ) and (b,σ)) · |Φ_{tJSiteHop s
  a b}⟩`.

The sign is `(-1)` to the occupied modes strictly between source and target in Jordan–Wigner order;
for the d=1 cycle's nearest-neighbour hops this exponent is `0` (the single intervening orbital is
empty), giving the sign-free hopping (handled in the next step).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Forward up-hop matrix element on the sector basis.**  For `a.val < b.val`, source `a` ↑, and
target `b` empty, `ĉ†_{b↑}ĉ_{a↑}` maps `|Φ_s⟩` to `(-1)^(between) · |Φ_{tJSiteHop s a b}⟩`, where
`between` counts the occupied modes strictly between the up-orbitals of `a` and `b`. -/
theorem tJ_uphop_forward_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hab : a.val < b.val) (ha : s a = 1) (hb : s b = 0) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N b 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 0)).mulVec
        (basisVec (tJConfigOf N s))
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k =>
            (spinfulIndex N a 0).val < k.val ∧ k.val < (spinfulIndex N b 0).val),
            (tJConfigOf N s k).val)
        • basisVec (tJConfigOf N (tJSiteHop s a b)) := by
  have hqp : (spinfulIndex N a 0).val < (spinfulIndex N b 0).val := by
    simp only [spinfulIndex]; omega
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hpne : spinfulIndex N b 0 ≠ spinfulIndex N a 0 := fun h =>
    hne ((spinfulIndex_eq_iff N b a 0 0).mp h).1.symm
  have hcq : tJConfigOf N s (spinfulIndex N a 0) = 1 := by rw [tJConfigOf_apply_up, if_pos ha]
  have hcp : (Function.update (tJConfigOf N s) (spinfulIndex N a 0) 0) (spinfulIndex N b 0) = 0 :=
      by
    rw [Function.update_of_ne hpne, tJConfigOf_apply_up, if_neg (by rw [hb]; decide)]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec, if_pos ⟨hcq, hcp⟩,
    jwSign_mul_jwSign_update_forward (2 * N + 1) (spinfulIndex N a 0) (spinfulIndex N b 0)
      (tJConfigOf N s) hqp, tJConfigOf_tJSiteHop_up N s a b ha hb]

/-- **Forward down-hop matrix element on the sector basis.**  For `a.val < b.val`, source `a` ↓, and
target `b` empty, `ĉ†_{b↓}ĉ_{a↓}` maps `|Φ_s⟩` to `(-1)^(between) · |Φ_{tJSiteHop s a b}⟩`, where
`between` counts the occupied modes strictly between the down-orbitals of `a` and `b`. -/
theorem tJ_downhop_forward_mulVec (N : ℕ) (s : Fin (N + 1) → Fin 3) (a b : Fin (N + 1))
    (hab : a.val < b.val) (ha : s a = 2) (hb : s b = 0) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N b 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N a 1)).mulVec
        (basisVec (tJConfigOf N s))
      = (-1 : ℂ) ^ (∑ k ∈ (Finset.univ : Finset (Fin (2 * N + 2))).filter (fun k =>
            (spinfulIndex N a 1).val < k.val ∧ k.val < (spinfulIndex N b 1).val),
            (tJConfigOf N s k).val)
        • basisVec (tJConfigOf N (tJSiteHop s a b)) := by
  have hqp : (spinfulIndex N a 1).val < (spinfulIndex N b 1).val := by
    simp only [spinfulIndex]; omega
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hpne : spinfulIndex N b 1 ≠ spinfulIndex N a 1 := fun h =>
    hne ((spinfulIndex_eq_iff N b a 1 1).mp h).1.symm
  have hcq : tJConfigOf N s (spinfulIndex N a 1) = 1 := by rw [tJConfigOf_apply_down, if_pos ha]
  have hcp : (Function.update (tJConfigOf N s) (spinfulIndex N a 1) 0) (spinfulIndex N b 1) = 0 :=
      by
    rw [Function.update_of_ne hpne, tJConfigOf_apply_down, if_neg (by rw [hb]; decide)]
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec, if_pos ⟨hcq, hcp⟩,
    jwSign_mul_jwSign_update_forward (2 * N + 1) (spinfulIndex N a 1) (spinfulIndex N b 1)
      (tJConfigOf N s) hqp, tJConfigOf_tJSiteHop_down N s a b ha hb]

end LatticeSystem.Fermion
