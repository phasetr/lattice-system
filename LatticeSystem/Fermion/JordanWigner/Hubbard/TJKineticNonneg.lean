import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis

/-!
# Tasaki 11.5: the general single-hop matrix element on the sector basis (Prop 11.24 PR-B7-3d)

The per-term hopping matrix element `⟨Φ_{s'} | ĉ†_{iσ}ĉ_{jσ} | Φ_s⟩` for *arbitrary* sites `i, j` and
spin `σ`, before any adjacency or allowed-hop assumption.  Reading off the single-hop action
(`fermionMultiCreation_mul_Annihilation_mulVec_basisVec`) at the bra configuration `tJConfigOf s'`,
the element vanishes unless the source orbital `(j,σ)` is occupied and the target orbital `(i,σ)` is
empty; in that case it is the product of the two Jordan–Wigner string signs times the orthonormality
indicator `[tJConfigOf s' = hopped config]`.  This is the off-diagonal kinetic summand whose
non-negativity (after the cyclic adjacency case split) feeds the Perron–Frobenius step.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **General single-hop matrix element.**  `⟨Φ_{s'} | ĉ†_{iσ}ĉ_{jσ} | Φ_s⟩` equals, when the source
`(j,σ)` is occupied and the target `(i,σ)` is empty after removing the source, the product of the two
string signs times `[tJConfigOf s' = hopped config]`, and `0` otherwise. -/
theorem tJ_hop_matrixElement_apply (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (i j : Fin (N + 1))
    (σ : Fin 2) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if tJConfigOf N s (spinfulIndex N j σ) = 1 ∧
          (Function.update (tJConfigOf N s) (spinfulIndex N j σ) 0) (spinfulIndex N i σ) = 0 then
          (jwSign (2 * N + 1) (spinfulIndex N j σ) (tJConfigOf N s) *
            jwSign (2 * N + 1) (spinfulIndex N i σ)
              (Function.update (tJConfigOf N s) (spinfulIndex N j σ) 0)) *
            basisVec
              (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j σ) 0)
                (spinfulIndex N i σ) 1)
              (tJConfigOf N s')
        else 0 := by
  rw [basisVec_sum_mul, fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  split
  · simp only [Pi.smul_apply, smul_eq_mul]
  · rfl

/-- **The source-empty single-hop matrix element vanishes.**  If site `j` does not carry spin `σ`,
the annihilation `ĉ_{jσ}` kills `|Φ_s⟩`, so the per-term element is `0`. -/
theorem tJ_hop_matrixElement_eq_zero_of_source (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (σ : Fin 2) (hsrc : tJConfigOf N s (spinfulIndex N j σ) = 0) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  rw [tJ_hop_matrixElement_apply, if_neg]
  rintro ⟨h1, _⟩
  rw [hsrc] at h1
  exact absurd h1 (by decide)

/-- **The target-occupied single-hop matrix element vanishes.**  If `i ≠ j` and site `i` already
carries spin `σ`, the creation `ĉ†_{iσ}` hits a filled mode, so the per-term element is `0`. -/
theorem tJ_hop_matrixElement_eq_zero_of_target (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (σ : Fin 2) (hij : i ≠ j) (htgt : tJConfigOf N s (spinfulIndex N i σ) = 1) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  rw [tJ_hop_matrixElement_apply, if_neg]
  rintro ⟨_, h2⟩
  rw [Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j σ σ).mp h).1), htgt] at h2
  exact absurd h2 (by decide)

/-- **The target-other-spin single-hop matrix element vanishes.**  If `i ≠ j` and site `i` carries
the *opposite* spin `σ' ≠ σ`, then creating `(i,σ)` on top of the occupied `(i,σ')` would
double-occupy site `i`; that hopped configuration is not hard-core, while every bra `tJConfigOf s'`
is, so the per-term element is `0`. -/
theorem tJ_hop_matrixElement_eq_zero_of_target_other (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (σ σ' : Fin 2) (hσσ' : σ' ≠ σ) (hij : i ≠ j)
    (hother : tJConfigOf N s (spinfulIndex N i σ') = 1) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  rw [tJ_hop_matrixElement_apply]
  split
  · -- the hopped config is non-hard-core at site `i`, so it differs from the hard-core bra
    rw [basisVec_apply, if_neg ?_, mul_zero]
    intro heq
    -- `tJConfigOf s'` would have both `(i,σ)` and `(i,σ')` occupied
    have hp : tJConfigOf N s' (spinfulIndex N i σ) = 1 := by
      rw [heq, Function.update_self]
    have hp' : tJConfigOf N s' (spinfulIndex N i σ') = 1 := by
      rw [heq, Function.update_of_ne (fun h => hσσ' ((spinfulIndex_eq_iff N i i σ' σ).mp h).2),
        Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j σ' σ).mp h).1), hother]
    -- but a hard-core site state occupies at most one orbital of `i`
    rcases (show σ = 0 ∧ σ' = 1 ∨ σ = 1 ∧ σ' = 0 from by
      fin_cases σ <;> fin_cases σ' <;> simp_all (config := { decide := true })) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [tJConfigOf_apply_up] at hp; rw [tJConfigOf_apply_down] at hp'
      split at hp <;> split at hp' <;> simp_all
    · rw [tJConfigOf_apply_down] at hp; rw [tJConfigOf_apply_up] at hp'
      split at hp <;> split at hp' <;> simp_all
  · rfl

end LatticeSystem.Fermion
