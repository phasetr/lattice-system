import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSiteModeCAR
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeMonomial

/-!
# Tasaki §11.3.1: peeling a site annihilation through an occupation monomial (toward block ≤ 1)

A site annihilation `ĉ_{x,σ}` applied to a rotated occupation/Fock monomial
`(∏_q Ĉ†_{q.2}(basis q.1)) |vac⟩` peels each mode creation in turn, picking up the single-particle
amplitude `(basis q.1)(x)` (when the spin matches) with the Koszul sign of the creation's position:
`ĉ_{x,σ}·(∏ Ĉ†)|vac⟩ = ∑_i (-1)^i·((basis M[i].1)(x) if M[i].2 = σ else 0)·monomial(eraseIdx i)`.

Proved by direct induction in the operators' native type, using the general site/mode CAR
`{ĉ_{x,σ}, Ĉ†_τ(w)} = (w(x) if σ=τ else 0)·1` to move the annihilation past each creation and
`ĉ_{x,σ} |vac⟩ = 0` to discharge the tail.  Unlike the `α`-Slater peel this acts directly on the
`flatBandModeMonomial` that the `flatBandOccBasis` is built from, so no list re-indexing is
needed to read occupation-basis coordinates.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- The single peeled contribution of position `i` in a rotated mode-monomial list. -/
noncomputable def flatBandModePeelTerm (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2)) (σ : Fin 2)
    (M : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) (i : Fin M.length) :
    (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) •
    ((if (M.get i).2 = σ then (flatBandBasis K ν (M.get i).1 x : ℂ) else 0) •
      flatBandModeMonomial K ν (M.eraseIdx i))

/-- **The occupation-monomial site-annihilation peel.**  `ĉ_{x,σ}` removes one mode creation at a
time from a rotated monomial, each with amplitude `(basis M[i].1)(x)` (if the spin matches) and
Koszul sign `(-1)^i`. -/
theorem flatBand_siteAnnihilation_peel_modeMonomial (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2))
    (σ : Fin 2) (M : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2)) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)).mulVec
        (flatBandModeMonomial K ν M)
      = ∑ i : Fin M.length, flatBandModePeelTerm K ν x σ M i := by
  induction M with
  | nil =>
    simp only [flatBandModeMonomial, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact fermionMultiAnnihilation_mulVec_vacuum (2 * (2 * K + 1) + 1) _
  | cons q l' ih =>
    have hcons : flatBandModeMonomial K ν (q :: l')
        = (flatBandModeCreation K q.2 (flatBandBasis K ν q.1)).mulVec
            (flatBandModeMonomial K ν l') :=
      (flatBandModeCreation_mulVec_monomial q.1 q.2 l').symm
    have hCAR : fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
          flatBandModeCreation K q.2 (flatBandBasis K ν q.1)
        = (if σ = q.2 then (flatBandBasis K ν q.1 x : ℂ) else 0) • 1
          - flatBandModeCreation K q.2 (flatBandBasis K ν q.1) *
            fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) := by
      rw [eq_sub_iff_add_eq]
      exact flatBand_siteAnnihilation_modeCreation_anticomm K σ q.2 (flatBandBasis K ν q.1) x
    rw [hcons, Matrix.mulVec_mulVec, hCAR, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_sum]
    change (if σ = q.2 then (flatBandBasis K ν q.1 x : ℂ) else 0) • flatBandModeMonomial K ν l'
        - ∑ i : Fin l'.length,
            (flatBandModeCreation K q.2 (flatBandBasis K ν q.1)).mulVec
              (flatBandModePeelTerm K ν x σ l' i)
      = ∑ i : Fin (l'.length + 1), flatBandModePeelTerm K ν x σ (q :: l') i
    rw [Fin.sum_univ_succ, sub_eq_iff_eq_add, add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero (fun i _ => ?_), add_zero]
    · simp only [flatBandModePeelTerm, List.get_cons_zero, List.eraseIdx_cons_zero, Fin.val_zero,
        pow_zero, one_smul]
      by_cases hσ : σ = q.2
      · rw [if_pos hσ, if_pos hσ.symm]
      · rw [if_neg hσ, if_neg (fun h => hσ h.symm), zero_smul]
    · simp only [flatBandModePeelTerm, List.get_cons_succ', List.eraseIdx_cons_succ, Fin.val_succ,
        pow_succ]
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, flatBandModeCreation_mulVec_monomial, ← add_smul]
      rw [show (-1 : ℂ) ^ (i : ℕ) * -1 + (-1 : ℂ) ^ (i : ℕ) = 0 by ring, zero_smul]

end LatticeSystem.Fermion
