import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSiteAnnihilation

/-!
# Tasaki §11.3.1: peeling a site annihilation through an `α`-Slater product (toward block ≤ 1)

A site annihilation `ĉ_{x,σ}` applied to an `α`-Slater product `(∏_q â†_{q.1,q.2}) |vac⟩` peels each
creation in turn, picking up the single-particle amplitude `α_{q.1}(x)` (when the spin matches) with
the Koszul sign of the creation's position:
`ĉ_{x,σ}·(∏ â†)|vac⟩ = ∑_i (-1)^i·(α_{l[i].1}(x) if l[i].2 = σ else 0)·monomial(eraseIdx i)`.

Proved by direct induction in the operators' native type (dodging the giant-type `isDefEq` blow-up),
using the site CAR `{ĉ_{x,σ}, â†_{p,τ}} = (α_p(x) if σ=τ else 0)·1` to move the annihilation past
each creation and `ĉ_{x,σ} |vac⟩ = 0` to discharge the tail.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- An `α`-Slater product on the vacuum: `(∏_{q ∈ l} â†_{q.1,q.2}) |vac⟩`. -/
noncomputable def flatBandASlater (K : ℕ) (ν : ℝ) (l : List (Fin (K + 1) × Fin 2)) :
    (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  ((l.map (fun q => flatBandACreation K ν q.1 q.2)).prod).mulVec
    (fermionMultiVacuum (2 * (2 * K + 1) + 1))

/-- Prepending a creation to an `α`-Slater product. -/
theorem flatBandASlater_cons (q : Fin (K + 1) × Fin 2) (l : List (Fin (K + 1) × Fin 2)) :
    flatBandASlater K ν (q :: l)
      = (flatBandACreation K ν q.1 q.2).mulVec (flatBandASlater K ν l) := by
  simp only [flatBandASlater, List.map_cons, List.prod_cons]
  rw [← Matrix.mulVec_mulVec]

/-- The single peeled contribution of position `i` in an `α`-Slater list. -/
noncomputable def flatBandPeelTerm (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2)) (σ : Fin 2)
    (l : List (Fin (K + 1) × Fin 2)) (i : Fin l.length) :
    (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ :=
  ((-1 : ℂ) ^ (i : ℕ)) •
    ((if (l.get i).2 = σ then (flatBandAlpha K ν (l.get i).1 x : ℂ) else 0) •
      flatBandASlater K ν (l.eraseIdx i))

/-- **The site-annihilation peel.**  `ĉ_{x,σ}` removes one `α` creation at a time from an `α`-Slater
product, each with amplitude `α_{l[i].1}(x)` (if the spin matches) and Koszul sign `(-1)^i`. -/
theorem flatBand_siteAnnihilation_peel (K : ℕ) (ν : ℝ) (x : Fin (2 * K + 2)) (σ : Fin 2)
    (l : List (Fin (K + 1) × Fin 2)) :
    (fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)).mulVec
        (flatBandASlater K ν l)
      = ∑ i : Fin l.length, flatBandPeelTerm K ν x σ l i := by
  induction l with
  | nil =>
    simp only [flatBandASlater, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact fermionMultiAnnihilation_mulVec_vacuum (2 * (2 * K + 1) + 1) _
  | cons q l' ih =>
    have hCAR : fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
          flatBandACreation K ν q.1 q.2
        = (if σ = q.2 then (flatBandAlpha K ν q.1 x : ℂ) else 0) • 1
          - flatBandACreation K ν q.1 q.2 *
            fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) := by
      rw [eq_sub_iff_add_eq]
      exact flatBand_siteAnnihilation_ACreation_anticomm K ν x σ q.2 q.1
    rw [flatBandASlater_cons, Matrix.mulVec_mulVec, hCAR, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_sum]
    -- restate the RHS index type `Fin (q::l').length` as the defeq `Fin (l'.length + 1)` so the
    -- `Fin.sum_univ_succ` cons-split matches syntactically
    change (if σ = q.2 then (flatBandAlpha K ν q.1 x : ℂ) else 0) • flatBandASlater K ν l'
        - ∑ i : Fin l'.length,
            (flatBandACreation K ν q.1 q.2).mulVec (flatBandPeelTerm K ν x σ l' i)
      = ∑ i : Fin (l'.length + 1), flatBandPeelTerm K ν x σ (q :: l') i
    -- leading term (position 0) is the peeled-off `q`; the `succ` terms cancel the moved-through â†
    rw [Fin.sum_univ_succ, sub_eq_iff_eq_add, add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero (fun i _ => ?_), add_zero]
    · -- leading: coeff_q • slater l' = flatBandPeelTerm (q::l') 0
      simp only [flatBandPeelTerm, List.get_cons_zero, List.eraseIdx_cons_zero, Fin.val_zero,
        pow_zero, one_smul]
      by_cases hσ : σ = q.2
      · rw [if_pos hσ, if_pos hσ.symm]
      · rw [if_neg hσ, if_neg (fun h => hσ h.symm), zero_smul]
    · -- per `succ` position: the peel term cancels the moved-through creation
      simp only [flatBandPeelTerm, List.get_cons_succ', List.eraseIdx_cons_succ, Fin.val_succ,
        pow_succ]
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← flatBandASlater_cons, ← add_smul]
      rw [show (-1 : ℂ) ^ (i : ℕ) * -1 + (-1 : ℂ) ^ (i : ℕ) = 0 by ring, zero_smul]

end LatticeSystem.Fermion
