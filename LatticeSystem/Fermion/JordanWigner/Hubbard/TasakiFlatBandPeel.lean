import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandOccBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandDualAnnihilation

/-!
# Tasaki §11.3.1: the dual-annihilator peel on occupation monomials (`BKernel ⊆ AlphaFock`)

The dual β-annihilator `d_{u,σ}` anticommutes (to `0`) with every rotated mode creation
`Ĉ†_τ(basis j)` except `b̂†_{u,σ}` (the mode `(inr u, σ)`), with which it gives the Kronecker `1`.
Hence `d_{u,σ}` peels the β-mode `(inr u, σ)` off an occupation monomial (removing it, up to a
nonzero sign) when present, and annihilates the monomial when absent.  This is the engine that
forces a
`b̂`-kernel vector to have no β-occupation, i.e. to lie in the α-Fock subspace.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **`{d_{u,σ}, Ĉ†_τ(basis j)} = 0`** for every rotated mode `(j, τ) ≠ (inr u, σ)`: the dual
annihilator passes every creation except its own `b̂†_{u,σ}` (`{d,â†}=0`, and `{d,b̂†_{w,τ}}=0`
unless `(w,τ)=(u,σ)`). -/
theorem flatBandDualBAnnihilation_basisCreation_anticomm (u : Fin (K + 1)) (σ τ : Fin 2)
    (j : Fin (K + 1) ⊕ Fin (K + 1)) (hj : (j, τ) ≠ (Sum.inr u, σ)) :
    flatBandDualBAnnihilation K ν u σ * flatBandModeCreation K τ (flatBandBasis K ν j)
      + flatBandModeCreation K τ (flatBandBasis K ν j) * flatBandDualBAnnihilation K ν u σ = 0 := by
  rw [flatBandModeCreation_basis]
  rcases j with p | w
  · rw [Sum.elim_inl]
    exact flatBandDualBAnnihilation_ACreation_anticomm K ν u p σ τ
  · rw [Sum.elim_inr, flatBandDualBAnnihilation_BCreation_anticomm]
    rw [if_neg (fun h => hj (by rw [h.1, h.2])), zero_smul]

/-- **`{d_{u,σ}, b̂†_{u,σ}} = 1`** (the matching β-mode). -/
theorem flatBandDualBAnnihilation_BCreation_self (u : Fin (K + 1)) (σ : Fin 2) :
    flatBandDualBAnnihilation K ν u σ * flatBandBCreation K ν u σ
      + flatBandBCreation K ν u σ * flatBandDualBAnnihilation K ν u σ = 1 := by
  rw [flatBandDualBAnnihilation_BCreation_anticomm, if_pos ⟨rfl, rfl⟩, one_smul]

/-- **The dual annihilator passes an ordered creation product down to the vacuum** when it
anticommutes with every factor.  Proved by a direct induction in the flat-band operators' native
type, so the generic `anticomm_listProd_mulVec_vacuum` (whose `Fin (M+1)` shape mismatches the
operators' `Fin (2*(2*K+1)+2)`) is avoided, dodging a giant-type `isDefEq` blow-up. -/
theorem flatBandDual_passThrough_listProd_mulVec_vacuum (u : Fin (K + 1)) (σ : Fin 2)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hl : ∀ q ∈ l, flatBandDualBAnnihilation K ν u σ *
          flatBandModeCreation K q.2 (flatBandBasis K ν q.1)
        + flatBandModeCreation K q.2 (flatBandBasis K ν q.1) *
          flatBandDualBAnnihilation K ν u σ = 0) :
    (flatBandDualBAnnihilation K ν u σ).mulVec
      (((l.map (fun q => flatBandModeCreation K q.2 (flatBandBasis K ν q.1))).prod).mulVec
        (fermionMultiVacuum (2 * (2 * K + 1) + 1))) = 0 := by
  induction l with
  | nil =>
    simpa using flatBandDualBAnnihilation_mulVec_vacuum K ν u σ
  | cons q l' ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      eq_neg_of_add_eq_zero_left (hl q (List.mem_cons.mpr (Or.inl rfl))),
      Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      ih (fun p hp => hl p (List.mem_cons.mpr (Or.inr hp))), Matrix.mulVec_zero, neg_zero]

/-- **The dual annihilator peels its own leading `b̂†_{u,σ}` off a product on the vacuum** (when it
passes every remaining factor): `d_{u,σ} · (b̂†_{u,σ} ∏) |vac⟩ = (∏) |vac⟩`.  Uses
`{d_{u,σ}, b̂†_{u,σ}} = 1` and the pass-through on the rest. -/
theorem flatBandDual_peelLeading_mulVec_vacuum (u : Fin (K + 1)) (σ : Fin 2)
    (l : List ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2))
    (hl : ∀ q ∈ l, flatBandDualBAnnihilation K ν u σ *
          flatBandModeCreation K q.2 (flatBandBasis K ν q.1)
        + flatBandModeCreation K q.2 (flatBandBasis K ν q.1) *
          flatBandDualBAnnihilation K ν u σ = 0) :
    (flatBandDualBAnnihilation K ν u σ).mulVec ((flatBandBCreation K ν u σ *
        ((l.map (fun q => flatBandModeCreation K q.2 (flatBandBasis K ν q.1))).prod)).mulVec
          (fermionMultiVacuum (2 * (2 * K + 1) + 1)))
      = ((l.map (fun q => flatBandModeCreation K q.2 (flatBandBasis K ν q.1))).prod).mulVec
          (fermionMultiVacuum (2 * (2 * K + 1) + 1)) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    show flatBandDualBAnnihilation K ν u σ * flatBandBCreation K ν u σ
        = 1 - flatBandBCreation K ν u σ * flatBandDualBAnnihilation K ν u σ from by
      rw [eq_sub_iff_add_eq]; exact flatBandDualBAnnihilation_BCreation_self u σ,
    Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, flatBandDual_passThrough_listProd_mulVec_vacuum u σ l hl,
    Matrix.mulVec_zero, sub_zero]

/-- **`d_{u,σ}` annihilates an occupation monomial with the β-mode `(inr u, σ)` empty.** -/
theorem flatBandDualBAnnihilation_mulVec_occMonomial_of_not_mem (u : Fin (K + 1)) (σ : Fin 2)
    (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) (hf : (Sum.inr u, σ) ∉ occFinset f) :
    (flatBandDualBAnnihilation K ν u σ).mulVec (occMonomial K ν f) = 0 := by
  rw [occMonomial, flatBandModeMonomial]
  refine flatBandDual_passThrough_listProd_mulVec_vacuum u σ (occFinset f).toList
    (fun q hq => ?_)
  refine flatBandDualBAnnihilation_basisCreation_anticomm u σ q.2 q.1 ?_
  rw [Prod.mk.eta]
  rintro rfl
  exact hf (Finset.mem_toList.mp hq)

end LatticeSystem.Fermion
