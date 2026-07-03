import LatticeSystem.Fermion.JordanWigner.AnnihilationCreationBasisVec

/-!
# Action of a single hopping term on computational basis states

Composing the single-mode annihilation/creation actions
(`fermionMultiAnnihilation_mulVec_basisVec`,
`fermionMultiCreation_mulVec_basisVec`), this file computes the action of a
single hopping term `c†_p c_q` on a computational basis state `basisVec c`, the
final operator-level ingredient for the Tasaki §11.2 hopping matrix elements
(eq. (11.2.4)/(11.2.5)).

The term `c†_p c_q` first annihilates an electron at mode `q` (requiring
`c q = 1`) and then creates one at mode `p` (requiring the intermediate
configuration to be empty at `p`). The result is the hopped basis state
`|c with q ↦ 0, p ↦ 1⟩` weighted by the product of the two Jordan–Wigner string
signs, and `0` otherwise.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, pp. 382-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- Action of a single hopping term `c†_p c_q` on a computational basis state:
the electron hops from `q` to `p` when `q` is occupied and the intermediate
configuration is empty at `p`, picking up the product of the two Jordan–Wigner
string signs; otherwise the result is `0`. -/
theorem fermionMultiCreation_mul_Annihilation_mulVec_basisVec
    (M : ℕ) (p q : Fin (M + 1)) (c : Fin (M + 1) → Fin 2) :
    (fermionMultiCreation M p * fermionMultiAnnihilation M q).mulVec (basisVec c) =
      if c q = 1 ∧ (Function.update c q 0) p = 0 then
        (jwSign M q c * jwSign M p (Function.update c q 0)) •
          basisVec (Function.update (Function.update c q 0) p 1)
      else 0 := by
  rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec]
  by_cases hq : c q = 1
  · rw [if_pos hq, Matrix.mulVec_smul, fermionMultiCreation_mulVec_basisVec]
    by_cases hp : (Function.update c q 0) p = 0
    · rw [if_pos hp, if_pos ⟨hq, hp⟩, smul_smul]
    · rw [if_neg hp, smul_zero, if_neg (fun h => hp h.2)]
  · rw [if_neg hq, Matrix.mulVec_zero, if_neg (fun h => hq h.1)]

/-- Action of a pair-creation term `c†_p c†_q` on a computational basis state:
the electrons are created at `q` then at `p` when `q` is empty and the
intermediate configuration is empty at `p`, picking up the product of the two
Jordan–Wigner string signs; otherwise the result is `0`. -/
theorem fermionMultiCreation_mul_Creation_mulVec_basisVec
    (M : ℕ) (p q : Fin (M + 1)) (c : Fin (M + 1) → Fin 2) :
    (fermionMultiCreation M p * fermionMultiCreation M q).mulVec (basisVec c) =
      if c q = 0 ∧ (Function.update c q 1) p = 0 then
        (jwSign M q c * jwSign M p (Function.update c q 1)) •
          basisVec (Function.update (Function.update c q 1) p 1)
      else 0 := by
  rw [← Matrix.mulVec_mulVec, fermionMultiCreation_mulVec_basisVec]
  by_cases hq : c q = 0
  · rw [if_pos hq, Matrix.mulVec_smul, fermionMultiCreation_mulVec_basisVec]
    by_cases hp : (Function.update c q 1) p = 0
    · rw [if_pos hp, if_pos ⟨hq, hp⟩, smul_smul]
    · rw [if_neg hp, smul_zero, if_neg (fun h => hp h.2)]
  · rw [if_neg hq, Matrix.mulVec_zero, if_neg (fun h => hq h.1)]

/-- Action of a pair-annihilation term `c_p c_q` on a computational basis state:
the electrons are annihilated at `q` then at `p` when `q` is occupied and the
intermediate configuration is occupied at `p`, picking up the product of the two
Jordan–Wigner string signs; otherwise the result is `0`. -/
theorem fermionMultiAnnihilation_mul_Annihilation_mulVec_basisVec
    (M : ℕ) (p q : Fin (M + 1)) (c : Fin (M + 1) → Fin 2) :
    (fermionMultiAnnihilation M p * fermionMultiAnnihilation M q).mulVec (basisVec c) =
      if c q = 1 ∧ (Function.update c q 0) p = 1 then
        (jwSign M q c * jwSign M p (Function.update c q 0)) •
          basisVec (Function.update (Function.update c q 0) p 0)
      else 0 := by
  rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec]
  by_cases hq : c q = 1
  · rw [if_pos hq, Matrix.mulVec_smul, fermionMultiAnnihilation_mulVec_basisVec]
    by_cases hp : (Function.update c q 0) p = 1
    · rw [if_pos hp, if_pos ⟨hq, hp⟩, smul_smul]
    · rw [if_neg hp, smul_zero, if_neg (fun h => hp h.2)]
  · rw [if_neg hq, Matrix.mulVec_zero, if_neg (fun h => hq h.1)]

end LatticeSystem.Fermion
