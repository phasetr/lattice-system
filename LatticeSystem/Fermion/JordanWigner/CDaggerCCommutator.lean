import LatticeSystem.Fermion.JordanWigner.CAR.SameSite

/-!
# Multi-mode Jordan–Wigner `c_i`–`c_i†` commutator
`[c_i, c_i†] = 1 − 2 · n_i`

Multi-mode (Jordan–Wigner) mirror of single-mode PR #989. The
same-site commutator

  `[c_i, c_i†] = c_i · c_i† − c_i† · c_i = (1 − n_i) − n_i
                                        = 1 − 2 · n_i`

follows from
- the same-site CAR `c_i · c_i† + c_i† · c_i = 1`
  (`fermionMultiAnticomm_self`, `JordanWigner/CAR/SameSite.lean`),
  giving `c_i · c_i† = 1 − c_i† · c_i = 1 − n_i`, and
- the definitional equality `n_i = c_i† · c_i`
  (`fermionMultiNumber` is defined this way in
  `JordanWigner/Operators.lean`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- `[c_i, c_i†] = c_i · c_i† − c_i† · c_i = 1 − 2 · n_i`. -/
theorem fermionMultiAnnihilation_commutator_fermionMultiCreation_self
    (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiCreation N i -
        fermionMultiCreation N i * fermionMultiAnnihilation N i =
      (1 : ManyBodyOp (Fin (N + 1))) -
        (2 : ℂ) • fermionMultiNumber N i := by
  -- From CAR: c_i · c_i† = 1 - c_i† · c_i = 1 - n_i.
  have hac := fermionMultiAnticomm_self N i
  have hac' : fermionMultiAnnihilation N i * fermionMultiCreation N i =
      1 - fermionMultiCreation N i * fermionMultiAnnihilation N i :=
    eq_sub_of_add_eq hac
  -- `n_i = c_i† · c_i` is definitional (`fermionMultiNumber`).
  rw [hac', show fermionMultiCreation N i * fermionMultiAnnihilation N i =
      fermionMultiNumber N i from rfl]
  -- Goal: (1 - n_i) - n_i = 1 - 2 • n_i.
  rw [show (2 : ℂ) • fermionMultiNumber N i =
      fermionMultiNumber N i + fermionMultiNumber N i from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  abel

end LatticeSystem.Fermion
