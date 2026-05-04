import LatticeSystem.Fermion.AnnihilationCreationIdentity

/-!
# Fermion `c`–`c†` commutator: `[c, c†] = 1 − 2 · n`

For the single-mode fermion the operators `c` and `c†` satisfy
the standard commutator identity

  `[c, c†] = c · c† − c† · c = (1 − n) − n = 1 − 2 · n`.

Direct from
- `c · c† = 1 − n` (PR #963), and
- `c† · c = n` (`fermionNumber_eq_creation_mul_annihilation`).

Together with the anticommutator `{c, c†} = 1` (`fermionAnticomm_self`)
this encodes the algebraic difference between fermions and bosons:
the bosonic commutator `[a, a†] = 1` is number-independent, while
its fermion counterpart `[c, c†] = 1 − 2n` becomes `+1` on the
vacuum (`n = 0`) and `−1` on the occupied state (`n = 1`).

Tracked as part of Phase 2 fermion infrastructure (Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `[c, c†] = c · c† − c† · c = 1 − 2 · n`. -/
theorem fermionAnnihilation_commutator_fermionCreation :
    fermionAnnihilation * fermionCreation
        - fermionCreation * fermionAnnihilation
      = 1 - (2 : ℂ) • fermionNumber := by
  rw [fermionAnnihilation_mul_fermionCreation_eq_one_sub_number,
    ← fermionNumber_eq_creation_mul_annihilation]
  -- Goal: (1 - n) - n = 1 - 2 • n.
  rw [show (2 : ℂ) • fermionNumber = fermionNumber + fermionNumber from by
    rw [show (2 : ℂ) = 1 + 1 from by norm_num, add_smul, one_smul]]
  abel

end LatticeSystem.Fermion
