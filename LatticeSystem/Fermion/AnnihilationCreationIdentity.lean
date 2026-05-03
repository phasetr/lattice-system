import LatticeSystem.Fermion.Mode

/-!
# `c · c† = 1 − n` for the single-mode fermion

Direct corollary of `fermionAnticomm_self` (`c · c† + c† · c = 1`)
and `fermionNumber_eq_creation_mul_annihilation` (`n = c† · c`):

  `c · c† = 1 − n`.

This is the standard "hole occupation" identity: the eigenvalue of
`c · c†` on the vacuum is `1` (vacuum is unoccupied) and on the
occupied state is `0` (occupied has no hole).

Tracked as part of Tasaki §2.4 / §2.5 / Phase 2 fermion infrastructure
(Issue #412).
-/

namespace LatticeSystem.Fermion

/-- `c · c† = 1 − n`. -/
theorem fermionAnnihilation_mul_fermionCreation_eq_one_sub_number :
    fermionAnnihilation * fermionCreation = 1 - fermionNumber := by
  -- From fermionAnticomm_self: c · c† + c† · c = 1.
  -- And fermionNumber = c† · c.
  -- So c · c† = 1 - c† · c = 1 - n.
  have hac := fermionAnticomm_self
  have hn := fermionNumber_eq_creation_mul_annihilation
  -- hac : c · c† + c† · c = 1, hn : n = c† · c.
  rw [hn]
  exact eq_sub_of_add_eq hac

end LatticeSystem.Fermion
