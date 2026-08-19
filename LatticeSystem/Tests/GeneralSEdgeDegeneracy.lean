import LatticeSystem.Quantum.SpinS.GeneralSOpenChainGroundSpace
import LatticeSystem.Quantum.SpinS.AKLTOpenChainCompleteness

/-!
# Tasaki §8.3.1: the exact `(S+1)²` edge degeneracy of the general-`S` open AKLT chain

Regression pins for the capstone of the general-`S` open-chain edge-degeneracy arc (#5292, PR-7):
the matching upper bound `finrank_openAKLTGroundSpaceGeneralS_le_succ_sq`, the two-sided capstone
`finrank_openAKLTGroundSpaceGeneralS_eq_succ_sq`, and the `S = 1` identification
`openAKLTGroundSpaceGeneralS_one` with the `S = 1` open-chain ground space `openAKLTGroundSpace`.

Every declaration these pins reference is production code that does **not exist yet** in this PR
(TDD Red); each pin is therefore stated as the target type with a `sorry` body rather than a call
to a not-yet-existing name, so the pin itself already fixes the signature to be implemented while
`warningAsError`/`mathlibStandardSet` turns the `sorry` into a build error until the real proof
lands.
-/

open Matrix MvPolynomial
open LatticeSystem.Quantum

namespace LatticeSystem.Tests.GeneralSEdgeDegeneracy

/-! ### 1. Signature pin: the upper bound -/

/-- **Signature pin: `(S+1)²` upper-bounds the general-`S` open-chain ground-space dimension.** -/
example {m S : ℕ} (hS : S ≠ 0) :
    Module.finrank ℂ (openAKLTGroundSpaceGeneralS (m + 2) S) ≤ (S + 1) ^ 2 := by
  sorry

/-! ### 2. Signature pin: the capstone (exact `(S+1)²` edge degeneracy) -/

/-- **Signature pin: the exact `(S+1)²` edge degeneracy** (Tasaki §8.3.1, p. 252). -/
example {m S : ℕ} (hS : S ≠ 0) :
    Module.finrank ℂ (openAKLTGroundSpaceGeneralS (m + 2) S) = (S + 1) ^ 2 := by
  sorry

/-! ### 3. Signature pin: the `S = 1` identification -/

/-- **Signature pin: at `S = 1` the general-`S` ground space is the `S = 1` open-chain ground
space.** -/
example {L : ℕ} (hL : 1 ≤ L) :
    openAKLTGroundSpaceGeneralS L 1 = openAKLTGroundSpace L := by
  sorry

/-! ### 4. `S = 1` cross-check: the capstone reproduces `finrank_openAKLTGroundSpace_eq_four` -/

/-- **Acceptance criterion: `S = 1` reproduces `finrank_openAKLTGroundSpace_eq_four`.**  This is the
issue's own cross-check that the general-`S` capstone, specialised at `S = 1` and pushed through the
`S = 1` identification, recovers the previously-proved `4`-fold degeneracy of the `S = 1` open
chain. -/
example {L : ℕ} (hL : 2 ≤ L) : Module.finrank ℂ (openAKLTGroundSpace L) = 4 := by
  sorry

/-! ### 5. Value pin: `S = 2`, `m = 0` — the nine-fold case Tasaki names on p. 252 -/

/-- **Value pin, equality version.**  The single-bond (`m = 0`) two-site chain at `S = 2` has
ground-space dimension *exactly* `9`, upgrading the `9 ≤` lower-bound pin of
`Tests/GeneralSEdgeDegeneracyLowerBound.lean`. -/
example : Module.finrank ℂ (openAKLTGroundSpaceGeneralS 2 2) = 9 := by
  sorry

end LatticeSystem.Tests.GeneralSEdgeDegeneracy
