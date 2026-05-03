import LatticeSystem.Quantum.SpinS.SingleSiteCasimirExpectation
import LatticeSystem.Quantum.SpinS.SingleSiteZExpectation

/-!
# Single-site xy-plane Casimir expectation on all-aligned states

For the all-aligned state `|c..c⟩`, the in-plane Casimir
`(Ŝ^{(1)}_x)² + (Ŝ^{(2)}_x)²` (sum of squares of the two
transverse single-site spin operators) has expectation value

  `N(N+2)/4 − (N/2 − c.val)²`

which simplifies to `N/4 = S/2` for the extremal cases `c = 0` (all
up) and `c = N` (all down). This is a clean direct subtraction
using the universal Casimir identity (PR #920) and the explicit
z-axis squared expectation (PR #925).

For the highest-weight state, this gives `S/2` per axis (split
evenly by symmetry between Ŝ^{(1)} and Ŝ^{(2)}). Together with
`⟨(Ŝ^{(3)})²⟩ = S²` (PR #925), the variance on |⊤⟩ is:
- `Var(Ŝ^{(α)})` for `α = 3`: `0` (since `⟨Ŝ^{(3)}⟩ = S`).
- `⟨(Ŝ^{(α)})²⟩` for `α = 1, 2`: `S/2` each (since `⟨Ŝ^{(α)}⟩ = 0`).

This contrasts with the SU(2)-symmetric AFM ground-state variance
`S(S+1)/3` (Tasaki Problem 2.5.c, γ-7), which requires SU(2)
invariance of the GS — a property the saturated ferromagnet does
not have.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Single-site xy-plane Casimir expectation on |c..c⟩**:

  `⟨|c..c⟩, ((Ŝ^{(1)}_x)² + (Ŝ^{(2)}_x)²) · |c..c⟩⟩ =
    N(N+2)/4 − (N/2 − c.val)²`.

Proof: subtract the z-axis squared expectation (PR #925) from the
universal full-Casimir expectation (PR #920). -/
theorem allAlignedStateS_expectation_onSiteS_spinSOp1_sq_add_spinSOp2_sq
    (x : V) (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      (((onSiteS x (spinSOp1 N) : ManyBodyOpS V N) *
          onSiteS x (spinSOp1 N) +
        onSiteS x (spinSOp2 N) * onSiteS x (spinSOp2 N)).mulVec
        (allAlignedStateS V N c)) =
      ((N : ℂ) * (N + 2) / 4) -
        (((N : ℂ) / 2 - (c.val : ℂ)) * ((N : ℂ) / 2 - (c.val : ℂ))) := by
  -- Use spinSDot x x N = (Ŝ^(1))² + (Ŝ^(2))² + (Ŝ^(3))² (def of spinSDot)
  -- to rewrite the expectation.
  have h_xy_eq : ((onSiteS x (spinSOp1 N) : ManyBodyOpS V N) *
      onSiteS x (spinSOp1 N) +
      onSiteS x (spinSOp2 N) * onSiteS x (spinSOp2 N)) =
      (spinSDot x x N : ManyBodyOpS V N) -
        (onSiteS x (spinSOp3 N) * onSiteS x (spinSOp3 N)) := by
    unfold spinSDot
    abel
  rw [h_xy_eq, Matrix.sub_mulVec, dotProduct_sub]
  rw [spinSDot_self_expectation_allAlignedStateS]
  rw [allAlignedStateS_expectation_onSiteS_spinSOp3_sq]

end LatticeSystem.Quantum
