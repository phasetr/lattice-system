import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Single-site `Ŝ^{(3)}_x` and `(Ŝ^{(3)}_x)²` expectations on
all-aligned states

For the all-aligned state `|c..c⟩` (constant configuration at value
`c : Fin (N + 1)`), the single-site z-component operator
`Ŝ^{(3)}_x = onSiteS x (spinSOp3 N)` has expectation values:

- `⟨|c..c⟩, Ŝ^{(3)}_x · |c..c⟩⟩ = (N/2 − c.val)` per site `x`.
- `⟨|c..c⟩, (Ŝ^{(3)}_x)² · |c..c⟩⟩ = (N/2 − c.val)²` per site `x`.

For the highest-weight state (`c = 0`), this gives `N/2 = S` and
`(N/2)² = S²` respectively. Note the variance per axis equals
`S²`, NOT the SU(2)-symmetric `S(S+1)/3` — reflecting that the
saturated-ferromagnet ground state is NOT SU(2)-invariant.

These computations contrast with PR #920's universal full-Casimir
expectation `S(S+1)`: the full Casimir splits unevenly across axes
in non-SU(2)-symmetric states. Background for Tasaki Problem 2.5.c
(γ-7), which derives `S(S+1)/3` only for the AFM SU(2)-symmetric
GS.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `Ŝ^{(3)}_x · |c..c⟩ = (N/2 − c.val) · |c..c⟩` (single-site
eigenvalue identity on the all-aligned state). -/
theorem onSiteS_spinSOp3_mulVec_allAlignedStateS (x : V)
    (c : Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) : ManyBodyOpS V N).mulVec
        (allAlignedStateS V N c) =
      ((N : ℂ) / 2 - (c.val : ℂ)) • allAlignedStateS V N c := by
  unfold allAlignedStateS
  rw [onSiteS_spinSOp3_mulVec_basisVecS]
  rfl

/-- Single-site `Ŝ^{(3)}_x` expectation on the all-aligned state:
`⟨|c..c⟩, Ŝ^{(3)}_x · |c..c⟩⟩ = N/2 − c.val`. -/
theorem allAlignedStateS_expectation_onSiteS_spinSOp3 (x : V)
    (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N).mulVec
        (allAlignedStateS V N c)) =
      (N : ℂ) / 2 - (c.val : ℂ) := by
  rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
  rw [dotProduct_smul, smul_eq_mul, allAlignedStateS_inner_self, mul_one]

/-- `(Ŝ^{(3)}_x)² · |c..c⟩ = (N/2 − c.val)² · |c..c⟩`: applying
the single-site z-operator twice. -/
theorem onSiteS_spinSOp3_sq_mulVec_allAlignedStateS (x : V)
    (c : Fin (N + 1)) :
    ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
      onSiteS x (spinSOp3 N)).mulVec (allAlignedStateS V N c) =
      (((N : ℂ) / 2 - (c.val : ℂ)) *
        ((N : ℂ) / 2 - (c.val : ℂ))) • allAlignedStateS V N c := by
  rw [← Matrix.mulVec_mulVec]
  rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
  rw [Matrix.mulVec_smul]
  rw [onSiteS_spinSOp3_mulVec_allAlignedStateS]
  rw [smul_smul]

/-- Single-site `(Ŝ^{(3)}_x)²` expectation on the all-aligned state:
`⟨|c..c⟩, (Ŝ^{(3)}_x)² · |c..c⟩⟩ = (N/2 − c.val)²`. -/
theorem allAlignedStateS_expectation_onSiteS_spinSOp3_sq (x : V)
    (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      (((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
        onSiteS x (spinSOp3 N)).mulVec (allAlignedStateS V N c)) =
      ((N : ℂ) / 2 - (c.val : ℂ)) * ((N : ℂ) / 2 - (c.val : ℂ)) := by
  rw [onSiteS_spinSOp3_sq_mulVec_allAlignedStateS]
  rw [dotProduct_smul, smul_eq_mul, allAlignedStateS_inner_self, mul_one]

end LatticeSystem.Quantum
