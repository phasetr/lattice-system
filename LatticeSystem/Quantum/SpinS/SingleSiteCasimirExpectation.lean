import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations

/-!
# Universal single-site Casimir expectation

For any state `Φ` on the multi-site spin-`S` Hilbert space and any
site `x : V`, the single-site Casimir `Ŝ_x · Ŝ_x` acts as the
scalar `S(S+1) = N(N+2)/4`:

  `(Ŝ_x · Ŝ_x).mulVec Φ = (N(N+2)/4) · Φ`,

independent of `Φ`. Hence the expectation value is

  `⟨Φ, Ŝ_x · Ŝ_x · Φ⟩ = (N(N+2)/4) · ⟨Φ, Φ⟩`.

For a normalized state, this is exactly `S(S+1)`. This is the
universal single-site Casimir identity (the spin operator at any
site has Casimir eigenvalue `S(S+1)` on every state).

Used in Tasaki Problem 2.5.c which derives
`⟨(Ŝ_x^{(α)})²⟩ = S(S+1)/3` per axis from this universal value
plus SU(2) symmetry of the AFM ground state.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The single-site Casimir acts as the scalar `N(N+2)/4` on any
state. Direct corollary of `spinSDot_self`. -/
theorem spinSDot_self_mulVec (x : V) (Φ : (V → Fin (N + 1)) → ℂ) :
    (spinSDot x x N).mulVec Φ = ((N : ℂ) * (N + 2) / 4) • Φ := by
  rw [spinSDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **Universal single-site Casimir expectation value**: for any
state `Φ`, `⟨Φ, Ŝ_x · Ŝ_x · Φ⟩ = (N(N+2)/4) · ⟨Φ, Φ⟩`. -/
theorem spinSDot_self_expectation (x : V)
    (Φ : (V → Fin (N + 1)) → ℂ) :
    dotProduct (star Φ) ((spinSDot x x N).mulVec Φ) =
      ((N : ℂ) * (N + 2) / 4) * dotProduct (star Φ) Φ := by
  rw [spinSDot_self_mulVec, dotProduct_smul, smul_eq_mul]

/-- For a normalized state (`⟨Φ, Φ⟩ = 1`), the single-site Casimir
expectation is exactly `S(S+1) = N(N+2)/4`. -/
theorem spinSDot_self_expectation_normalized (x : V)
    {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ : dotProduct (star Φ) Φ = 1) :
    dotProduct (star Φ) ((spinSDot x x N).mulVec Φ) =
      ((N : ℂ) * (N + 2) / 4) := by
  rw [spinSDot_self_expectation, hΦ, mul_one]

/-- Specialisation to the all-aligned states (which are normalized
by PR #913 `allAlignedStateS_inner_self`). -/
theorem spinSDot_self_expectation_allAlignedStateS
    (x : V) (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      ((spinSDot x x N).mulVec (allAlignedStateS V N c)) =
      ((N : ℂ) * (N + 2) / 4) := by
  exact spinSDot_self_expectation_normalized x (allAlignedStateS_inner_self c)

end LatticeSystem.Quantum
