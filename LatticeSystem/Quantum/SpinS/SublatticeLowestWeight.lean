import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder

/-!
# Sublattice lowest-weight Casimir relation

Scaffold for the minimal-total-spin joint eigenstate (Issue #3674, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

A sublattice-weight vector annihilated by the sublattice *lowering* operator
`Ŝ_A^-` is a `(Ŝ_A)²`-eigenvector with eigenvalue `m_A(m_A − 1)`, where `m_A` is
its `Ŝ_A^(3)` eigenvalue.  This is the lowest-weight companion of
`sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpPlus_eq_zero` (#3663), derived
from the other sublattice Cartan identity
`Ŝ_A^+ Ŝ_A^- = (Ŝ_A^1)² + (Ŝ_A^2)² + Ŝ_A^(3)`.

For the lowest weight `m_A = −s_A` this gives `(Ŝ_A)² = (−s_A)(−s_A − 1) =
s_A(s_A + 1)` — the maximal sublattice Casimir — so the all-spins-down sublattice
state realizes the max `(Ŝ_A)²` eigenvalue, the building block (together with the
all-spins-up state on the complement) of the minimal-total-spin state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Sublattice lowest-weight Casimir relation**: if `Ŝ_A^(3) w = m_A · w` and
`Ŝ_A^- w = 0`, then `(Ŝ_A)² w = m_A(m_A − 1) · w`.

`(Ŝ_A)² = Ŝ_A^+ Ŝ_A^- − Ŝ_A^(3) + (Ŝ_A^(3))²` (the other sublattice Cartan
identity); on a lowest-weight `Ŝ_A^(3)`-eigenvector the `Ŝ_A^+ Ŝ_A^-` term vanishes
and the rest is `m_A² − m_A = m_A(m_A − 1)`. -/
theorem sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpMinus_eq_zero
    (A : V → Bool) {m_A : ℂ} {w : (V → Fin (N + 1)) → ℂ}
    (hmag : (sublatticeSpinSOp3 N A).mulVec w = m_A • w)
    (hker : (sublatticeSpinSOpMinus N A).mulVec w = 0) :
    (sublatticeSpinSquaredS N A).mulVec w = (m_A * (m_A - 1)) • w := by
  have hrearr := sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq (Λ := V) (N := N) A
  have hcasimir : sublatticeSpinSquaredS N A =
      (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A)
        - sublatticeSpinSOp3 N A
        + sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A := by
    rw [sublatticeSpinSquaredS_def, hrearr]
    abel
  rw [hcasimir, Matrix.add_mulVec, Matrix.sub_mulVec]
  have h1 : (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A).mulVec w = 0 := by
    rw [← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  have h2 : (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec w =
      (m_A * m_A) • w := by
    rw [← Matrix.mulVec_mulVec, hmag, Matrix.mulVec_smul, hmag, smul_smul]
  rw [h1, hmag, h2, zero_sub, ← neg_smul, ← add_smul]
  congr 1
  ring

end LatticeSystem.Quantum
