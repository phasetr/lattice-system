import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder

/-!
# Sublattice highest-weight Casimir relation

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

A sublattice-weight vector annihilated by the sublattice raising operator
`Ŝ_A^+` is a `(Ŝ_A)²`-eigenvector with eigenvalue `m_A(m_A+1)`, where `m_A` is its
`Ŝ_A^(3)` eigenvalue.  This is the sublattice analogue of
`tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpPlus_eq_zero_of_mem_magSubspaceS`,
derived from the sublattice Cartan identity
`Ŝ_A^- Ŝ_A^+ = (Ŝ_A^1)² + (Ŝ_A^2)² − Ŝ_A^(3)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Sublattice highest-weight Casimir relation**: if `Ŝ_A^(3) w = m_A · w` and
`Ŝ_A^+ w = 0`, then `(Ŝ_A)² w = m_A(m_A+1) · w`.

`(Ŝ_A)² = Ŝ_A^- Ŝ_A^+ + Ŝ_A^(3) + (Ŝ_A^(3))²` (sublattice Cartan identity); on a
highest-weight `Ŝ_A^(3)`-eigenvector the `Ŝ_A^- Ŝ_A^+` term vanishes and the rest is
`m_A + m_A² = m_A(m_A+1)`. -/
theorem sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpPlus_eq_zero
    (A : V → Bool) {m_A : ℂ} {w : (V → Fin (N + 1)) → ℂ}
    (hmag : (sublatticeSpinSOp3 N A).mulVec w = m_A • w)
    (hker : (sublatticeSpinSOpPlus N A).mulVec w = 0) :
    (sublatticeSpinSquaredS N A).mulVec w = (m_A * (m_A + 1)) • w := by
  have hrearr := sublatticeSpinSOpMinus_mul_sublatticeSpinSOpPlus_eq (Λ := V) (N := N) A
  have hcasimir : sublatticeSpinSquaredS N A =
      (sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A)
        + sublatticeSpinSOp3 N A
        + sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A := by
    rw [sublatticeSpinSquaredS_def, hrearr]
    abel
  rw [hcasimir, Matrix.add_mulVec, Matrix.add_mulVec]
  -- (Ŝ_A^- Ŝ_A^+) w = 0
  have h1 : (sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N A).mulVec w = 0 := by
    rw [← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
  -- (Ŝ_A^(3))² w = (m_A * m_A) • w
  have h2 : (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A).mulVec w =
      (m_A * m_A) • w := by
    rw [← Matrix.mulVec_mulVec, hmag, Matrix.mulVec_smul, hmag, smul_smul]
  rw [h1, hmag, h2, zero_add]
  rw [← add_smul]
  congr 1
  ring

end LatticeSystem.Quantum
