import LatticeSystem.Quantum.SpinS.SaturatedFMJointZeroEqTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderSpan

/-!
# Dimension of the maximum-Casimir `(Ŝ_tot)²` eigenspace

The `(Ŝ_tot)²`-eigenspace at the maximum Casimir eigenvalue
`saturatedFerromagnetCasimirEigenvalueS V N = m_max(m_max+1)` has
dimension exactly `|V|·N + 1 = 2 m_max + 1`:

  `Module.finrank ℂ
       (Module.End.eigenspace (Ŝ_tot)².mulVecLin
         (saturatedFerromagnetCasimirEigenvalueS V N))
     = Fintype.card V * N + 1`.

This is the operator-level dimension of the spin-`m_max`
irreducible SU(2) representation living at the top weight of the
multi-site Hilbert space.

Proof: combine PR #2801
(`saturatedFerromagnetJointEigenspace 0 N = (Ŝ_tot)² eigenspace`)
with PR #2769
(`saturatedFerromagnetJointEigenspace_finrank_eq`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **Max-Casimir `(Ŝ_tot)²` eigenspace has finrank `|V|·N + 1`**.
Operator-level dimension of the spin-`m_max` irrep. -/
theorem totalSpinSSquaredEigenspace_max_finrank_eq_succ_card_mul_N
    [Nonempty V] :
    Module.finrank ℂ
      (Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N)) =
      Fintype.card V * N + 1 := by
  rw [← saturatedFerromagnetJointEigenspace_zero_eq_totalSpinSSquaredEigenspace
        (V := V) (N := N)]
  exact saturatedFerromagnetJointEigenspace_finrank_eq (J := 0)

end LatticeSystem.Quantum
