import LatticeSystem.Quantum.SpinS.FerrimagneticLRO
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# `SU(2)` invariance of the squared staggered order operator (toward Tasaki Theorem 4.4)

The `SU(2)`-invariant squared staggered order operator `staggeredCasimirOpS A N =
∑_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` (Tasaki §4.1, eq. (4.1.12)) genuinely commutes with the total-spin
operators `Ŝ^{(α)}_tot` (`α = 1, 2, 3`) and the ladder operators `Ŝ^±_tot`.  This is the algebraic
content behind the docstring claim that "(Ô_Λ)² is `SU(2)` invariant, so its ground-state
expectation is independent of the choice of ground state".

The proof is immediate: each per-pair spin–spin dot product `spinSDot x y N` *individually* commutes
with `Ŝ^{(α)}_tot` (`spinSDot_commutator_totalSpinSOp{1,2,3}` in `MultiSiteDotComm.lean` are zero
per pair), so the real-symmetric-coefficient sum `∑_{x,y} ε_x ε_y · spinSDot x y N` does too —
exactly as for the Heisenberg Hamiltonian `∑_{x,y} J_{xy} · spinSDot x y N`
(`heisenbergHamiltonianS_commute_totalSpinSOp*` in `AllAlignedState.lean`), with the coupling `J`
replaced by the staggered sign product `ε_x ε_y`.

This is the first ingredient (a) of the universal-form transfer needed to discharge the stated
`shenQiuTian_ferrimagnetic_lro` axiom (Tasaki §4.1 Theorem 4.4): the remaining ingredient (b) is the
ground-multiplet expectation transfer (Issue #4604).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, eq. (4.1.12).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `SU(2)` invariance of the squared staggered order operator, axis 1: `[Ô_Λ², Ŝ^{(1)}_tot] = 0`.
Each per-pair `spinSDot x y N` commutes with `Ŝ^{(1)}_tot`, so the real-coefficient double sum does
too. -/
theorem staggeredCasimirOpS_commutator_totalSpinSOp1 (A : Λ → Bool) (N : ℕ) :
    staggeredCasimirOpS A N * totalSpinSOp1 Λ N -
        totalSpinSOp1 Λ N * staggeredCasimirOpS A N = 0 := by
  unfold staggeredCasimirOpS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp1, smul_zero]

/-- `SU(2)` invariance of the squared staggered order operator, axis 2: `[Ô_Λ², Ŝ²_tot] = 0`. -/
theorem staggeredCasimirOpS_commutator_totalSpinSOp2 (A : Λ → Bool) (N : ℕ) :
    staggeredCasimirOpS A N * totalSpinSOp2 Λ N -
        totalSpinSOp2 Λ N * staggeredCasimirOpS A N = 0 := by
  unfold staggeredCasimirOpS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp2, smul_zero]

/-- `SU(2)` invariance of the squared staggered order operator, axis 3: `[Ô_Λ², Ŝ³_tot] = 0`. -/
theorem staggeredCasimirOpS_commutator_totalSpinSOp3 (A : Λ → Bool) (N : ℕ) :
    staggeredCasimirOpS A N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * staggeredCasimirOpS A N = 0 := by
  unfold staggeredCasimirOpS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp3, smul_zero]

/-- The squared staggered order operator commutes with `Ŝ^{(1)}_tot`. -/
theorem staggeredCasimirOpS_commute_totalSpinSOp1 (A : Λ → Bool) (N : ℕ) :
    Commute (staggeredCasimirOpS A N) (totalSpinSOp1 Λ N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (staggeredCasimirOpS_commutator_totalSpinSOp1 A N)

/-- The squared staggered order operator commutes with `Ŝ^{(2)}_tot`. -/
theorem staggeredCasimirOpS_commute_totalSpinSOp2 (A : Λ → Bool) (N : ℕ) :
    Commute (staggeredCasimirOpS A N) (totalSpinSOp2 Λ N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (staggeredCasimirOpS_commutator_totalSpinSOp2 A N)

/-- The squared staggered order operator commutes with `Ŝ^{(3)}_tot`. -/
theorem staggeredCasimirOpS_commute_totalSpinSOp3 (A : Λ → Bool) (N : ℕ) :
    Commute (staggeredCasimirOpS A N) (totalSpinSOp3 Λ N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (staggeredCasimirOpS_commutator_totalSpinSOp3 A N)

/-- The squared staggered order operator commutes with the total raising operator `Ŝ^+_tot`. -/
theorem staggeredCasimirOpS_commute_totalSpinSOpPlus (A : Λ → Bool) (N : ℕ) :
    Commute (staggeredCasimirOpS A N) (totalSpinSOpPlus Λ N) := by
  rw [totalSpinSOpPlus_eq_add]
  exact (staggeredCasimirOpS_commute_totalSpinSOp1 A N).add_right
    ((staggeredCasimirOpS_commute_totalSpinSOp2 A N).smul_right Complex.I)

/-- The squared staggered order operator commutes with the total lowering operator `Ŝ^-_tot`. -/
theorem staggeredCasimirOpS_commute_totalSpinSOpMinus (A : Λ → Bool) (N : ℕ) :
    Commute (staggeredCasimirOpS A N) (totalSpinSOpMinus Λ N) := by
  rw [totalSpinSOpMinus_eq_sub]
  exact (staggeredCasimirOpS_commute_totalSpinSOp1 A N).sub_right
    ((staggeredCasimirOpS_commute_totalSpinSOp2 A N).smul_right Complex.I)

end LatticeSystem.Quantum
