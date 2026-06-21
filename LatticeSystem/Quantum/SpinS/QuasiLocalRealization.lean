import LatticeSystem.Quantum.SpinS.QuasiLocalInductiveLimit
import LatticeSystem.Quantum.SpinS.StaggeredBulkSpin

/-!
# Tasaki Appendix A.7: a quasi-local realization of the infinite spin system

Tasaki Appendix A.7 takes the quasi-local `C*`-algebra to be the inductive limit
(norm closure of the directed union) of the increasing local-algebra net.  Since
the abstract `InfiniteSpinSystem.localAlg` is a *free* field, this identification
cannot be asserted globally (an arbitrary system need not have its local algebra
exhausted by the box tower).  Instead we bundle it as a `structure`:

`QuasiLocalRealization` packages an `InfiniteSpinSystem`, a `LocalSupportData`, and
the two operator-algebraic hypotheses (`BoxTowerExhaustsLocalAlg`,
`BoxTowerClosureIsQuasiLocalAlgebra`) as fields.  For any such realization we prove,
all **axiom-free**, the conditional consequences: the box tower supremum equals the
local algebra, its norm closure is the whole algebra, the local algebra is dense,
and the spins / finite-box Hamiltonians / staggered bulk observables are local and
lie in the realized closure.

No new axiom is introduced and no existing axiom is touched; the deep content is
supplied per realization as hypotheses, matching the documented-axiom policy for
operator-algebraic existence.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), Appendix A.7, pp. 530–533; §4.3.1, pp. 112–115.
-/

namespace LatticeSystem.Quantum

open scoped Topology

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

/-- A **quasi-local realization** (Tasaki Appendix A.7): an infinite spin system
together with local-support data whose box-local tower exhausts the local algebra
and whose norm closure is the whole quasi-local algebra. -/
structure QuasiLocalRealization (d : ℕ) (A : Type*) [CStarAlgebra A] where
  /-- The underlying infinite-volume spin system. -/
  system : InfiniteSpinSystem d A
  /-- The local-support data realizing the box-local tower. -/
  support : LocalSupportData system
  /-- The box-local tower exhausts the local algebra (`A_loc ≤ ⨆ₙ A_{Λ_n}`). -/
  boxTower_exhausts_localAlg : support.BoxTowerExhaustsLocalAlg
  /-- The ambient algebra is the norm closure of the box-local tower. -/
  boxTower_closure_is_quasiLocalAlgebra : support.BoxTowerClosureIsQuasiLocalAlgebra

namespace QuasiLocalRealization

variable (R : QuasiLocalRealization d A)

/-- The box-local tower supremum equals the local algebra. -/
theorem boxLocalTowerSup_eq_localAlg :
    R.support.boxLocalTowerSup = R.system.localAlg :=
  R.support.boxLocalTowerSup_eq_localAlg_of_exhausts R.boxTower_exhausts_localAlg

/-- The norm closure of the box-local tower is the whole algebra. -/
theorem boxLocalTowerClosure_eq_top : R.support.boxLocalTowerClosure = ⊤ :=
  R.boxTower_closure_is_quasiLocalAlgebra

/-- The local algebra is contained in the box-local tower supremum. -/
theorem localAlg_le_boxLocalTowerSup :
    R.system.localAlg ≤ R.support.boxLocalTowerSup :=
  R.boxTower_exhausts_localAlg

/-- The local algebra is contained in the norm closure of the box-local tower. -/
theorem localAlg_le_boxLocalTowerClosure :
    R.system.localAlg ≤ R.support.boxLocalTowerClosure :=
  R.localAlg_le_boxLocalTowerSup.trans R.support.boxLocalTowerSup_le_boxLocalTowerClosure

/-- The local algebra is **dense** in the quasi-local algebra: its norm closure is
the whole algebra. -/
theorem localAlg_topologicalClosure_eq_top :
    R.system.localAlg.topologicalClosure = ⊤ := by
  rw [← R.boxLocalTowerSup_eq_localAlg]
  exact R.boxLocalTowerClosure_eq_top

/-- Every ambient observable lies in the realized closure (which is the whole
algebra). -/
theorem mem_boxLocalTowerClosure (a : A) : a ∈ R.support.boxLocalTowerClosure := by
  rw [R.boxLocalTowerClosure_eq_top]
  exact StarSubalgebra.mem_top

/-- A per-site spin operator is a local observable. -/
theorem spin_mem_localAlg (x : Fin d → ℤ) (α : Fin 3) :
    R.system.spin x α ∈ R.system.localAlg :=
  R.system.spin_mem x α

/-- A per-site spin operator lies in the realized closure. -/
theorem spin_mem_boxLocalTowerClosure (x : Fin d → ℤ) (α : Fin 3) :
    R.system.spin x α ∈ R.support.boxLocalTowerClosure :=
  R.mem_boxLocalTowerClosure _

/-- The finite-box partial Hamiltonian is a local observable. -/
theorem boxLocalHamiltonian_mem_localAlg (n : ℕ) :
    boxLocalHamiltonian R.system n ∈ R.system.localAlg :=
  R.support.boxLocalHamiltonian_mem_localAlg n

/-- The finite-box partial Hamiltonian lies in the realized closure. -/
theorem boxLocalHamiltonian_mem_boxLocalTowerClosure (n : ℕ) :
    boxLocalHamiltonian R.system n ∈ R.support.boxLocalTowerClosure :=
  R.mem_boxLocalTowerClosure _

/-- The staggered cell observable is a local observable. -/
theorem staggeredCellSpin_mem_localAlg (u : Fin d → ℤ) (α : Fin 3) :
    InfiniteSpinSystem.staggeredCellSpin R.system u α ∈ R.system.localAlg :=
  R.support.staggeredCellSpin_mem_localAlg u α

/-- The staggered cell observable lies in the realized closure. -/
theorem staggeredCellSpin_mem_boxLocalTowerClosure (u : Fin d → ℤ) (α : Fin 3) :
    InfiniteSpinSystem.staggeredCellSpin R.system u α ∈ R.support.boxLocalTowerClosure :=
  R.mem_boxLocalTowerClosure _

/-- The staggered bulk observable is a local observable. -/
theorem staggeredBulkSpin_mem_localAlg (u : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    InfiniteSpinSystem.staggeredBulkSpin R.system u α n ∈ R.system.localAlg := by
  rw [InfiniteSpinSystem.staggeredBulkSpin_eq_bulkOp_sub]
  exact sub_mem (R.support.bulkOp_spin_mem_localAlg 0 α n)
    (R.support.bulkOp_spin_mem_localAlg u α n)

/-- The staggered bulk observable lies in the realized closure. -/
theorem staggeredBulkSpin_mem_boxLocalTowerClosure (u : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    InfiniteSpinSystem.staggeredBulkSpin R.system u α n ∈ R.support.boxLocalTowerClosure :=
  R.mem_boxLocalTowerClosure _

/-- The staggered bulk density is a local observable. -/
theorem staggeredBulkSpinDensity_mem_localAlg (u : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    InfiniteSpinSystem.staggeredBulkSpinDensity R.system u α n ∈ R.system.localAlg := by
  rw [InfiniteSpinSystem.staggeredBulkSpinDensity, InfiniteSpinSystem.bulkDensity,
    Algebra.smul_def]
  exact mul_mem (algebraMap_mem _ _) (R.staggeredBulkSpin_mem_localAlg u α n)

/-- The staggered bulk density lies in the realized closure. -/
theorem staggeredBulkSpinDensity_mem_boxLocalTowerClosure (u : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    InfiniteSpinSystem.staggeredBulkSpinDensity R.system u α n ∈
      R.support.boxLocalTowerClosure :=
  R.mem_boxLocalTowerClosure _

end QuasiLocalRealization

end LatticeSystem.Quantum
