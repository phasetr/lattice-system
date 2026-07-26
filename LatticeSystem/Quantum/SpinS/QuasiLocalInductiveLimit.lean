import LatticeSystem.Quantum.SpinS.QuasiLocalSupport
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Tasaki Appendix A.7: the inductive-limit interface of the box-local tower

The quasi-local `C*`-algebra is the **inductive limit** (norm closure of the
directed union) of the increasing local-algebra tower (Tasaki Appendix A.7).  This
module records that interface for the box-local tower
`A_{Λ_0} ≤ A_{Λ_1} ≤ ⋯` built in `QuasiLocalSupport.lean`:

* the algebraic supremum `A_box = ⨆ₙ A_{Λ_n}` and its **norm closure**, with the
  axiom-free order facts (each box subalgebra sits inside, the supremum sits
  inside `A_loc`, the tower is directed);
* the two genuinely operator-algebraic identifications — that the tower **exhausts**
  the local algebra (`A_loc ≤ A_box`) and that the ambient algebra is the **norm
  closure** of the tower (`closure(A_box) = ⊤`) — recorded as `def : Prop`
  hypotheses (`BoxTowerExhaustsLocalAlg`, `BoxTowerClosureIsQuasiLocalAlgebra`),
  **not asserted**: `LocalSupportData` only supplies the easy inclusion, and the
  reverse needs the finite-support property of the concrete realization.

No new axiom is introduced and no existing axiom is touched.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), Appendix A.7 (the quasi-local algebra as an
  inductive limit), pp. 530–533; §4.3.1, pp. 112–115.
-/

namespace LatticeSystem.Quantum

open scoped ComplexOrder Topology

variable {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

namespace LocalSupportData

variable {S : InfiniteSpinSystem d A} (D : LocalSupportData S)

/-- The **algebraic supremum** `A_box = ⨆ₙ A_{Λ_n}` of the box-local tower. -/
noncomputable def boxLocalTowerSup : StarSubalgebra ℂ A :=
  ⨆ n : ℕ, D.boxLocalSubalgebra n

/-- Each box-local subalgebra sits inside the tower supremum. -/
theorem boxLocalSubalgebra_le_boxLocalTowerSup (n : ℕ) :
    D.boxLocalSubalgebra n ≤ D.boxLocalTowerSup := by
  simpa [boxLocalTowerSup] using le_iSup (fun n : ℕ => D.boxLocalSubalgebra n) n

/-- The tower supremum is contained in the algebra of local observables:
`A_box ≤ A_loc`. -/
theorem boxLocalTowerSup_le_localAlg : D.boxLocalTowerSup ≤ S.localAlg := by
  rw [boxLocalTowerSup]
  exact iSup_le fun n => D.boxLocalSubalgebra_le_localAlg n

/-- The box-local tower is directed (it is monotone). -/
theorem boxLocalSubalgebra_directed : Directed (· ≤ ·) D.boxLocalSubalgebra :=
  D.boxLocalSubalgebra_mono.directed_le

/-- **Exhaustion hypothesis** (`def : Prop`, not asserted): the box-local tower
exhausts the local algebra, `A_loc ≤ A_box`.  The reverse (easy) inclusion is
`boxLocalTowerSup_le_localAlg`; this direction is the operator-algebraic content
that needs the finite-support property of the concrete realization. -/
def BoxTowerExhaustsLocalAlg : Prop := S.localAlg ≤ D.boxLocalTowerSup

/-- Under the exhaustion hypothesis the tower supremum equals the local algebra. -/
theorem boxLocalTowerSup_eq_localAlg_of_exhausts (h : D.BoxTowerExhaustsLocalAlg) :
    D.boxLocalTowerSup = S.localAlg :=
  le_antisymm D.boxLocalTowerSup_le_localAlg h

/-- The **norm closure** of the box-local tower (the candidate quasi-local
algebra, Tasaki Appendix A.7). -/
noncomputable def boxLocalTowerClosure : StarSubalgebra ℂ A :=
  D.boxLocalTowerSup.topologicalClosure

/-- The tower supremum sits inside its norm closure. -/
theorem boxLocalTowerSup_le_boxLocalTowerClosure :
    D.boxLocalTowerSup ≤ D.boxLocalTowerClosure :=
  D.boxLocalTowerSup.le_topologicalClosure

/-- Each box-local subalgebra sits inside the norm closure of the tower. -/
theorem boxLocalSubalgebra_le_boxLocalTowerClosure (n : ℕ) :
    D.boxLocalSubalgebra n ≤ D.boxLocalTowerClosure :=
  (D.boxLocalSubalgebra_le_boxLocalTowerSup n).trans
    D.boxLocalTowerSup_le_boxLocalTowerClosure

/-- **Quasi-local realization hypothesis** (`def : Prop`, not asserted): the
ambient algebra `A` is the norm closure of the box-local tower (Tasaki Appendix
A.7's inductive-limit identification). -/
def BoxTowerClosureIsQuasiLocalAlgebra : Prop := D.boxLocalTowerClosure = ⊤

end LocalSupportData

end LatticeSystem.Quantum
