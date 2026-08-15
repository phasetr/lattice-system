import LatticeSystem.Quantum.SpinS.SpinHalfSpecializationMultiSite
import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDefCore
import LatticeSystem.Quantum.SpinS.ToyHamiltonian
import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeSpinDot
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian

/-!
# Sublattice spin-`S` specialisation at `N = 1`: equals spin-`1/2`

Continuation of `SpinHalfSpecializationMultiSite.lean` at the
**sublattice** layer of the Marshall–Lieb–Mattis development: the
spin-`S` sublattice operators of `Quantum/SpinS/` evaluated at `N = 1`
equal the spin-`1/2` sublattice operators of
`Quantum/MarshallLiebMattis/`.

Covered objects: the sublattice spin components
(`sublatticeSpinSOp{1,2,3}`), the sublattice ladder operators
(`sublatticeSpinSOp{Plus,Minus}`), the sublattice Casimir
(`sublatticeSpinSquaredS`), the cross-sublattice inner product
(`sublatticeSpinSDot`), and the MLM toy Hamiltonian
(`heisenbergToyHamiltonianS`).

Unlike `SpinHalfSpecializationMultiSite.lean`, this module refers to
the spin-`1/2` sublattice definitions of
`Quantum/MarshallLiebMattis/`. It is therefore **scaffolding for the
reduction of that spin-`1/2` sublattice layer to the general spin-`S`
one**: its scope is exactly the set of spin-`1/2` sublattice objects
that still have their own definitions, and it shrinks as those are
retired.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 eqs. (2.5.10)–(2.5.11), pp. 40–42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Sublattice spin components -/

/-- `Ŝ_A^{(1)}` at `N = 1` is the spin-`1/2` sublattice spin in the 1-axis. -/
theorem sublatticeSpinSOp1_one_eq_sublatticeSpinHalfOp1 (A : Λ → Bool) :
    (sublatticeSpinSOp1 1 A : ManyBodyOpS Λ 1) = sublatticeSpinHalfOp1 A := by
  unfold sublatticeSpinSOp1 sublatticeSpinHalfOp1
  rw [spinSOp1_one_eq_spinHalfOp1]
  simp only [onSiteS_one_eq_onSite]

/-- `Ŝ_A^{(2)}` at `N = 1` is the spin-`1/2` sublattice spin in the 2-axis. -/
theorem sublatticeSpinSOp2_one_eq_sublatticeSpinHalfOp2 (A : Λ → Bool) :
    (sublatticeSpinSOp2 1 A : ManyBodyOpS Λ 1) = sublatticeSpinHalfOp2 A := by
  unfold sublatticeSpinSOp2 sublatticeSpinHalfOp2
  rw [spinSOp2_one_eq_spinHalfOp2]
  simp only [onSiteS_one_eq_onSite]

/-- `Ŝ_A^{(3)}` at `N = 1` is the spin-`1/2` sublattice spin in the 3-axis. -/
theorem sublatticeSpinSOp3_one_eq_sublatticeSpinHalfOp3 (A : Λ → Bool) :
    (sublatticeSpinSOp3 1 A : ManyBodyOpS Λ 1) = sublatticeSpinHalfOp3 A := by
  unfold sublatticeSpinSOp3 sublatticeSpinHalfOp3
  rw [spinSOp3_one_eq_spinHalfOp3]
  simp only [onSiteS_one_eq_onSite]

/-! ## Sublattice ladder operators -/

/-- `Ŝ_A^+` at `N = 1` is the spin-`1/2` sublattice raising operator. -/
theorem sublatticeSpinSOpPlus_one_eq_sublatticeSpinHalfOpPlus (A : Λ → Bool) :
    (sublatticeSpinSOpPlus 1 A : ManyBodyOpS Λ 1) = sublatticeSpinHalfOpPlus A := by
  unfold sublatticeSpinSOpPlus sublatticeSpinHalfOpPlus
  rw [spinSOpPlus_one_eq_spinHalfOpPlus]
  simp only [onSiteS_one_eq_onSite]

/-- `Ŝ_A^-` at `N = 1` is the spin-`1/2` sublattice lowering operator. -/
theorem sublatticeSpinSOpMinus_one_eq_sublatticeSpinHalfOpMinus (A : Λ → Bool) :
    (sublatticeSpinSOpMinus 1 A : ManyBodyOpS Λ 1) = sublatticeSpinHalfOpMinus A := by
  unfold sublatticeSpinSOpMinus sublatticeSpinHalfOpMinus
  rw [spinSOpMinus_one_eq_spinHalfOpMinus]
  simp only [onSiteS_one_eq_onSite]

/-! ## Sublattice Casimir and cross-sublattice inner product -/

/-- `(Ŝ_A)² = Σ_α (Ŝ_A^{(α)})²` at `N = 1` is the spin-`1/2`
sublattice Casimir (Tasaki §2.5 eq. (2.5.11)). -/
theorem sublatticeSpinSquaredS_one_eq_sublatticeSpinHalfSquared (A : Λ → Bool) :
    (sublatticeSpinSquaredS 1 A : ManyBodyOpS Λ 1) = sublatticeSpinHalfSquared A := by
  unfold sublatticeSpinSquaredS sublatticeSpinHalfSquared
  rw [sublatticeSpinSOp1_one_eq_sublatticeSpinHalfOp1,
    sublatticeSpinSOp2_one_eq_sublatticeSpinHalfOp2,
    sublatticeSpinSOp3_one_eq_sublatticeSpinHalfOp3]

/-- `Ŝ_A · Ŝ_B = Σ_α Ŝ_A^{(α)} Ŝ_B^{(α)}` at `N = 1` is the spin-`1/2`
cross-sublattice inner product (Tasaki §2.5 eq. (2.5.10)). -/
theorem sublatticeSpinSDot_one_eq_sublatticeSpinDot (A B : Λ → Bool) :
    (sublatticeSpinSDot 1 A B : ManyBodyOpS Λ 1) = sublatticeSpinDot A B := by
  unfold sublatticeSpinSDot sublatticeSpinDot
  rw [sublatticeSpinSOp1_one_eq_sublatticeSpinHalfOp1,
    sublatticeSpinSOp1_one_eq_sublatticeSpinHalfOp1,
    sublatticeSpinSOp2_one_eq_sublatticeSpinHalfOp2,
    sublatticeSpinSOp2_one_eq_sublatticeSpinHalfOp2,
    sublatticeSpinSOp3_one_eq_sublatticeSpinHalfOp3,
    sublatticeSpinSOp3_one_eq_sublatticeSpinHalfOp3]

/-! ## Toy Hamiltonian -/

/-- `Ĥ_toy` at `N = 1` is the spin-`1/2` MLM toy Hamiltonian, i.e. the
Heisenberg Hamiltonian with bipartite coupling (Tasaki §2.5
eq. (2.5.10)). -/
theorem heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian (A : Λ → Bool) :
    (heisenbergToyHamiltonianS A 1 : ManyBodyOpS Λ 1) = heisenbergToyHamiltonian A := by
  unfold heisenbergToyHamiltonianS heisenbergToyHamiltonian
  exact heisenbergHamiltonianS_one_eq_heisenbergHamiltonian _

end LatticeSystem.Quantum
