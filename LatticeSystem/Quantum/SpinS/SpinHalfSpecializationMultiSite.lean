import LatticeSystem.Quantum.SpinS.SpinHalfSpecialization
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.TotalSquaredCore
import LatticeSystem.Quantum.SpinS.HeisenbergCore
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelCore
import LatticeSystem.Quantum.SpinS.ToyHamiltonian
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian
import LatticeSystem.Quantum.SpinDot.HamiltonianCore
import LatticeSystem.Quantum.TotalSpin.Casimir
import LatticeSystem.Quantum.NeelState.Definition

/-!
# Many-body spin-`S` specialisation at `N = 1`: equals spin-`1/2`

`SpinHalfSpecialization.lean` identifies the **single-site** spin-`S`
matrices at `N = 1` with the spin-`1/2` matrices. This module lifts
that identification to the **many-body** layer: every multi-site
spin-`S` object of `Quantum/SpinS/` evaluated at `N = 1` equals its
spin-`1/2` counterpart of `Quantum/`.

The two operator spaces `ManyBodyOpS Λ 1` and `ManyBodyOp Λ` are
definitionally equal (`Fin (1 + 1)` versus `Fin 2`), so the bridges
below are plain equalities requiring no cast.

Covered objects: site embeddings (`onSiteS`), the two-site inner
product (`spinSDot`), the Heisenberg-type Hamiltonian
(`heisenbergHamiltonianS`), the total spin operators
(`totalSpinSOp{1,2,3}`) and Casimir (`totalSpinSSquared`), the
computational-basis / Néel state constructors (`basisVecS`,
`neelConfigOfS`, `neelStateOfS`), and the Marshall–Lieb–Mattis toy
Hamiltonian (`heisenbergToyHamiltonianS`).

These transfer identities let a theorem proved once in the general
spin-`S` development be read off as a statement about the genuinely
spin-`1/2` objects, so that spin-`1/2` results need not be reproved.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.2 (2.2.13) and §2.5 eqs. (2.5.2), (2.5.10),
  pp. 27, 37, 40–42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Site embeddings -/

/-- `onSiteS i A = onSite i A` at `N = 1`: the spin-`S` site embedding
of a `2 × 2` matrix is the spin-`1/2` site embedding. -/
theorem onSiteS_one_eq_onSite (i : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ 1) = onSite i A := rfl

/-! ## Two-site inner product and Heisenberg Hamiltonian -/

/-- `Ŝ_x · Ŝ_y` at `N = 1` is the spin-`1/2` two-site inner product
(Tasaki §2.2 (2.2.13)). -/
theorem spinSDot_one_eq_spinHalfDot (x y : Λ) :
    (spinSDot x y 1 : ManyBodyOpS Λ 1) = spinHalfDot x y := by
  unfold spinSDot spinHalfDot
  rw [spinSOp1_one_eq_spinHalfOp1, spinSOp2_one_eq_spinHalfOp2,
    spinSOp3_one_eq_spinHalfOp3]
  simp only [onSiteS_one_eq_onSite]

/-- `Ĥ_J = Σ_{x, y} J(x, y) Ŝ_x · Ŝ_y` at `N = 1` is the spin-`1/2`
Heisenberg-type Hamiltonian with the same coupling. -/
theorem heisenbergHamiltonianS_one_eq_heisenbergHamiltonian (J : Λ → Λ → ℂ) :
    (heisenbergHamiltonianS J 1 : ManyBodyOpS Λ 1) = heisenbergHamiltonian J := by
  unfold heisenbergHamiltonianS heisenbergHamiltonian
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [spinSDot_one_eq_spinHalfDot]

/-! ## Total spin operators and Casimir -/

/-- `Ŝ_tot^{(1)}` at `N = 1` is the spin-`1/2` total spin in the 1-axis. -/
theorem totalSpinSOp1_one_eq_totalSpinHalfOp1 :
    (totalSpinSOp1 Λ 1 : ManyBodyOpS Λ 1) = totalSpinHalfOp1 Λ := by
  unfold totalSpinSOp1 totalSpinHalfOp1
  rw [spinSOp1_one_eq_spinHalfOp1]
  simp only [onSiteS_one_eq_onSite]

/-- `Ŝ_tot^{(2)}` at `N = 1` is the spin-`1/2` total spin in the 2-axis. -/
theorem totalSpinSOp2_one_eq_totalSpinHalfOp2 :
    (totalSpinSOp2 Λ 1 : ManyBodyOpS Λ 1) = totalSpinHalfOp2 Λ := by
  unfold totalSpinSOp2 totalSpinHalfOp2
  rw [spinSOp2_one_eq_spinHalfOp2]
  simp only [onSiteS_one_eq_onSite]

/-- `Ŝ_tot^{(3)}` at `N = 1` is the spin-`1/2` total spin in the 3-axis. -/
theorem totalSpinSOp3_one_eq_totalSpinHalfOp3 :
    (totalSpinSOp3 Λ 1 : ManyBodyOpS Λ 1) = totalSpinHalfOp3 Λ := by
  unfold totalSpinSOp3 totalSpinHalfOp3
  rw [spinSOp3_one_eq_spinHalfOp3]
  simp only [onSiteS_one_eq_onSite]

/-- `(Ŝ_tot)² = Σ_α (Ŝ_tot^{(α)})²` at `N = 1` is the spin-`1/2`
Casimir operator. -/
theorem totalSpinSSquared_one_eq_totalSpinHalfSquared :
    (totalSpinSSquared Λ 1 : ManyBodyOpS Λ 1) = totalSpinHalfSquared Λ := by
  unfold totalSpinSSquared totalSpinHalfSquared
  rw [totalSpinSOp1_one_eq_totalSpinHalfOp1, totalSpinSOp2_one_eq_totalSpinHalfOp2,
    totalSpinSOp3_one_eq_totalSpinHalfOp3]

/-! ## Computational basis and Néel state -/

omit [DecidableEq Λ] in
/-- `basisVecS σ = basisVec σ` at `N = 1`: the spin-`S` computational
basis vector is the spin-`1/2` one. -/
theorem basisVecS_one_eq_basisVec (σ : Λ → Fin 2) :
    (basisVecS σ : (Λ → Fin 2) → ℂ) = basisVec σ := rfl

omit [Fintype Λ] [DecidableEq Λ] in
/-- `neelConfigOfS A 1 = neelConfigOf A`: at `N = 1` the spin-`S` Néel
configuration (`0` on `A`, `Fin.last N` off `A`) is the spin-`1/2` one
(`0 ↔ ↑` on `A`, `1 ↔ ↓` off `A`), pinning the two developments to the
same sublattice orientation (Tasaki §2.5 eq. (2.5.2)). -/
theorem neelConfigOfS_one_eq_neelConfigOf (A : Λ → Bool) :
    neelConfigOfS A 1 = neelConfigOf A := rfl

/-- `Φ_Néel(A, 1) = Φ_Néel(A)`: at `N = 1` the spin-`S` Néel state is
the spin-`1/2` Néel state (Tasaki §2.5 eq. (2.5.2)). -/
theorem neelStateOfS_one_eq_neelStateOf (A : Λ → Bool) :
    (neelStateOfS A 1 : (Λ → Fin 2) → ℂ) = neelStateOf A := rfl

/-! ## Marshall–Lieb–Mattis toy Hamiltonian -/

/-- `Ĥ_toy` at `N = 1` is the spin-`1/2` MLM toy Hamiltonian, i.e. the
Heisenberg Hamiltonian with bipartite coupling (Tasaki §2.5
eq. (2.5.10)). -/
theorem heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian (A : Λ → Bool) :
    (heisenbergToyHamiltonianS A 1 : ManyBodyOpS Λ 1) = heisenbergToyHamiltonian A := by
  unfold heisenbergToyHamiltonianS heisenbergToyHamiltonian
  exact heisenbergHamiltonianS_one_eq_heisenbergHamiltonian _

end LatticeSystem.Quantum
