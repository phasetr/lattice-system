import LatticeSystem.Quantum.SpinS.HeisenbergCore
import LatticeSystem.Quantum.SpinS.AndersonTower

/-!
# Signature pin: the ordered-pair bond sum is `heisenbergHamiltonianS`

Repository-internal regression guard, **not** a Tasaki result on its own but pinning the
reindexing step used throughout the ordered-pair accounting of §2.4 eq. (2.4.1)
(`heisenbergHamiltonianS` as the double sum `∑_{x,y} J(x,y) • Ŝ_x·Ŝ_y`). This file pins the
promoted lemma's signature, general and at the `torusNNCoupling` specialization the §4.2 stack
consumes.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4, eq. (2.4.1).
-/

namespace LatticeSystem.Tests.HeisenbergCoreBondSumPin

open LatticeSystem.Quantum

/-- **Signature pin.** The ordered-pair bond sum is the Heisenberg Hamiltonian, stated over a
general index type and available from `HeisenbergCore` rather than from any §4.2 module. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (J : Λ → Λ → ℂ) (N : ℕ) :
    ∑ p : Λ × Λ, J p.1 p.2 • spinSDot p.1 p.2 N = heisenbergHamiltonianS (Λ := Λ) J N :=
  sum_prod_smul_spinSDot J N

/-- **Positive control.** The general lemma observed at a concrete small instance
(`Λ := Fin 2`, `N := 1`, constant coupling `J := 1`), so the pin exercises an actual value rather
than only a signature. -/
example : ∑ p : Fin 2 × Fin 2, (fun _ _ : Fin 2 => (1 : ℂ)) p.1 p.2 • spinSDot p.1 p.2 1
    = heisenbergHamiltonianS (Λ := Fin 2) (fun _ _ => 1) 1 :=
  sum_prod_smul_spinSDot (Λ := Fin 2) (fun _ _ => 1) 1

/-- **Signature pin.** The `torusNNCoupling` specialization the §4.2 local-decay stack consumes is
the general lemma applied, not a separate fact. -/
example (d L N : ℕ) [NeZero L] :
    heisenbergHamiltonianS (torusNNCoupling d L) N
      = ∑ p : HypercubicTorus d L × HypercubicTorus d L,
          torusNNCoupling d L p.1 p.2 • spinSDot p.1 p.2 N :=
  (sum_prod_smul_spinSDot (torusNNCoupling d L) N).symm

end LatticeSystem.Tests.HeisenbergCoreBondSumPin
