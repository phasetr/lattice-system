import LatticeSystem.Quantum.SpinS.HeisenbergCore

/-!
# Signature pin: the ordered-pair form of the spin-`S` Heisenberg Hamiltonian

Repository-internal regression guard, **not** a Tasaki result on its own.  The spin-`S`
Heisenberg-type Hamiltonian is the weighted double sum `Ĥ_J = Σ_{x, y ∈ Λ} J(x, y) Ŝ_x · Ŝ_y`;
reindexing it along `Fintype.sum_prod_type` presents the same operator as a single sum over
ordered pairs `Λ × Λ`.  Tasaki's ferromagnetic Heisenberg Hamiltonian
`Ĥ = − Σ_{{x, y} ∈ B} Ŝ_x · Ŝ_y` (eq. (2.4.1)) runs over *unordered* bonds with a fixed
coefficient and is the specialization at a coupling of the form `couplingOf G (−1/2)`, each bond
contributing once in each order.

The only import is the module carrying the lemma, so the pin observes the lemma's location as
well as its statement.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4, eq. (2.4.1), p. 32.
-/

namespace LatticeSystem.Tests.HeisenbergCoreBondSumGeneralPin

open LatticeSystem.Quantum

/-- **Signature pin.** The sum over ordered pairs of the weighted bond terms is the Heisenberg
Hamiltonian, over a general index type. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (J : Λ → Λ → ℂ) (N : ℕ) :
    ∑ p : Λ × Λ, J p.1 p.2 • spinSDot p.1 p.2 N = heisenbergHamiltonianS (Λ := Λ) J N :=
  sum_prod_smul_spinSDot J N

/-- **Positive control.** The general lemma observed at a concrete small instance
(`Λ := Fin 2`, `N := 1`, constant coupling `J := 1`), so the pin exercises an actual value rather
than only a signature. -/
example : ∑ p : Fin 2 × Fin 2, (fun _ _ : Fin 2 => (1 : ℂ)) p.1 p.2 • spinSDot p.1 p.2 1
    = heisenbergHamiltonianS (Λ := Fin 2) (fun _ _ => 1) 1 :=
  sum_prod_smul_spinSDot (Λ := Fin 2) (fun _ _ => 1) 1

end LatticeSystem.Tests.HeisenbergCoreBondSumGeneralPin
