import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# The anisotropic Hamiltonian reduces to Heisenberg at `λ = 1, D = 0`

Issue #3739 (Tasaki §2.5 Theorem 2.4).  Split out of `AnisotropicHeisenberg.lean` so that the
core anisotropic-Hamiltonian definitions do not import the heavy `Heisenberg` module (this is
the only place `heisenbergHamiltonianS` is referenced).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- At `λ = 1, D = 0` the anisotropic Hamiltonian is the isotropic Heisenberg Hamiltonian. -/
theorem anisotropicHeisenbergS_one_zero (J : Λ → Λ → ℂ) (N : ℕ) :
    anisotropicHeisenbergS (Λ := Λ) J 1 0 N = heisenbergHamiltonianS J N := by
  rw [anisotropicHeisenbergS_def, singleIonAnisotropyS_zero, add_zero, heisenbergHamiltonianS_def]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [spinSDotXXZ_one]

end LatticeSystem.Quantum
