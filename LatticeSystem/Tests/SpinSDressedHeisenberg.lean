import LatticeSystem.Quantum.SpinS.DressedHeisenberg

/-!
# Test coverage for spin-`S` dressed Heisenberg matrix elements
(Tasaki §2.5 Phase B-γ γ-2)
-/

namespace LatticeSystem.Tests.SpinSDressedHeisenberg

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Diagonal dressed element equals the plain diagonal element. -/
example {N : ℕ} (A : V → Bool) (J : V → V → ℂ) (σ : V → Fin (N + 1)) :
    dressedHeisenbergS A J N σ σ =
      (heisenbergHamiltonianS J N) σ σ :=
  dressedHeisenbergS_diag A J N σ

/-- Dressed Heisenberg with trivial sublattice = plain matrix element. -/
example {N : ℕ} (J : V → V → ℂ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS (fun _ : V => false) J N σ σ' =
      (heisenbergHamiltonianS J N) σ σ' :=
  dressedHeisenbergS_A_false J N σ σ'

/-- Dressed Heisenberg star-swap symmetry for real coupling. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (hreal : ∀ x y, star (J x y) = J x y)
    (σ σ' : V → Fin (N + 1)) :
    star (dressedHeisenbergS A J N σ' σ) = dressedHeisenbergS A J N σ σ' :=
  dressedHeisenbergS_star_swap A N hreal σ σ'

/-- Dressed Heisenberg diagonal is real for real coupling. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (hreal : ∀ x y, star (J x y) = J x y)
    (σ : V → Fin (N + 1)) :
    star (dressedHeisenbergS A J N σ σ) = dressedHeisenbergS A J N σ σ :=
  dressedHeisenbergS_diag_star A N hreal σ

end LatticeSystem.Tests.SpinSDressedHeisenberg
