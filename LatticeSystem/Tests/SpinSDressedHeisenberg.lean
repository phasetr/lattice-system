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

/-- Dressed Heisenberg diagonal imaginary part is zero. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (hreal : ∀ x y, star (J x y) = J x y)
    (σ : V → Fin (N + 1)) :
    (dressedHeisenbergS A J N σ σ).im = 0 :=
  dressedHeisenbergS_diag_im_zero A N hreal σ

/-- Dressed Heisenberg diagonal as ofReal of its real part. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ} (hreal : ∀ x y, star (J x y) = J x y)
    (σ : V → Fin (N + 1)) :
    dressedHeisenbergS A J N σ σ =
      ((dressedHeisenbergS A J N σ σ).re : ℂ) :=
  dressedHeisenbergS_diag_eq_ofReal A N hreal σ

/-- Dressed Heisenberg with zero coupling = 0. -/
example {N : ℕ} (A : V → Bool) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun _ _ : V => (0 : ℂ)) N σ σ' = 0 :=
  dressedHeisenbergS_zero_J A N σ σ'

/-- Dressed Heisenberg additivity in J. -/
example {N : ℕ} (A : V → Bool) (J J' : V → V → ℂ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => J x y + J' x y) N σ σ' =
      dressedHeisenbergS A J N σ σ' + dressedHeisenbergS A J' N σ σ' :=
  dressedHeisenbergS_add_J A J J' N σ σ'

/-- Dressed Heisenberg homogeneity in J. -/
example {N : ℕ} (A : V → Bool) (c : ℂ) (J : V → V → ℂ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => c * J x y) N σ σ' =
      c * dressedHeisenbergS A J N σ σ' :=
  dressedHeisenbergS_smul_J A c J N σ σ'

/-- Dressed Heisenberg negation in J. -/
example {N : ℕ} (A : V → Bool) (J : V → V → ℂ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => -(J x y)) N σ σ' =
      -(dressedHeisenbergS A J N σ σ') :=
  dressedHeisenbergS_neg_J A J N σ σ'

/-- Dressed Heisenberg subtraction in J. -/
example {N : ℕ} (A : V → Bool) (J J' : V → V → ℂ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => J x y - J' x y) N σ σ' =
      dressedHeisenbergS A J N σ σ' - dressedHeisenbergS A J' N σ σ' :=
  dressedHeisenbergS_sub_J A J J' N σ σ'

/-- Dressed Heisenberg vanishes when underlying Heisenberg vanishes. -/
example {N : ℕ} (A : V → Bool) (J : V → V → ℂ)
    {σ σ' : V → Fin (N + 1)}
    (h : (heisenbergHamiltonianS J N) σ σ' = 0) :
    dressedHeisenbergS A J N σ σ' = 0 :=
  dressedHeisenbergS_zero_of_heisenberg_zero A J N h

/-- Dressed Heisenberg matrix is Hermitian for real coupling. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ}
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSMatrix A J N).IsHermitian :=
  dressedHeisenbergSMatrix_isHermitian A N hreal

/-- Dressed Heisenberg on graph couplings is Hermitian for real edge weight. -/
example {N : ℕ} (A : V → Bool) (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) :
    (dressedHeisenbergSMatrix A
        (LatticeSystem.Lattice.couplingOf G J) N).IsHermitian :=
  dressedHeisenbergSMatrix_couplingOf_isHermitian A G hJ N

/-- Dressed Heisenberg on chain Hermitian. -/
example (M : ℕ) (A : Fin (M + 1) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.pathGraph (M + 1)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSMatrix_chain_isHermitian M A J N

/-- Dressed Heisenberg on periodic chain Hermitian. -/
example (M : ℕ) (A : Fin (M + 2) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.cycleGraph (M + 2)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSMatrix_periodicChain_isHermitian M A J N

end LatticeSystem.Tests.SpinSDressedHeisenberg
