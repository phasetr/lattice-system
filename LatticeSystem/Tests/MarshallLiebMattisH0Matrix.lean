import LatticeSystem.Quantum.MarshallLiebMattis.H0Matrix

/-!
# Test coverage for the H_0 dressed Heisenberg matrix
-/

namespace LatticeSystem.Tests.MarshallLiebMattisH0Matrix

open LatticeSystem.Quantum

/-- Symmetry of the dressed matrix. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x) :
    (dressedHeisenbergMatrixH0 (Λ := Fin 2) A J).IsSymm :=
  dressedHeisenbergMatrixH0_isSymm A hJ_real hJ_symm

/-- Off-diagonal entries non-positive on H_0 for distinct configurations. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    {σ τ : H₀Index (Fin 2)} (hne : σ ≠ τ) :
    dressedHeisenbergMatrixH0 A J σ τ ≤ 0 :=
  dressedHeisenbergMatrixH0_offdiag_nonpos A hJ_real hJ_nn hJ_bipartite hne

end LatticeSystem.Tests.MarshallLiebMattisH0Matrix
