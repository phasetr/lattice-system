import LatticeSystem.Quantum.MarshallLiebMattis.H0Shifted

/-!
# Test coverage for the shifted dressed Heisenberg matrix on `H_0`
-/

namespace LatticeSystem.Tests.MarshallLiebMattisH0Shifted

open LatticeSystem.Quantum

/-- Symmetry. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x) (c : ℝ) :
    (dressedHeisenbergShifted (Λ := Fin 2) A J c).IsSymm :=
  dressedHeisenbergShifted_isSymm A hJ_real hJ_symm c

/-- Off-diagonal non-negativity. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (c : ℝ) {σ τ : H₀Index (Fin 2)} (hne : σ ≠ τ) :
    0 ≤ dressedHeisenbergShifted A J c σ τ :=
  dressedHeisenbergShifted_offdiag_nonneg A hJ_real hJ_nn hJ_bipartite c hne

/-- All-entry non-negativity under the diagonal-bound hypothesis. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (c : ℝ)
    (hc : ∀ σ : H₀Index (Fin 2), dressedHeisenbergMatrixH0 A J σ σ ≤ c)
    (σ τ : H₀Index (Fin 2)) :
    0 ≤ dressedHeisenbergShifted A J c σ τ :=
  dressedHeisenbergShifted_nonneg A hJ_real hJ_nn hJ_bipartite c hc σ τ

end LatticeSystem.Tests.MarshallLiebMattisH0Shifted
