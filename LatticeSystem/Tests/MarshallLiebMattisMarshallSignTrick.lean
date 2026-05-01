import LatticeSystem.Quantum.MarshallLiebMattis.MarshallSignTrick

/-!
# Test coverage for the Marshall sign trick (Tasaki §2.5 Property (ii))
-/

namespace LatticeSystem.Tests.MarshallLiebMattisMarshallSignTrick

open LatticeSystem.Quantum

/-- Marshall sign relation under bipartite antiparallel swap. -/
example (A : Fin 2 → Bool) (hA : A 0 ≠ A 1)
    {σ : Fin 2 → Fin 2} (h : σ 0 ≠ σ 1) :
    marshallSignOf A σ * marshallSignOf A (basisSwap σ 0 1) = -1 :=
  marshallSignOf_mul_marshallSignOf_basisSwap_of_bipartite_antiparallel
    A (by decide : (0 : Fin 2) ≠ 1) hA h

/-- Per-bond contribution non-positivity. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : (J 0 1).im = 0) (hJ_nn : 0 ≤ (J 0 1).re)
    (hJ_bipartite : A 0 = A 1 → J 0 1 = 0)
    {σ σ' : Fin 2 → Fin 2} (hne : σ ≠ σ') :
    (marshallSignOf A σ * marshallSignOf A σ' *
        (J 0 1 * (spinHalfDot (0 : Fin 2) 1) σ σ')).re ≤ 0 :=
  bond_dressed_contribution_re_nonpos A 0 1 hJ_real hJ_nn hJ_bipartite hne

/-- Main theorem: dressed off-diagonal pairing has non-positive real part. -/
example (A : Fin 2 → Bool)
    {J : Fin 2 → Fin 2 → ℂ}
    (hJ_real : ∀ x y : Fin 2, (J x y).im = 0)
    (hJ_nn : ∀ x y : Fin 2, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y : Fin 2, A x = A y → J x y = 0)
    {σ σ' : Fin 2 → Fin 2} (hne : σ ≠ σ') :
    (∑ τ : Fin 2 → Fin 2,
        marshallDressedBasis A σ τ *
          ((heisenbergHamiltonian J).mulVec
            (marshallDressedBasis A σ')) τ).re ≤ 0 :=
  dot_marshallDressed_heisenbergHamiltonian_marshallDressed_re_nonpos_of_ne
    A hJ_real hJ_nn hJ_bipartite hne

end LatticeSystem.Tests.MarshallLiebMattisMarshallSignTrick
