import LatticeSystem.Quantum.MarshallLiebMattis.Realness

/-!
# Test coverage for the realness of dressed Heisenberg matrix entries
(Tasaki §2.5, p. 41, Property (i))
-/

namespace LatticeSystem.Tests.MarshallLiebMattisRealness

open LatticeSystem.Quantum

/-! ## API smoke checks on `Fin 2` -/

/-- Every two-site spin product matrix entry has zero imaginary part. -/
example (σ σ' : Fin 2 → Fin 2) :
    ((spinHalfDot (0 : Fin 2) 1) σ σ').im = 0 :=
  spinHalfDot_apply_im_eq_zero 0 1 σ σ'

/-- Same-site spin product matrix entry has zero imaginary part. -/
example (σ σ' : Fin 2 → Fin 2) :
    ((spinHalfDot (0 : Fin 2) 0) σ σ').im = 0 :=
  spinHalfDot_apply_im_eq_zero 0 0 σ σ'

/-- Heisenberg Hamiltonian matrix entry is real for real coupling. -/
example (J : Fin 2 → Fin 2 → ℂ) (hJ : ∀ x y, (J x y).im = 0)
    (σ σ' : Fin 2 → Fin 2) :
    ((heisenbergHamiltonian J) σ σ').im = 0 :=
  heisenbergHamiltonian_apply_im_eq_zero hJ σ σ'

/-- Marshall sign is real on any sublattice indicator and any
configuration. -/
example (A : Fin 2 → Bool) (σ : Fin 2 → Fin 2) :
    (marshallSignOf A σ).im = 0 :=
  marshallSignOf_im_eq_zero A σ

/-- The dressed Heisenberg bilinear pairing is real for real coupling
on `Fin 2`. -/
example (A : Fin 2 → Bool) (J : Fin 2 → Fin 2 → ℂ)
    (hJ : ∀ x y, (J x y).im = 0) (σ σ' : Fin 2 → Fin 2) :
    (∑ τ : Fin 2 → Fin 2,
        marshallDressedBasis A σ τ *
          ((heisenbergHamiltonian J).mulVec
            (marshallDressedBasis A σ')) τ).im = 0 :=
  dot_marshallDressed_heisenbergHamiltonian_marshallDressed_im_eq_zero A hJ σ σ'

end LatticeSystem.Tests.MarshallLiebMattisRealness
