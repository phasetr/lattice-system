import LatticeSystem.Quantum.SpinS.SpinHalfSpecializationSublattice

/-!
# Test coverage for the many-body spin-`1/2` specialisation bridges

Pins the `N = 1` identification of the multi-site and sublattice
spin-`S` objects with their spin-`1/2` counterparts
(`SpinHalfSpecializationMultiSite.lean`,
`SpinHalfSpecializationSublattice.lean`).

Three viewpoints:

1. **Type level** — each bridge elaborates at `Λ = Fin 2` between
   `ManyBodyOpS (Fin 2) 1` and `ManyBodyOp (Fin 2)` without a cast.
2. **Behaviour** — a concrete matrix element and a concrete
   eigenvalue, which pin the Néel orientation convention
   (`A ↦ 0` up, `¬A ↦ Fin.last`) rather than merely the types.
3. **Transfer** — a spin-`1/2` sublattice Casimir theorem is
   reproduced from its spin-`S` source through the bridges alone.
-/

namespace LatticeSystem.Tests.SpinHalfSpecializationMultiSite

open LatticeSystem.Quantum

/-! ## Type level: multi-site bridges -/

/-- `onSiteS i A = onSite i A` at `N = 1`. -/
example (i : Fin 2) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onSiteS i A : ManyBodyOpS (Fin 2) 1) = onSite i A :=
  onSiteS_one_eq_onSite i A

/-- `Ŝ_x · Ŝ_y` at `N = 1` is `spinHalfDot x y`. -/
example (x y : Fin 2) :
    (spinSDot x y 1 : ManyBodyOpS (Fin 2) 1) = spinHalfDot x y :=
  spinSDot_one_eq_spinHalfDot x y

/-- `Ĥ_J` at `N = 1` is the spin-`1/2` Heisenberg Hamiltonian. -/
example (J : Fin 2 → Fin 2 → ℂ) :
    (heisenbergHamiltonianS J 1 : ManyBodyOpS (Fin 2) 1) = heisenbergHamiltonian J :=
  heisenbergHamiltonianS_one_eq_heisenbergHamiltonian J

/-- `Ŝ_tot^{(1)}` at `N = 1` is `totalSpinHalfOp1`. -/
example :
    (totalSpinSOp1 (Fin 2) 1 : ManyBodyOpS (Fin 2) 1) = totalSpinHalfOp1 (Fin 2) :=
  totalSpinSOp1_one_eq_totalSpinHalfOp1

/-- `Ŝ_tot^{(2)}` at `N = 1` is `totalSpinHalfOp2`. -/
example :
    (totalSpinSOp2 (Fin 2) 1 : ManyBodyOpS (Fin 2) 1) = totalSpinHalfOp2 (Fin 2) :=
  totalSpinSOp2_one_eq_totalSpinHalfOp2

/-- `Ŝ_tot^{(3)}` at `N = 1` is `totalSpinHalfOp3`. -/
example :
    (totalSpinSOp3 (Fin 2) 1 : ManyBodyOpS (Fin 2) 1) = totalSpinHalfOp3 (Fin 2) :=
  totalSpinSOp3_one_eq_totalSpinHalfOp3

/-- `(Ŝ_tot)²` at `N = 1` is `totalSpinHalfSquared`. -/
example :
    (totalSpinSSquared (Fin 2) 1 : ManyBodyOpS (Fin 2) 1) = totalSpinHalfSquared (Fin 2) :=
  totalSpinSSquared_one_eq_totalSpinHalfSquared

/-- `basisVecS σ = basisVec σ` at `N = 1`. -/
example (σ : Fin 2 → Fin 2) :
    (basisVecS σ : (Fin 2 → Fin 2) → ℂ) = basisVec σ :=
  basisVecS_one_eq_basisVec σ

/-- `neelConfigOfS A 1 = neelConfigOf A`. -/
example (A : Fin 2 → Bool) : neelConfigOfS A 1 = neelConfigOf A :=
  neelConfigOfS_one_eq_neelConfigOf A

/-- `Φ_Néel(A, 1) = Φ_Néel(A)`. -/
example (A : Fin 2 → Bool) :
    (neelStateOfS A 1 : (Fin 2 → Fin 2) → ℂ) = neelStateOf A :=
  neelStateOfS_one_eq_neelStateOf A

/-! ## Type level: sublattice bridges -/

/-- `Ŝ_A^{(1)}` at `N = 1` is `sublatticeSpinHalfOp1`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinSOp1 1 A : ManyBodyOpS (Fin 2) 1) = sublatticeSpinHalfOp1 A :=
  sublatticeSpinSOp1_one_eq_sublatticeSpinHalfOp1 A

/-- `Ŝ_A^{(2)}` at `N = 1` is `sublatticeSpinHalfOp2`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinSOp2 1 A : ManyBodyOpS (Fin 2) 1) = sublatticeSpinHalfOp2 A :=
  sublatticeSpinSOp2_one_eq_sublatticeSpinHalfOp2 A

/-- `Ŝ_A^{(3)}` at `N = 1` is `sublatticeSpinHalfOp3`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinSOp3 1 A : ManyBodyOpS (Fin 2) 1) = sublatticeSpinHalfOp3 A :=
  sublatticeSpinSOp3_one_eq_sublatticeSpinHalfOp3 A

/-- `Ŝ_A^+` at `N = 1` is `sublatticeSpinHalfOpPlus`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinSOpPlus 1 A : ManyBodyOpS (Fin 2) 1) = sublatticeSpinHalfOpPlus A :=
  sublatticeSpinSOpPlus_one_eq_sublatticeSpinHalfOpPlus A

/-- `Ŝ_A^-` at `N = 1` is `sublatticeSpinHalfOpMinus`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinSOpMinus 1 A : ManyBodyOpS (Fin 2) 1) = sublatticeSpinHalfOpMinus A :=
  sublatticeSpinSOpMinus_one_eq_sublatticeSpinHalfOpMinus A

/-- `(Ŝ_A)²` at `N = 1` is `sublatticeSpinHalfSquared`. -/
example (A : Fin 2 → Bool) :
    (sublatticeSpinSquaredS 1 A : ManyBodyOpS (Fin 2) 1) = sublatticeSpinHalfSquared A :=
  sublatticeSpinSquaredS_one_eq_sublatticeSpinHalfSquared A

/-- `Ŝ_A · Ŝ_B` at `N = 1` is `sublatticeSpinDot`. -/
example (A B : Fin 2 → Bool) :
    (sublatticeSpinSDot 1 A B : ManyBodyOpS (Fin 2) 1) = sublatticeSpinDot A B :=
  sublatticeSpinSDot_one_eq_sublatticeSpinDot A B

/-- `Ĥ_toy` at `N = 1` is `heisenbergToyHamiltonian`. -/
example (A : Fin 2 → Bool) :
    (heisenbergToyHamiltonianS A 1 : ManyBodyOpS (Fin 2) 1) = heisenbergToyHamiltonian A :=
  heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian A

/-! ## Behaviour: concrete matrix element and eigenvalue -/

/-- The spin-`S` diagonal formula transported to `N = 1` gives the
spin-`1/2` antiparallel value `(Ŝ_0 · Ŝ_1) σ σ = -1/4` on the Néel
configuration, which fixes the orientation `A ↦ ↑`, `¬A ↦ ↓`. -/
example :
    (spinHalfDot (0 : Fin 2) 1) (neelConfigOf (fun x : Fin 2 => x == 0))
        (neelConfigOf (fun x : Fin 2 => x == 0)) = -(1 / 4 : ℂ) := by
  rw [← spinSDot_one_eq_spinHalfDot, ← neelConfigOfS_one_eq_neelConfigOf,
    spinSDot_apply_diag_of_ne (by decide)]
  norm_num [neelConfigOfS]

/-- On the single-site sublattice `A = {0}` of `Fin 2`, the transported
spin-`S` Casimir eigenvalue is `3/4 = (1/2)(1/2 + 1)`. -/
example :
    (sublatticeSpinHalfSquared (fun x : Fin 2 => x == 0)).mulVec
        (neelStateOf (fun x : Fin 2 => x == 0)) =
      (3 / 4 : ℂ) • neelStateOf (fun x : Fin 2 => x == 0) := by
  have h := sublatticeSpinSquaredS_mulVec_neelStateOfS (Λ := Fin 2) (fun x => x == 0) 1
  rw [sublatticeSpinSquaredS_one_eq_sublatticeSpinHalfSquared,
    neelStateOfS_one_eq_neelStateOf] at h
  rw [h]
  congr 1
  have hcard : (Finset.univ.filter (fun x : Fin 2 => (x == 0) = true)).card = 1 := by decide
  rw [hcard]
  norm_num

/-! ## Transfer: a spin-`1/2` theorem from its spin-`S` source -/

/-- `(Ŝ_A)² · |Φ_Néel(A)⟩ = (|A|(|A| + 2)/4) · |Φ_Néel(A)⟩`, obtained
from the spin-`S` theorem at `N = 1` through the bridges alone. This is
the regression check that the two developments agree on statements, not
just on definitions. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) :
    (sublatticeSpinHalfSquared A).mulVec (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card + 2) / 4) •
        neelStateOf A := by
  have h := sublatticeSpinSquaredS_mulVec_neelStateOfS (Λ := Λ) A 1
  rw [sublatticeSpinSquaredS_one_eq_sublatticeSpinHalfSquared,
    neelStateOfS_one_eq_neelStateOf] at h
  rw [h]
  congr 1
  push_cast
  ring

end LatticeSystem.Tests.SpinHalfSpecializationMultiSite
