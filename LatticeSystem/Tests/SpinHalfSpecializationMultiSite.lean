import LatticeSystem.Quantum.SpinS.SpinHalfSpecializationMultiSite
import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir

/-!
# Test coverage for the many-body spin-`1/2` specialisation bridges

Pins the `N = 1` identification of the multi-site spin-`S` objects with
their spin-`1/2` counterparts
(`SpinHalfSpecializationMultiSite.lean`).

Three viewpoints:

1. **Type level** — each bridge elaborates at `Λ = Fin 2` between
   `ManyBodyOpS (Fin 2) 1` and `ManyBodyOp (Fin 2)` without a cast.
2. **Behaviour** — a concrete matrix element, which pins the Néel
   orientation convention (`A ↦ 0` up, `¬A ↦ Fin.last`) rather than
   merely the types.
3. **Transfer** — spin-`1/2` theorems (the SU(2) invariance and the
   symmetry of the MLM toy Hamiltonian) are reproduced from their
   spin-`S` sources through the bridges alone.
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

/-- `Ĥ_toy` at `N = 1` is `heisenbergToyHamiltonian`. -/
example (A : Fin 2 → Bool) :
    (heisenbergToyHamiltonianS A 1 : ManyBodyOpS (Fin 2) 1) = heisenbergToyHamiltonian A :=
  heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian A

/-! ## Behaviour: concrete matrix element -/

/-- The spin-`S` diagonal formula transported to `N = 1` gives the
spin-`1/2` antiparallel value `(Ŝ_0 · Ŝ_1) σ σ = -1/4` on the Néel
configuration, which fixes the orientation `A ↦ ↑`, `¬A ↦ ↓`. -/
example :
    (spinHalfDot (0 : Fin 2) 1) (neelConfigOf (fun x : Fin 2 => x == 0))
        (neelConfigOf (fun x : Fin 2 => x == 0)) = -(1 / 4 : ℂ) := by
  rw [← spinSDot_one_eq_spinHalfDot, ← neelConfigOfS_one_eq_neelConfigOf,
    spinSDot_apply_diag_of_ne (by decide)]
  norm_num [neelConfigOfS]

/-! ## Transfer: a spin-`1/2` theorem from its spin-`S` source -/

/-- `Commute Ĥ_toy (Ŝ_tot)²`: the spin-`1/2` MLM toy Hamiltonian commutes
with the total spin Casimir, obtained from the spin-`S` SU(2) invariance
at `N = 1` through the bridges alone (Tasaki §2.5 (2.5.11)). -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonian A) (totalSpinHalfSquared Λ) := by
  have h := heisenbergToyHamiltonianS_commute_totalSpinSSquared (Λ := Λ) 1 A
  rwa [heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian,
    totalSpinSSquared_one_eq_totalSpinHalfSquared] at h

/-- `Commute Ĥ_toy Ŝ_tot^{(α)}` for all three axes: the spin-`1/2` toy
Hamiltonian is SU(2) invariant at the axis level, transferred from the
spin-`S` axis commutators at `N = 1`. The axis-`3` component is the
magnetisation-sector conservation `[Ĥ_toy, Ŝ_tot^z] = 0`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) :
    Commute (heisenbergToyHamiltonian A) (totalSpinHalfOp1 Λ) ∧
      Commute (heisenbergToyHamiltonian A) (totalSpinHalfOp2 Λ) ∧
        Commute (heisenbergToyHamiltonian A) (totalSpinHalfOp3 Λ) := by
  have h1 := heisenbergToyHamiltonianS_commute_totalSpinSOp1 (Λ := Λ) 1 A
  have h2 := heisenbergToyHamiltonianS_commute_totalSpinSOp2 (Λ := Λ) 1 A
  have h3 := heisenbergToyHamiltonianS_commute_totalSpinSOp3 (Λ := Λ) 1 A
  rw [heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian,
    totalSpinSOp1_one_eq_totalSpinHalfOp1] at h1
  rw [heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian,
    totalSpinSOp2_one_eq_totalSpinHalfOp2] at h2
  rw [heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian,
    totalSpinSOp3_one_eq_totalSpinHalfOp3] at h3
  exact ⟨h1, h2, h3⟩

/-- The spin-`1/2` MLM toy Hamiltonian is matrix-symmetric, transferred
from its spin-`S` source at `N = 1` (real symmetric coupling plus
Hermiticity). -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) :
    (heisenbergToyHamiltonian A).IsSymm := by
  have h := heisenbergToyHamiltonianS_isSymm (Λ := Λ) 1 A
  rwa [heisenbergToyHamiltonianS_one_eq_heisenbergToyHamiltonian] at h

end LatticeSystem.Tests.SpinHalfSpecializationMultiSite
