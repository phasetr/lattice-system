import LatticeSystem.Quantum.SpinS.SublatticeSpinDot

/-!
# Test coverage for the spin-`S` cross-sublattice spin dot product
(Tasaki §2.5 eqs. (2.5.10)–(2.5.11))
-/

namespace LatticeSystem.Tests.SpinSSublatticeSpinDot

open LatticeSystem.Quantum

/-- `Ŝ_A · Ŝ_B = Σ_α Ŝ_A^(α) Ŝ_B^(α)`. -/
example (A B : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSDot N A B =
      sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N B +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N B +
        sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N B :=
  sublatticeSpinSDot_def N A B

/-- `Ŝ_A · Ŝ_B` expands as `Σ_{x : A x} Σ_{y : B y} Ŝ_x · Ŝ_y`. -/
example (A B : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSDot N A B =
      ∑ x : Fin 2, ∑ y : Fin 2,
        if A x ∧ B y then spinSDot x y N else 0 :=
  sublatticeSpinSDot_eq_sum_sum N A B

/-- `Ŝ_A · Ŝ_¬A` is Hermitian. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSDot N A (fun x => ! A x)).IsHermitian :=
  sublatticeSpinSDot_complement_isHermitian N A

/-- `(Ŝ_A)² = Σ_{x ∈ A} Σ_{y ∈ A} Ŝ_x · Ŝ_y`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSquaredS N A =
      ∑ x : Fin 2, ∑ y : Fin 2,
        if A x ∧ A y then spinSDot x y N else 0 :=
  sublatticeSpinSquaredS_eq_sum_dot N A

/-- `(Ŝ_A)² · |σ_⊤⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |σ_⊤⟩` on the all-up
state, the maximum-spin Casimir value of the `A`-subsystem. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N A).mulVec
        (allAlignedStateS (Fin 2) N (0 : Fin (N + 1))) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        allAlignedStateS (Fin 2) N (0 : Fin (N + 1)) :=
  sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero N A

/-- `(Ŝ_A)² · |σ_⊥⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |σ_⊥⟩` on the all-down
state, i.e. the lowest weight carries the same Casimir eigenvalue. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N A).mulVec
        (allAlignedStateS (Fin 2) N (Fin.last N)) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        allAlignedStateS (Fin 2) N (Fin.last N) :=
  sublatticeSpinSquaredS_mulVec_allAlignedStateS_last N A

/-- `(Ŝ_A)² · |σ⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |σ⟩` whenever `σ` is
constant at the highest weight on `A` (arbitrary on `¬A`). -/
example (A : Fin 2 → Bool) (N : ℕ) {σ : Fin 2 → Fin (N + 1)}
    (hσ : ∀ x : Fin 2, A x = true → σ x = 0) :
    (sublatticeSpinSquaredS N A).mulVec (basisVecS σ) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        basisVecS σ :=
  sublatticeSpinSquaredS_mulVec_basisVecS_of_const_zero_on N A hσ

/-- `(Ŝ_A)² · |σ⟩ = ((|A|·N/2)·(|A|·N/2+1)) · |σ⟩` whenever `σ` is
constant at the lowest weight on `A` (arbitrary on `¬A`). -/
example (A : Fin 2 → Bool) (N : ℕ) {σ : Fin 2 → Fin (N + 1)}
    (hσ : ∀ x : Fin 2, A x = true → σ x = Fin.last N) :
    (sublatticeSpinSquaredS N A).mulVec (basisVecS σ) =
      (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Fin 2 => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) •
        basisVecS σ :=
  sublatticeSpinSquaredS_mulVec_basisVecS_of_const_last_on N A hσ

end LatticeSystem.Tests.SpinSSublatticeSpinDot
