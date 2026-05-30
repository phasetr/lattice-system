import LatticeSystem.Quantum.SpinS.SublatticeHighestWeight
import LatticeSystem.Quantum.SpinS.SublatticeLowestWeight
import LatticeSystem.Quantum.SpinS.SublatticeSzBound

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# The anti-aligned product state realizes the maximal sublattice Casimirs

Scaffold for the minimal-total-spin joint eigenstate (Issue #3674, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The basis configuration `σ₀` with all `A`-sites maximally up (`σ = 0`) and all
`¬A`-sites maximally down (`σ = N`) is a simultaneous eigenvector of `(Ŝ_A)²` and
`(Ŝ_¬A)²` at the maximal sublattice Casimir values `s_A(s_A+1)` and `s_B(s_B+1)`:
the `A`-block is the sublattice highest weight (`Ŝ_A^+ |σ₀⟩ = 0`, #3663), the
`¬A`-block is the sublattice lowest weight (`Ŝ_¬A^- |σ₀⟩ = 0`, #3681).  Its total
magnetization is `s_A − s_B` (the extremal sector).  Projecting `|σ₀⟩` onto the
`(Ŝ_tot)² = predicted` eigenspace will yield the minimal-total-spin state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The anti-aligned product configuration: `A`-sites maximally up (`0`),
`¬A`-sites maximally down (`Fin.last N`). -/
def antiAlignedConfigS (A : V → Bool) (N : ℕ) : V → Fin (N + 1) :=
  fun x => if A x then 0 else Fin.last N

omit [DecidableEq V] in
/-- The `A`-sublattice `Ŝ_A^(3)` eigenvalue of the anti-aligned state is `s_A`. -/
theorem sublatticeMagEigenvalue_antiAligned_A (A : V → Bool) :
    (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
        ((N : ℂ) / 2 - ((antiAlignedConfigS A N x).val : ℂ))) =
      ((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) * (N : ℂ) / 2 := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : V => A x = true),
      ((N : ℂ) / 2 - ((antiAlignedConfigS A N x).val : ℂ)) = (N : ℂ) / 2 := by
    intro x hx
    have hx' : A x = true := (Finset.mem_filter.mp hx).2
    simp [antiAlignedConfigS, hx']
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  ring

omit [DecidableEq V] in
/-- The `¬A`-sublattice `Ŝ_¬A^(3)` eigenvalue of the anti-aligned state is `−s_B`. -/
theorem sublatticeMagEigenvalue_antiAligned_notA (A : V → Bool) :
    (∑ x ∈ Finset.univ.filter (fun x : V => (! A x) = true),
        ((N : ℂ) / 2 - ((antiAlignedConfigS A N x).val : ℂ))) =
      -(((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) * (N : ℂ) / 2) := by
  have h : ∀ x ∈ Finset.univ.filter (fun x : V => (! A x) = true),
      ((N : ℂ) / 2 - ((antiAlignedConfigS A N x).val : ℂ)) = -((N : ℂ) / 2) := by
    intro x hx
    have hx' : (! A x) = true := (Finset.mem_filter.mp hx).2
    have hxA : A x = false := by simpa using hx'
    simp [antiAlignedConfigS, hxA, Fin.val_last]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Anti-aligned state is a joint maximal-sublattice-Casimir eigenvector** for
`A`: `(Ŝ_A)² |σ₀⟩ = s_A(s_A+1) |σ₀⟩`. -/
theorem sublatticeSpinSquaredS_antiAligned_eq_max (A : V → Bool) :
    (sublatticeSpinSquaredS N A).mulVec (basisVecS (antiAlignedConfigS A N)) =
      (((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) * (N : ℂ) / 2 *
        (((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) * (N : ℂ) / 2 + 1)) •
        basisVecS (antiAlignedConfigS A N) := by
  have hmag := sublatticeSpinSOp3_mulVec_basisVecS A (antiAlignedConfigS A N)
  have hker : (sublatticeSpinSOpPlus N A).mulVec (basisVecS (antiAlignedConfigS A N)) = 0 := by
    apply sublatticeSpinSOpPlus_mulVec_basisVecS_zero_on
    intro x hx
    simp [antiAlignedConfigS, hx]
  have hcas := sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpPlus_eq_zero A hmag hker
  rw [hcas, sublatticeMagEigenvalue_antiAligned_A A]

/-- **Anti-aligned state is a joint maximal-sublattice-Casimir eigenvector** for
`¬A`: `(Ŝ_¬A)² |σ₀⟩ = s_B(s_B+1) |σ₀⟩`. -/
theorem sublatticeSpinSquaredS_complement_antiAligned_eq_max (A : V → Bool) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (basisVecS (antiAlignedConfigS A N)) =
      (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) * (N : ℂ) / 2 *
        (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) * (N : ℂ) / 2 + 1)) •
        basisVecS (antiAlignedConfigS A N) := by
  have hmag := sublatticeSpinSOp3_mulVec_basisVecS (fun x => ! A x) (antiAlignedConfigS A N)
  have hker :
      (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (basisVecS (antiAlignedConfigS A N)) = 0 := by
    apply sublatticeSpinSOpMinus_mulVec_basisVecS_last_on
    intro x hx
    have hxA : A x = false := by simpa using hx
    simp [antiAlignedConfigS, hxA]
  have hcas := sublatticeSpinSquaredS_mulVec_of_sublatticeSpinSOpMinus_eq_zero (fun x => ! A x) hmag hker
  rw [hcas, sublatticeMagEigenvalue_antiAligned_notA A]
  congr 1
  ring

end LatticeSystem.Quantum
