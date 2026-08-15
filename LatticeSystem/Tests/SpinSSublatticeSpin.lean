import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDefCore

/-!
# Test coverage for the spin-`S` sublattice spin operators
(Tasaki §2.5 eqs. (2.5.10)–(2.5.11))

Covers the sublattice components `Ŝ_A^{(α)}` and the sublattice
Casimir `(Ŝ_A)²` of `Quantum/SpinS/SublatticeSpin.lean`, together with
the sublattice ladder operators `Ŝ_A^±` and their Cartan relations of
`Quantum/SpinS/SublatticeSpinLadderDefCore.lean`.
-/

namespace LatticeSystem.Tests.SpinSSublatticeSpin

open LatticeSystem.Quantum

/-! ## Sublattice components and Casimir -/

/-- `Ŝ_tot^{(α)} = Ŝ_A^{(α)} + Ŝ_¬A^{(α)}` (axis 1). -/
example (A : Fin 2 → Bool) (N : ℕ) :
    totalSpinSOp1 (Fin 2) N =
      sublatticeSpinSOp1 N A + sublatticeSpinSOp1 N (fun x => ! A x) :=
  totalSpinSOp1_eq_sublattice_sum N A

/-- `Ŝ_A^{(α)}` is Hermitian (axis 1). -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSOp1 N A).IsHermitian :=
  sublatticeSpinSOp1_isHermitian N A

/-- `Ŝ_A^{(1)}` and `Ŝ_¬A^{(1)}` commute. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSOp1 N A) (sublatticeSpinSOp1 N (fun x => ! A x)) :=
  sublatticeSpinSOp1_cross_commute N A

/-- `(Ŝ_A)²` is Hermitian. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSquaredS N A).IsHermitian :=
  sublatticeSpinSquaredS_isHermitian N A

/-- Mixed-axes cross-commute: `Ŝ_A^{(1)}` and `Ŝ_¬A^{(2)}` commute. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSOp1 N A) (sublatticeSpinSOp2 N (fun x => ! A x)) :=
  sublatticeSpinSOp1_cross_commute_op2 N A

/-- Mixed-axes cross-commute: `Ŝ_A^{(2)}` and `Ŝ_¬A^{(3)}` commute. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSOp2 N A) (sublatticeSpinSOp3 N (fun x => ! A x)) :=
  sublatticeSpinSOp2_cross_commute_op3 N A

/-- Mixed-axes cross-commute: `Ŝ_A^{(3)}` and `Ŝ_¬A^{(1)}` commute. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSOp3 N A) (sublatticeSpinSOp1 N (fun x => ! A x)) :=
  sublatticeSpinSOp3_cross_commute_op1 N A

/-- The two sublattice Casimirs commute: `Commute (Ŝ_A)² (Ŝ_¬A)²`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A)
            (sublatticeSpinSquaredS N (fun x => ! A x)) :=
  sublatticeSpinSquaredS_cross_commute N A

/-- Sublattice SU(2) algebra: `[Ŝ_A^{(1)}, Ŝ_A^{(2)}] = i · Ŝ_A^{(3)}`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSOp1 N A * sublatticeSpinSOp2 N A
        - sublatticeSpinSOp2 N A * sublatticeSpinSOp1 N A : ManyBodyOpS (Fin 2) N) =
      Complex.I • sublatticeSpinSOp3 N A :=
  sublatticeSpinSOp1_commutator_sublatticeSpinSOp2 N A

/-- Sublattice SU(2) algebra: `[Ŝ_A^{(2)}, Ŝ_A^{(3)}] = i · Ŝ_A^{(1)}`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSOp2 N A * sublatticeSpinSOp3 N A
        - sublatticeSpinSOp3 N A * sublatticeSpinSOp2 N A : ManyBodyOpS (Fin 2) N) =
      Complex.I • sublatticeSpinSOp1 N A :=
  sublatticeSpinSOp2_commutator_sublatticeSpinSOp3 N A

/-- Sublattice SU(2) algebra: `[Ŝ_A^{(3)}, Ŝ_A^{(1)}] = i · Ŝ_A^{(2)}`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    (sublatticeSpinSOp3 N A * sublatticeSpinSOp1 N A
        - sublatticeSpinSOp1 N A * sublatticeSpinSOp3 N A : ManyBodyOpS (Fin 2) N) =
      Complex.I • sublatticeSpinSOp2 N A :=
  sublatticeSpinSOp3_commutator_sublatticeSpinSOp1 N A

/-- Sublattice Casimir self-invariance: `Commute (Ŝ_A)² (Ŝ_A^{(1)})`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp1 N A) :=
  sublatticeSpinSquaredS_commute_sublatticeSpinSOp1 N A

/-- Sublattice Casimir self-invariance: `Commute (Ŝ_A)² (Ŝ_A^{(2)})`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp2 N A) :=
  sublatticeSpinSquaredS_commute_sublatticeSpinSOp2 N A

/-- Sublattice Casimir self-invariance: `Commute (Ŝ_A)² (Ŝ_A^{(3)})`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp3 N A) :=
  sublatticeSpinSquaredS_commute_sublatticeSpinSOp3 N A

/-- `Commute (Ŝ_A)² (Ŝ_¬A^{(1)})`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A) (sublatticeSpinSOp1 N (fun x => ! A x)) :=
  sublatticeSpinSquaredS_commute_sublatticeSpinSOp1_complement N A

/-- `Commute (Ŝ_A)² (Ŝ_tot^{(1)})`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSOp1 (Fin 2) N) :=
  sublatticeSpinSquaredS_commute_totalSpinSOp1 N A

/-- `Commute (Ŝ_A)² (Ŝ_tot)²`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    Commute (sublatticeSpinSquaredS N A) (totalSpinSSquared (Fin 2) N) :=
  sublatticeSpinSquaredS_commute_totalSpinSSquared N A

/-! ## Sublattice ladder operators -/

/-- `Ŝ_A^+ = Ŝ_A^{(1)} + i · Ŝ_A^{(2)}`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSOpPlus N A =
      sublatticeSpinSOp1 N A + Complex.I • sublatticeSpinSOp2 N A :=
  sublatticeSpinSOpPlus_eq_add N A

/-- `Ŝ_A^- = Ŝ_A^{(1)} − i · Ŝ_A^{(2)}`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSOpMinus N A =
      sublatticeSpinSOp1 N A - Complex.I • sublatticeSpinSOp2 N A :=
  sublatticeSpinSOpMinus_eq_sub N A

/-- `Ŝ_tot^+ = Ŝ_A^+ + Ŝ_¬A^+`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    totalSpinSOpPlus (Fin 2) N =
      sublatticeSpinSOpPlus N A + sublatticeSpinSOpPlus N (fun x => ! A x) :=
  totalSpinSOpPlus_eq_sublattice_sum N A

/-- `Ŝ_tot^- = Ŝ_A^- + Ŝ_¬A^-`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    totalSpinSOpMinus (Fin 2) N =
      sublatticeSpinSOpMinus N A + sublatticeSpinSOpMinus N (fun x => ! A x) :=
  totalSpinSOpMinus_eq_sublattice_sum N A

/-- Sublattice Cartan relation: `[Ŝ_A^{(3)}, Ŝ_A^+] = Ŝ_A^+`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSOp3 N A * sublatticeSpinSOpPlus N A
        - sublatticeSpinSOpPlus N A * sublatticeSpinSOp3 N A =
      sublatticeSpinSOpPlus N A :=
  sublatticeSpinSOp3_commutator_sublatticeSpinSOpPlus N A

/-- Sublattice Cartan relation: `[Ŝ_A^{(3)}, Ŝ_A^-] = −Ŝ_A^-`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    sublatticeSpinSOp3 N A * sublatticeSpinSOpMinus N A
        - sublatticeSpinSOpMinus N A * sublatticeSpinSOp3 N A =
      -sublatticeSpinSOpMinus N A :=
  sublatticeSpinSOp3_commutator_sublatticeSpinSOpMinus N A

/-- Total Cartan relation: `[Ŝ_tot^{(3)}, Ŝ_A^+] = Ŝ_A^+`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    totalSpinSOp3 (Fin 2) N * sublatticeSpinSOpPlus N A
        - sublatticeSpinSOpPlus N A * totalSpinSOp3 (Fin 2) N =
      sublatticeSpinSOpPlus N A :=
  totalSpinSOp3_commutator_sublatticeSpinSOpPlus N A

/-- Total Cartan relation: `[Ŝ_tot^{(3)}, Ŝ_A^-] = −Ŝ_A^-`. -/
example (A : Fin 2 → Bool) (N : ℕ) :
    totalSpinSOp3 (Fin 2) N * sublatticeSpinSOpMinus N A
        - sublatticeSpinSOpMinus N A * totalSpinSOp3 (Fin 2) N =
      -sublatticeSpinSOpMinus N A :=
  totalSpinSOp3_commutator_sublatticeSpinSOpMinus N A

end LatticeSystem.Tests.SpinSSublatticeSpin
