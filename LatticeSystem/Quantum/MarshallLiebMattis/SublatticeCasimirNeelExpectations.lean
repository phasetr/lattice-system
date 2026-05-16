import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Sublattice Casimir expectations on the Néel state

This companion file holds the spin-`1/2` Néel-state expectation values of
sublattice spin operators, total spin operators, and the toy Heisenberg
Hamiltonian. Extracted from `SublatticeCasimirNeel.lean` at refactor #53
(PR #3128) to reduce the parent's transitive import cost (18.0s → split).

Contents:
- z-axis cross expectation
- ladder cross expectations (all four `(+,+) / (-,-) / (+,-) / (-,+)`)
- full cross-sublattice spin dot-product expectation
- `(Ŝ_tot^(3))²` action and expectation on Néel
- full `(Ŝ_tot)²` expectation on Néel (filter-card and `|Λ|` forms)
- `Ŝ_tot^(3)` expectation on Néel
- complement Cartan ladder action `Ŝ_¬A^- · Ŝ_¬A^+ · |Φ_Néel⟩ = |¬A| · |Φ_Néel⟩`
- Heisenberg toy Hamiltonian expectation on Néel.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `<Φ_Néel | Ŝ_A^(3)·Ŝ_¬A^(3) | Φ_Néel> = -|A|·|¬A|/4`. Spin-`1/2` mirror of
γ-4 step 116. -/
theorem neelStateOf_sublattice3_cross_complement3_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOp3 A *
            sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec
          (neelStateOf A)) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) /
          4)) := by
  rw [sublatticeSpinHalfOp3_cross_complement_mulVec_neelStateOf]
  rw [dotProduct_smul]
  rw [neelStateOf_inner_self, smul_eq_mul, mul_one]

/-- `<Φ_Néel | Ŝ_A^+ · Ŝ_¬A^+ | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 120. -/
theorem neelStateOf_sublattice_plus_complement_plus_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpPlus A *
            sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [sublatticeSpinHalfOpPlus_complement_plus_mulVec_neelStateOf]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^- · Ŝ_¬A^- | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 120. -/
theorem neelStateOf_sublattice_minus_complement_minus_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpMinus A *
            sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [sublatticeSpinHalfOpMinus_complement_minus_mulVec_neelStateOf]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^+ · Ŝ_¬A^- | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 118:
trivial via Ŝ_¬A^- annihilation. -/
theorem neelStateOf_sublattice_plus_complement_minus_expectation
    (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpPlus A *
            sublatticeSpinHalfOpMinus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [sublatticeSpinHalfOpPlus_complement_minus_mulVec_neelStateOf]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^- · Ŝ_¬A^+ | Φ_Néel> = 0`. Spin-`1/2` mirror of γ-4 step 114:
cross-flip expectation vanishes via Hermitian conjugate. -/
theorem neelStateOf_sublattice_minus_plus_cross_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOpMinus A *
            sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
          (neelStateOf A)) = 0 := by
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [show sublatticeSpinHalfOpMinus A =
      (sublatticeSpinHalfOpPlus A).conjTranspose from
    (sublatticeSpinHalfOpPlus_conjTranspose A).symm]
  rw [← Matrix.star_mulVec]
  rw [sublatticeSpinHalfOpPlus_mulVec_neelStateOf]
  rw [star_zero]
  exact zero_dotProduct _

/-- `<Φ_Néel | Ŝ_A · Ŝ_¬A | Φ_Néel> = -|A|·|¬A|/4`. Spin-`1/2` mirror of γ-4
step 124: cross-sublattice spin dot product expectation. Combines γ-4
steps 117 (z-axis), 123 (ladder identity), 119 + 115 (cross-flip
expectations). -/
theorem neelStateOf_sublatticeSpinHalfDot_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 (fun x => ! A x) +
          sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 (fun x => ! A x) +
          sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 (fun x => ! A x)).mulVec
          (neelStateOf A)) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) /
          4)) := by
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  rw [dotProduct_add, dotProduct_add]
  rw [neelStateOf_sublattice3_cross_complement3_expectation]
  rw [show
      dotProduct (star (neelStateOf A))
          ((sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 (fun x => ! A x)).mulVec
            (neelStateOf A)) +
        dotProduct (star (neelStateOf A))
          ((sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 (fun x => ! A x)).mulVec
            (neelStateOf A)) = 0 from ?_]
  · ring
  rw [← dotProduct_add, ← Matrix.add_mulVec]
  rw [sublatticeSpinHalfOp1_mul_op1_add_op2_mul_op2_eq_ladder]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [Matrix.add_mulVec, dotProduct_add]
  rw [neelStateOf_sublattice_plus_complement_minus_expectation]
  rw [neelStateOf_sublattice_minus_plus_cross_expectation]
  simp

/-- `(Ŝ_tot^(3))² · |Φ_Néel⟩ = ((|A|-|¬A|)/2)² · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 128: Néel is exact (Ŝ_tot^(3))²-eigenvector. -/
theorem totalSpinHalfOp3_sq_mulVec_neelStateOf (A : Λ → Bool) :
    (totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (neelStateOf A) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ^ 2 •
        neelStateOf A := by
  rw [← Matrix.mulVec_mulVec]
  rw [totalSpinHalfOp3_mulVec_neelStateOf]
  rw [Matrix.mulVec_smul]
  rw [totalSpinHalfOp3_mulVec_neelStateOf]
  rw [smul_smul]
  congr 1
  ring

/-- `<Φ_Néel | (Ŝ_tot^(3))² | Φ_Néel> = ((|A|-|¬A|)/2)²`. Spin-`1/2` mirror
of γ-4 step 155. -/
theorem neelStateOf_totalSpinHalfOp3_sq_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ * totalSpinHalfOp3 Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ^ 2 := by
  rw [totalSpinHalfOp3_sq_mulVec_neelStateOf]
  rw [dotProduct_smul, neelStateOf_inner_self, smul_eq_mul, mul_one]


/-- `<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|-|¬A|)/2)² + (|A|+|¬A|)/2`. Spin-`1/2`
mirror of γ-4 step 126. The full total-spin Casimir expectation on Néel. -/
theorem neelStateOf_totalSpinHalfSquared_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) /
          2) ^ 2 +
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) /
          2 := by
  rw [totalSpinHalfSquared_eq_sublattice_casimir A]
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  rw [dotProduct_add, dotProduct_add]
  rw [sublatticeSpinHalfSquared_mulVec_neelStateOf]
  rw [sublatticeSpinHalfSquared_complement_mulVec_neelStateOf]
  rw [Matrix.smul_mulVec]
  rw [show sublatticeSpinDot A (fun x => ! A x) =
      sublatticeSpinHalfOp1 A * sublatticeSpinHalfOp1 (fun x => ! A x) +
        sublatticeSpinHalfOp2 A * sublatticeSpinHalfOp2 (fun x => ! A x) +
        sublatticeSpinHalfOp3 A * sublatticeSpinHalfOp3 (fun x => ! A x) from rfl]
  simp only [dotProduct_smul, neelStateOf_inner_self,
    neelStateOf_sublatticeSpinHalfDot_expectation,
    smul_eq_mul, mul_one]
  ring

/-- `<Φ_Néel | Ŝ_tot^(3) | Φ_Néel> = (|A| - |¬A|)/2`. Spin-`1/2` mirror of
γ-4 step 112: Néel state magnetization expectation. -/
theorem neelStateOf_totalSpinHalfOp3_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfOp3 Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) := by
  rw [totalSpinHalfOp3_mulVec_neelStateOf]
  rw [dotProduct_smul]
  rw [neelStateOf_inner_self, smul_eq_mul, mul_one]

/-- `Ŝ_¬A^- · Ŝ_¬A^+ · |Φ_Néel⟩ = |¬A| · |Φ_Néel⟩`. Spin-`1/2` mirror of
γ-4 step 104 via dual Cartan identity. -/
theorem sublatticeSpinHalfOpComplementMinus_complement_plus_mulVec_neelStateOf
    (A : Λ → Bool) :
    (sublatticeSpinHalfOpMinus (fun x => ! A x) *
        sublatticeSpinHalfOpPlus (fun x => ! A x)).mulVec
        (neelStateOf A) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) •
        neelStateOf A := by
  rw [sublatticeSpinHalfOpMinus_mul_sublatticeSpinHalfOpPlus_eq]
  rw [Matrix.sub_mulVec]
  rw [sublatticeSpinHalfOp12sq_complement_mulVec_neelStateOf]
  rw [sublatticeSpinHalfOp3_complement_mulVec_neelStateOf]
  rw [← sub_smul]
  congr 1
  ring

/-- `<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|-|¬A|)/2)² + |Λ|/2`. Spin-`1/2`
reformulation of γ-4 step 127 using `|A| + |¬A| = |Λ|`. -/
theorem neelStateOf_totalSpinHalfSquared_expectation_card_Lambda (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((totalSpinHalfSquared Λ).mulVec (neelStateOf A)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ^ 2 +
        (Fintype.card Λ : ℂ) / 2 := by
  rw [neelStateOf_totalSpinHalfSquared_expectation]
  congr 1
  have h : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
      (Fintype.card Λ : ℂ) := by
    have h1 : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
        Finset.univ.card (α := Λ) := by
      have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
          Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
        congr 1
        funext x
        by_cases hA : A x = true
        · simp [hA]
        · simp [hA]
      rw [hfilter_eq]
      exact Finset.card_filter_add_card_filter_not (fun x : Λ => A x = true)
    have h2 : (Finset.univ.card (α := Λ) : ℂ) = (Fintype.card Λ : ℂ) := by
      rw [Finset.card_univ]
    rw [← h2]
    exact_mod_cast h1
  rw [h]

/-- `<Φ_Néel | Ĥ_toy | Φ_Néel> = -|A|·|¬A|/2`. Spin-`1/2` mirror of γ-4
step 131. Uses the generic basis-vector expectation lemma
`basisVec_expectation_eq_diagonal` (γ-4 step 132). -/
theorem neelStateOf_heisenbergToyHamiltonian_expectation (A : Λ → Bool) :
    dotProduct (star (neelStateOf A))
        ((heisenbergToyHamiltonian A : ManyBodyOp Λ).mulVec (neelStateOf A)) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) / 2) := by
  unfold neelStateOf
  rw [basisVec_expectation_eq_diagonal]
  exact heisenbergToyHamiltonian_apply_diag_neel A

end LatticeSystem.Quantum
