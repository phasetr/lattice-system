import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Spin-`1/2` Néel-basisVec triple/quad linear independence
and finrank-span (γ-4 steps 174 mirrors)

Extracted from `SublatticeCasimirNeel.lean` (build-speed refactor).
This file contains the spin-`1/2` mirrors of γ-4 step 174 onwards:
triple/quad linear independence and finrank-of-span lemmas for
combinations of {`basisVec(const 0)`, `basisVec(const 1)`,
`Φ_Néel(A)`, `Φ_Néel(¬A)`}.

Theorems:
- `neelStateOf_basisVec_triple_independent` / `_linearIndependent`
- `neelStateOf_basisVec_triple_finrank_span` / `_set`
- `neelStateOf_complement_linearIndependent` / `_finrank_span` / `_set`
- `neelStateOf_complement_basisVec_triple_independent` / `_linearIndependent`
- `neelStateOf_complement_basisVec_triple_finrank_span` / `_set`
- `neelStateOf_basisVec_quad_independent` / `_linearIndependent`
- `neelStateOf_basisVec_quad_finrank_span` / `_set`
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Triple linear independence** of {`basisVec(const 0)`, `basisVec(const 1)`,
`Φ_Néel(A)`} (spin-`1/2`): when `Λ` is non-empty and both sublattices are
non-empty, any zero linear combination has all coefficients zero.
Spin-`1/2` mirror of γ-4 step 174. -/
theorem neelStateOf_basisVec_triple_independent
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false)
    {c1 c2 c3 : ℂ}
    (h : c1 • basisVec (fun _ : Λ => (0 : Fin 2)) +
         c2 • basisVec (fun _ : Λ => (1 : Fin 2)) +
         c3 • neelStateOf A = 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have h_top_top := basisVec_const_zero_inner_self (Λ := Λ)
  have h_bot_bot := basisVec_const_one_inner_self (Λ := Λ)
  have h_neel_neel := neelStateOf_inner_self A
  have h_top_bot := basisVec_const_zero_const_one_orthogonal (Λ := Λ)
  have h_bot_top : dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
      (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
    have := h_top_bot
    rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
            (basisVec (fun _ : Λ => (1 : Fin 2))) =
          star (dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
            (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_top_neel := neelStateOf_allUp_orthogonal A hAc
  have h_bot_neel := neelStateOf_allDown_orthogonal A hA
  have h_neel_top : dotProduct (star (neelStateOf A))
      (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
    have := h_top_neel
    rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
            (neelStateOf A) =
          star (dotProduct (star (neelStateOf A))
            (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neel_bot : dotProduct (star (neelStateOf A))
      (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
    have := h_bot_neel
    rw [show dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
            (neelStateOf A) =
          star (dotProduct (star (neelStateOf A))
            (basisVec (fun _ : Λ => (1 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have hc1 : c1 = 0 := by
    have := congrArg
      (dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h_top_top, h_top_bot, h_top_neel, dotProduct_zero] at this
    simp at this
    exact this
  have hc2 : c2 = 0 := by
    have := congrArg
      (dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h_bot_top, h_bot_bot, h_bot_neel, dotProduct_zero] at this
    simp at this
    exact this
  have hc3 : c3 = 0 := by
    have := congrArg (dotProduct (star (neelStateOf A))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h_neel_top, h_neel_bot, h_neel_neel, dotProduct_zero] at this
    simp at this
    exact this
  exact ⟨hc1, hc2, hc3⟩

/-- **mathlib `LinearIndependent` form of the triple LI** (spin-`1/2`):
`LinearIndependent ℂ ![basisVec(0), basisVec(1), Φ_Néel(A)]` when `Λ`
non-empty and both sublattices non-empty. Spin-`1/2` mirror of γ-4
step 187. -/
theorem neelStateOf_basisVec_triple_linearIndependent
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    LinearIndependent ℂ
      (![basisVec (fun _ : Λ => (0 : Fin 2)),
         basisVec (fun _ : Λ => (1 : Fin 2)),
         neelStateOf A] : Fin 3 → _) := by
  rw [Fintype.linearIndependent_iff]
  intros g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  obtain ⟨h0, h1, h2⟩ :=
    neelStateOf_basisVec_triple_independent A hA hAc hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **`finrank` of the spin-`1/2` triple span equals 3**. -/
theorem neelStateOf_basisVec_triple_finrank_span
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (![basisVec (fun _ : Λ => (0 : Fin 2)),
             basisVec (fun _ : Λ => (1 : Fin 2)),
             neelStateOf A] : Fin 3 → _))) = 3 := by
  rw [finrank_span_eq_card
        (neelStateOf_basisVec_triple_linearIndependent A hA hAc)]
  rfl

/-- **Set form** of the spin-`1/2` triple finrank: `finrank ℂ (span ℂ
{basisVec(0), basisVec(1), Φ_Néel(A)}) = 3`. Spin-`1/2` mirror of
γ-4 step 190. -/
theorem neelStateOf_basisVec_triple_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({basisVec (fun _ : Λ => (0 : Fin 2)),
          basisVec (fun _ : Λ => (1 : Fin 2)),
          neelStateOf A} : Set _)) = 3 := by
  have hrange :
      Set.range
        (![basisVec (fun _ : Λ => (0 : Fin 2)),
           basisVec (fun _ : Λ => (1 : Fin 2)),
           neelStateOf A] : Fin 3 → _) =
      ({basisVec (fun _ : Λ => (0 : Fin 2)),
        basisVec (fun _ : Λ => (1 : Fin 2)),
        neelStateOf A} : Set _) := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr (Or.inl hi.symm)
      · exact Or.inr (Or.inr hi.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hrange]
  exact neelStateOf_basisVec_triple_finrank_span A hA hAc

/-- **mathlib LinearIndependent** form of the Néel-complement pair LI
(spin-`1/2`): `LinearIndependent ℂ ![Φ_Néel(A), Φ_Néel(¬A)]` when `Λ`
is non-empty. Spin-`1/2` mirror of γ-4 step 185. -/
theorem neelStateOf_complement_linearIndependent
    [Nonempty Λ] (A : Λ → Bool) :
    LinearIndependent ℂ
      ![neelStateOf A, neelStateOf (fun x : Λ => ! A x)] := by
  rw [LinearIndependent.pair_iff]
  intros s t h
  exact neelStateOf_complement_pair_independent A h

/-- **`finrank` of the Néel-complement pair span equals 2** (spin-`1/2`).
Spin-`1/2` mirror of γ-4 step 186. -/
theorem neelStateOf_complement_finrank_span
    [Nonempty Λ] (A : Λ → Bool) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range ![neelStateOf A, neelStateOf (fun x : Λ => ! A x)])) = 2 := by
  rw [finrank_span_eq_card (neelStateOf_complement_linearIndependent A)]
  rfl

/-- **Set form** (spin-`1/2`): `finrank ℂ (span ℂ {Φ_Néel(A), Φ_Néel(¬A)}) = 2`.
Spin-`1/2` mirror of γ-4 step 189. -/
theorem neelStateOf_complement_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({neelStateOf A, neelStateOf (fun x : Λ => ! A x)} : Set _)) = 2 := by
  have hrange :
      Set.range ![neelStateOf A, neelStateOf (fun x : Λ => ! A x)] =
      ({neelStateOf A, neelStateOf (fun x : Λ => ! A x)} : Set _) := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr hi.symm
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hrange]
  exact neelStateOf_complement_finrank_span A

/-- **Triple linear independence** (spin-`1/2`) of
{`basisVec(const 0)`, `basisVec(const 1)`, `Φ_Néel(¬A)`}: spin-`1/2`
mirror of γ-4 step 183, applies γ-4 step 175 with `A := ¬A`. -/
theorem neelStateOf_complement_basisVec_triple_independent
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false)
    {c1 c2 c3 : ℂ}
    (h : c1 • basisVec (fun _ : Λ => (0 : Fin 2)) +
         c2 • basisVec (fun _ : Λ => (1 : Fin 2)) +
         c3 • neelStateOf (fun x : Λ => ! A x) = 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have hA' : ∃ x : Λ, (! A x) = true := by
    obtain ⟨x, hx⟩ := hAc
    exact ⟨x, by simp [hx]⟩
  have hAc' : ∃ x : Λ, (! A x) = false := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, by simp [hx]⟩
  exact neelStateOf_basisVec_triple_independent
    (fun x : Λ => ! A x) hA' hAc' h

/-- **Quadruple linear independence** (spin-`1/2`) of
{`basisVec(const 0)`, `basisVec(const 1)`, `Φ_Néel(A)`, `Φ_Néel(¬A)`}:
when `Λ` non-empty and both sublattices non-empty, all four coefficients
in any zero linear combination vanish. Spin-`1/2` mirror of γ-4 step 181. -/
theorem neelStateOf_basisVec_quad_independent
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false)
    {c1 c2 c3 c4 : ℂ}
    (h : c1 • basisVec (fun _ : Λ => (0 : Fin 2)) +
         c2 • basisVec (fun _ : Λ => (1 : Fin 2)) +
         c3 • neelStateOf A +
         c4 • neelStateOf (fun x : Λ => ! A x) = 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  have h_top_top := basisVec_const_zero_inner_self (Λ := Λ)
  have h_bot_bot := basisVec_const_one_inner_self (Λ := Λ)
  have h_neelA_neelA := neelStateOf_inner_self A
  have h_neelcA_neelcA := neelStateOf_inner_self (fun x : Λ => ! A x)
  have h_top_bot := basisVec_const_zero_const_one_orthogonal (Λ := Λ)
  have h_bot_top : dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
      (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
    have := h_top_bot
    rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
            (basisVec (fun _ : Λ => (1 : Fin 2))) =
          star (dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
            (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_top_neelA := neelStateOf_allUp_orthogonal A hAc
  have h_bot_neelA := neelStateOf_allDown_orthogonal A hA
  have h_top_neelcA := neelStateOf_complement_allUp_orthogonal A hA
  have h_bot_neelcA := neelStateOf_complement_allDown_orthogonal A hAc
  have h_neelA_neelcA := neelStateOf_complement_orthogonal A
  -- Reverse orthogonalities via Matrix.star_dotProduct.
  have h_neelA_top : dotProduct (star (neelStateOf A))
      (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
    have := h_top_neelA
    rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
            (neelStateOf A) =
          star (dotProduct (star (neelStateOf A))
            (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelA_bot : dotProduct (star (neelStateOf A))
      (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
    have := h_bot_neelA
    rw [show dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
            (neelStateOf A) =
          star (dotProduct (star (neelStateOf A))
            (basisVec (fun _ : Λ => (1 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelcA_top : dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
      (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
    have := h_top_neelcA
    rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
            (neelStateOf (fun x : Λ => ! A x)) =
          star (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
            (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelcA_bot : dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
      (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
    have := h_bot_neelcA
    rw [show dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
            (neelStateOf (fun x : Λ => ! A x)) =
          star (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
            (basisVec (fun _ : Λ => (1 : Fin 2)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelcA_neelA : dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
      (neelStateOf A) = 0 := by
    have := h_neelA_neelcA
    rw [show dotProduct (star (neelStateOf A))
            (neelStateOf (fun x : Λ => ! A x)) =
          star (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
            (neelStateOf A)) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have hc1 : c1 = 0 := by
    have := congrArg
      (dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_top_top, h_top_bot, h_top_neelA, h_top_neelcA, dotProduct_zero] at this
    simp at this
    exact this
  have hc2 : c2 = 0 := by
    have := congrArg
      (dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_bot_top, h_bot_bot, h_bot_neelA, h_bot_neelcA, dotProduct_zero] at this
    simp at this
    exact this
  have hc3 : c3 = 0 := by
    have := congrArg (dotProduct (star (neelStateOf A))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_neelA_top, h_neelA_bot, h_neelA_neelA, h_neelA_neelcA,
        dotProduct_zero] at this
    simp at this
    exact this
  have hc4 : c4 = 0 := by
    have := congrArg
      (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_neelcA_top, h_neelcA_bot, h_neelcA_neelA, h_neelcA_neelcA,
        dotProduct_zero] at this
    simp at this
    exact this
  exact ⟨hc1, hc2, hc3, hc4⟩

/-- **mathlib `LinearIndependent` form** of the complement-Néel triple LI
(spin-`1/2`). Spin-`1/2` mirror of γ-4 step 192. -/
theorem neelStateOf_complement_basisVec_triple_linearIndependent
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    LinearIndependent ℂ
      (![basisVec (fun _ : Λ => (0 : Fin 2)),
         basisVec (fun _ : Λ => (1 : Fin 2)),
         neelStateOf (fun x : Λ => ! A x)] : Fin 3 → _) := by
  rw [Fintype.linearIndependent_iff]
  intros g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  obtain ⟨h0, h1, h2⟩ :=
    neelStateOf_complement_basisVec_triple_independent A hA hAc hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **`finrank` of the spin-`1/2` complement-Néel triple span equals 3**. -/
theorem neelStateOf_complement_basisVec_triple_finrank_span
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (![basisVec (fun _ : Λ => (0 : Fin 2)),
             basisVec (fun _ : Λ => (1 : Fin 2)),
             neelStateOf (fun x : Λ => ! A x)] : Fin 3 → _))) = 3 := by
  rw [finrank_span_eq_card
        (neelStateOf_complement_basisVec_triple_linearIndependent A hA hAc)]
  rfl

/-- **Set form** of the spin-`1/2` complement-Néel triple finrank.
Spin-`1/2` mirror of γ-4 step 193. -/
theorem neelStateOf_complement_basisVec_triple_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({basisVec (fun _ : Λ => (0 : Fin 2)),
          basisVec (fun _ : Λ => (1 : Fin 2)),
          neelStateOf (fun x : Λ => ! A x)} : Set _)) = 3 := by
  have hrange :
      Set.range
        (![basisVec (fun _ : Λ => (0 : Fin 2)),
           basisVec (fun _ : Λ => (1 : Fin 2)),
           neelStateOf (fun x : Λ => ! A x)] : Fin 3 → _) =
      ({basisVec (fun _ : Λ => (0 : Fin 2)),
        basisVec (fun _ : Λ => (1 : Fin 2)),
        neelStateOf (fun x : Λ => ! A x)} : Set _) := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr (Or.inl hi.symm)
      · exact Or.inr (Or.inr hi.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hrange]
  exact neelStateOf_complement_basisVec_triple_finrank_span A hA hAc

/-- **Quadruple `LinearIndependent`** (spin-`1/2`):
`LinearIndependent ℂ ![basisVec(0), basisVec(1), Φ_Néel(A), Φ_Néel(¬A)]`
when `Λ` non-empty and both sublattices non-empty. Spin-`1/2` mirror of
γ-4 step 188. -/
theorem neelStateOf_basisVec_quad_linearIndependent
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    LinearIndependent ℂ
      (![basisVec (fun _ : Λ => (0 : Fin 2)),
         basisVec (fun _ : Λ => (1 : Fin 2)),
         neelStateOf A,
         neelStateOf (fun x : Λ => ! A x)] : Fin 4 → _) := by
  rw [Fintype.linearIndependent_iff]
  intros g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  obtain ⟨h0, h1, h2, h3⟩ :=
    neelStateOf_basisVec_quad_independent A hA hAc hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **`finrank` of the spin-`1/2` quadruple span equals 4**. -/
theorem neelStateOf_basisVec_quad_finrank_span
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (![basisVec (fun _ : Λ => (0 : Fin 2)),
             basisVec (fun _ : Λ => (1 : Fin 2)),
             neelStateOf A,
             neelStateOf (fun x : Λ => ! A x)] : Fin 4 → _))) = 4 := by
  rw [finrank_span_eq_card
        (neelStateOf_basisVec_quad_linearIndependent A hA hAc)]
  rfl

/-- **Set form** of the spin-`1/2` quadruple finrank: `finrank ℂ (span ℂ
{basisVec(0), basisVec(1), Φ_Néel(A), Φ_Néel(¬A)}) = 4`. Spin-`1/2`
mirror of γ-4 step 191. -/
theorem neelStateOf_basisVec_quad_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({basisVec (fun _ : Λ => (0 : Fin 2)),
          basisVec (fun _ : Λ => (1 : Fin 2)),
          neelStateOf A,
          neelStateOf (fun x : Λ => ! A x)} : Set _)) = 4 := by
  have hrange :
      Set.range
        (![basisVec (fun _ : Λ => (0 : Fin 2)),
           basisVec (fun _ : Λ => (1 : Fin 2)),
           neelStateOf A,
           neelStateOf (fun x : Λ => ! A x)] : Fin 4 → _) =
      ({basisVec (fun _ : Λ => (0 : Fin 2)),
        basisVec (fun _ : Λ => (1 : Fin 2)),
        neelStateOf A,
        neelStateOf (fun x : Λ => ! A x)} : Set _) := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr (Or.inl hi.symm)
      · exact Or.inr (Or.inr (Or.inl hi.symm))
      · exact Or.inr (Or.inr (Or.inr hi.symm))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  rw [← hrange]
  exact neelStateOf_basisVec_quad_finrank_span A hA hAc


end LatticeSystem.Quantum
