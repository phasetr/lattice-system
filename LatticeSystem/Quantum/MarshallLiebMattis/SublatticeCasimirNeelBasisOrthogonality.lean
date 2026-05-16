import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Néel-state vs constant-basis-vector orthogonality (spin-`1/2`)

Companion of `SublatticeCasimirNeel.lean` extracted in refactor #50
(PR #3065). Contains the 13 orthogonality / distinctness / inner-self
theorems involving constant basis vectors `basisVec (fun _ => 0)`
(all-up) and `basisVec (fun _ => 1)` (all-down):

- `neelStateOf_allUp_orthogonal`,
  `neelStateOf_allDown_orthogonal` (spin-`1/2` mirrors of γ-4 steps
  133 / 173).
- `neelStateOf_ne_basisVec_const_zero`,
  `neelStateOf_ne_basisVec_const_one` (γ-4 step 184).
- `neelStateOf_complement_allUp_orthogonal`,
  `neelStateOf_complement_allDown_orthogonal` (γ-4 step 180).
- `allUp_neelStateOf_orthogonal`,
  `allDown_neelStateOf_orthogonal`,
  `allUp_neelStateOf_complement_orthogonal`,
  `allDown_neelStateOf_complement_orthogonal` (γ-4 step 196,
  reverse-direction).
- `basisVec_const_zero_const_one_orthogonal`,
  `basisVec_const_zero_inner_self`,
  `basisVec_const_one_inner_self` (constant-basis pair).

Original parent file: `SublatticeCasimirNeel.lean` lines 1030-1245
prior to this refactor.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `<basisVec (fun _ => 0) | Φ_Néel> = 0` when `|¬A| > 0`. Spin-`1/2`
analog of γ-4 step 133: the all-up basis state is orthogonal to the
Néel state whenever `¬A` is non-empty. -/
theorem neelStateOf_allUp_orthogonal
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = false) :
    dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        (neelStateOf A) = 0 := by
  unfold neelStateOf dotProduct
  have hne : neelConfigOf A ≠ (fun _ : Λ => (0 : Fin 2)) := by
    obtain ⟨x, hx⟩ := hA
    intro heq
    have h := congrFun heq x
    unfold neelConfigOf at h
    rw [if_neg (by rw [hx]; decide : ¬ A x = true)] at h
    exact (by decide : (1 : Fin 2) ≠ 0) h
  rw [Finset.sum_eq_zero]
  intro τ _
  by_cases hτ : τ = neelConfigOf A
  · rw [hτ]
    have : basisVec (fun _ : Λ => (0 : Fin 2)) (neelConfigOf A) = 0 :=
      basisVec_of_ne hne
    simp [Pi.star_apply, this]
  · rw [basisVec_of_ne hτ]
    simp

/-- `<basisVec (fun _ => 1) | Φ_Néel> = 0` when `|A| > 0`. Spin-`1/2`
mirror of γ-4 step 173: the all-down basis state is orthogonal to the
Néel state whenever `A` is non-empty. -/
theorem neelStateOf_allDown_orthogonal
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
        (neelStateOf A) = 0 := by
  unfold neelStateOf dotProduct
  have hne : neelConfigOf A ≠ (fun _ : Λ => (1 : Fin 2)) := by
    obtain ⟨x, hx⟩ := hA
    intro heq
    have h := congrFun heq x
    unfold neelConfigOf at h
    rw [if_pos hx] at h
    exact (by decide : (0 : Fin 2) ≠ 1) h
  rw [Finset.sum_eq_zero]
  intro τ _
  by_cases hτ : τ = neelConfigOf A
  · rw [hτ]
    have : basisVec (fun _ : Λ => (1 : Fin 2)) (neelConfigOf A) = 0 :=
      basisVec_of_ne hne
    simp [Pi.star_apply, this]
  · rw [basisVec_of_ne hτ]
    simp

/-- **State-level distinctness** (spin-`1/2`): `Φ_Néel(A) ≠ basisVec(const 0)`
when `|¬A| > 0`. Spin-`1/2` mirror of γ-4 step 184. Equality would force
the all-up basis vector's norm-squared to vanish, contradicting it being
`1`. -/
theorem neelStateOf_ne_basisVec_const_zero
    (A : Λ → Bool) (hAc : ∃ x : Λ, A x = false) :
    neelStateOf A ≠ basisVec (fun _ : Λ => (0 : Fin 2)) := by
  intro h
  have horth := neelStateOf_allUp_orthogonal A hAc
  rw [h] at horth
  have hself : dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        (basisVec (fun _ : Λ => (0 : Fin 2))) = 1 := by
    unfold dotProduct
    rw [Finset.sum_eq_single (fun _ : Λ => (0 : Fin 2))]
    · simp [Pi.star_apply, basisVec_self]
    · intros τ _ hτ
      simp [Pi.star_apply, basisVec_of_ne hτ]
    · intro hempty
      exact (hempty (Finset.mem_univ _)).elim
  rw [hself] at horth
  exact one_ne_zero horth

/-- **State-level distinctness** (spin-`1/2`): `Φ_Néel(A) ≠ basisVec(const 1)`
when `|A| > 0`. Spin-`1/2` mirror of γ-4 step 184. -/
theorem neelStateOf_ne_basisVec_const_one
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = true) :
    neelStateOf A ≠ basisVec (fun _ : Λ => (1 : Fin 2)) := by
  intro h
  have horth := neelStateOf_allDown_orthogonal A hA
  rw [h] at horth
  have hself : dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
        (basisVec (fun _ : Λ => (1 : Fin 2))) = 1 := by
    unfold dotProduct
    rw [Finset.sum_eq_single (fun _ : Λ => (1 : Fin 2))]
    · simp [Pi.star_apply, basisVec_self]
    · intros τ _ hτ
      simp [Pi.star_apply, basisVec_of_ne hτ]
    · intro hempty
      exact (hempty (Finset.mem_univ _)).elim
  rw [hself] at horth
  exact one_ne_zero horth

/-- `<basisVec(const 0) | Φ_Néel(¬A)> = 0` when `|A| > 0`. Spin-`1/2`
mirror of γ-4 step 180: complement Néel orthogonal to all-up via
sublattice swap. -/
theorem neelStateOf_complement_allUp_orthogonal
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        (neelStateOf (fun x : Λ => ! A x)) = 0 := by
  have hAc' : ∃ x : Λ, (! A x) = false := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, by simp [hx]⟩
  exact neelStateOf_allUp_orthogonal (fun x : Λ => ! A x) hAc'

/-- `<basisVec(const 1) | Φ_Néel(¬A)> = 0` when `|¬A| > 0`. Spin-`1/2`
mirror of γ-4 step 180: complement Néel orthogonal to all-down. -/
theorem neelStateOf_complement_allDown_orthogonal
    (A : Λ → Bool) (hAc : ∃ x : Λ, A x = false) :
    dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
        (neelStateOf (fun x : Λ => ! A x)) = 0 := by
  have hA' : ∃ x : Λ, (! A x) = true := by
    obtain ⟨x, hx⟩ := hAc
    exact ⟨x, by simp [hx]⟩
  exact neelStateOf_allDown_orthogonal (fun x : Λ => ! A x) hA'

/-- **Reverse direction** (spin-`1/2`): `<Φ_Néel(A) | basisVec(const 0)> = 0`
when `|¬A| > 0`. Spin-`1/2` mirror of γ-4 step 196. -/
theorem allUp_neelStateOf_orthogonal
    (A : Λ → Bool) (hAc : ∃ x : Λ, A x = false) :
    dotProduct (star (neelStateOf A))
        (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
  have := neelStateOf_allUp_orthogonal A hAc
  rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
          (neelStateOf A) =
        star (dotProduct (star (neelStateOf A))
          (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- **Reverse direction** (spin-`1/2`): `<Φ_Néel(A) | basisVec(const 1)> = 0`
when `|A| > 0`. Spin-`1/2` mirror of γ-4 step 196. -/
theorem allDown_neelStateOf_orthogonal
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (neelStateOf A))
        (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
  have := neelStateOf_allDown_orthogonal A hA
  rw [show dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
          (neelStateOf A) =
        star (dotProduct (star (neelStateOf A))
          (basisVec (fun _ : Λ => (1 : Fin 2)))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- **Reverse direction** (spin-`1/2`): `<Φ_Néel(¬A) | basisVec(const 0)> = 0`
when `|A| > 0`. Spin-`1/2` mirror of γ-4 step 196. -/
theorem allUp_neelStateOf_complement_orthogonal
    (A : Λ → Bool) (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
        (basisVec (fun _ : Λ => (0 : Fin 2))) = 0 := by
  have := neelStateOf_complement_allUp_orthogonal A hA
  rw [show dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
          (neelStateOf (fun x : Λ => ! A x)) =
        star (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
          (basisVec (fun _ : Λ => (0 : Fin 2)))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- **Reverse direction** (spin-`1/2`): `<Φ_Néel(¬A) | basisVec(const 1)> = 0`
when `|¬A| > 0`. Spin-`1/2` mirror of γ-4 step 196. -/
theorem allDown_neelStateOf_complement_orthogonal
    (A : Λ → Bool) (hAc : ∃ x : Λ, A x = false) :
    dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
        (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
  have := neelStateOf_complement_allDown_orthogonal A hAc
  rw [show dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
          (neelStateOf (fun x : Λ => ! A x)) =
        star (dotProduct (star (neelStateOf (fun x : Λ => ! A x)))
          (basisVec (fun _ : Λ => (1 : Fin 2)))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- All-up vs all-down basis vectors are orthogonal: `<basisVec(const 0) |
basisVec(const 1)> = 0` when `Λ` is non-empty. Distinct constant
configurations on `Fin 2`. -/
theorem basisVec_const_zero_const_one_orthogonal [Nonempty Λ] :
    dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        (basisVec (fun _ : Λ => (1 : Fin 2))) = 0 := by
  unfold dotProduct
  obtain ⟨x⟩ := ‹Nonempty Λ›
  have hne : (fun _ : Λ => (0 : Fin 2)) ≠ (fun _ : Λ => (1 : Fin 2)) := by
    intro h
    have := congrFun h x
    exact (by decide : (0 : Fin 2) ≠ 1) this
  rw [Finset.sum_eq_zero]
  intro τ _
  by_cases hτ : τ = (fun _ : Λ => (0 : Fin 2))
  · rw [hτ]
    simp [Pi.star_apply, basisVec_self, basisVec_of_ne hne]
  · simp [Pi.star_apply, basisVec_of_ne hτ]

/-- All-up basis vector has norm-squared 1. -/
theorem basisVec_const_zero_inner_self [Nonempty Λ] :
    dotProduct (star (basisVec (fun _ : Λ => (0 : Fin 2))))
        (basisVec (fun _ : Λ => (0 : Fin 2))) = 1 := by
  unfold dotProduct
  rw [Finset.sum_eq_single (fun _ : Λ => (0 : Fin 2))]
  · simp [Pi.star_apply, basisVec_self]
  · intros τ _ hτ
    simp [Pi.star_apply, basisVec_of_ne hτ]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- All-down basis vector has norm-squared 1. -/
theorem basisVec_const_one_inner_self [Nonempty Λ] :
    dotProduct (star (basisVec (fun _ : Λ => (1 : Fin 2))))
        (basisVec (fun _ : Λ => (1 : Fin 2))) = 1 := by
  unfold dotProduct
  rw [Finset.sum_eq_single (fun _ : Λ => (1 : Fin 2))]
  · simp [Pi.star_apply, basisVec_self]
  · intros τ _ hτ
    simp [Pi.star_apply, basisVec_of_ne hτ]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end LatticeSystem.Quantum
