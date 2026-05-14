import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations

/-!
# Néel-vs-all-aligned orthogonality, linear independence, and finrank
spans (build-speed companion)

Build-speed companion to `SublatticeCasimirNeel.lean`. Hosts the
mid block on orthogonality of `neelStateOfS` (and its complement
orientation) against the all-up / all-down states `allAlignedStateS`,
together with the linear-independence and finrank-of-span results
for the Néel-plus-allAligned triple / quad systems (originally
lines 1180..1889 of the pre-#35 parent file).

Splitting this self-contained block out drops the parent from
~1889 lines to ~1179 lines.

No in-repo downstream consumers of the moved names — all 31
theorems were used only inside this block.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]


/-- `<Φ_⊤ | Φ_Néel> = 0` when `|¬A| > 0`. The all-up state and Néel state
are orthogonal whenever there is at least one site in `¬A`, since they
correspond to distinct configurations: `allAlignedConfigS V N 0` has all
sites at `0`, while `neelConfigOfS A N` has `Fin.last N` on the
non-empty `¬A`. -/
theorem neelStateOfS_allAlignedStateS_orthogonal
    (A : Λ → Bool) (N : ℕ)
    (hN : 0 < N)
    (hA : ∃ x : Λ, A x = false) :
    dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
        (neelStateOfS A N) = 0 := by
  unfold allAlignedStateS neelStateOfS
  have hne : neelConfigOfS A N ≠ allAlignedConfigS Λ N 0 := by
    obtain ⟨x, hx⟩ := hA
    intro heq
    have h := congrFun heq x
    unfold neelConfigOfS allAlignedConfigS at h
    rw [if_neg (by rw [hx]; decide : ¬ A x = true)] at h
    simp [Fin.last] at h
    omega
  exact basisVecS_inner_of_ne hne

/-- `<Φ_⊥ | Φ_Néel> = 0` when `|A| > 0` and `0 < N`. The all-down state
and Néel state are orthogonal whenever there is at least one site in
`A` and the spin label is non-trivial: at any `x ∈ A`,
`allAlignedConfigS V N (Fin.last N) x = Fin.last N` while
`neelConfigOfS A N x = 0`, and `0 ≠ Fin.last N` precisely when `0 < N`.
Symmetric counterpart of `neelStateOfS_allAlignedStateS_orthogonal`. -/
theorem neelStateOfS_allAlignedStateS_last_orthogonal
    (A : Λ → Bool) (N : ℕ)
    (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
        (neelStateOfS A N) = 0 := by
  unfold allAlignedStateS neelStateOfS
  have hne : neelConfigOfS A N ≠ allAlignedConfigS Λ N (Fin.last N) := by
    obtain ⟨x, hx⟩ := hA
    intro heq
    have h := congrFun heq x
    unfold neelConfigOfS allAlignedConfigS at h
    rw [if_pos hx] at h
    have hval : (0 : Fin (N + 1)).val = (Fin.last N).val := by rw [h]
    simp [Fin.last] at hval
    omega
  exact basisVecS_inner_of_ne hne

/-- **State-level distinctness** `Φ_Néel(A) ≠ Φ_⊤` (spin-S): when `0 < N`
and `|¬A| > 0`, the Néel state is distinct from the all-up state.
Equality would force `<Φ_⊤ | Φ_⊤> = 0`, contradicting norm-squared = 1
(γ-4 step 184). -/
theorem neelStateOfS_ne_allAlignedStateS_zero
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hAc : ∃ x : Λ, A x = false) :
    neelStateOfS A N ≠ allAlignedStateS Λ N (0 : Fin (N + 1)) := by
  intro h
  have horth := neelStateOfS_allAlignedStateS_orthogonal A N hN hAc
  rw [h, allAlignedStateS_inner_self] at horth
  exact one_ne_zero horth

/-- **State-level distinctness** `Φ_Néel(A) ≠ Φ_⊥` (spin-S): when `0 < N`
and `|A| > 0`, the Néel state is distinct from the all-down state
(γ-4 step 184). -/
theorem neelStateOfS_ne_allAlignedStateS_last
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) :
    neelStateOfS A N ≠ allAlignedStateS Λ N (Fin.last N) := by
  intro h
  have horth := neelStateOfS_allAlignedStateS_last_orthogonal A N hN hA
  rw [h, allAlignedStateS_inner_self] at horth
  exact one_ne_zero horth

/-- **Reverse direction** of γ-4 step 133: `<Φ_Néel(A) | Φ_⊤> = 0`
when `0 < N` and `|¬A| > 0`. Derived from
`neelStateOfS_allAlignedStateS_orthogonal` via
`Matrix.star_dotProduct` (γ-4 step 196). -/
theorem allAlignedStateS_zero_neelStateOfS_orthogonal
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hAc : ∃ x : Λ, A x = false) :
    dotProduct (star (neelStateOfS A N))
        (allAlignedStateS Λ N (0 : Fin (N + 1))) = 0 := by
  have := neelStateOfS_allAlignedStateS_orthogonal A N hN hAc
  rw [show dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
          (neelStateOfS A N) =
        star (dotProduct (star (neelStateOfS A N))
          (allAlignedStateS Λ N (0 : Fin (N + 1)))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- **Reverse direction** of γ-4 step 173: `<Φ_Néel(A) | Φ_⊥> = 0`
when `0 < N` and `|A| > 0` (γ-4 step 196). -/
theorem allAlignedStateS_last_neelStateOfS_orthogonal
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (neelStateOfS A N))
        (allAlignedStateS Λ N (Fin.last N)) = 0 := by
  have := neelStateOfS_allAlignedStateS_last_orthogonal A N hN hA
  rw [show dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          (neelStateOfS A N) =
        star (dotProduct (star (neelStateOfS A N))
          (allAlignedStateS Λ N (Fin.last N))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- `<Φ_⊤ | Φ_Néel(¬A)> = 0` when `|A| > 0` and `0 < N`. The complement
Néel state has `Fin.last N` on `A` (the original sublattice with `A x =
true`), so it differs from `Φ_⊤` (all `0`) at any vertex of `A`. Direct
application of `neelStateOfS_allAlignedStateS_orthogonal` with `A`
replaced by `¬A`. -/
theorem neelStateOfS_complement_allAlignedStateS_orthogonal
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
        (neelStateOfS (fun x : Λ => ! A x) N) = 0 := by
  have hAc' : ∃ x : Λ, (! A x) = false := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, by simp [hx]⟩
  exact neelStateOfS_allAlignedStateS_orthogonal (fun x : Λ => ! A x) N hN hAc'

/-- `<Φ_⊥ | Φ_Néel(¬A)> = 0` when `|¬A| > 0` and `0 < N`. Symmetric
counterpart for the all-down state. Direct application of
`neelStateOfS_allAlignedStateS_last_orthogonal` with `A` replaced by `¬A`. -/
theorem neelStateOfS_complement_allAlignedStateS_last_orthogonal
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N) (hAc : ∃ x : Λ, A x = false) :
    dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
        (neelStateOfS (fun x : Λ => ! A x) N) = 0 := by
  have hA' : ∃ x : Λ, (! A x) = true := by
    obtain ⟨x, hx⟩ := hAc
    exact ⟨x, by simp [hx]⟩
  exact neelStateOfS_allAlignedStateS_last_orthogonal (fun x : Λ => ! A x) N hN hA'

/-- **Reverse direction**: `<Φ_Néel(¬A) | Φ_⊤> = 0` when `0 < N` and
`|A| > 0` (γ-4 step 196). -/
theorem allAlignedStateS_zero_neelStateOfS_complement_orthogonal
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) :
    dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
        (allAlignedStateS Λ N (0 : Fin (N + 1))) = 0 := by
  have := neelStateOfS_complement_allAlignedStateS_orthogonal A N hN hA
  rw [show dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
          (neelStateOfS (fun x : Λ => ! A x) N) =
        star (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
          (allAlignedStateS Λ N (0 : Fin (N + 1)))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- **Reverse direction**: `<Φ_Néel(¬A) | Φ_⊥> = 0` when `0 < N` and
`|¬A| > 0` (γ-4 step 196). -/
theorem allAlignedStateS_last_neelStateOfS_complement_orthogonal
    (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hAc : ∃ x : Λ, A x = false) :
    dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
        (allAlignedStateS Λ N (Fin.last N)) = 0 := by
  have := neelStateOfS_complement_allAlignedStateS_last_orthogonal A N hN hAc
  rw [show dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          (neelStateOfS (fun x : Λ => ! A x) N) =
        star (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
          (allAlignedStateS Λ N (Fin.last N))) from by
      rw [← Matrix.star_dotProduct]] at this
  exact star_eq_zero.mp this

/-- **Triple linear independence** of {`Φ_⊤`, `Φ_⊥`, `Φ_Néel(A)`} (spin-S):
when `Λ` is non-empty, `0 < N`, and both sublattices are non-empty, any
linear combination equal to `0` has all coefficients `0`. The triple
spans a 3-dimensional subspace of the many-body Hilbert space, derived
from the pairwise orthogonalities (γ-4 step 173 plus
`allAlignedStateS_inner_of_ne` and `neelStateOfS_allAlignedStateS_orthogonal`)
and norm-squared = 1 of each state. -/
theorem neelStateOfS_allAligned_triple_independent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false)
    {c1 c2 c3 : ℂ}
    (h : c1 • allAlignedStateS Λ N (0 : Fin (N + 1)) +
         c2 • allAlignedStateS Λ N (Fin.last N) +
         c3 • neelStateOfS A N = 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have h_zero_ne_last : (0 : Fin (N + 1)) ≠ Fin.last N := by
    intro hh
    have : (0 : Fin (N + 1)).val = (Fin.last N).val := by rw [hh]
    simp [Fin.last] at this
    omega
  have h_top_top := allAlignedStateS_inner_self (V := Λ) (N := N) 0
  have h_bot_bot := allAlignedStateS_inner_self (V := Λ) (N := N) (Fin.last N)
  have h_neel_neel := neelStateOfS_inner_self A N
  have h_top_bot := allAlignedStateS_inner_of_ne (V := Λ) (N := N) h_zero_ne_last
  have h_bot_top := allAlignedStateS_inner_of_ne (V := Λ) (N := N) h_zero_ne_last.symm
  have h_top_neel := neelStateOfS_allAlignedStateS_orthogonal A N hN hAc
  have h_bot_neel := neelStateOfS_allAlignedStateS_last_orthogonal A N hN hA
  have h_neel_top : dotProduct (star (neelStateOfS A N))
      (allAlignedStateS Λ N (0 : Fin (N + 1))) = 0 := by
    have := h_top_neel
    rw [show dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            (neelStateOfS A N) =
          star (dotProduct (star (neelStateOfS A N))
            (allAlignedStateS Λ N (0 : Fin (N + 1)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neel_bot : dotProduct (star (neelStateOfS A N))
      (allAlignedStateS Λ N (Fin.last N)) = 0 := by
    have := h_bot_neel
    rw [show dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            (neelStateOfS A N) =
          star (dotProduct (star (neelStateOfS A N))
            (allAlignedStateS Λ N (Fin.last N))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have hc1 : c1 = 0 := by
    have := congrArg
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h_top_top, h_top_bot, h_top_neel, dotProduct_zero] at this
    simp at this
    exact this
  have hc2 : c2 = 0 := by
    have := congrArg
      (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h_bot_top, h_bot_bot, h_bot_neel, dotProduct_zero] at this
    simp at this
    exact this
  have hc3 : c3 = 0 := by
    have := congrArg (dotProduct (star (neelStateOfS A N))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h_neel_top, h_neel_bot, h_neel_neel, dotProduct_zero] at this
    simp at this
    exact this
  exact ⟨hc1, hc2, hc3⟩

/-- **mathlib `LinearIndependent` form of the triple LI** (spin-S):
`LinearIndependent ℂ ![Φ_⊤, Φ_⊥, Φ_Néel(A)]` when `Λ` non-empty,
`0 < N`, and both sublattices non-empty. Direct conversion of γ-4
step 174 via `Fintype.linearIndependent_iff` and
`Fin.sum_univ_three` (γ-4 step 187). -/
theorem neelStateOfS_allAligned_triple_linearIndependent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    LinearIndependent ℂ
      (![allAlignedStateS Λ N (0 : Fin (N + 1)),
         allAlignedStateS Λ N (Fin.last N),
         neelStateOfS A N] : Fin 3 → _) := by
  rw [Fintype.linearIndependent_iff]
  intros g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  obtain ⟨h0, h1, h2⟩ :=
    neelStateOfS_allAligned_triple_independent A N hN hA hAc hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **`finrank` of the triple span equals 3** (spin-S). Direct
corollary of γ-4 step 187 via `finrank_span_eq_card`. -/
theorem neelStateOfS_allAligned_triple_finrank_span
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (![allAlignedStateS Λ N (0 : Fin (N + 1)),
             allAlignedStateS Λ N (Fin.last N),
             neelStateOfS A N] : Fin 3 → _))) = 3 := by
  rw [finrank_span_eq_card
        (neelStateOfS_allAligned_triple_linearIndependent A N hN hA hAc)]
  rfl

/-- **Set form** of the triple finrank (spin-S):
`finrank ℂ (span ℂ {Φ_⊤, Φ_⊥, Φ_Néel(A)}) = 3` (γ-4 step 190). -/
theorem neelStateOfS_allAligned_triple_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({allAlignedStateS Λ N (0 : Fin (N + 1)),
          allAlignedStateS Λ N (Fin.last N),
          neelStateOfS A N} : Set _)) = 3 := by
  have hrange :
      Set.range
        (![allAlignedStateS Λ N (0 : Fin (N + 1)),
           allAlignedStateS Λ N (Fin.last N),
           neelStateOfS A N] : Fin 3 → _) =
      ({allAlignedStateS Λ N (0 : Fin (N + 1)),
        allAlignedStateS Λ N (Fin.last N),
        neelStateOfS A N} : Set _) := by
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
  exact neelStateOfS_allAligned_triple_finrank_span A N hN hA hAc

/-- **mathlib LinearIndependent** form of the Néel-complement pair LI
(spin-S): `LinearIndependent ℂ ![Φ_Néel(A), Φ_Néel(¬A)]` when `Λ` is
non-empty and `0 < N`. Direct conversion of γ-4 step 172 via
`LinearIndependent.pair_iff` (γ-4 step 185). -/
theorem neelStateOfS_complement_linearIndependent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    LinearIndependent ℂ
      ![neelStateOfS A N, neelStateOfS (fun x : Λ => ! A x) N] := by
  rw [LinearIndependent.pair_iff]
  intros s t h
  exact neelStateOfS_complement_pair_independent A N hN h

/-- **`finrank` of the Néel-complement pair span equals 2** (spin-S).
Direct application of `finrank_span_eq_card` to the
`LinearIndependent` of γ-4 step 185 (γ-4 step 186). -/
theorem neelStateOfS_complement_finrank_span
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          ![neelStateOfS A N, neelStateOfS (fun x : Λ => ! A x) N])) = 2 := by
  rw [finrank_span_eq_card
        (neelStateOfS_complement_linearIndependent A N hN)]
  rfl

/-- **Set form**: `finrank ℂ (span ℂ {Φ_Néel(A), Φ_Néel(¬A)}) = 2`
(spin-S). Bridge from γ-4 step 186 via the explicit
`Set.range ![v0, v1] = {v0, v1}` identity, proved by membership
(γ-4 step 189). -/
theorem neelStateOfS_complement_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({neelStateOfS A N, neelStateOfS (fun x : Λ => ! A x) N} : Set _)) = 2 := by
  have hrange :
      Set.range
        ![neelStateOfS A N, neelStateOfS (fun x : Λ => ! A x) N] =
      ({neelStateOfS A N, neelStateOfS (fun x : Λ => ! A x) N} : Set _) := by
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
  exact neelStateOfS_complement_finrank_span A N hN

/-- **Triple linear independence** of {`Φ_⊤`, `Φ_⊥`, `Φ_Néel(¬A)`}
(spin-S, complement variant): direct application of γ-4 step 174 with
`A := ¬A`, exchanging the existence hypotheses (γ-4 step 183). -/
theorem neelStateOfS_complement_allAligned_triple_independent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false)
    {c1 c2 c3 : ℂ}
    (h : c1 • allAlignedStateS Λ N (0 : Fin (N + 1)) +
         c2 • allAlignedStateS Λ N (Fin.last N) +
         c3 • neelStateOfS (fun x : Λ => ! A x) N = 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have hA' : ∃ x : Λ, (! A x) = true := by
    obtain ⟨x, hx⟩ := hAc
    exact ⟨x, by simp [hx]⟩
  have hAc' : ∃ x : Λ, (! A x) = false := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, by simp [hx]⟩
  exact neelStateOfS_allAligned_triple_independent
    (fun x : Λ => ! A x) N hN hA' hAc' h

/-- **Quadruple linear independence** of {`Φ_⊤`, `Φ_⊥`, `Φ_Néel(A)`,
`Φ_Néel(¬A)`} (spin-S): when `Λ` non-empty, `0 < N`, and both sublattices
are non-empty, any zero linear combination has all four coefficients
zero. The quadruple spans a 4-dimensional subspace, derived from the six
pairwise orthogonalities (γ-4 steps 133/171/173/180 and
`allAlignedStateS_inner_of_ne`) and norm-squared = 1. -/
theorem neelStateOfS_allAligned_quad_independent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false)
    {c1 c2 c3 c4 : ℂ}
    (h : c1 • allAlignedStateS Λ N (0 : Fin (N + 1)) +
         c2 • allAlignedStateS Λ N (Fin.last N) +
         c3 • neelStateOfS A N +
         c4 • neelStateOfS (fun x : Λ => ! A x) N = 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  have h_zero_ne_last : (0 : Fin (N + 1)) ≠ Fin.last N := by
    intro hh
    have : (0 : Fin (N + 1)).val = (Fin.last N).val := by rw [hh]
    simp [Fin.last] at this
    omega
  have h_top_top := allAlignedStateS_inner_self (V := Λ) (N := N) 0
  have h_bot_bot := allAlignedStateS_inner_self (V := Λ) (N := N) (Fin.last N)
  have h_neelA_neelA := neelStateOfS_inner_self A N
  have h_neelcA_neelcA := neelStateOfS_inner_self (fun x : Λ => ! A x) N
  have h_top_bot := allAlignedStateS_inner_of_ne (V := Λ) (N := N) h_zero_ne_last
  have h_bot_top := allAlignedStateS_inner_of_ne (V := Λ) (N := N) h_zero_ne_last.symm
  have h_top_neelA := neelStateOfS_allAlignedStateS_orthogonal A N hN hAc
  have h_bot_neelA := neelStateOfS_allAlignedStateS_last_orthogonal A N hN hA
  have h_top_neelcA :=
    neelStateOfS_complement_allAlignedStateS_orthogonal A N hN hA
  have h_bot_neelcA :=
    neelStateOfS_complement_allAlignedStateS_last_orthogonal A N hN hAc
  have h_neelA_neelcA := neelStateOfS_complement_orthogonal A N hN
  -- Reverse orthogonalities (Néel-allAligned and Néel(¬A)-allAligned, etc.) by symmetry:
  have h_neelA_top : dotProduct (star (neelStateOfS A N))
      (allAlignedStateS Λ N (0 : Fin (N + 1))) = 0 := by
    have := h_top_neelA
    rw [show dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            (neelStateOfS A N) =
          star (dotProduct (star (neelStateOfS A N))
            (allAlignedStateS Λ N (0 : Fin (N + 1)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelA_bot : dotProduct (star (neelStateOfS A N))
      (allAlignedStateS Λ N (Fin.last N)) = 0 := by
    have := h_bot_neelA
    rw [show dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            (neelStateOfS A N) =
          star (dotProduct (star (neelStateOfS A N))
            (allAlignedStateS Λ N (Fin.last N))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelcA_top : dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
      (allAlignedStateS Λ N (0 : Fin (N + 1))) = 0 := by
    have := h_top_neelcA
    rw [show dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            (neelStateOfS (fun x : Λ => ! A x) N) =
          star (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
            (allAlignedStateS Λ N (0 : Fin (N + 1)))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelcA_bot : dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
      (allAlignedStateS Λ N (Fin.last N)) = 0 := by
    have := h_bot_neelcA
    rw [show dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
            (neelStateOfS (fun x : Λ => ! A x) N) =
          star (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
            (allAlignedStateS Λ N (Fin.last N))) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have h_neelcA_neelA : dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
      (neelStateOfS A N) = 0 := by
    have := h_neelA_neelcA
    rw [show dotProduct (star (neelStateOfS A N))
            (neelStateOfS (fun x : Λ => ! A x) N) =
          star (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
            (neelStateOfS A N)) from by
        rw [← Matrix.star_dotProduct]] at this
    exact star_eq_zero.mp this
  have hc1 : c1 = 0 := by
    have := congrArg
      (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_top_top, h_top_bot, h_top_neelA, h_top_neelcA, dotProduct_zero] at this
    simp at this
    exact this
  have hc2 : c2 = 0 := by
    have := congrArg
      (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_bot_top, h_bot_bot, h_bot_neelA, h_bot_neelcA, dotProduct_zero] at this
    simp at this
    exact this
  have hc3 : c3 = 0 := by
    have := congrArg (dotProduct (star (neelStateOfS A N))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_neelA_top, h_neelA_bot, h_neelA_neelA, h_neelA_neelcA,
        dotProduct_zero] at this
    simp at this
    exact this
  have hc4 : c4 = 0 := by
    have := congrArg
      (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))) h
    rw [dotProduct_add, dotProduct_add, dotProduct_add,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        h_neelcA_top, h_neelcA_bot, h_neelcA_neelA, h_neelcA_neelcA,
        dotProduct_zero] at this
    simp at this
    exact this
  exact ⟨hc1, hc2, hc3, hc4⟩

/-- **Quadruple `LinearIndependent`** (spin-S):
`LinearIndependent ℂ ![Φ_⊤, Φ_⊥, Φ_Néel(A), Φ_Néel(¬A)]` when `Λ` non-empty,
`0 < N`, and both sublattices non-empty. Direct conversion of γ-4
step 181 via `Fintype.linearIndependent_iff` and `Fin.sum_univ_four`
(γ-4 step 188). -/
theorem neelStateOfS_allAligned_quad_linearIndependent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    LinearIndependent ℂ
      (![allAlignedStateS Λ N (0 : Fin (N + 1)),
         allAlignedStateS Λ N (Fin.last N),
         neelStateOfS A N,
         neelStateOfS (fun x : Λ => ! A x) N] : Fin 4 → _) := by
  rw [Fintype.linearIndependent_iff]
  intros g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  obtain ⟨h0, h1, h2, h3⟩ :=
    neelStateOfS_allAligned_quad_independent A N hN hA hAc hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **`finrank` of the quadruple span equals 4** (spin-S). -/
theorem neelStateOfS_allAligned_quad_finrank_span
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (![allAlignedStateS Λ N (0 : Fin (N + 1)),
             allAlignedStateS Λ N (Fin.last N),
             neelStateOfS A N,
             neelStateOfS (fun x : Λ => ! A x) N] : Fin 4 → _))) = 4 := by
  rw [finrank_span_eq_card
        (neelStateOfS_allAligned_quad_linearIndependent A N hN hA hAc)]
  rfl

/-- **mathlib `LinearIndependent` form** of the complement-Néel triple LI
(spin-S): direct conversion of γ-4 step 183 via `Fintype.linearIndependent_iff`
and `Fin.sum_univ_three` (γ-4 step 192). -/
theorem neelStateOfS_complement_allAligned_triple_linearIndependent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    LinearIndependent ℂ
      (![allAlignedStateS Λ N (0 : Fin (N + 1)),
         allAlignedStateS Λ N (Fin.last N),
         neelStateOfS (fun x : Λ => ! A x) N] : Fin 3 → _) := by
  rw [Fintype.linearIndependent_iff]
  intros g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  obtain ⟨h0, h1, h2⟩ :=
    neelStateOfS_complement_allAligned_triple_independent A N hN hA hAc hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **`finrank` of the complement-Néel triple span equals 3** (spin-S). -/
theorem neelStateOfS_complement_allAligned_triple_finrank_span
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range
          (![allAlignedStateS Λ N (0 : Fin (N + 1)),
             allAlignedStateS Λ N (Fin.last N),
             neelStateOfS (fun x : Λ => ! A x) N] : Fin 3 → _))) = 3 := by
  rw [finrank_span_eq_card
        (neelStateOfS_complement_allAligned_triple_linearIndependent
          A N hN hA hAc)]
  rfl

/-- **Set form** of the complement-Néel triple finrank (spin-S):
`finrank ℂ (span ℂ {Φ_⊤, Φ_⊥, Φ_Néel(¬A)}) = 3` (γ-4 step 193). -/
theorem neelStateOfS_complement_allAligned_triple_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({allAlignedStateS Λ N (0 : Fin (N + 1)),
          allAlignedStateS Λ N (Fin.last N),
          neelStateOfS (fun x : Λ => ! A x) N} : Set _)) = 3 := by
  have hrange :
      Set.range
        (![allAlignedStateS Λ N (0 : Fin (N + 1)),
           allAlignedStateS Λ N (Fin.last N),
           neelStateOfS (fun x : Λ => ! A x) N] : Fin 3 → _) =
      ({allAlignedStateS Λ N (0 : Fin (N + 1)),
        allAlignedStateS Λ N (Fin.last N),
        neelStateOfS (fun x : Λ => ! A x) N} : Set _) := by
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
  exact neelStateOfS_complement_allAligned_triple_finrank_span A N hN hA hAc

/-- **Set form** of the quadruple finrank (spin-S):
`finrank ℂ (span ℂ {Φ_⊤, Φ_⊥, Φ_Néel(A), Φ_Néel(¬A)}) = 4` (γ-4 step 191). -/
theorem neelStateOfS_allAligned_quad_finrank_span_set
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    (hA : ∃ x : Λ, A x = true) (hAc : ∃ x : Λ, A x = false) :
    Module.finrank ℂ
      (Submodule.span ℂ
        ({allAlignedStateS Λ N (0 : Fin (N + 1)),
          allAlignedStateS Λ N (Fin.last N),
          neelStateOfS A N,
          neelStateOfS (fun x : Λ => ! A x) N} : Set _)) = 4 := by
  have hrange :
      Set.range
        (![allAlignedStateS Λ N (0 : Fin (N + 1)),
           allAlignedStateS Λ N (Fin.last N),
           neelStateOfS A N,
           neelStateOfS (fun x : Λ => ! A x) N] : Fin 4 → _) =
      ({allAlignedStateS Λ N (0 : Fin (N + 1)),
        allAlignedStateS Λ N (Fin.last N),
        neelStateOfS A N,
        neelStateOfS (fun x : Λ => ! A x) N} : Set _) := by
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
  exact neelStateOfS_allAligned_quad_finrank_span A N hN hA hAc

/-- The Néel configuration packaged as an element of the magnetization
sector `magConfigS Λ N (|¬A| · N)`. The `Ŝ_tot^(3)` eigenvalue is
`|Λ|·N/2 - |¬A|·N = (|A| − |¬A|)·N/2`. -/
def neelMagConfigS (A : Λ → Bool) (N : ℕ) :
    magConfigS Λ N ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N) :=
  ⟨neelConfigOfS A N, magSumS_neelConfigOfS A N⟩

/-- The magnetization sector with magSum `|¬A| · N` is non-empty: it
contains `neelMagConfigS A N`. Useful for typeclass resolution where
`Nonempty (magConfigS Λ N M)` is required (e.g., `ToyPF.lean`). -/
instance neelMagConfigS_nonempty (A : Λ → Bool) (N : ℕ) :
    Nonempty (magConfigS Λ N
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N)) :=
  ⟨neelMagConfigS A N⟩

/-- The underlying configuration of `neelMagConfigS A N` is `neelConfigOfS A N`. -/
@[simp]
theorem neelMagConfigS_val (A : Λ → Bool) (N : ℕ) :
    (neelMagConfigS A N).1 = neelConfigOfS A N := rfl

/-- The Néel state equals `basisVecS` of the underlying configuration of
`neelMagConfigS A N`. Bridges the `neelStateOfS` API and the `magConfigS`
subtype API. -/
theorem neelStateOfS_eq_basisVecS_neelMagConfigS (A : Λ → Bool) (N : ℕ) :
    neelStateOfS A N = basisVecS (neelMagConfigS A N).1 := by
  unfold neelStateOfS
  rw [neelMagConfigS_val]

/-- The magnetization sector `magConfigS Λ N (|¬A|·N)` has at least one
element (the Néel config). -/
theorem magConfigS_card_pos_via_neel (A : Λ → Bool) (N : ℕ) :
    1 ≤ Fintype.card (magConfigS Λ N
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N)) :=
  Fintype.card_pos

/-- The line spanned by the spin-`S` Néel state is 1-dimensional:
`finrank ℂ (ℂ ∙ Φ_Néel_S) = 1`. -/
theorem neelStateOfS_finrank_span (A : Λ → Bool) (N : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ {neelStateOfS A N}) = 1 :=
  finrank_span_singleton (neelStateOfS_ne_zero A N)

/-- `<Φ_⊤ | Ĥ_toy_S | Φ_⊤> = +|A|·|¬A|·N²/2`. The all-up state's toy
Hamiltonian expectation. Positive sign (variational signature opposite
to the Néel state's negative expectation, γ-4 step 131). -/
theorem allAlignedStateS_zero_heisenbergToyHamiltonianS_expectation
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (allAlignedStateS Λ N (0 : Fin (N + 1)))) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        ((N : ℂ) * (N : ℂ)) / 2 := by
  rw [heisenbergToyHamiltonianS_mulVec_allAlignedStateS_zero_simplified]
  rw [dotProduct_smul, allAlignedStateS_inner_self]
  rw [smul_eq_mul, mul_one]

/-- **Variational spin gap**:
`<Φ_⊤|Ĥ_toy_S|Φ_⊤> - <Φ_Néel|Ĥ_toy_S|Φ_Néel> = |A|·|¬A|·N²`.

The all-up state has positive toy Hamiltonian expectation `+|A|·|¬A|·N²/2`,
the Néel state has negative `-|A|·|¬A|·N²/2`. Their difference is
strictly positive when both sublattices are non-empty, demonstrating
the variational separation underpinning Tasaki §2.5 Theorem 2.3. -/
theorem heisenbergToyHamiltonianS_variational_gap
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (allAlignedStateS Λ N (0 : Fin (N + 1)))) -
      dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec (neelStateOfS A N)) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        ((N : ℂ) * (N : ℂ)) := by
  rw [allAlignedStateS_zero_heisenbergToyHamiltonianS_expectation,
    neelStateOfS_heisenbergToyHamiltonianS_expectation]
  ring


end LatticeSystem.Quantum
