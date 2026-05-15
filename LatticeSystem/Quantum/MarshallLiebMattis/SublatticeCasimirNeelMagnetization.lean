import LatticeSystem.Quantum.MarshallLiebMattis.SublatticeCasimirNeel

/-!
# Spin-`1/2` Néel state in magnetization subspaces

Extracted from `SublatticeCasimirNeel.lean` (refactor #46, 2026-05-16):
the trailing magnetization-subspace membership section was relocated
to a focused companion file. The split reduces the parent file from
1308 → 1221 lines.

These theorems establish:
- `Φ_Néel(A) ∈ magnetizationSubspace Λ ((|A|-|¬A|)/2)` (and complement
  variant).
- Non-triviality of magnetization subspaces witnessed by Néel states.
- Span inclusions into magnetization subspaces.
- `finrank` of the Néel state's span = 1.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5.
- γ-4 steps 176, 178, 194, 197.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The spin-`1/2` Néel state lies in the magnetization-`M` subspace
where `M = (|A|-|¬A|)/2`. Direct from `totalSpinHalfOp3_mulVec_neelStateOf`. -/
theorem neelStateOf_mem_magnetizationSubspace (A : Λ → Bool) :
    neelStateOf A ∈ magnetizationSubspace Λ
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) := by
  rw [mem_magnetizationSubspace_iff]
  exact totalSpinHalfOp3_mulVec_neelStateOf A

/-- **Complement Néel sits in the opposite magnetization sector**
(spin-`1/2`): `Φ_Néel(¬A) ∈ magnetizationSubspace ((|¬A|-|A|)/2)`.
Direct application of `neelStateOf_mem_magnetizationSubspace` with `A`
replaced by `¬A`, then simplifying `! ! A x = A x` (γ-4 step 176). -/
theorem neelStateOf_complement_mem_magnetizationSubspace (A : Λ → Bool) :
    neelStateOf (fun x : Λ => ! A x) ∈ magnetizationSubspace Λ
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) / 2) := by
  have := neelStateOf_mem_magnetizationSubspace (fun x : Λ => ! A x)
  simpa [Bool.not_not] using this

/-- **Spin-`1/2` complement magnetization subspace non-triviality**: the
opposite-sign sector `(|¬A|-|A|)/2` is also non-trivial, witnessed by
the non-zero complement Néel state `Φ_Néel(¬A)` (γ-4 step 178). -/
theorem magnetizationSubspace_complement_nontrivial_via_neel (A : Λ → Bool) :
    magnetizationSubspace Λ
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) / 2) ≠ ⊥ := by
  intro hbot
  have hmem := neelStateOf_complement_mem_magnetizationSubspace A
  rw [hbot, Submodule.mem_bot] at hmem
  exact neelStateOf_ne_zero (fun x : Λ => ! A x) hmem

/-- The magnetization-`(|A|-|¬A|)/2` subspace is non-trivial: it contains
the non-zero Néel state. Spin-`1/2` analog of `neelMagConfigS_nonempty`. -/
theorem magnetizationSubspace_nontrivial_via_neel (A : Λ → Bool) :
    magnetizationSubspace Λ
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ≠ ⊥ := by
  intro hbot
  have hmem := neelStateOf_mem_magnetizationSubspace A
  rw [hbot, Submodule.mem_bot] at hmem
  exact neelStateOf_ne_zero A hmem

/-- The line spanned by the Néel state is contained in the magnetization
subspace at `M = (|A|-|¬A|)/2`. -/
theorem neelStateOf_span_le_magnetizationSubspace (A : Λ → Bool) :
    Submodule.span ℂ {neelStateOf A} ≤
      magnetizationSubspace Λ
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact neelStateOf_mem_magnetizationSubspace A

/-- The line spanned by the spin-`1/2` complement Néel state is contained
in the magnetization subspace at `-M = (|¬A|-|A|)/2`. Spin-`1/2` mirror
of γ-4 step 194. -/
theorem neelStateOf_complement_span_le_magnetizationSubspace (A : Λ → Bool) :
    Submodule.span ℂ {neelStateOf (fun x : Λ => ! A x)} ≤
      magnetizationSubspace Λ
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) / 2) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact neelStateOf_complement_mem_magnetizationSubspace A

/-- Spin-`1/2` Néel pair span ⊆ supremum of opposite-sign magnetization
subspaces. Spin-`1/2` mirror of γ-4 step 197. -/
theorem neelStateOf_pair_span_le_magnetizationSubspace_sup (A : Λ → Bool) :
    Submodule.span ℂ
        ({neelStateOf A, neelStateOf (fun x : Λ => ! A x)} : Set _) ≤
      magnetizationSubspace Λ
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) / 2) ⊔
        magnetizationSubspace Λ
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) / 2) := by
  rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · exact Submodule.mem_sup_left (neelStateOf_mem_magnetizationSubspace A)
  · exact Submodule.mem_sup_right (neelStateOf_complement_mem_magnetizationSubspace A)

/-- The line spanned by the Néel state is 1-dimensional:
`finrank ℂ (ℂ ∙ Φ_Néel) = 1`. -/
theorem neelStateOf_finrank_span (A : Λ → Bool) :
    Module.finrank ℂ (Submodule.span ℂ {neelStateOf A}) = 1 :=
  finrank_span_singleton (neelStateOf_ne_zero A)

end LatticeSystem.Quantum
