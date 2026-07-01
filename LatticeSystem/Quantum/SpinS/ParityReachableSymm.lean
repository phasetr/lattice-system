import LatticeSystem.Quantum.SpinS.ParityReachable

/-!
# Symmetry of `ParityReachableS` and its underlying elementary steps

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Every elementary parity-block step (`RaiseLowerStepS`, `ParityBondStepS`, `SingleIonStepS`) is
defined by a disjunction of raise / lower branches, so each is symmetric: swapping the two
branches yields the same proposition with `σ` and `σ'` swapped.  Hence the disjoint sum
`ParityStepS` is symmetric, and so is its reflexive-transitive closure `ParityReachableS` via
`Relation.ReflTransGen.symmetric` (Mathlib).

The symmetry of `ParityReachableS` is the missing piece for the (d.3) full reachability layer
of the (d) reachability totality assembly: given the canonical-form embedding `σ → canonical_σ`
(#3806) we need `canonical_σ' → σ'` for the closing leg, which is exactly the reverse direction
that symmetry provides.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- **Symmetry of a `ParityBondStepS`**. -/
theorem parityBondStepS_symm {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityBondStepS G σ σ') : ParityBondStepS G σ' σ := by
  obtain ⟨x, y, hadj, hor, hoff⟩ := h
  refine ⟨x, y, hadj, ?_, ?_⟩
  · rcases hor with ⟨hx_raise, hy_raise⟩ | ⟨hx_lower, hy_lower⟩
    · exact Or.inr ⟨hx_raise, hy_raise⟩
    · exact Or.inl ⟨hx_lower, hy_lower⟩
  · intro k hkx hky
    exact (hoff k hkx hky).symm

omit [Fintype V] [DecidableEq V] in
/-- **Symmetry of a `SingleIonStepS`**. -/
theorem singleIonStepS_symm {σ σ' : V → Fin (N + 1)}
    (h : SingleIonStepS σ σ') : SingleIonStepS σ' σ := by
  obtain ⟨x, hor, hoff⟩ := h
  refine ⟨x, ?_, ?_⟩
  · rcases hor with hxraise | hxlower
    · exact Or.inr hxraise
    · exact Or.inl hxlower
  · intro k hkx
    exact (hoff k hkx).symm

omit [Fintype V] [DecidableEq V] in
/-- **Symmetry of `ParityStepS`**: dispatching on the three elementary-step disjuncts and using
their individual symmetries. -/
theorem parityStepS_symm {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityStepS G σ σ') : ParityStepS G σ' σ := by
  rcases h with hRL | hPB | hSI
  · exact Or.inl (RaiseLowerStepS.symm hRL)
  · exact Or.inr (Or.inl (parityBondStepS_symm hPB))
  · exact Or.inr (Or.inr (singleIonStepS_symm hSI))

omit [Fintype V] [DecidableEq V] in
/-- **Symmetry of `ParityReachableS`**: lifting the single-step symmetry through the
reflexive-transitive closure (via `Relation.ReflTransGen.symmetric`).  Together with reflexivity
and transitivity, `ParityReachableS G` is an equivalence relation on configurations. -/
theorem parityReachableS_symm {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : ParityReachableS G σ σ') : ParityReachableS G σ' σ :=
  Relation.ReflTransGen.symmetric (fun _ _ => parityStepS_symm) h

end LatticeSystem.Quantum
