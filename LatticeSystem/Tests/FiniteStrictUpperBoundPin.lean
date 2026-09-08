import LatticeSystem.Math.FiniteStrictUpperBound

/-!
# Signature pin: a finite family of reals has a strict upper bound

Repository-internal regression guard, **not** a Tasaki result on its own, pinning a generic
real-analysis fact consumed by several diagonal-boundedness arguments: a family of reals indexed
by any finite type admits a strict upper bound, with no nonemptiness hypothesis on the index
type.
-/

namespace LatticeSystem.Tests.FiniteStrictUpperBoundPin

/-- **Signature pin.** A finite family of reals has a strict upper bound, over a general index
type with no nonemptiness hypothesis. -/
example {ι : Type*} [Finite ι] (f : ι → ℝ) : ∃ c : ℝ, ∀ i, f i < c :=
  LatticeSystem.Math.exists_gt_of_finite f

/-- **Positive control.** The lemma observed at a concrete family, so the pin exercises a value
rather than only a signature. -/
example :
    ∃ c : ℝ, ∀ i : Fin 3, (if i = 0 then (1 : ℝ) else if i = 1 then 5 else 2) < c := by
  obtain ⟨c, hc⟩ :=
    LatticeSystem.Math.exists_gt_of_finite
      (fun i : Fin 3 => if i = 0 then (1 : ℝ) else if i = 1 then 5 else 2)
  exact ⟨c, hc⟩

/-- **Strength control.** The empty index type: this instantiation would not type-check against a
`Finset.sup'`-based statement, which needs `Nonempty`. It pins that the consolidation actually
weakened the hypothesis rather than merely relocating the old one. -/
example (f : Empty → ℝ) : ∃ c : ℝ, ∀ i, f i < c :=
  LatticeSystem.Math.exists_gt_of_finite f

end LatticeSystem.Tests.FiniteStrictUpperBoundPin
