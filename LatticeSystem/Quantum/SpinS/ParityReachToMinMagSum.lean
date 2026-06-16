import LatticeSystem.Quantum.SpinS.ParityReachStepDownFull

/-!
# WF-iteration of `parityReachableS_step_down` to reach a sector-min canonical

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Iterating the full step-down dispatcher (#3821) by strong induction on `magSumS σ` shows that
every configuration reaches some `σ_min` with `magSumS σ_min < 2` — i.e. either the all-zero
config (for even parity) or a single-1-site config (for odd parity).

Combined with the within-sector reachability lift (#3817) and `ParityReachableS` symmetry
(#3816), this is the penultimate step before the full `parityReachableS_total` discharging
the
parity-block matrix irreducibility theorem (#3797).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.unusedDecidableInType false in
/-- **Auxiliary: strong induction on `n = magSumS σ`** to iterate the step-down dispatcher. -/
theorem parityReachableS_to_min_magSum_aux
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false) :
    ∀ (n : ℕ) (σ : V → Fin (N + 1)), magSumS σ = n →
      ∃ σ_min : V → Fin (N + 1),
        magSumS σ_min < 2 ∧
        ParityReachableS (bipartiteCompleteGraphOf A) σ σ_min := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hmag
    by_cases hsmall : n < 2
    · refine ⟨σ, ?_, ParityReachableS.refl _ _⟩
      omega
    · have h_pos : 2 ≤ magSumS σ := by omega
      obtain ⟨σ', h_mag', h_reach⟩ := parityReachableS_step_down A hA_ne hB_ne h_pos
      obtain ⟨σ_min, h_min_small, h_min_reach⟩ :=
        ih (magSumS σ') (by omega) σ' rfl
      exact ⟨σ_min, h_min_small, ParityReachableS.trans h_reach h_min_reach⟩

set_option linter.unusedDecidableInType false in
/-- **Step-down to a sector-min canonical**: any configuration reaches some `σ_min` with
`magSumS σ_min < 2` via `ParityReachableS`.  By the parity invariance of `ParityReachableS`
(#3786), `magSumS σ_min ≡ magSumS σ (mod 2)`, so the minimum value is `0` (even parity) or
`1` (odd parity). -/
theorem parityReachableS_to_min_magSum
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (σ : V → Fin (N + 1)) :
    ∃ σ_min : V → Fin (N + 1),
      magSumS σ_min < 2 ∧
      ParityReachableS (bipartiteCompleteGraphOf A) σ σ_min :=
  parityReachableS_to_min_magSum_aux A hA_ne hB_ne (magSumS σ) σ rfl

end LatticeSystem.Quantum
