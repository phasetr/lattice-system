import LatticeSystem.Quantum.SpinS.ParityReachShuffleIter

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Drain a single A-site into the target via the iterated shuffle

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

A specialised form of the iterated `n`-unit shuffle (#3800) where the transferred amount is
exactly `(σ a).val`.  After the move, `σ' a = 0` and `σ' a₀ = (σ a₀).val + (σ a).val`.  This is
the "drain `a` into `a₀`" primitive used in the multi-site concentration argument of (d)
reachability totality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Drain `a` into `a₀`**: starting from `σ`, the config with `σ' a = 0` and `σ' a₀` increased
by `(σ a).val` (with `σ b` net unchanged and everything else unchanged) is `ParityReachableS`-
reachable, provided the room conditions hold. -/
theorem parityReachableS_drain_a_into_a0
    (A : V → Bool) {a a₀ b : V} (ha_a₀ : a ≠ a₀)
    (haba : (bipartiteCompleteGraphOf A).Adj a b)
    (ha₀b : (bipartiteCompleteGraphOf A).Adj a₀ b)
    {σ : V → Fin (N + 1)}
    (hroom : (σ a₀).val + (σ a).val ≤ N) (hkb : (σ b).val + 1 ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a a₀ ⟨0, by omega⟩ ⟨(σ a₀).val + (σ a).val, by omega⟩) := by
  have hka : (σ a).val ≤ (σ a).val := le_refl _
  have hka₀ : (σ a₀).val + (σ a).val ≤ N := hroom
  have hreach :=
    parityReachableS_shuffle_n_units A ha_a₀ haba ha₀b (n := (σ a).val) hka hka₀ hkb
  -- The target has σ' a = ⟨σ a - σ a, _⟩ = 0 and σ' a₀ = σ a₀ + σ a.
  have htarget_eq :
      configUpdateTwo σ a a₀
        ⟨(σ a).val - (σ a).val, by have := (σ a).isLt; omega⟩
        ⟨(σ a₀).val + (σ a).val, by omega⟩ =
      configUpdateTwo σ a a₀ ⟨0, by omega⟩ ⟨(σ a₀).val + (σ a).val, by omega⟩ := by
    funext j
    unfold configUpdateTwo
    by_cases hja : j = a
    · rw [hja, if_pos rfl, if_pos rfl]
      ext
      change (σ a).val - (σ a).val = 0
      omega
    · rw [if_neg hja, if_neg hja]
  rw [htarget_eq] at hreach
  exact hreach

end LatticeSystem.Quantum
