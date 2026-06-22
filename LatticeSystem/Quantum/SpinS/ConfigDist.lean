import LatticeSystem.Quantum.SpinS.ConfigDistCore

/-!
# Spin-`S` configuration distance
(Tasaki §2.5 Phase B-γ γ-3 connectivity prep)

The configuration distance `configDistS σ σ' := ∑_x |σ x − σ' x|`
(natural-number absolute difference) measures how far apart two
spin-`S` configurations are. It is the spin-`S` generalisation of the
Hamming distance used in the spin-`1/2` connectivity argument
(`LatticeSystem/Quantum/MarshallLiebMattis/EqMagnetizationReachable.lean`).

Key properties:
- `configDistS_eq_zero_iff`: distance zero iff configurations are equal.
- `configDistS_comm`: symmetry.

These are stepping stones for the irreducibility argument: starting
from two equal-magnetization configurations of positive distance, find
sites `x, y` where `σ x > σ' x` and `σ y < σ' y`, transport one unit
to reduce the distance, and iterate.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Reachability for the complete graph -/

omit [DecidableEq V] in
/-- For the complete graph `G = ⊤` (every distinct pair of vertices is
adjacent), any two configurations with equal magnetization sum are
`RaiseLowerReachableS`. The proof inducts on `configDistS σ σ'`,
using `exists_over_under` to find the witness sites and
`configDistS_decrease_of_over_under` to drive the reduction. -/
theorem raiseLowerReachableS_completeGraph_of_eq_magSumS
    {σ σ' : V → Fin (N + 1)} (hmag : magSumS σ = magSumS σ') :
    RaiseLowerReachableS (⊤ : SimpleGraph V) σ σ' := by
  classical
  -- Strong induction on configDistS σ σ'.
  suffices h : ∀ n, ∀ σ σ' : V → Fin (N + 1),
      magSumS σ = magSumS σ' → configDistS σ σ' ≤ n →
      RaiseLowerReachableS (⊤ : SimpleGraph V) σ σ' from
    h (configDistS σ σ') σ σ' hmag (le_refl _)
  intro n
  induction n with
  | zero =>
    intro σ σ' _ hd
    have hsigma : σ = σ' :=
      (configDistS_eq_zero_iff σ σ').mp (Nat.le_zero.mp hd)
    rw [hsigma]
    exact RaiseLowerReachableS.refl _ _
  | succ n ih =>
    intro σ σ' hmag hd
    by_cases hne : σ = σ'
    · rw [hne]; exact RaiseLowerReachableS.refl _ _
    · -- Find over/under sites.
      obtain ⟨⟨x, hover⟩, y, hunder⟩ :=
        exists_over_under_of_eq_magSumS hne hmag
      -- x ≠ y (else (σ' x).val < (σ x).val and (σ x).val < (σ' x).val).
      have hxy : x ≠ y := fun heq => by
        subst heq; omega
      -- Bounds for the raise/lower update.
      have hx_bound : (σ x).val - 1 < N + 1 := by
        have := (σ x).isLt; omega
      have hy_bound : (σ y).val + 1 < N + 1 := by
        have := (σ' y).isLt; omega
      -- Define σ''.
      let σ'' : V → Fin (N + 1) :=
        Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) y
          ⟨(σ y).val + 1, hy_bound⟩
      -- Distance reduces by 2.
      have hreduce : configDistS σ'' σ' + 2 = configDistS σ σ' :=
        configDistS_decrease_of_over_under hxy hover hunder
      -- σ'' agrees with σ off {x, y}.
      have hagree : ∀ k, k ≠ x → k ≠ y → σ'' k = σ k := by
        intro k hkx hky
        change (Function.update (Function.update σ x _) y _) k = σ k
        rw [Function.update_of_ne hky, Function.update_of_ne hkx]
      -- σ'' x and σ'' y values.
      have hupd_x : (σ'' x).val = (σ x).val - 1 := by
        change (Function.update (Function.update σ x _) y _ x).val = _
        rw [Function.update_of_ne hxy, Function.update_self]
      have hupd_y : (σ'' y).val = (σ y).val + 1 := by
        change (Function.update (Function.update σ x _) y _ y).val = _
        rw [Function.update_self]
      -- Adjacency in ⊤: any distinct pair.
      have hadj : (⊤ : SimpleGraph V).Adj x y := by
        rw [SimpleGraph.top_adj]
        exact hxy
      -- Step σ ↦ σ'': lower at x, raise at y.
      have hstep : RaiseLowerStepS (⊤ : SimpleGraph V) σ σ'' := by
        refine ⟨x, y, hadj, Or.inr ⟨?_, ?_⟩, hagree⟩
        · -- (σ'' x).val + 1 = (σ x).val.
          rw [hupd_x]; omega
        · -- (σ y).val + 1 = (σ'' y).val.
          rw [hupd_y]
      -- magSumS σ'' = magSumS σ (raise/lower preserves sum).
      have hmag_step : magSumS σ'' = magSumS σ :=
        magSumS_eq_of_raiseLowerStepS hstep
      -- Apply IH on σ''.
      have hIH : RaiseLowerReachableS (⊤ : SimpleGraph V) σ'' σ' := by
        apply ih
        · rw [hmag_step]; exact hmag
        · -- configDistS σ'' σ' ≤ n (since +2 = configDistS σ σ' ≤ n + 1).
          omega
      -- Combine step σ → σ'' with reachable σ'' → σ'.
      exact (RaiseLowerReachableS.single hstep).trans hIH

end LatticeSystem.Quantum
