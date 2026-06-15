import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Diagonal extraction from an iterated limit (Tasaki Lemma 4.16)

A double sequence `f : ℕ → ℕ → ℝ` (`f L m`) whose iterated limit vanishes,
`lim_{m→∞} lim_{L→∞} f L m = 0`, admits a *diagonal* slow-diverging index `m(L)` along which it still
vanishes: there is a nondecreasing `m : ℕ → ℕ` with `m(L) → ∞` and `lim_{L→∞} f L (m L) = 0`.

This is the elementary real-analysis lemma Tasaki uses to choose the slowly diverging tower size
`M(L)` in the proofs of §4.2 (it underlies the existence of a suitable `M(L)` in Proposition 4.10).
It is purely analytic — no operators or physics — so we **discharge it axiom-free**.

Construction (Tasaki's proof): with `g m = lim_L f L m → 0` and `ε m = 1/(m+1)`, pick a strictly
increasing threshold `T m` with `T m ≥ N m` (where `|f L m − g m| < ε m` for `L ≥ N m`); set
`m(L) = `the largest `k ≤ L` with `T k ≤ L` (`Nat.findGreatest`).  Then `m` is monotone, diverges, and
`|f L (m L)| ≤ |f L (m L) − g (m L)| + |g (m L)| → 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Lemma 4.16, p. 108.
-/

namespace LatticeSystem.Math

open Filter Topology

/-- A strictly increasing threshold sequence dominating `N`: `T 0 = N 0`, `T (k+1) = max (T k + 1)
(N (k+1))`. -/
def thresholdSeq (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0
  | k + 1 => max (thresholdSeq N k + 1) (N (k + 1))

/-- The diagonal index: the largest `k ≤ L` with `T k ≤ L`. -/
def diagIndex (T : ℕ → ℕ) (L : ℕ) : ℕ := Nat.findGreatest (fun k => T k ≤ L) L

/-- **Tasaki Lemma 4.16 (diagonal extraction from an iterated limit).**  If for each `m` the column
`L ↦ f L m` converges to `g m`, and `g m → 0`, then there is a nondecreasing diagonal index
`m : ℕ → ℕ` with `m(L) → ∞` along which `f L (m L) → 0`. -/
theorem diagonal_tendsto_zero (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ m, Tendsto (fun L : ℕ => f L m) atTop (𝓝 (g m)))
    (hg0 : Tendsto g atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, Monotone m ∧ Tendsto m atTop atTop ∧
      Tendsto (fun L : ℕ => f L (m L)) atTop (𝓝 0) := by
  -- For each `m`, a threshold `N m` past which `f L m` is within `1/(m+1)` of `g m`.
  have hN : ∀ m : ℕ, ∃ Nm : ℕ, ∀ L : ℕ, Nm ≤ L → |f L m - g m| < 1 / (m + 1 : ℝ) := by
    intro m
    obtain ⟨Nm, hNm⟩ := Metric.tendsto_atTop.mp (hg m) (1 / (m + 1 : ℝ)) (by positivity)
    exact ⟨Nm, fun L hL => by rw [← Real.dist_eq]; exact hNm L hL⟩
  choose N hNspec using hN
  -- Strictly increasing thresholds `T` with `T m ≥ N m`.
  set T : ℕ → ℕ := thresholdSeq N with hTdef
  have hT_ge_N : ∀ m, N m ≤ T m := by
    intro m; cases m with
    | zero => exact le_rfl
    | succ k => exact le_max_right _ _
  have hT_strictMono : StrictMono T := by
    apply strictMono_nat_of_lt_succ
    intro m
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hT_ge_self : ∀ m, m ≤ T m := by
    intro m; induction m with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have : T k < T (k + 1) := hT_strictMono (Nat.lt_succ_self k)
      omega
  -- The diagonal index: the largest `k ≤ L` with `T k ≤ L`.
  set m : ℕ → ℕ := diagIndex T with hmdef
  -- key facts: `T (m L) ≤ L` whenever `T 0 ≤ L`, and `K ≤ m L` whenever `L ≥ T K`.
  have hTmL : ∀ L, T 0 ≤ L → T (m L) ≤ L := by
    intro L hL
    change T (Nat.findGreatest (fun k => T k ≤ L) L) ≤ L
    exact Nat.findGreatest_spec (P := fun k => T k ≤ L) (Nat.zero_le L) hL
  have hmL_ge : ∀ K L, T K ≤ L → K ≤ m L := by
    intro K L hL
    change K ≤ Nat.findGreatest (fun k => T k ≤ L) L
    exact Nat.le_findGreatest (P := fun k => T k ≤ L) (le_trans (hT_ge_self K) hL) hL
  refine ⟨m, ?_, ?_, ?_⟩
  · -- Monotone `m`.
    intro a b hab
    change Nat.findGreatest (fun k => T k ≤ a) a ≤ Nat.findGreatest (fun k => T k ≤ b) b
    exact Nat.findGreatest_mono (P := fun k => T k ≤ a) (Q := fun k => T k ≤ b)
      (fun k hk => le_trans hk hab) hab
  · -- `m L → ∞`.
    rw [tendsto_atTop_atTop]
    exact fun K => ⟨T K, fun L hL => hmL_ge K L hL⟩
  · -- `f L (m L) → 0`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K₁, hK₁⟩ :=
      Metric.tendsto_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (ε / 2)
        (by positivity)
    obtain ⟨K₂, hK₂⟩ := Metric.tendsto_atTop.mp hg0 (ε / 2) (by positivity)
    refine ⟨T (max K₁ K₂), fun L hL => ?_⟩
    have hT0 : T 0 ≤ L := le_trans (hT_strictMono.monotone (Nat.zero_le _)) hL
    have hge : max K₁ K₂ ≤ m L := hmL_ge _ L hL
    have hNmL : N (m L) ≤ L := le_trans (hT_ge_N (m L)) (hTmL L hT0)
    have h1 : |f L (m L) - g (m L)| < 1 / (m L + 1 : ℝ) := hNspec (m L) L hNmL
    have h2 : 1 / (m L + 1 : ℝ) < ε / 2 := by
      have := hK₁ (m L) (le_trans (le_max_left _ _) hge)
      rwa [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at this
    have h3 : |g (m L)| < ε / 2 := by
      have := hK₂ (m L) (le_trans (le_max_right _ _) hge)
      rwa [Real.dist_eq, sub_zero] at this
    rw [Real.dist_eq, sub_zero]
    calc |f L (m L)| = |(f L (m L) - g (m L)) + g (m L)| := by ring_nf
      _ ≤ |f L (m L) - g (m L)| + |g (m L)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring

end LatticeSystem.Math
