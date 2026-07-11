/-
Conditional absence of long-range order in one dimension, modulo the susceptibility bound
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Assembling the full Falk–Bruch chain — the `O(L)` oscillator-strength bound, the susceptibility
reduction, and the ground-state eigenvalue bridge — yields the exact `ε`–`δ` statement of Corollary
4.3 *modulo a single reflection-positivity hypothesis*: if the staggered static susceptibility of
every ground state is `O(L)`, then the squared staggered order parameter per site vanishes in the
thermodynamic limit, `lim_{L↑∞} ⟨Φ_GS|(Ô_L/L)²|Φ_GS⟩ = 0`.  This isolates the remaining work for the
unconditional Corollary 4.3 to the susceptibility bound `Re⟨y, ÔΦ⟩ ≤ C·L` (the DLS infrared bound).
-/
import LatticeSystem.Quantum.SpinS.StaggeredOrderSusceptibility
import LatticeSystem.Quantum.SpinS.HermitianGroundStateEigenvalue

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- Hermiticity of the zero-field ring Heisenberg Hamiltonian. -/
private theorem ringHeisenberg_isHermitian (L N : ℕ) :
    (heisenbergHamiltonianS (ringCoupling L) N).IsHermitian :=
  heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N

/-- **Conditional Corollary 4.3 (absence of long-range order in one dimension), modulo the
susceptibility bound.**  Suppose the staggered static susceptibility of every normalized ground
state of the zero-field **even** ring is `O(L)`: there is `C ≥ 0` such that for every even `L ≥ 2`
and every
normalized
ground state `Φ` (eigenvalue `hermitianMinEigenvalue`) there is a potential `y` for `ÔΦ`
(`(Ĥ − E₀) y = ÔΦ`) with `Re⟨y, ÔΦ⟩ ≤ C·L`.  Then the squared staggered order parameter per site
vanishes in the thermodynamic limit: for every `ε > 0` there is `L₀` beyond which every normalized
ground state of an even ring `L ≥ L₀` has `|⟨Φ, Ô² Φ⟩.re / L²| < ε`.  The `Even L` guard is
essential: only bipartite (even) rings carry a balanced staggered sublattice, so `ÔΦ ⊥ Φ` and the
resolvent potential `y` exists; odd rings are non-bipartite and lie outside Tasaki's §4.1
setting. -/
theorem no_long_range_order_1d_of_susceptibility (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 0 ≤ C)
    (hsusc : ∀ L : ℕ, 2 ≤ L → Even L → ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
      (heisenbergHamiltonianS (ringCoupling L) N).mulVec Φ
          = (hermitianMinEigenvalue (ringHeisenberg_isHermitian L N) : ℂ) • Φ →
      ∃ y : (Fin L → Fin (N + 1)) → ℂ,
        (heisenbergHamiltonianS (ringCoupling L) N
            - (hermitianMinEigenvalue (ringHeisenberg_isHermitian L N) : ℂ)
              • (1 : ManyBodyOpS (Fin L) N)).mulVec y
          = (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ
        ∧ (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re ≤ C * (L : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)|
          < ε := by
  intro ε hε
  -- Archimedean threshold: `m > 6 N³ C / ε²`
  obtain ⟨m, hm⟩ := exists_nat_gt (6 * (N : ℝ) ^ 3 * C / ε ^ 2)
  refine ⟨max m 2, fun L hL hLeven Φ hΦnorm hgs => ?_⟩
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hLm : m ≤ L := le_trans (le_max_left _ _) hL
  haveI : NeZero L := ⟨by omega⟩
  -- zero-field Hamiltonian = the ring Heisenberg Hamiltonian
  have hzero : staggeredFieldChainHamiltonianS L 0 N
      = heisenbergHamiltonianS (ringCoupling L) N := by
    simp [staggeredFieldChainHamiltonianS]
  obtain ⟨E₀, heig, hmin, _⟩ := hgs
  rw [hzero] at heig hmin
  -- ground-state eigenvalue bridge
  have hHeig := groundState_mulVec_eq_hermitianMinEigenvalue (ringHeisenberg_isHermitian L N)
    hΦnorm heig hmin
  -- susceptibility potential
  obtain ⟨y, hy, hχ⟩ := hsusc L hL2 hLeven Φ hΦnorm hHeig
  -- Falk–Bruch + oscillator: `2 (⟨Ô²⟩.re)² ≤ 12 N³ L · χ`
  have hpr68 := staggeredOrder_sq_le_susceptibility L N hL2 hN hΦnorm hHeig hy
  set s := (star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N
      * staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re with hs
  set χ := (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re with hχdef
  -- `s ≥ 0` (= ‖ÔΦ‖²)
  have hs_nonneg : 0 ≤ s := by
    rw [hs, hermitian_dotProduct_shift (staggeredOrderOpS_isHermitian _ N) Φ]
    exact (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  -- positivity of constants and `L`
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hNC : (0 : ℝ) ≤ 6 * (N : ℝ) ^ 3 * C := by positivity
  -- `s² ≤ 6 N³ C L²`
  have hsq : s ^ 2 ≤ 6 * (N : ℝ) ^ 3 * C * (L : ℝ) ^ 2 := by
    have hχL : 12 * (N : ℝ) ^ 3 * (L : ℝ) * χ ≤ 12 * (N : ℝ) ^ 3 * (L : ℝ) * (C * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hχ (by positivity)
    have hB : 12 * (N : ℝ) ^ 3 * (L : ℝ) * (C * (L : ℝ))
        = 2 * (6 * (N : ℝ) ^ 3 * C * (L : ℝ) ^ 2) := by ring
    linarith [hpr68, hχL, hB]
  -- `ε² L² > 6 N³ C` from `L ≥ m > 6 N³ C / ε²`
  have hmL : 6 * (N : ℝ) ^ 3 * C / ε ^ 2 < (L : ℝ) := lt_of_lt_of_le hm (by exact_mod_cast hLm)
  have hεL : 6 * (N : ℝ) ^ 3 * C < ε ^ 2 * (L : ℝ) ^ 2 := by
    have h1 : 6 * (N : ℝ) ^ 3 * C < ε ^ 2 * (L : ℝ) := by
      rw [div_lt_iff₀ (by positivity)] at hmL; nlinarith [hmL]
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
    have hLL : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith [hL1]
    nlinarith [h1, mul_le_mul_of_nonneg_left hLL (sq_nonneg ε)]
  -- conclude `|s / L²| < ε`
  rw [abs_of_nonneg (div_nonneg hs_nonneg (by positivity)), div_lt_iff₀ (by positivity)]
  have hstep : 6 * (N : ℝ) ^ 3 * C * (L : ℝ) ^ 2 < ε ^ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hεL (by positivity)
  have hub : s ^ 2 < (ε * (L : ℝ) ^ 2) ^ 2 := by nlinarith [hsq, hstep]
  have hεpos : 0 < ε * (L : ℝ) ^ 2 := by positivity
  nlinarith [hub, hs_nonneg, hεpos]

end LatticeSystem.Quantum
