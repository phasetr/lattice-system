import LatticeSystem.Quantum.SpinS.AndersonTowerField
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaCapstone

/-!
# Tasaki §4.2.2 Theorem 4.13 — realizing-family trial-energy input (axiom-free)

This module hosts the **trial-energy input** to Tasaki's Theorem 4.13 variational argument,
`tanakaSSB_realizingFamily_energyBound`, **proved** (no companion axiom): for a realizing Tanaka
ground-state family (`IsRealizingTanakaGroundStateFamily`) the Tanaka symmetry-breaking state
`Ξ = tanakaSSBState A N (M L) (Φ L)` obeys the Rayleigh-ratio bound
`⟨Ξ, Ĥ Ξ⟩ / ⟨Ξ, Ξ⟩ ≤ (E₀ L).re + C₂ (M(L) + 1)² / L^d` eventually
(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer, 2020,
Theorem 4.8, eq. (4.2.11), p. 98).

The bound is **derived from the already-proved Theorem 4.8**
(`tanakaSSB_lowLying_energy_bound`, `IsTanakaSSBConstants`), not axiomatized.  The key is the
`o(L^{d/2})` slow-divergence conjunct of `IsRealizingTanakaGroundStateFamily`: obtaining Theorem
4.8's constants `C₁_E, C₂_E` first and *then* instantiating that conjunct at `c := C₁_E` supplies
the Theorem 4.8 growth **gate** `M(L) + 1 ≤ C₁_E L^{d/2}` for the specific existential `C₁_E`
Theorem 4.8 fixes.  The long-range-order limit conjunct at `ε := q₀/2` supplies the per-`L` LRO
premise `q₀/2 ≤ ⟨Φ, ô² Φ⟩ / (⟨Φ,Φ⟩ V²)` (running Theorem 4.8 at `q₀' = q₀/2`); the remaining
Theorem 4.8 hypotheses (eigenvector, minimizer, `Φ ≠ 0`, singlet `Ŝ³Φ = Ŝ¹Φ = 0`, `0 < M L`,
tower positivity) are verbatim family block conjuncts.

`#print axioms tanakaSSB_realizingFamily_energyBound` therefore lists only the standard three
(`propext`, `Classical.choice`, `Quot.sound`).  This companion is consumed by Theorem 4.13
(`tanakaSSB_field_lowerBound`); together with Theorem 4.11 (`√(3 q₀) ≤ m∗`) it yields the
`m∗ ≥ √(3 q₀) > 0` conclusion.  The family is unsatisfiable in `d = 1` (no long-range order,
Corollary 4.3), so the bound applies exactly where it should.

Reference: Hal Tasaki, §4.2.2, Theorem 4.8, eq. (4.2.11), p. 98; Theorem 4.9, footnote 21, p. 98;
Lemma 4.16, pp. 108–109.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Tasaki Theorem 4.8 trial-energy input for a realizing family, PROVED (axiom-free).**  For a
realizing Tanaka ground-state family (`hFamily : IsRealizingTanakaGroundStateFamily
d N q₀ mStar C₁ Φ E₀ M`), there is a constant `C₂ > 0` and a threshold `L₀` beyond which every
even-side torus obeys the Tanaka symmetry-breaking trial-energy bound (eq. (4.2.11), p. 98)
`⟨Ξ, Ĥ Ξ⟩ / ⟨Ξ, Ξ⟩ ≤ (E₀ L).re + C₂ (M(L) + 1)² / L^d`, with `Ξ = tanakaSSBState A N (M L) (Φ L)`.

Proof (all axiom-free, given Theorem 4.8 proved).  Run Theorem 4.8
(`tanakaSSB_lowLying_energy_bound`) at `q₀' := q₀/2` to fix `C₁_E, C₂_E` with
`IsTanakaSSBConstants d N (q₀/2) C₁_E C₂_E`; set `C₂ := C₂_E`.  Instantiate the family's
`o(L^{d/2})` slow-divergence conjunct at `c := C₁_E` to get the Theorem 4.8 **gate**
`M(L) + 1 ≤ C₁_E L^{d/2}` eventually, and the long-range-order limit conjunct at `ε := q₀/2` to get
`q₀/2 ≤ ⟨Φ, ô² Φ⟩ / (⟨Φ,Φ⟩ V²)` eventually.  Beyond the max of the three thresholds, feed
`IsTanakaSSBConstants` its verbatim block hypotheses (eigenvector, minimizer, `Φ ≠ 0`, singlet
`Ŝ³Φ = Ŝ¹Φ = 0`, `0 < M L`, tower positivity) together with the gate and the LRO bound; it fires
the trial-energy inequality.

`#print axioms tanakaSSB_realizingFamily_energyBound` = `propext`, `Classical.choice`, `Quot.sound`
only.  This is the companion consumed by Theorem 4.13 (`tanakaSSB_field_lowerBound`); with Theorem
4.11 it yields `m∗ ≥ √(3 q₀) > 0`.  Unsatisfiable in `d = 1` (Corollary 4.3), so vacuous there.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Theorem 4.8, eq. (4.2.11), p. 98; Theorem 4.9, footnote 21, p. 98. -/
theorem tanakaSSB_realizingFamily_energyBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (_hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      (star (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) ⬝ᵥ
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
            (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L))).re /
        (star (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) ⬝ᵥ
          tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)).re ≤
      (E₀ L).re + C₂ * ((M L : ℝ) + 1) ^ 2 / (L : ℝ) ^ d := by
  -- Theorem 4.8 at `q₀/2` fixes the constants `C₁_E`, `C₂_E`.
  obtain ⟨C₁_E, C₂_E, _hAnd, hSSB⟩ :=
    tanakaSSB_lowLying_energy_bound d N hd (q₀ / 2) (by positivity)
  -- Family per-`L` block, `o(L^{d/2})` growth (at `c := C₁_E`), and LRO limit (at `ε := q₀/2`).
  obtain ⟨L₁_block, hblock⟩ := hFamily.2.1
  obtain ⟨L_gate, hgate⟩ := hFamily.2.2.2.2.2 C₁_E hSSB.1
  obtain ⟨L_lro, hlro⟩ := hFamily.2.2.1 (q₀ / 2) (by positivity)
  refine ⟨C₂_E, hSSB.2.1, max (max L₁_block L_gate) L_lro, fun L _ hL h2 hev => ?_⟩
  have hLb : L₁_block ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLg : L_gate ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLl : L_lro ≤ L := le_trans (le_max_right _ _) hL
  -- Verbatim block conjuncts (reversal `_hrev` and the `O`-form growth `_hMO` are unused here).
  obtain ⟨hev0, hmin, hne, hs3, hs1, _hrev, hMpos, _hMO, htw1, htw2, hst⟩ :=
    hblock L hLb h2 hev
  -- LRO limit ⟹ `q₀/2 ≤` ratio (the Theorem 4.8 per-`L` LRO premise at `q₀' = q₀/2`).
  have hlroL := hlro L hLl h2 hev
  rw [abs_lt] at hlroL
  have hq2 : q₀ / 2 ≤ (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
      staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
      ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) := by linarith [hlroL.1]
  -- Feed Theorem 4.8 (`IsTanakaSSBConstants`) its hypotheses; the gate is `hgate L …`.
  exact hSSB.2.2 L h2 hev (Φ L) (E₀ L) (M L) hev0 hmin hne hs3 hs1 hq2 hMpos
    (hgate L hLg h2 hev) htw1 htw2 hst

end LatticeSystem.Quantum
