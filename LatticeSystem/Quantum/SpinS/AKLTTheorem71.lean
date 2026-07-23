import LatticeSystem.Quantum.SpinS.AKLTUniqueness.GroundStateUnique
import LatticeSystem.Quantum.SpinS.AKLTCorrelationDecay

/-!
# Tasaki §7.1.1: the AKLT main theorem (Theorem 7.1), fully proved

This module is the **final consolidation** of Tasaki Theorem 7.1 (the AKLT main theorem): it
assembles the four assertions of the theorem — each already discharged as an independent theorem —
into a single statement `aklt_theorem_7_1`, which was previously recorded as a documented axiom
in `AKLT.lean`.  The proof is a pure composition of the three suppliers, so no new axiom is added:

* **existence, eigenvalue, ground energy, and gap** (conjuncts 1, 2, 3, 5) come from
  `AKLTExactCertificateSector234Sequential.aklt_knabe_ring_gap` (§7.1.4, Knabe's argument, `L ≥ 5`);
* **uniqueness** (conjunct 4) comes from `aklt_ring_ground_state_unique` (§7.1.3, `L ≥ 3`);
* **exponential correlation decay** (conjunct 6, eq. (7.1.2)) comes from `aklt_correlation_decay`
  (§7.2.2).

The witnesses are `ΔE₀ = 1/5` (the uniform Knabe gap), the valence-bond-solid family
`Φ n = akltVBSState (n + 1)` shared by all three suppliers, the ground energy
`E₀ n = −(2/3)(n + 1)`, and the threshold `n₀ = max nK 2` (`nK = 4` is Knabe's threshold, `2` is the
uniqueness threshold).  With this module the documented axiom `aklt_theorem_7_1` is retired and
Theorem 7.1 is **axiom-free** (`#print axioms aklt_theorem_7_1` = Standard 3).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.1, Theorem 7.1, eqs. (7.1.1)–(7.1.2), pp. 177–179; I. Affleck, T. Kennedy, E. Lieb,
H. Tasaki, Phys. Rev. Lett. **59**, 799 (1987) and Commun. Math. Phys. **115**, 477 (1988).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Tasaki Theorem 7.1 (the AKLT main theorem), PROVED (axiom-free).**  The `S = 1` AKLT chain
`Ĥ_AKLT` (eq. (7.1.1)) has, for all sufficiently large chains, a **unique ground state** `Φ` (a
nonzero eigenvector at the ground energy `E₀`, with every ground eigenvector a scalar multiple of
`Φ`); a **spectral gap** bounded below by a positive `L`-independent constant `ΔE₀`
(`ΔE₀ ≤ gap`, with `IsPositiveSpectralGap`); and an **exponentially decaying, sign-alternating
correlation function** (eq. (7.1.2)): for any fixed sites `x, y` with `|x − y| ≥ 1`,
`⟨Φ, Ŝ_x · Ŝ_y Φ⟩ / ⟨Φ, Φ⟩ → 4 (−3)^{−|x − y|}` as the chain length `L = n + 1 ↑ ∞` (stated in the
sound eventual-`ε` form, with the fixed `ℕ`-sites embedded by `chainSite`).

The constant `ΔE₀ = 1/5` and the valence-bond-solid family `Φ n = akltVBSState (n + 1)` are
quantified outermost, so `ΔE₀` is genuinely `L`-independent and the same `Φ` carries both the gap
and the correlation.  No parity restriction on `L`.  Formerly a documented axiom (`AKLT.lean`); now
proved by
composing `aklt_knabe_ring_gap` (existence + eigenvalue + ground energy + gap, §7.1.4),
`aklt_ring_ground_state_unique` (uniqueness, §7.1.3) and `aklt_correlation_decay` (correlation,
§7.2.2). -/
theorem aklt_theorem_7_1 :
    ∃ (ΔE₀ : ℝ) (Φ : (n : ℕ) → (Fin (n + 1) → Fin 3) → ℂ) (E₀ : ℕ → ℝ),
      0 < ΔE₀ ∧ ∃ n₀ : ℕ,
        (∀ n : ℕ, n₀ ≤ n →
          Φ n ≠ 0 ∧
          (akltHamiltonianS (n + 1)).mulVec (Φ n) = (E₀ n : ℂ) • Φ n ∧
          IsGroundEnergy (akltHamiltonianS (n + 1)) (E₀ n) ∧
          (∀ Ψ : (Fin (n + 1) → Fin 3) → ℂ, Ψ ≠ 0 →
            (akltHamiltonianS (n + 1)).mulVec Ψ = (E₀ n : ℂ) • Ψ → ∃ c : ℂ, Ψ = c • Φ n) ∧
          ∃ gap : ℝ, ΔE₀ ≤ gap ∧ IsPositiveSpectralGap (akltHamiltonianS (n + 1)) gap) ∧
        ∀ (x y : ℕ), 1 ≤ Nat.dist x y → ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
          |expectationRatioRe (spinSDot (chainSite n x) (chainSite n y) 2) (Φ n)
            - (4 : ℝ) * (-3 : ℝ) ^ (-(Nat.dist x y : ℤ))| < ε := by
  obtain ⟨nK, hK⟩ := AKLTExactCertificateSector234Sequential.aklt_knabe_ring_gap
  refine ⟨1 / 5, fun n => akltVBSState (n + 1), fun n => -(2 : ℝ) / 3 * ((n : ℝ) + 1),
    by norm_num, max nK 2, ?_, aklt_correlation_decay⟩
  intro n hn
  have hnK : nK ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hne, heig, hgrd, hgap⟩ := hK n hnK
  exact ⟨hne, heig, hgrd,
    fun Ψ hΨ0 hev => aklt_ring_ground_state_unique n hn2 Ψ hΨ0 hev, hgap⟩

end LatticeSystem.Quantum
