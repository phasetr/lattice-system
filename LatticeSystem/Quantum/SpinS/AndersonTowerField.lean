import LatticeSystem.Quantum.SpinS.AndersonTower

/-!
# Tasaki §4.2: spontaneous symmetry breaking under an infinitesimal staggered field (Theorem 4.13)

Adding an infinitesimal staggered magnetic field `−h Ô_L^{(1)}` to the antiferromagnetic Heisenberg
Hamiltonian triggers spontaneous symmetry breaking.  With the field Hamiltonian (eq. (4.2.27))
`Ĥ_h = Ĥ − h Ô_L^{(1)}` and its ground state `Φ_GS,h`, Theorem 4.13 (eq. (4.2.28)) states
`lim_{h↓0} liminf_{L↑∞} ⟨Φ_GS,h| Ô_L^{(1)}/L^d |Φ_GS,h⟩ ≥ m∗`,
so the staggered moment per site survives the `L↑∞` then `h↓0` limits — symmetry breaking.  Combined
with Theorem 4.11 (`m∗ ≥ √(3 q₀)`) this gives a strictly positive order parameter.

We record it as a documented axiom over the torus family, following the established design (codex):
the double limit is stated in explicit `ε`–`δ` form with the *inner* threshold `L₀` depending on the
field `h` (outer `h↓0`, inner `liminf_L`); the field ground states `Φ_GS,h` are a *given* family
(eigenvector + minimizer of `Ĥ_h`, nonzero — not chosen by definition, since they need not be
unique); `m∗` is the genuine order parameter, pinned by a realizing unperturbed ground state
(`IsTanakaFullSSBConstants` + exact LRO/SSB limits, as in Theorem 4.11), which is unsatisfiable in
`d = 1` (no LRO, Corollary 4.3), so the statement is vacuous there.  The matching `m∗ ≥ √(3 q₀)` is
left to Theorem 4.11 (`tanakaSSB_orderParameter_lowerBound`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1, Theorem 4.13, eqs. (4.2.27)–(4.2.28), pp. 102–103 (footnote 26: rigorously `liminf`).
-/

namespace LatticeSystem.Quantum

open Matrix Filter

variable {N : ℕ}

/-- The **staggered-field Hamiltonian** `Ĥ_h = Ĥ − h Ô_L^{(1)}` (eq. (4.2.27)) on the
`d`-dimensional
hypercubic torus: the antiferromagnetic nearest-neighbor Heisenberg Hamiltonian minus an external
staggered field `h ≥ 0` coupled to the `1`-axis staggered order operator. -/
noncomputable def staggeredFieldHamiltonianS (d L N : ℕ) [NeZero L] (h : ℝ) :
    ManyBodyOpS (HypercubicTorus d L) N :=
  heisenbergHamiltonianS (torusNNCoupling d L) N -
    (h : ℂ) • staggeredOrderOp1S (torusParitySublattice d L) N

/-- **Tasaki Theorem 4.13 (SSB under an infinitesimal staggered field), AXIOM.**  For the
staggered-field Hamiltonian `Ĥ_h = Ĥ − h Ô_L^{(1)}`, the per-site staggered moment of the
field ground state survives the iterated limit `lim_{h↓0} liminf_{L↑∞}` and is bounded below by the
SSB order parameter `m∗` (eq. (4.2.28)): for every `ε > 0` there is a field threshold `δ > 0` such
that for each `0 < h < δ` there is a size threshold `L₀` (depending on `h`) beyond which every
even-side field ground state `Φ_GS,h,L` has `m∗ − ε ≤ ⟨Φ_GS,h,L, Ô_L^{(1)} Φ_GS,h,L⟩.re / L^d`.

`m∗` is the genuine order parameter, pinned (as in Theorem 4.11) by a realizing *unperturbed* ground
state family `Φ₀` and slow tower `M` (`hFamily : IsRealizingTanakaGroundStateFamily …`: exact LRO
and
staggered-moment limits plus `IsTanakaFullSSBConstants`) — these are unsatisfiable in `d = 1` (no
LRO
ground state, Corollary 4.3), so the statement is vacuous there.
The field ground states `Φ_GS,h` are a *given* family of eigenvector/minimizer/nonzero states of
`Ĥ_h` (`hField`).  Combined with Theorem 4.11, this yields `≥ m∗ ≥ √(3 q₀) > 0`. -/
axiom tanakaSSB_field_lowerBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ₀ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ₀ E₀ M)
    (PhiGS : ℝ → (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (EField : ℝ → ℕ → ℂ)
    (hField : ∀ h : ℝ, 0 < h → ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (staggeredFieldHamiltonianS d L N h).mulVec (PhiGS h L) = EField h L • PhiGS h L ∧
      (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (staggeredFieldHamiltonianS d L N h).mulVec Ψ = E • Ψ → (EField h L).re ≤ E.re) ∧
      PhiGS h L ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        mStar - ε ≤
          expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) N) (PhiGS h L) /
            (L : ℝ) ^ d

end LatticeSystem.Quantum
