import LatticeSystem.Quantum.SpinS.AnisotropicLargeD

/-!
# Tasaki §8.1.2–§8.1.3: hidden antiferromagnetic order and edge states (Theorem 8.2)

The **Haldane phase** of the anisotropic `S = 1` chain (8.1.1) is distinguished from the large-`D`
phase by **hidden antiferromagnetic order**, measured by the den Nijs–Rommelse string order
parameter
`O_string^{(α)}(D)` (§7.2.1) of its ground state.  It is conjectured that `O_string^{(α)}(D) > 0`
for
`0 ≤ D < D_c` (Haldane phase) and `= 0` for `D > D_c` (large-`D` phase), so the string order
parameter
is the order parameter separating the two phases.  The positivity in the Haldane phase is the
**hidden-order assumption** (8.1.10): for sufficiently large `L`,
`⟨Φ_GS| (Ô_string^{(α)} / L)² |Φ_GS⟩ ≥ q_α`  with `L`-independent `q_α > 0`.

Koma and Tasaki then proved, exactly as in the tower-of-states argument of Theorem 3.1
(Horsch–von der Linden), that hidden order forces low-lying excitations — the **edge states**:

**Theorem 8.2**: for the *open* anisotropic chain, assume the hidden-order bound (8.1.10) for the
unique ground state.  Then there exist **three independent excited states** `|Ψ_ν⟩` (`ν = 1, 2, 3`)
whose energies satisfy `E_GS < E_ν ≤ E_GS + C_ν / L` with `L`-independent constants `C_ν`.  Thus
hidden antiferromagnetic order forces a near four-fold degeneracy of low-lying states (the free
`S = 1/2` edge spins of the open chain).  Edge states are an open-boundary phenomenon, so the
theorem uses the open-chain Hamiltonian `openAnisotropicChainHamiltonianS`.

The hidden-order assumption (8.1.10) is now carried by the **concrete** ratio-form marker
`HasStringLRO`, built from the genuine global prefix-string operator `edgeStringOrderOpS`
(§7.3.1-style per-site half-turn phase composed as a left prefix, not the two-endpoint window of
`AKLTStringOrderDefs`).  Theorem 8.2 is stated (RED state: proof body is `sorry`, see the PR-1
Red/TDD gate) with the source-faithful quantifier order confirmed by the design round recorded in
`.self-local/active/issue-4718.md`: eventual threshold `L0 = 1`, `L`-independent constants `C_ν`,
and three nonzero linearly independent excited eigenvectors with `O(1/L)` energy bounds above the
**unique** ground energy.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.2–§8.1.3, Theorem 8.2, eqs. (8.1.8)–(8.1.12), pp. 236–238; T. Koma, H. Tasaki, J. Stat.
Phys. **76**, 745 (1994); M. den Nijs, K. Rommelse, Phys. Rev. B **40**, 4709 (1989).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **open-chain nearest-neighbour coupling** on `Fin L`: `J x y = 1` iff `y = x + 1` (directed,
no periodic wrap-around), so the bonds are `{0,1}, {1,2}, …, {L−2, L−1}` (each counted once) and the
two end sites `0` and `L−1` each have a single neighbour — the open boundary that carries the
`S = 1/2` edge spins. -/
def openAnisotropicChainCoupling (L : ℕ) (x y : Fin L) : ℂ :=
  if y.val = x.val + 1 then 1 else 0

/-- The **open-chain anisotropic `S = 1` Hamiltonian** with crystal-field anisotropy `D`: the
open-boundary analogue of `anisotropicChainHamiltonianS`,
`Ĥ_D^open = Σ_{x=0}^{L-2} Ŝ_x·Ŝ_{x+1} + D Σ_x (Ŝ_x^{(3)})²` (eq. (8.1.1) with open boundary).  The
free boundary spins make the edge states of Theorem 8.2 possible. -/
noncomputable def openAnisotropicChainHamiltonianS (L : ℕ) (D : ℝ) : ManyBodyOpS (Fin L) 2 :=
  heisenbergHamiltonianS (openAnisotropicChainCoupling L) 2 +
    (D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2

/-- **The per-site spin-one half turn** `u_α = exp(i π Ŝ^{(α)}) = 1 - 2 (Ŝ^{(α)})²`, the closed form
valid because `(Ŝ^{(α)})³ = Ŝ^{(α)}` at `S = 1` (Tasaki (2.1.21)/(2.1.23), pp. 17–18; footnote 11,
p. 237, records that the `S = 1` restriction is essential for this closed form).  This is a
provisional Red-state placement in the model-definitions file; per the active record's file
boundaries it belongs in a new shared module `LatticeSystem/Quantum/SpinS/SpinOneHalfTurn.lean`
(M1a), to be moved there at the implementation gate.  Its axis-`3` value overlaps definitionally
with the existing `spinSStringPhaseS1` (`AKLTStringOrderDefs.lean:41`); this overlap is disclosed
here and will be disclosed again in the PR body per the design record. -/
noncomputable def spinOneHalfTurnS (alpha : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  1 - (2 : ℂ) • (![spinSOp1 2, spinSOp2 2, spinSOp3 2] alpha) ^ 2

/-- **The prefix rotation** `R^{(α)}_{<m} = ∏_{y < m} u_α^{(y)}`, the product of half turns over the
sites strictly left of `m`.  Indexed by `m : ℕ` (not `x : Fin L`) so the single declaration also
serves the support-count argument, which compares `m ≤ z` and `z + 2 ≤ m`.  Provisional Red-state
placement; belongs in `AnisotropicEdgeStringOrder.lean` per the file boundaries. -/
noncomputable def edgeStringPrefixRotationS
    (L : ℕ) (alpha : Fin 3) (m : ℕ) : ManyBodyOpS (Fin L) 2 :=
  (List.ofFn fun y : Fin L =>
    if y.val < m then onSiteS y (spinOneHalfTurnS alpha) else 1).prod

/-- **The global edge-string order operator** `Ô^{(α)}_string = Σ_x Ŝ^{(α)}_x R^{(α)}_{<x}`
(the (8.1.8)-faithful left-prefix string, distinct from `AKLTStringOrderDefs`'s two-endpoint window
string).  Provisional Red-state placement; belongs in `AnisotropicEdgeStringOrder.lean`. -/
noncomputable def edgeStringOrderOpS
    (L : ℕ) (alpha : Fin 3) : ManyBodyOpS (Fin L) 2 :=
  ∑ x : Fin L, spinSSiteComponentS alpha x * edgeStringPrefixRotationS L alpha x.val

/-- **Hidden-order (string long-range order) marker** `HasStringLRO L Φ q`, the concrete
ratio-form (8.1.10) bound: for every axis `α`, the normalized Rayleigh expectation of
`(Ô^{(α)}_string / L)²` at the state `Φ` is at least `q_α`.  Replaces the former uninterpreted
marker `HasStringLRO L D Φ q`; `D` is deliberately absent, since the ratio form is the (8.1.10)
definition itself and not a `D`-dependent hypothesis. -/
def HasStringLRO (L : ℕ) (Phi : (Fin L → Fin 3) → ℂ)
    (q : Fin 3 → ℝ) : Prop :=
  ∀ alpha : Fin 3, q alpha ≤ expectationRatioRe
    (((((L : ℂ)⁻¹) • edgeStringOrderOpS L alpha) ^ 2)) Phi

/-- **Tasaki Theorem 8.2 (hidden order forces edge states).**  Fix the anisotropy `D ≥ 0` and hidden
-order constants `q_α > 0`.  Then there is an eventual threshold `L0` and **`L`-independent**
constants `C_ν > 0` such that: for every `L ≥ L0`, whenever `Φ` is the **unique** ground state of the
*open-chain* Hamiltonian `Ĥ_D^open` at ground energy `E₀` (`IsUniqueChainGroundState`) exhibiting
hidden antiferromagnetic order (`HasStringLRO L Φ q`, the bound (8.1.10)), there exist **three
nonzero, mutually linearly independent excited states** `Ψ_ν` (`ν : Fin 3`) with energies `E_ν`
satisfying `Ĥ_D^open Ψ_ν = E_ν Ψ_ν` and `E₀ < E_ν ≤ E₀ + C_ν / L`.  Hidden antiferromagnetic order
thus forces a near four-fold degeneracy of low-lying states — the free `S = 1/2` spins at the two
open ends.  The constants `C_ν` are quantified outside `∀ L`, so the `O(1/L)` splitting is genuinely
length-uniform.  Proved by the Horsch–von der Linden / Koma–Tasaki variational (trial-state)
argument, as in Theorem 3.1.  **RED STATE (PR-1 Red/TDD gate): the proof body is `sorry` pending the
implementation gate**; only the statement shape is authorized at this step. -/
theorem tasaki_theorem_8_2
    (D : ℝ) (hD : 0 ≤ D) (q : Fin 3 → ℝ) (hq : ∀ alpha : Fin 3, 0 < q alpha) :
    ∃ L0 : ℕ, ∃ C : Fin 3 → ℝ,
      (∀ nu : Fin 3, 0 < C nu) ∧
      ∀ L : ℕ, L0 ≤ L →
        ∀ (E0 : ℝ) (Phi : (Fin L → Fin 3) → ℂ),
          IsUniqueChainGroundState (openAnisotropicChainHamiltonianS L D) E0 Phi →
          HasStringLRO L Phi q →
          ∃ (E : Fin 3 → ℝ) (Psi : Fin 3 → ((Fin L → Fin 3) → ℂ)),
            LinearIndependent ℂ Psi ∧
            ∀ nu : Fin 3,
              Psi nu ≠ 0 ∧
              (openAnisotropicChainHamiltonianS L D).mulVec (Psi nu) = (E nu : ℂ) • Psi nu ∧
              E0 < E nu ∧ E nu ≤ E0 + C nu / (L : ℝ) := by
  sorry

end LatticeSystem.Quantum
