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

The hidden-order assumption (8.1.10) is carried by the uninterpreted marker `HasStringLRO` (its
faithful form needs the global normalized string operator, not yet defined).  Theorem 8.2, whose
proof
is the variational/trial-state (Horsch–von der Linden, Koma–Tasaki) argument, is recorded as a
documented axiom; the three low-lying states are exhibited as a linearly independent triple of
eigenvectors with energies within `C_ν / L` of the ground energy.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.2–§8.1.3, Theorem 8.2, eqs. (8.1.9)–(8.1.11), pp. 229–238; T. Koma, H. Tasaki, J. Stat.
Phys. **76**, 745 (1994); M. den Nijs, K. Rommelse, Phys. Rev. B **40**, 4709 (1989).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **open-chain nearest-neighbour coupling** on `Fin L`: `J x y = 1` iff `y = x + 1` (no
periodic wrap-around), so the bonds are `{0,1}, {1,2}, …, {L−2, L−1}` and the two end sites `0` and
`L−1` each have a single neighbour — the open boundary that carries the `S = 1/2` edge spins. -/
def openChainCoupling (L : ℕ) (x y : Fin L) : ℂ :=
  if y.val = x.val + 1 then 1 else 0

/-- The **open-chain anisotropic `S = 1` Hamiltonian** with crystal-field anisotropy `D`: the
open-boundary analogue of `anisotropicChainHamiltonianS`,
`Ĥ_D^open = Σ_{x=0}^{L-2} Ŝ_x·Ŝ_{x+1} + D Σ_x (Ŝ_x^{(3)})²` (eq. (8.1.1) with open boundary).  The
free boundary spins make the edge states of Theorem 8.2 possible. -/
noncomputable def openAnisotropicChainHamiltonianS (L : ℕ) (D : ℝ) : ManyBodyOpS (Fin L) 2 :=
  heisenbergHamiltonianS (openChainCoupling L) 2 +
    (D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2

/-- **Hidden-order (string long-range order) marker** `HasStringLRO L D Φ q`: the ground state `Φ`
of the anisotropic chain `Ĥ_D` exhibits hidden antiferromagnetic order in all three directions,
i.e. the den Nijs–Rommelse bound (8.1.10) `⟨Φ| (Ô_string^{(α)} / L)² |Φ⟩ ≥ q_α` holds for each `α`
with the `L`-independent constants `q_α`.  A faithful definition needs the global normalized string
operator; it is kept as an uninterpreted predicate so Theorem 8.2 assumes only the genuine hidden
order. -/
axiom HasStringLRO (L : ℕ) (D : ℝ) (Φ : (Fin L → Fin 3) → ℂ) (q : Fin 3 → ℝ) : Prop

/-- **Tasaki Theorem 8.2 (hidden order forces edge states), AXIOM.**  Fix the anisotropy `D` and
hidden-order constants `q_α > 0`.  Then there are **`L`-independent** constants `C_ν > 0` such that:
for every `L`, whenever `Φ` is the **unique** ground state of the *open-chain* Hamiltonian
`Ĥ_D^open` at ground energy `E₀` (`IsUniqueChainGroundState`) exhibiting hidden antiferromagnetic
order (`HasStringLRO L D Φ q`, the bound (8.1.10)), there exist **three linearly independent excited
states** `Ψ_ν` (`ν : Fin 3`) with energies `E_ν` satisfying `Ĥ_D^open Ψ_ν = E_ν Ψ_ν` and
`E₀ < E_ν ≤ E₀ + C_ν / L`.  Hidden antiferromagnetic order thus forces a near four-fold degeneracy
of low-lying states — the free `S = 1/2` spins at the two open ends.  The constants `C_ν` are
quantified outside `∀ L`, so the `O(1/L)` splitting is genuinely length-uniform.  Proved by the
Horsch–von der Linden / Koma–Tasaki variational (trial-state) argument, as in Theorem 3.1; recorded
as a documented axiom. -/
axiom tasaki_theorem_8_2 (D : ℝ) (q : Fin 3 → ℝ) (hq : ∀ α : Fin 3, 0 < q α) :
    ∃ C : Fin 3 → ℝ, (∀ ν : Fin 3, 0 < C ν) ∧
      ∀ (L : ℕ) (Φ : (Fin L → Fin 3) → ℂ) (E₀ : ℝ),
        IsUniqueChainGroundState (openAnisotropicChainHamiltonianS L D) E₀ Φ →
        HasStringLRO L D Φ q →
        ∃ (Ψ : Fin 3 → ((Fin L → Fin 3) → ℂ)) (E : Fin 3 → ℝ),
          LinearIndependent ℂ Ψ ∧
            ∀ ν : Fin 3,
              (openAnisotropicChainHamiltonianS L D).mulVec (Ψ ν) = (E ν : ℂ) • Ψ ν ∧
                E₀ < E ν ∧ E ν ≤ E₀ + C ν / (L : ℝ)

end LatticeSystem.Quantum
