import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrder
import Mathlib.Data.Nat.Dist

/-!
# Tasaki §7.1.1: the Affleck–Kennedy–Lieb–Tasaki model and the main theorem (Theorem 7.1)

The **AKLT model** is the `S = 1` antiferromagnetic quantum spin chain with the Hamiltonian
(eq. (7.1.1))
`Ĥ_AKLT = Σ_x { Ŝ_x · Ŝ_{x+1} + ⅓ (Ŝ_x · Ŝ_{x+1})² }`  (periodic, `Ŝ_{L+1} = Ŝ_1`).
It is antiferromagnetic and `SU(2)` invariant, but the biquadratic term `⅓ (Ŝ_x · Ŝ_{x+1})²` puts it
outside the reach of the Marshall–Lieb–Mattis theorem.  Its ground state — the **valence-bond solid
(VBS) state** `|Φ_VBS⟩` — can be written down explicitly, and the model has a unique gapped ground
state with exponentially decaying correlations, giving strong support to Haldane's picture (though
it is a *different* model from the Heisenberg chain).

**Theorem 7.1** (the AKLT main theorem): for any chain length `L` (even or odd):

* the ground state of `Ĥ_AKLT` is **unique**;
* the **energy gap** above the ground state is at least a positive `L`-independent constant `ΔE₀`
  for all sufficiently large `L`;
* the ground-state **correlation function** decays exponentially with an alternating sign
  (eq. (7.1.2)): `lim_{L↑∞} ⟨Φ_VBS, Ŝ_x · Ŝ_y Φ_VBS⟩ / ⟨Φ_VBS, Φ_VBS⟩ = 4 (−3)^{−|x−y|}`, for
  `|x − y| ≥ 1`.

This is proved in [AKLT 1987] via the explicit VBS state and its matrix-product representation.  The
AKLT Hamiltonian is *defined* here; the main theorem itself is stated and **proved axiom-free** as
the theorem `aklt_theorem_7_1` in the downstream leaf module
`LatticeSystem.Quantum.SpinS.AKLTTheorem71` (it cannot live here because its correlation conjunct is
proved in `AKLTCorrelationDecay.lean`, which imports this module).  The gap is phrased through the
spectral-gap predicate `IsPositiveSpectralGap` of §6.1, and the correlation through the per-chain
ground-state family (sites `x, y ∈ ℕ` fixed, the chain length `L = n + 1 ↑ ∞`, so for large `n` the
sites embed as themselves).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.1, Theorem 7.1, eqs. (7.1.1)–(7.1.2), pp. 177–179; I. Affleck, T. Kennedy, E. Lieb,
H. Tasaki, Phys. Rev. Lett. **59**, 799 (1987) and Commun. Math. Phys. **115**, 477 (1988).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **AKLT Hamiltonian** `Ĥ_AKLT = Σ_x { Ŝ_x · Ŝ_{x+1} + ⅓ (Ŝ_x · Ŝ_{x+1})² }` (eq. (7.1.1)) on
the `S = 1` ring `Fin L` (`N = 2`): the antiferromagnetic Heisenberg chain plus the biquadratic term
`⅓ (Ŝ_x · Ŝ_{x+1})²`, with periodic boundary conditions (via the nearest-neighbor
`ringCoupling`). -/
noncomputable def akltHamiltonianS (L : ℕ) : ManyBodyOpS (Fin L) 2 :=
  ∑ x : Fin L, ∑ y : Fin L, ringCoupling L x y •
    (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2))

/-- The **site `x` on the ring of length `n + 1`**: the residue `x mod (n + 1) ∈ Fin (n + 1)`.  For
`n + 1 > x` it is just `x`; used to embed a fixed `ℕ`-site into the growing chain for the
infinite-volume correlation limit. -/
def chainSite (n x : ℕ) : Fin (n + 1) := ⟨x % (n + 1), Nat.mod_lt x (Nat.succ_pos n)⟩

-- **Tasaki Theorem 7.1 (the AKLT main theorem)** is stated and **proved axiom-free** as the theorem
-- `aklt_theorem_7_1` in `LatticeSystem.Quantum.SpinS.AKLTTheorem71`, which composes the four
-- independently discharged conjuncts: existence + eigenvalue + ground energy + gap
-- (`aklt_knabe_ring_gap`, §7.1.4), uniqueness (`aklt_ring_ground_state_unique`, §7.1.3) and the
-- correlation-function decay (`aklt_correlation_decay`, §7.2.2).  The theorem cannot live here
-- because its correlation conjunct is proved in `AKLTCorrelationDecay.lean`, which imports this
-- module; the consolidation therefore sits in the downstream leaf `AKLTTheorem71.lean`.

end LatticeSystem.Quantum
