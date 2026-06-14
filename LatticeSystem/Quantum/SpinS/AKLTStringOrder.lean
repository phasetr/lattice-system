import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.AndersonTower
import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrder

/-!
# Tasaki §7.2.1: hidden antiferromagnetic order and the string order parameter

The AKLT VBS ground state has no Néel order, yet it carries a subtle **hidden antiferromagnetic
order**: if one deletes the `0`'s (the `Ŝ^z = 0` sites) from a typical spin configuration, the
remaining `+`'s and `−`'s alternate perfectly.  Den Nijs and Rommelse measured this through the
**string order parameter** (eqs. (7.2.6)–(7.2.7))
`S^{(3)}_{x,y}(Φ) := −⟨Φ| Ŝ_x^{(3)} exp(iπ Σ_{x<z<y} Ŝ_z^{(3)}) Ŝ_y^{(3)} |Φ⟩`,
`O_string^{(3)}(Φ) := −lim_{y−x↑∞} lim_{L↑∞} S^{(3)}_{x,y}(Φ)`,
where the *string* `exp(iπ Ŝ_z^{(3)})` of phase operators sits between `x` and `y`.  The two leading
minus signs cancel, so `O_string^{(3)}(Φ) = lim lim ⟨Φ| Ŝ_x^{(3)} exp(iπ Σ Ŝ^{(3)}) Ŝ_y^{(3)} |Φ⟩`.

For the VBS state the string order parameter is **positive** — explicitly (eq. (7.2.8))
`O_string^{(1)}(Φ_VBS) = O_string^{(2)}(Φ_VBS) = O_string^{(3)}(Φ_VBS) = 4/9 > 0`
(equal across the three directions by SU(2) invariance), while `O_Néel(Φ_VBS) = 0`.  This is the
hallmark of the Haldane phase.

The string phase operator, the string operator, and the finite-volume string correlation are
*defined* here (concretely; for `S = 1` the phase `exp(iπ Ŝ^z)` is the diagonal `diag(−1, 1, −1)`).
The thermodynamic double limit and the explicit value `4/9` rest on the VBS / matrix-product
construction (not yet formalized); following the project policy they are recorded as a documented
axiom, with the VBS ground-state family carried by the uninterpreted marker
`IsAKLTVBSGroundStateFamily`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.1, eqs. (7.2.6)–(7.2.8), pp. 192–194; M. den Nijs, K. Rommelse, Phys. Rev. B **40**,
4709 (1989).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The single-site **string phase operator** `exp(iπ Ŝ^{(3)})` for an `S = 1` spin: the diagonal
matrix `diag(−1, 1, −1)` on `Fin 3` (z-spin `m = +1, 0, −1` ↦ phase `e^{iπ m} = −1, 1, −1`).  In the
index convention `Ŝ^{(3)} = diag(N/2 − k)` the entry at `k` is `(−1)^{k+1}`, which is `−1, 1, −1`
for `k = 0, 1, 2`. -/
noncomputable def spinSStringPhaseS1 : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun k => (-1 : ℂ) ^ (k.val + 1)

/-- The **string operator** `exp(iπ Σ_{x<z<y} Ŝ_z^{(3)}) = ∏_{x<z<y} exp(iπ Ŝ_z^{(3)})` on the ring
`Fin L`: the product of the single-site string phase operators over the sites strictly between `x`
and `y`.  As each factor is the diagonal `diag(−1, 1, −1)`, the product is the single diagonal
many-body operator acting on a configuration `σ` by the phase `∏_{x<z<y} (−1)^{σ_z + 1}` (the
factors on distinct sites commute, so this unordered diagonal product is well defined). -/
noncomputable def stringOperatorS (x y : Fin L) : ManyBodyOpS (Fin L) 2 :=
  Matrix.diagonal fun σ : Fin L → Fin 3 =>
    ∏ z ∈ Finset.univ.filter fun z : Fin L => x.val < z.val ∧ z.val < y.val,
      (-1 : ℂ) ^ ((σ z).val + 1)

/-- The **finite-volume string correlation** `⟨Φ| Ŝ_x^{(3)} exp(iπ Σ_{x<z<y} Ŝ_z^{(3)}) Ŝ_y^{(3)}
|Φ⟩` (a Rayleigh ratio).  This is `−S^{(3)}_{x,y}(Φ)` in the notation of eq. (7.2.6); with the two
minus signs of eqs. (7.2.6)–(7.2.7), the den Nijs–Rommelse string order parameter is
`O_string^{(3)}(Φ) = lim_{y−x↑∞} lim_{L↑∞}` of this quantity. -/
noncomputable def stringCorrelationS (x y : Fin L) (Φ : (Fin L → Fin 3) → ℂ) : ℝ :=
  expectationRatioRe (spinSSiteOp3 x 2 * stringOperatorS x y * spinSSiteOp3 y 2) Φ

/-- **The AKLT VBS ground-state family marker** `IsAKLTVBSGroundStateFamily Φ`: the family `Φ L` is
the unique valence-bond-solid ground state of the AKLT chain `akltHamiltonianS L` for each ring
length `L`.  A faithful definition needs the explicit VBS / matrix-product construction; it is kept
as an uninterpreted predicate so the string-order axiom applies only to the genuine VBS family. -/
axiom IsAKLTVBSGroundStateFamily (Φ : (L : ℕ) → (Fin L → Fin 3) → ℂ) : Prop

/-- **Tasaki §7.2.1 hidden antiferromagnetic order (eq. (7.2.8)), AXIOM.**  For the AKLT VBS
ground-state family, the den Nijs–Rommelse string order parameter equals `4/9`:
`O_string^{(3)}(Φ_VBS) = lim_{d↑∞} lim_{L↑∞} ⟨Φ_L| Ŝ_x^{(3)} exp(iπ Σ Ŝ^{(3)}) Ŝ_y^{(3)} |Φ_L⟩
= 4/9`,
written in the explicit double-`ε` form (the inner thermodynamic limit `L↑∞` taken before the
separation limit `d = ringDist↑∞`).  Since `4/9 > 0`, the VBS state has **positive string order**,
i.e. hidden antiferromagnetic order in the `3`-direction (and, by SU(2) invariance, in all three
directions); the ordinary Néel order vanishes.  The positivity is the hallmark of the Haldane phase.
The explicit value rests on the VBS / matrix-product computation; recorded as a documented axiom. -/
axiom aklt_string_order_7_2_8
    (Φ : (L : ℕ) → (Fin L → Fin 3) → ℂ) (hΦ : IsAKLTVBSGroundStateFamily Φ) :
    ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ x y : Fin L, ringDist L x y = d → |stringCorrelationS x y (Φ L) - 4 / 9| < ε

end LatticeSystem.Quantum
