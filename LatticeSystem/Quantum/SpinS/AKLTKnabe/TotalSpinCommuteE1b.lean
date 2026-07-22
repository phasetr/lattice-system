import LatticeSystem.Quantum.SpinS.AKLTKnabe.SiteBlockEmbeddingD5b
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Gate E1b: the AKLT window commutes with the total raising operator

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) is the **minimal
experiment** of the `sl₂`-ladder route to the Knabe window inequality
`ĥ² ≥ (2/5) ĥ` (design note `aklt-theorem-7-1-e1a-general-window-bound-design.md`, §(h)):
the open three-bond window

  `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃`  on `(ℂ³)^{⊗4}`  (Tasaki eq. (7.1.30) with `ℓ = 3`, p. 189)

is `SU(2)`-invariant, i.e. it commutes with the total raising operator `Ŝ⁺_tot`.  This is what
makes the whole dimensional reduction `81 → 1 + 3 + 6 + 6 + 3` possible, because it lets the
highest-weight spaces `ker Ŝ⁺_tot ∩ V_m` be `ĥ`-invariant.

The proof is entirely structural — **no `81 × 81` entry computation occurs anywhere**:

* the bond operator `Ŝ_x · Ŝ_y` commutes with each Cartesian total-spin axis operator
  `Ŝ^{(1)}_tot`, `Ŝ^{(2)}_tot`, by the production lemmas `spinSDot_commutator_totalSpinSOp1` and
  `spinSDot_commutator_totalSpinSOp2` (Tasaki §2.2 eq. (2.2.17) generalised to spin `S`);
* hence it commutes with `Ŝ⁺_tot = Ŝ^{(1)}_tot + i Ŝ^{(2)}_tot` (`totalSpinSOpPlus_eq_add`);
* hence so does the bond projection `P̂_{x,y} = ½ (Ŝ_x · Ŝ_y) + ⅙ (Ŝ_x · Ŝ_y)² + ⅓`
  (`bondSpin2ProjectionS`, Tasaki eq. (7.1.6), p. 182), being a polynomial in it;
* hence so does the three-term sum `ĥ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2 eq. (2.2.17) p. 24, §7.1.3 eq. (7.1.6) p. 182, §7.1.4 eq. (7.1.30) p. 189;
S. Knabe, *J. Stat. Phys.* **52**, 627–638 (1988).
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open LatticeSystem.Quantum

section Bond

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **`SU(2)` invariance of a single bond operator against the total raising operator**:
`[Ŝ_x · Ŝ_y, Ŝ⁺_tot] = 0`.  Obtained from the two Cartesian-axis commutator identities
`spinSDot_commutator_totalSpinSOp1` / `spinSDot_commutator_totalSpinSOp2` (Tasaki §2.2
eq. (2.2.17), p. 24, in its spin-`S` form) through the decomposition
`Ŝ⁺_tot = Ŝ^{(1)}_tot + i Ŝ^{(2)}_tot`. -/
theorem spinSDot_commute_totalSpinSOpPlus (x y : Λ) (N : ℕ) :
    Commute (spinSDot x y N) (totalSpinSOpPlus Λ N) := by
  have h1 : Commute (spinSDot x y N) (totalSpinSOp1 Λ N) := by
    unfold Commute SemiconjBy
    exact sub_eq_zero.mp (spinSDot_commutator_totalSpinSOp1 x y N)
  have h2 : Commute (spinSDot x y N) (totalSpinSOp2 Λ N) := by
    unfold Commute SemiconjBy
    exact sub_eq_zero.mp (spinSDot_commutator_totalSpinSOp2 x y N)
  rw [totalSpinSOpPlus_eq_add]
  exact h1.add_right (h2.smul_right Complex.I)

end Bond

/-- **`SU(2)` invariance of the AKLT bond projection**: `[P̂_{x,y}, Ŝ⁺_tot] = 0` for any two sites
of a spin-1 chain.  The projection is the polynomial `½ D + ⅙ D² + ⅓` in the bond operator
`D = Ŝ_x · Ŝ_y` (Tasaki eq. (7.1.6), p. 182), so this follows term by term from
`spinSDot_commute_totalSpinSOpPlus`. -/
theorem bondSpin2ProjectionS_commute_totalSpinSOpPlus {L : ℕ} (x y : Fin L) :
    Commute (bondSpin2ProjectionS x y : ManyBodyOpS (Fin L) 2)
      (totalSpinSOpPlus (Fin L) 2) := by
  have h : Commute (spinSDot x y 2 : ManyBodyOpS (Fin L) 2) (totalSpinSOpPlus (Fin L) 2) :=
    spinSDot_commute_totalSpinSOpPlus x y 2
  simp only [bondSpin2ProjectionS]
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact h.smul_left _
  · exact (h.mul_left h).smul_left _
  · exact (Commute.one_left _).smul_left _

/-- **Gate E1: the open three-bond AKLT window commutes with the total raising operator**,
`[ĥ, Ŝ⁺_tot] = 0` with `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` on `(ℂ³)^{⊗4}` (Tasaki eq. (7.1.30) with `ℓ = 3`,
p. 189).

This is the structural fact that replaces the machine-generated `81 × 81` certificate stack: it
says that `ĥ` preserves every highest-weight space `ker Ŝ⁺_tot ∩ V_m`, so the Knabe inequality
`ĥ² ≥ (2/5) ĥ` need only be checked on the five blocks of sizes `1, 3, 6, 6, 3`.  Cross-checked
before formalisation by exact rational arithmetic on the full `81 × 81` matrices, together with
three negative controls (a single-site raising operator, an Ising bond, and a single-site `Ŝ^z`
all fail to commute). -/
theorem akltWindow3H_commute_totalSpinSOpPlus :
    Commute akltWindow3H (totalSpinSOpPlus (Fin 4) 2) := by
  simp only [akltWindow3H]
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact bondSpin2ProjectionS_commute_totalSpinSOpPlus _ _
  · exact bondSpin2ProjectionS_commute_totalSpinSOpPlus _ _
  · exact bondSpin2ProjectionS_commute_totalSpinSOpPlus _ _

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
