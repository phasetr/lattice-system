import LatticeSystem.Quantum.SpinS.AKLT

/-!
# Tasaki §7.1.3: the bond spin-2 projection and the local VBS characterization (Lemma 7.4)

The AKLT interaction is built from the **bond projection onto total spin 2**.  For two `S = 1`
spins, `P̂₂[Ŝ_x + Ŝ_{x+1}]` projects onto the (5-dimensional) total-spin-2 subspace; the AKLT local
term is its affine image (eq. (7.1.5))
`Ŝ_x · Ŝ_{x+1} + ⅓ (Ŝ_x · Ŝ_{x+1})² = 2 P̂₂[Ŝ_x + Ŝ_{x+1}] − ⅔`,
so the AKLT Hamiltonian penalizes only the spin-2 component of each bond, and its ground states are
exactly the states annihilated by every bond projection `P̂₂`.  Inverting the identity gives the
projection as a polynomial in `Ŝ_x · Ŝ_{x+1}`:
`P̂₂[Ŝ_x + Ŝ_{x+1}] = ½ (Ŝ_x · Ŝ_{x+1}) + ⅙ (Ŝ_x · Ŝ_{x+1})² + ⅓`.

**Lemma 7.4** (eqs. (7.1.19)–(7.1.20)): a state `|Φ⟩` of the `S = 1` chain satisfies
`P̂₂[Ŝ_x + Ŝ_{x+1}] |Φ⟩ = 0` if and only if it has the **valence-bond-solid singlet-tensor form**
(7.1.20) — built (after duplicating each `S = 1` site into two `S = 1/2` spins) from a singlet pair
on the bond `{x, x+1}` tensored with an arbitrary state on the rest of the chain.

The bond projection and the affine identity (7.1.5) are *defined and proved* here.  The full VBS
singlet-tensor form (7.1.20) needs the duplicated-`S = 1/2` / Schwinger-boson construction, which is
not formalized; following the project policy, the single-bond characterization is recorded with the
deep singlet form kept as the uninterpreted marker `IsVBSGroundForm` (so the equivalence is faithful
and cannot be applied to an unrelated property).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.2–§7.1.3, Lemma 7.4, eqs. (7.1.5)–(7.1.6), (7.1.19)–(7.1.20), pp. 181–187; T. Kennedy,
E. Lieb, H. Tasaki, J. Stat. Phys. **53**, 383 (1988).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **cyclic successor** `x ↦ x + 1 (mod L)` on the ring `Fin L`, giving the right endpoint of
the periodic bond `{x, x+1}`. -/
def ringSucc (x : Fin L) : Fin L :=
  ⟨(x.val + 1) % L, Nat.mod_lt _ x.pos⟩

/-- The **bond projection onto total spin 2** `P̂₂[Ŝ_x + Ŝ_y]` for two adjacent `S = 1` spins, as
the polynomial `½ (Ŝ_x · Ŝ_y) + ⅙ (Ŝ_x · Ŝ_y)² + ⅓` in the bond Heisenberg operator (the inverse of
the affine identity (7.1.5)). -/
noncomputable def bondSpin2ProjectionS (x y : Fin L) : ManyBodyOpS (Fin L) 2 :=
  (1 / 2 : ℂ) • spinSDot x y 2 + (1 / 6 : ℂ) • (spinSDot x y 2 * spinSDot x y 2) +
    (1 / 3 : ℂ) • (1 : ManyBodyOpS (Fin L) 2)

/-- **Tasaki eq. (7.1.5), PROVED.**  The AKLT bond term `Ŝ_x · Ŝ_y + ⅓ (Ŝ_x · Ŝ_y)²` equals
`2 P̂₂[Ŝ_x + Ŝ_y] − ⅔`, so it is the bond projection onto total spin 2 up to an affine shift. -/
theorem aklt_bond_term_eq_bondSpin2Projection (x y : Fin L) :
    spinSDot x y 2 + (1 / 3 : ℂ) • (spinSDot x y 2 * spinSDot x y 2) =
      (2 : ℂ) • bondSpin2ProjectionS x y - (2 / 3 : ℂ) • (1 : ManyBodyOpS (Fin L) 2) := by
  simp only [bondSpin2ProjectionS, smul_add, smul_smul]
  norm_num

/-- **The VBS singlet-form marker** `IsVBSGroundForm L x Φ`: the state `Φ` has the
valence-bond-solid singlet-tensor form (7.1.20) on the bond `{x, x+1}` — a singlet pair of the
duplicated `S = 1/2` spins on `x` and `x+1`, tensored with an arbitrary state on the remaining
sites.  A faithful
definition needs the duplicated-chain / Schwinger-boson construction; it is kept as an uninterpreted
predicate so that Lemma 7.4 is stated only for the genuine singlet form. -/
axiom IsVBSGroundForm (L : ℕ) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) : Prop

/-- **Tasaki Lemma 7.4 (local VBS ground-state characterization), AXIOM.**  A state `Φ` of the
`S = 1` chain is annihilated by the bond projection onto total spin 2 at the (periodic) bond
`{x, x+1}`, `P̂₂[Ŝ_x + Ŝ_{x+1}] Φ = 0` (eq. (7.1.19)), if and only if `Φ` has the valence-bond-solid
singlet-tensor form (7.1.20) on that bond (`IsVBSGroundForm`).

This is the local characterization that drives the Kennedy–Lieb–Tasaki uniqueness proof: a state
lies in the AKLT ground space iff it is annihilated by *every* bond projection, i.e. iff every bond
carries a singlet pair (the VBS state).  The concrete bond projection and the affine identity
(7.1.5) are proved above; the deep singlet form (7.1.20) is recorded through the marker
`IsVBSGroundForm`, so the equivalence is a faithful, sound documented axiom.  The hypothesis
`1 < L` ensures the bond `{x, ringSucc x}` is genuinely two-site: on the degenerate one-site ring
`L = 1` one has `ringSucc x = x`, so the operator would be a single-site self-interaction rather
than the two-site bond projection of Lemma 7.4. -/
axiom tasaki_lemma_7_4 (hL : 1 < L) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec Φ = 0 ↔ IsVBSGroundForm L x Φ

end LatticeSystem.Quantum
