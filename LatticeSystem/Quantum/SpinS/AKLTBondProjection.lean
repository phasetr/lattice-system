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

The bond projection and the affine identity (7.1.5) are *defined and proved* here.  The VBS
singlet-tensor form (7.1.20) is realized **concretely** by the Weyl symmetrization
`Sym²(ℂ²) ≅ spin-1` (eq. (7.1.22)): each `S = 1` site is the symmetric part of two `S = 1/2` spins,
and the four bond
vectors `Ψ_{σσ'}` obtained by placing a singlet on the inner qubits span the total-spin `≤ 1`
subspace `W ⊂ ℂ³ ⊗ ℂ³` (`vbsBondSubspace`).  The predicate `IsVBSGroundForm` is then the concrete
statement that every two-site bond slice of `Φ` lies in `W`; being defined through `W` alone (with
no reference to `P̂₂`), it makes Lemma 7.4 a non-tautological equivalence.  The equivalence itself
(`tasaki_lemma_7_4`) is kept as a documented axiom in this PR pending the tensor-slice discharge.

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

/-- The **Weyl symmetrization embedding** `Sym²(ℂ²) ≅ spin-1` (Tasaki eq. (7.1.22), p. 187): the map
sending the two duplicated `S = 1/2` spins on one site to the physical `S = 1` state,
`|↑↑⟩ ↦ |+⟩`, `|↓↓⟩ ↦ |−⟩`, `|↑↓⟩, |↓↑⟩ ↦ (1/√2)|0⟩`.  The qubit basis `Fin 2` is `↑ = 0`, `↓ = 1`;
the spin-1 basis `Fin 3` is `|+⟩ = 0`, `|0⟩ = 1`, `|−⟩ = 2` (the `spinSOp3 = diag(1,0,−1)`
convention).  This is the shared substrate used both by the global VBS state (§7.1.2) and by the
§7.2.8 string order, so it is defined once here for reuse. -/
noncomputable def spin1SymEmbed : Matrix (Fin 3) (Fin 2 × Fin 2) ℂ :=
  fun m q =>
    if m = 0 ∧ q = (0, 0) then 1
    else if m = 2 ∧ q = (1, 1) then 1
    else if m = 1 ∧ (q = (0, 1) ∨ q = (1, 0)) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    else 0

/-- The four **VBS bond vectors** `Ψ_{σσ'}` on a single bond of the duplicated `S = 1` chain (Tasaki
eqs. (7.1.19)–(7.1.20), p. 186): the two-site spin-1 states obtained by putting the outer qubits
`σ, σ' ∈ {↑ = 0, ↓ = 1}` on `(x, L)` and `(x+1, R)`, a singlet on the inner qubits
`(x, R), (x+1, L)`, and symmetrizing each site into spin-1.  Written with the `√2` cleared, so the
components are
rational (spin-1 basis `|+⟩ = 0`, `|0⟩ = 1`, `|−⟩ = 2`):
`Ψ_{↑↑} = ½(|+,0⟩ − |0,+⟩)`, `Ψ_{↓↓} = ½(|0,−⟩ − |−,0⟩)`, `Ψ_{↑↓} ∝ 2|+,−⟩ − |0,0⟩`,
`Ψ_{↓↑} ∝ |0,0⟩ − 2|−,+⟩`.  All four have total spin `≤ 1`, so they span the kernel of the bond
spin-2 projection. -/
noncomputable def vbsBondVec (σ σ' : Fin 2) : (Fin 2 → Fin 3) → ℂ :=
  fun a =>
    if σ = 0 then
      if σ' = 0 then
        (1 / 2 : ℂ) * ((if a 0 = 0 ∧ a 1 = 1 then 1 else 0)
          - (if a 0 = 1 ∧ a 1 = 0 then 1 else 0))
      else
        (2 : ℂ) * (if a 0 = 0 ∧ a 1 = 2 then 1 else 0)
          - (if a 0 = 1 ∧ a 1 = 1 then 1 else 0)
    else
      if σ' = 0 then
        (if a 0 = 1 ∧ a 1 = 1 then 1 else 0)
          - (2 : ℂ) * (if a 0 = 2 ∧ a 1 = 0 then 1 else 0)
      else
        (1 / 2 : ℂ) * ((if a 0 = 1 ∧ a 1 = 2 then 1 else 0)
          - (if a 0 = 2 ∧ a 1 = 1 then 1 else 0))

/-- The **VBS bond subspace** `W ⊂ ℂ³ ⊗ ℂ³` (Tasaki eqs. (7.1.20)–(7.1.21), pp. 186–187): the span
of the four bond vectors `Ψ_{σσ'}`, i.e. the total-spin `≤ 1` subspace (`dim W = 4`) that will be
shown to be the kernel of the single-bond spin-2 projection.  Membership of a bond slice in `W` is
the local VBS ground-state condition. -/
noncomputable def vbsBondSubspace : Submodule ℂ ((Fin 2 → Fin 3) → ℂ) :=
  Submodule.span ℂ (Set.range fun p : Fin 2 × Fin 2 => vbsBondVec p.1 p.2)

/-- **Glue a bond configuration into a rest configuration.**  `glueBond x a τ` places the two-site
bond values `a : Fin 2 → Fin 3` on the sites `{x, x+1}` (`a 0` on the left endpoint `x`, `a 1` on
the right endpoint `ringSucc x`) and keeps the rest-of-chain configuration `τ` elsewhere.  This
realizes the change of variables `≅ (bond 2 sites) × (rest)` used to reduce the global bond operator
to the local `9 × 9` problem (Tasaki eqs. (7.1.20)–(7.1.21), p. 186). -/
def glueBond (x : Fin L) (a : Fin 2 → Fin 3) (τ : Fin L → Fin 3) : Fin L → Fin 3 :=
  fun k => if k = x then a 0 else if k = ringSucc x then a 1 else τ k

/-- The **two-site bond slice** of a chain state `Φ` at the bond `{x, x+1}` for a fixed
rest-of-chain configuration `τ`: the vector `a ↦ Φ (glueBond x a τ)` obtained by freezing
every site outside the bond to `τ` (Tasaki eqs. (7.1.20)–(7.1.21), p. 186). -/
def bondSlice (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) (τ : Fin L → Fin 3) :
    (Fin 2 → Fin 3) → ℂ :=
  fun a => Φ (glueBond x a τ)

/-- **The VBS singlet-form predicate** `IsVBSGroundForm L x Φ` (Tasaki eqs. (7.1.19)–(7.1.20),
p. 186), now a concrete definition: the state `Φ` of the `S = 1` chain has the valence-bond-solid
singlet-tensor form on the bond `{x, x+1}` iff, for every rest-of-chain configuration `τ`, its
two-site bond slice lies in the VBS bond subspace `W` (`vbsBondSubspace`) — a singlet pair of the
duplicated `S = 1/2` spins on the bond, tensored with an arbitrary state on the remaining sites.
Stated purely through the singlet subspace `W`, independently of the spin-2 projection `P̂₂`, so
Lemma 7.4 below is not a tautology. -/
def IsVBSGroundForm (L : ℕ) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) : Prop :=
  ∀ τ : Fin L → Fin 3, bondSlice x Φ τ ∈ vbsBondSubspace

/-- **Tasaki Lemma 7.4 (local VBS ground-state characterization), AXIOM.**  A state `Φ` of the
`S = 1` chain is annihilated by the bond projection onto total spin 2 at the (periodic) bond
`{x, x+1}`, `P̂₂[Ŝ_x + Ŝ_{x+1}] Φ = 0` (eq. (7.1.19)), if and only if `Φ` has the valence-bond-solid
singlet-tensor form (7.1.20) on that bond (`IsVBSGroundForm`).

This is the local characterization that drives the Kennedy–Lieb–Tasaki uniqueness proof: a state
lies in the AKLT ground space iff it is annihilated by *every* bond projection, i.e. iff every bond
carries a singlet pair (the VBS state).  The concrete bond projection and the affine identity
(7.1.5) are proved above; the singlet form (7.1.20) is now the concrete predicate `IsVBSGroundForm`
(bond slices in the VBS subspace `W`).  The forward/backward tensor-slice discharge of this
equivalence is staged over the following PRs, so it is kept here as a documented axiom.  The
hypothesis
`1 < L` ensures the bond `{x, ringSucc x}` is genuinely two-site: on the degenerate one-site ring
`L = 1` one has `ringSucc x = x`, so the operator would be a single-site self-interaction rather
than the two-site bond projection of Lemma 7.4. -/
axiom tasaki_lemma_7_4 (hL : 1 < L) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec Φ = 0 ↔ IsVBSGroundForm L x Φ

end LatticeSystem.Quantum
