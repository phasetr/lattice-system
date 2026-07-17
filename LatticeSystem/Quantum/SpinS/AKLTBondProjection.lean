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

/-! ## Forward kernel inclusion `W ⊆ ker P̂₂^{loc}` (Lemma 7.4, PR-2)

The four bond vectors `Ψ_{σσ'}` have total spin `≤ 1`, hence lie in the kernel of the single-bond
spin-2 projection `P̂₂^{loc} = bondSpin2ProjectionS (0 : Fin 2) 1` on `ℂ³ ⊗ ℂ³` (`Λ = Fin 2`,
`L = 2`).  This is Tasaki's forward direction (7.1.20) ⇒ (7.1.19), verified here by an explicit
`9`-dimensional linear-algebra computation. -/

/-- Enumeration of a sum over the `9` two-site configurations `Fin 2 → Fin 3`. -/
private lemma sum_fin2_fin3 (f : (Fin 2 → Fin 3) → ℂ) :
    ∑ σ : Fin 2 → Fin 3, f σ =
      f ![0, 0] + f ![0, 1] + f ![0, 2] + f ![1, 0] + f ![1, 1] + f ![1, 2]
        + f ![2, 0] + f ![2, 1] + f ![2, 2] := by
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp f, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, finTwoArrowEquiv_symm_apply]
  ring

/-- On `Λ = Fin 2` the off-bond delta of the two-site dot product is vacuous, so
`Ŝ_0 · Ŝ_1` is the plain tensor `∑_α Ŝ^{(α)} ⊗ Ŝ^{(α)}` of single-site operators. -/
private lemma spinSDot_fin2_apply (σ' σ : Fin 2 → Fin 3) :
    spinSDot (0 : Fin 2) 1 2 σ' σ =
      spinSOp1 2 (σ' 0) (σ 0) * spinSOp1 2 (σ' 1) (σ 1)
        + spinSOp2 2 (σ' 0) (σ 0) * spinSOp2 2 (σ' 1) (σ 1)
        + spinSOp3 2 (σ' 0) (σ 0) * spinSOp3 2 (σ' 1) (σ 1) := by
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have hvac : ∀ k : Fin 2, k ≠ 0 → k ≠ 1 → σ' k = σ k := by
    intro k h0 h1; fin_cases k
    · exact absurd rfl h0
    · exact absurd rfl h1
  rw [spinSDot_def]
  simp only [Matrix.add_apply]
  rw [onSiteS_mul_onSiteS_apply_eq hne, onSiteS_mul_onSiteS_apply_eq hne,
    onSiteS_mul_onSiteS_apply_eq hne]
  simp only [if_pos hvac]

/-- Raising-operator entries at `N = 2` (`Ŝ^+` on the spin-1 ladder): `√2` on the two raising
pairs, `0` otherwise. -/
private lemma plus2 (i j : Fin 3) :
    spinSOpPlus 2 i j =
      if i.val + 1 = j.val then ((Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h : i.val + 1 = j.val
  · rw [spinSOpPlus_apply_raise 2 h, if_pos h]
    have hj : j.val = 1 ∨ j.val = 2 := by omega
    rcases hj with hj | hj <;> rw [hj] <;> norm_num
  · rw [spinSOpPlus_apply_other 2 h, if_neg h]

/-- Lowering-operator entries at `N = 2` (`Ŝ^-` on the spin-1 ladder): `√2` on the two lowering
pairs, `0` otherwise. -/
private lemma minus2 (i j : Fin 3) :
    spinSOpMinus 2 i j =
      if j.val + 1 = i.val then ((Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h : j.val + 1 = i.val
  · rw [spinSOpMinus_apply_lower 2 h, if_pos h]
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with hj | hj <;> rw [hj] <;> norm_num
  · rw [spinSOpMinus_apply_other 2 h, if_neg h]

/-- `Ŝ^{(3)}` entries at `N = 2`: diagonal `1 − k` (magnetic quantum number), off-diagonal `0`. -/
private lemma three2 (i j : Fin 3) :
    spinSOp3 2 i j = if i = j then (1 : ℂ) - (i.val : ℂ) else 0 := by
  unfold spinSOp3
  rw [Matrix.diagonal_apply]
  split
  · norm_num
  · rfl

/-- Imaginary-free form of the two-site dot product on `Fin 2`:
`Ŝ_0 · Ŝ_1 = ½ (Ŝ^+ ⊗ Ŝ^- + Ŝ^- ⊗ Ŝ^+) + Ŝ^{(3)} ⊗ Ŝ^{(3)}`, eliminating `Ŝ^{(1)}, Ŝ^{(2)}`
(and hence `I`) so the kernel computation stays over rational multiples of `√2`. -/
private lemma spinSDot_fin2_apply' (σ' σ : Fin 2 → Fin 3) :
    spinSDot (0 : Fin 2) 1 2 σ' σ =
      (1 / 2 : ℂ) * (spinSOpPlus 2 (σ' 0) (σ 0) * spinSOpMinus 2 (σ' 1) (σ 1)
        + spinSOpMinus 2 (σ' 0) (σ 0) * spinSOpPlus 2 (σ' 1) (σ 1))
        + spinSOp3 2 (σ' 0) (σ 0) * spinSOp3 2 (σ' 1) (σ 1) := by
  rw [spinSDot_fin2_apply, spinSOp1, spinSOp2]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  have hI : (1 : ℂ) / (2 * Complex.I) = -Complex.I / 2 := by
    rw [mul_comm, ← div_div, Complex.div_I]; ring
  rw [hI]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `(√2)² = 2` inside `ℂ`, used to clear the radicals from the kernel computation. -/
private lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `√2 · √2 = 2` inside `ℂ` (product form), used to clear the radicals from the kernel
computation. -/
private lemma sqrt2_mul : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- The image `Ŝ_0 · Ŝ_1 |Ψ_{↑↓}⟩` of the mixed bond vector `Ψ_{↑↓} = vbsBondVec 0 1`
(`2|+,-⟩ − |0,0⟩`) under the two-site dot product: `−3|+,-⟩ + 2|0,0⟩ − |-,+⟩`. -/
private def dotImageUpDn : (Fin 2 → Fin 3) → ℂ := fun a =>
  (if a 0 = 0 ∧ a 1 = 2 then -3 else 0) + (if a 0 = 1 ∧ a 1 = 1 then 2 else 0)
    + (if a 0 = 2 ∧ a 1 = 0 then -1 else 0)

/-- The second image `(Ŝ_0 · Ŝ_1)² |Ψ_{↑↓}⟩ = Ŝ_0 · Ŝ_1 |dotImageUpDn⟩`:
`5|+,-⟩ − 4|0,0⟩ + 3|-,+⟩`. -/
private def dotImage2UpDn : (Fin 2 → Fin 3) → ℂ := fun a =>
  (if a 0 = 0 ∧ a 1 = 2 then 5 else 0) + (if a 0 = 1 ∧ a 1 = 1 then -4 else 0)
    + (if a 0 = 2 ∧ a 1 = 0 then 3 else 0)

/-- The image `Ŝ_0 · Ŝ_1 |Ψ_{↓↑}⟩` of the mixed bond vector `Ψ_{↓↑} = vbsBondVec 1 0`
(`|0,0⟩ − 2|-,+⟩`) under the two-site dot product: `|+,-⟩ − 2|0,0⟩ + 3|-,+⟩`. -/
private def dotImageDnUp : (Fin 2 → Fin 3) → ℂ := fun a =>
  (if a 0 = 0 ∧ a 1 = 2 then 1 else 0) + (if a 0 = 1 ∧ a 1 = 1 then -2 else 0)
    + (if a 0 = 2 ∧ a 1 = 0 then 3 else 0)

/-- The second image `(Ŝ_0 · Ŝ_1)² |Ψ_{↓↑}⟩ = Ŝ_0 · Ŝ_1 |dotImageDnUp⟩`:
`−3|+,-⟩ + 4|0,0⟩ − 5|-,+⟩`. -/
private def dotImage2DnUp : (Fin 2 → Fin 3) → ℂ := fun a =>
  (if a 0 = 0 ∧ a 1 = 2 then -3 else 0) + (if a 0 = 1 ∧ a 1 = 1 then 4 else 0)
    + (if a 0 = 2 ∧ a 1 = 0 then -5 else 0)

/-- Definitional expansion of the local bond projection `P̂₂^{loc}` as a polynomial in
`Ŝ_0 · Ŝ_1`. -/
private lemma bondLocal_expand :
    bondSpin2ProjectionS (0 : Fin 2) 1
      = (1 / 2 : ℂ) • spinSDot 0 1 2 + (1 / 6 : ℂ) • (spinSDot 0 1 2 * spinSDot 0 1 2)
        + (1 / 3 : ℂ) • 1 := rfl

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- `Ŝ_0 · Ŝ_1 |Ψ_{↑↑}⟩ = −|Ψ_{↑↑}⟩`: the aligned bond vector is a spin-1 eigenvector
(eigenvalue `−1`). -/
private lemma dot_mulVec_upUp :
    (spinSDot (0 : Fin 2) 1 2).mulVec (vbsBondVec 0 0) = -(vbsBondVec 0 0) := by
  funext idx
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
  simp only [vbsBondVec, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  fin_cases a <;> fin_cases b <;>
    simp only [Pi.neg_apply, vbsBondVec, spinSDot_fin2_apply', Matrix.cons_val_zero,
      Matrix.cons_val_one, plus2, minus2, three2, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [sqrt2_mul, sqrt2_sq]

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- `Ŝ_0 · Ŝ_1 |Ψ_{↓↓}⟩ = −|Ψ_{↓↓}⟩`: the anti-aligned bond vector is a spin-1 eigenvector. -/
private lemma dot_mulVec_dnDn :
    (spinSDot (0 : Fin 2) 1 2).mulVec (vbsBondVec 1 1) = -(vbsBondVec 1 1) := by
  funext idx
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
  simp only [vbsBondVec, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  fin_cases a <;> fin_cases b <;>
    simp only [Pi.neg_apply, vbsBondVec, spinSDot_fin2_apply', Matrix.cons_val_zero,
      Matrix.cons_val_one, plus2, minus2, three2, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [sqrt2_mul, sqrt2_sq]

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- First dot-product image of the mixed bond vector `Ψ_{↑↓}` (`vbsBondVec 0 1`). -/
private lemma dot_mulVec_upDn :
    (spinSDot (0 : Fin 2) 1 2).mulVec (vbsBondVec 0 1) = dotImageUpDn := by
  funext idx
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
  simp only [vbsBondVec, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  fin_cases a <;> fin_cases b <;>
    simp only [dotImageUpDn, spinSDot_fin2_apply', Matrix.cons_val_zero,
      Matrix.cons_val_one, plus2, minus2, three2, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [sqrt2_mul, sqrt2_sq]

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- Second dot-product image of `Ψ_{↑↓}`: `Ŝ_0 · Ŝ_1 |dotImageUpDn⟩ = dotImage2UpDn`. -/
private lemma dot_mulVec2_upDn :
    (spinSDot (0 : Fin 2) 1 2).mulVec dotImageUpDn = dotImage2UpDn := by
  funext idx
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
  simp only [dotImageUpDn, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  fin_cases a <;> fin_cases b <;>
    simp only [dotImage2UpDn, spinSDot_fin2_apply', Matrix.cons_val_zero,
      Matrix.cons_val_one, plus2, minus2, three2, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [sqrt2_mul, sqrt2_sq]

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- First dot-product image of the mixed bond vector `Ψ_{↓↑}` (`vbsBondVec 1 0`). -/
private lemma dot_mulVec_dnUp :
    (spinSDot (0 : Fin 2) 1 2).mulVec (vbsBondVec 1 0) = dotImageDnUp := by
  funext idx
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
  simp only [vbsBondVec, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  fin_cases a <;> fin_cases b <;>
    simp only [dotImageDnUp, spinSDot_fin2_apply', Matrix.cons_val_zero,
      Matrix.cons_val_one, plus2, minus2, three2, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [sqrt2_mul, sqrt2_sq]

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- Second dot-product image of `Ψ_{↓↑}`: `Ŝ_0 · Ŝ_1 |dotImageDnUp⟩ = dotImage2DnUp`. -/
private lemma dot_mulVec2_dnUp :
    (spinSDot (0 : Fin 2) 1 2).mulVec dotImageDnUp = dotImage2DnUp := by
  funext idx
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
  simp only [dotImageDnUp, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  fin_cases a <;> fin_cases b <;>
    simp only [dotImage2DnUp, spinSDot_fin2_apply', Matrix.cons_val_zero,
      Matrix.cons_val_one, plus2, minus2, three2, Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [sqrt2_mul, sqrt2_sq]

/-- The aligned bond vector `Ψ_{↑↑}` lies in the kernel of the local spin-2 projection: the spin-1
eigenvalue `−1` gives `P̂₂^{loc}(−1) = ½(−1) + ⅙(−1)² + ⅓ = 0`. -/
private lemma bondLocal_mulVec_upUp :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec 0 0) = 0 := by
  rw [bondLocal_expand]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec]
  rw [dot_mulVec_upUp, Matrix.mulVec_neg, dot_mulVec_upUp]
  funext idx
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- The anti-aligned bond vector `Ψ_{↓↓}` lies in the kernel of the local spin-2 projection. -/
private lemma bondLocal_mulVec_dnDn :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec 1 1) = 0 := by
  rw [bondLocal_expand]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec]
  rw [dot_mulVec_dnDn, Matrix.mulVec_neg, dot_mulVec_dnDn]
  funext idx
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- The mixed bond vector `Ψ_{↑↓}` lies in the kernel: `(Ŝ·Ŝ)² + 3(Ŝ·Ŝ) + 2` annihilates it,
which is `6 P̂₂^{loc}` (the spin-0 ⊕ spin-1 part). -/
private lemma bondLocal_mulVec_upDn :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec 0 1) = 0 := by
  rw [bondLocal_expand]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec]
  rw [dot_mulVec_upDn, dot_mulVec2_upDn]
  funext idx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotImage2UpDn, dotImageUpDn,
    vbsBondVec, Pi.zero_apply]
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] <;>
    (try simp) <;>
    norm_num

/-- The mixed bond vector `Ψ_{↓↑}` lies in the kernel of the local spin-2 projection. -/
private lemma bondLocal_mulVec_dnUp :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec 1 0) = 0 := by
  rw [bondLocal_expand]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec]
  rw [dot_mulVec_dnUp, dot_mulVec2_dnUp]
  funext idx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotImage2DnUp, dotImageDnUp,
    vbsBondVec, Pi.zero_apply]
  obtain ⟨a, b, hσ⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
    ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
  subst hσ
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] <;>
    (try simp) <;>
    norm_num

/-- **Forward direction of Lemma 7.4 (7.1.20) ⇒ (7.1.19), per bond vector.**  Each VBS bond vector
`Ψ_{σσ'}` is annihilated by the single-bond spin-2 projection `P̂₂^{loc}` on `ℂ³ ⊗ ℂ³`, since it has
total spin `≤ 1` (Tasaki §7.1.3, p. 186). -/
theorem bondLocal_mulVec_vbsBondVec (σ σ' : Fin 2) :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec σ σ') = 0 := by
  fin_cases σ <;> fin_cases σ'
  · exact bondLocal_mulVec_upUp
  · exact bondLocal_mulVec_upDn
  · exact bondLocal_mulVec_dnUp
  · exact bondLocal_mulVec_dnDn

/-- **Kernel inclusion `W ⊆ ker P̂₂^{loc}` (Lemma 7.4, forward).**  The VBS bond subspace `W`
(`vbsBondSubspace`, the span of the four `Ψ_{σσ'}`) is contained in the kernel of the single-bond
spin-2 projection `bondSpin2ProjectionS (0 : Fin 2) 1` on `ℂ³ ⊗ ℂ³` (Tasaki §7.1.3, eqs.
(7.1.19)–(7.1.20), p. 186).  The reverse inclusion (hence equality, `dim = 4`) is discharged in the
following PR. -/
theorem vbsBondSubspace_le_ker :
    vbsBondSubspace ≤
      LinearMap.ker (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1)) := by
  rw [vbsBondSubspace, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact bondLocal_mulVec_vbsBondVec p.1 p.2

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
