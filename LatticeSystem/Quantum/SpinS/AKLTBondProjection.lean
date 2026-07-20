import LatticeSystem.Quantum.SpinS.AKLT
import LatticeSystem.Quantum.SpinS.SpinOneTwoSiteEntries

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

The bond projection and the affine identity (7.1.5) are *defined and proved* here.  The four
concrete bond vectors `Ψ_{σσ'}` obtained by placing a singlet on the inner qubits span the
total-spin `≤ 1` subspace `W ⊂ ℂ³ ⊗ ℂ³` (`vbsBondSubspace`).  The predicate
`IsVBSGroundForm` is the concrete statement that every two-site bond slice of `Φ` lies in `W`;
being defined through `W` alone (with no reference to `P̂₂`), it makes Lemma 7.4 a
non-tautological equivalence.  The local kernel computation proves `ker P̂₂^{loc} = W`, and the
global tensor-slice identity then proves `tasaki_lemma_7_4`.

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

The four bond vectors `Ψ_{σσ'}` have total spin `≤ 1`, hence lie in the
kernel of the single-bond spin-2 projection
`P̂₂^{loc} = bondSpin2ProjectionS (0 : Fin 2) 1` on `ℂ³ ⊗ ℂ³`
(`Λ = Fin 2`, `L = 2`).  This is Tasaki's forward direction
(7.1.20) ⇒ (7.1.19), verified here by an explicit `9`-dimensional
linear-algebra computation.  The entry-level formulas for the spin-1 operators used throughout
(`sum_fin2_fin3`, `spinSDot_fin2_apply`, `spinSDot_fin2_apply'`, `spinSOpPlus_two_apply`,
`spinSOpMinus_two_apply`, `spinSOp3_two_apply`)
live in `LatticeSystem.Quantum.SpinS.SpinOneTwoSiteEntries`. -/

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
/-- `Ŝ_0 · Ŝ_1 |Ψ_{↑↑}⟩ = −|Ψ_{↑↑}⟩`: the aligned bond vector is a
spin-1 eigenvector (eigenvalue `−1`). -/
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
      Matrix.cons_val_one, spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply,
      Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]

set_option maxHeartbeats 1000000 in -- `9`-dim single mulVec exceeds the default heartbeat budget
/-- `Ŝ_0 · Ŝ_1 |Ψ_{↓↓}⟩ = −|Ψ_{↓↓}⟩`: the aligned bond vector is a
spin-1 eigenvector. -/
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
      Matrix.cons_val_one, spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply,
      Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]

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
      Matrix.cons_val_one, spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply,
      Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]

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
      Matrix.cons_val_one, spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply,
      Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]

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
      Matrix.cons_val_one, spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply,
      Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]

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
      Matrix.cons_val_one, spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply,
      Fin.isValue, Fin.val_zero,
      Fin.val_one, Fin.val_two] <;>
    (try simp) <;>
    norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]

/-- The aligned bond vector `Ψ_{↑↑}` lies in the kernel of the local
spin-2 projection: the spin-1 eigenvalue `−1` gives
`P̂₂^{loc}(−1) = ½(−1) + ⅙(−1)² + ⅓ = 0`. -/
private lemma bondLocal_mulVec_upUp :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec 0 0) = 0 := by
  rw [bondLocal_expand]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec]
  rw [dot_mulVec_upUp, Matrix.mulVec_neg, dot_mulVec_upUp]
  funext idx
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- The aligned bond vector `Ψ_{↓↓}` lies in the kernel of the local spin-2 projection. -/
private lemma bondLocal_mulVec_dnDn :
    (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (vbsBondVec 1 1) = 0 := by
  rw [bondLocal_expand]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec]
  rw [dot_mulVec_dnDn, Matrix.mulVec_neg, dot_mulVec_dnDn]
  funext idx
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- The mixed bond vector `Ψ_{↑↓}` lies in the kernel:
`(Ŝ·Ŝ)² + 3(Ŝ·Ŝ) + 2` annihilates it, which is `6 P̂₂^{loc}`
(the spin-0 ⊕ spin-1 part). -/
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
`Ψ_{σσ'}` is annihilated by the single-bond spin-2 projection
`P̂₂^{loc}` on `ℂ³ ⊗ ℂ³`, since it has total spin `≤ 1`
(Tasaki §7.1.3, p. 186). -/
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
(7.1.19)–(7.1.20), p. 186).  The reverse inclusion follows below from the local rank and
nullity computation. -/
theorem vbsBondSubspace_le_ker :
    vbsBondSubspace ≤
      LinearMap.ker (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1)) := by
  rw [vbsBondSubspace, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact bondLocal_mulVec_vbsBondVec p.1 p.2

/-! ## The local kernel `ker P̂₂^{loc} = W` (Lemma 7.4) -/

/-- The four VBS bond vectors `Ψ_{σσ'}` are linearly independent.  Their coefficients are
successively isolated by the product-basis coordinates `|+,0⟩`, `|+,−⟩`, `|−,+⟩`, and
`|0,−⟩`. -/
theorem vbsBondVec_linearIndependent :
    LinearIndependent ℂ (fun p : Fin 2 × Fin 2 => vbsBondVec p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have h00 := congrFun hc ![0, 1]
  have h01 := congrFun hc ![0, 2]
  have h10 := congrFun hc ![2, 0]
  have h11 := congrFun hc ![1, 2]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vbsBondVec, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h00 h01 h10 h11
  rw [Fintype.sum_prod_type] at h00 h01 h10 h11
  simp only [Fin.sum_univ_two] at h00 h01 h10 h11
  rcases p with ⟨p₀, p₁⟩
  fin_cases p₀ <;> fin_cases p₁
  · norm_num at h00 ⊢
    simpa using h00
  · norm_num at h01 ⊢
    simpa using h01
  · norm_num at h10 ⊢
    simpa using h10
  · norm_num at h11 ⊢
    simpa using h11

/-- The VBS bond subspace `W`, spanned by the four independent vectors `Ψ_{σσ'}`, has complex
dimension four. -/
theorem finrank_vbsBondSubspace :
    Module.finrank ℂ vbsBondSubspace = 4 := by
  rw [vbsBondSubspace, finrank_span_eq_card vbsBondVec_linearIndependent]
  norm_num

set_option maxHeartbeats 2000000 in
-- The explicit five-vector rank computation exceeds the default heartbeat budget.
/-- The single-bond spin-2 projection has rank exactly five.  The lower bound uses five
independent spin-2 vectors selected from the total-magnetization sectors `2, 1, 0, −1, −2`.
The upper bound follows from `W ≤ ker P̂₂^{loc}` and rank-nullity. -/
theorem bondLocal_rank :
    Matrix.rank (bondSpin2ProjectionS (0 : Fin 2) 1) = 5 := by
  let P := bondSpin2ProjectionS (0 : Fin 2) 1
  let basisVec : (Fin 2 → Fin 3) → ((Fin 2 → Fin 3) → ℂ) :=
    fun a => Pi.single a 1
  let w : Fin 5 → ((Fin 2 → Fin 3) → ℂ) :=
    ![basisVec ![0, 0],
      basisVec ![0, 1] + basisVec ![1, 0],
      basisVec ![0, 2] + (2 : ℂ) • basisVec ![1, 1] + basisVec ![2, 0],
      basisVec ![1, 2] + basisVec ![2, 1],
      basisVec ![2, 2]]
  have hLIw : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 := congrFun hc ![0, 0]
    have h1 := congrFun hc ![0, 1]
    have h2 := congrFun hc ![1, 1]
    have h3 := congrFun hc ![1, 2]
    have h4 := congrFun hc ![2, 2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Fin.sum_univ_five, w, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
      basisVec, Pi.single_apply, Pi.smul_apply, Fin.isValue] at h0 h1 h2 h3 h4
    fin_cases i <;> norm_num at h0 h1 h2 h3 h4 ⊢
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
  have hdot (i : Fin 5) : (spinSDot (0 : Fin 2) 1 2).mulVec (w i) = w i := by
    funext idx
    obtain ⟨a, b, hidx⟩ : ∃ a b : Fin 3, idx = ![a, b] :=
      ⟨idx 0, idx 1, by funext k; fin_cases k <;> rfl⟩
    subst hidx
    rw [Matrix.mulVec, dotProduct, sum_fin2_fin3]
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp only [w, basisVec, spinSDot_fin2_apply', spinSOpPlus_two_apply,
        spinSOpMinus_two_apply, spinSOp3_two_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] <;>
      (try simp) <;>
      norm_num [← Complex.ofReal_mul, Real.mul_self_sqrt]
  have hfix (i : Fin 5) : P.mulVec (w i) = w i := by
    change (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (w i) = w i
    rw [bondLocal_expand]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.one_mulVec, hdot]
    funext idx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hLI : LinearIndependent ℂ (fun i : Fin 5 => P.mulVec (w i)) := by
    simpa only [hfix] using hLIw
  have hspan :
      Submodule.span ℂ (Set.range fun i : Fin 5 => P.mulVec (w i)) ≤
        LinearMap.range (Matrix.mulVecLin P) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨w i, rfl⟩
  have hlower : 5 ≤ Matrix.rank P := by
    rw [Matrix.rank]
    calc
      5 = Module.finrank ℂ
          (Submodule.span ℂ (Set.range fun i : Fin 5 => P.mulVec (w i))) := by
            rw [finrank_span_eq_card hLI]
            norm_num
      _ ≤ Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin P)) :=
        Submodule.finrank_mono hspan
  have hker : 4 ≤ Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin P)) := by
    rw [← finrank_vbsBondSubspace]
    exact Submodule.finrank_mono vbsBondSubspace_le_ker
  have hnullity := (Matrix.mulVecLin P).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℂ ((Fin 2 → Fin 3) → ℂ) = 9 := by
    rw [Module.finrank_pi ℂ]
    norm_num
  rw [hdim] at hnullity
  have hupper : Matrix.rank P ≤ 5 := by
    rw [Matrix.rank]
    omega
  exact le_antisymm hupper hlower

/-- The kernel of the single-bond spin-2 projection has complex dimension four. -/
theorem finrank_bondLocal_ker :
    Module.finrank ℂ
      (LinearMap.ker (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1))) = 4 := by
  have hnullity :=
    (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1)).finrank_range_add_finrank_ker
  change Matrix.rank (bondSpin2ProjectionS (0 : Fin 2) 1) +
      Module.finrank ℂ
        (LinearMap.ker (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1))) =
      Module.finrank ℂ ((Fin 2 → Fin 3) → ℂ) at hnullity
  rw [bondLocal_rank, Module.finrank_pi ℂ] at hnullity
  norm_num at hnullity
  omega

/-- The kernel of the local spin-2 bond projection is exactly the four-dimensional VBS bond
subspace `W`.  The reverse inclusion is forced by equal finite dimensions from the previously
proved forward inclusion `vbsBondSubspace_le_ker`. -/
theorem bondLocal_ker_eq_vbsBondSubspace :
    LinearMap.ker (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1)) =
      vbsBondSubspace := by
  refine (Submodule.eq_of_le_of_finrank_le vbsBondSubspace_le_ker ?_).symm
  rw [finrank_bondLocal_ker, finrank_vbsBondSubspace]

/-! ## Global bond action on two-site slices -/

/-- The global spin-2 projection on the periodic bond `{x, ringSucc x}` acts on every fixed-rest
bond slice as the local two-site spin-2 projection.  This holds for every genuine bond `1 < L`,
including the wrap bond and both ordered bonds when `L = 2`. -/
theorem bondSlice_bondSpin2ProjectionS_mulVec
    (hL : 1 < L) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) (τ : Fin L → Fin 3) :
    bondSlice x ((bondSpin2ProjectionS x (ringSucc x)).mulVec Φ) τ =
      (bondSpin2ProjectionS (0 : Fin 2) 1).mulVec (bondSlice x Φ τ) := by
  have hxy : x ≠ ringSucc x := by
    intro h
    have hv := congrArg Fin.val h
    simp only [ringSucc] at hv
    by_cases hx : x.val + 1 < L
    · rw [Nat.mod_eq_of_lt hx] at hv
      omega
    · have heq : x.val + 1 = L := by omega
      rw [heq, Nat.mod_self] at hv
      omega
  have hOnSite {ι : Type} [Fintype ι] [DecidableEq ι]
      (i : ι) (A : Matrix (Fin 3) (Fin 3) ℂ)
      (Ψ : (ι → Fin 3) → ℂ) (q : ι → Fin 3) :
      (onSiteS i A : ManyBodyOpS ι 2).mulVec Ψ q =
        ∑ t : Fin 3, A (q i) t * Ψ (Function.update q i t) := by
    rw [Matrix.mulVec, dotProduct]
    simp only [onSiteS_apply]
    have hterm (σ : ι → Fin 3) :
        (if ∀ k, k ≠ i → q k = σ k then A (q i) (σ i) else 0) * Ψ σ =
          if σ = Function.update q i (σ i) then A (q i) (σ i) * Ψ σ else 0 := by
      by_cases hσ : σ = Function.update q i (σ i)
      · have hoff : ∀ k, k ≠ i → q k = σ k := by
          intro k hki
          rw [hσ, Function.update_of_ne hki]
        rw [if_pos hσ, if_pos hoff]
      · have hoff : ¬ ∀ k, k ≠ i → q k = σ k := by
          intro hall
          apply hσ
          funext k
          by_cases hki : k = i
          · subst k
            rw [Function.update_self]
          · rw [Function.update_of_ne hki]
            exact (hall k hki).symm
        rw [if_neg hσ, if_neg hoff, zero_mul]
    rw [Finset.sum_congr rfl (fun σ _ => hterm σ), ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun (t : Fin 3) _ => Function.update q i t) ?_ ?_ ?_ ?_
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      funext k
      by_cases hki : k = i
      · subst k
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hki, Function.update_of_ne hki]
    · intro s _ t _ hst
      have := congrFun hst i
      simpa only [Function.update_self] using this
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      exact ⟨σ i, Finset.mem_univ _, hσ.symm⟩
    · intro t _
      simp only [Function.update_self]
  have hglue_update_left (a : Fin 2 → Fin 3) (ρ : Fin L → Fin 3) (t : Fin 3) :
      Function.update (glueBond x a ρ) x t =
        glueBond x (Function.update a 0 t) ρ := by
    funext k
    by_cases hkx : k = x
    · subst k
      simp [glueBond]
    · by_cases hky : k = ringSucc x
      · subst k
        rw [Function.update_of_ne hxy.symm]
        simp [glueBond, hxy.symm]
      · simp [glueBond, hkx, hky, Function.update_of_ne]
  have hglue_update_right (a : Fin 2 → Fin 3) (ρ : Fin L → Fin 3) (t : Fin 3) :
      Function.update (glueBond x a ρ) (ringSucc x) t =
        glueBond x (Function.update a 1 t) ρ := by
    funext k
    by_cases hkx : k = x
    · subst k
      rw [Function.update_of_ne hxy]
      simp [glueBond]
    · by_cases hky : k = ringSucc x
      · subst k
        simp [glueBond, hxy.symm]
      · simp [glueBond, hkx, hky, Function.update_of_ne]
  have hSliceLeft (A : Matrix (Fin 3) (Fin 3) ℂ)
      (Ψ : (Fin L → Fin 3) → ℂ) (ρ : Fin L → Fin 3) :
      bondSlice x ((onSiteS x A : ManyBodyOpS (Fin L) 2).mulVec Ψ) ρ =
        (onSiteS (0 : Fin 2) A : ManyBodyOpS (Fin 2) 2).mulVec
          (bondSlice x Ψ ρ) := by
    funext a
    simp only [bondSlice]
    rw [hOnSite x A Ψ (glueBond x a ρ),
      hOnSite (0 : Fin 2) A (bondSlice x Ψ ρ) a]
    apply Finset.sum_congr rfl
    intro t _
    rw [show glueBond x a ρ x = a 0 by simp [glueBond], hglue_update_left]
    rfl
  have hSliceRight (A : Matrix (Fin 3) (Fin 3) ℂ)
      (Ψ : (Fin L → Fin 3) → ℂ) (ρ : Fin L → Fin 3) :
      bondSlice x ((onSiteS (ringSucc x) A : ManyBodyOpS (Fin L) 2).mulVec Ψ) ρ =
        (onSiteS (1 : Fin 2) A : ManyBodyOpS (Fin 2) 2).mulVec
          (bondSlice x Ψ ρ) := by
    funext a
    simp only [bondSlice]
    rw [hOnSite (ringSucc x) A Ψ (glueBond x a ρ),
      hOnSite (1 : Fin 2) A (bondSlice x Ψ ρ) a]
    apply Finset.sum_congr rfl
    intro t _
    rw [show glueBond x a ρ (ringSucc x) = a 1 by simp [glueBond, hxy.symm],
      hglue_update_right]
    rfl
  have hSlicePair (A B : Matrix (Fin 3) (Fin 3) ℂ)
      (Ψ : (Fin L → Fin 3) → ℂ) (ρ : Fin L → Fin 3) :
      bondSlice x
          (((onSiteS x A * onSiteS (ringSucc x) B :
            ManyBodyOpS (Fin L) 2).mulVec Ψ)) ρ =
        (onSiteS (0 : Fin 2) A * onSiteS (1 : Fin 2) B :
          ManyBodyOpS (Fin 2) 2).mulVec (bondSlice x Ψ ρ) := by
    rw [← Matrix.mulVec_mulVec, hSliceLeft, hSliceRight, Matrix.mulVec_mulVec]
  have hSliceAdd (Ψ Ψ' : (Fin L → Fin 3) → ℂ) (ρ : Fin L → Fin 3) :
      bondSlice x (Ψ + Ψ') ρ = bondSlice x Ψ ρ + bondSlice x Ψ' ρ := rfl
  have hSliceSmul (c : ℂ) (Ψ : (Fin L → Fin 3) → ℂ) (ρ : Fin L → Fin 3) :
      bondSlice x (c • Ψ) ρ = c • bondSlice x Ψ ρ := rfl
  have hSliceDot (Ψ : (Fin L → Fin 3) → ℂ) (ρ : Fin L → Fin 3) :
      bondSlice x ((spinSDot x (ringSucc x) 2).mulVec Ψ) ρ =
        (spinSDot (0 : Fin 2) 1 2).mulVec (bondSlice x Ψ ρ) := by
    rw [spinSDot_def, spinSDot_def, Matrix.add_mulVec, Matrix.add_mulVec,
      Matrix.add_mulVec, Matrix.add_mulVec, hSliceAdd, hSliceAdd,
      hSlicePair, hSlicePair, hSlicePair]
  rw [bondSpin2ProjectionS, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    hSliceAdd, hSliceAdd, hSliceSmul, hSliceSmul, hSliceSmul,
    ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hSliceDot, hSliceDot]
  rw [bondSpin2ProjectionS, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [hSliceDot]

/-- The global bond spin-2 projection annihilates a chain state exactly when every fixed-rest
two-site bond slice belongs to the kernel of the local spin-2 projection.  The equivalence is
uniform in the periodic bond, including the wrap bond and the two-site ring. -/
theorem bondSpin2ProjectionS_mulVec_eq_zero_iff_bondSlice_mem_ker
    (hL : 1 < L) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec Φ = 0 ↔
      ∀ τ : Fin L → Fin 3,
        bondSlice x Φ τ ∈
          LinearMap.ker (Matrix.mulVecLin (bondSpin2ProjectionS (0 : Fin 2) 1)) := by
  constructor
  · intro hΦ τ
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      ← bondSlice_bondSpin2ProjectionS_mulVec hL x Φ τ, hΦ]
    rfl
  · intro hslice
    funext q
    let a : Fin 2 → Fin 3 := ![q x, q (ringSucc x)]
    have hglue : glueBond x a q = q := by
      have hxy : x ≠ ringSucc x := by
        intro h
        have hv := congrArg Fin.val h
        simp only [ringSucc] at hv
        by_cases hx : x.val + 1 < L
        · rw [Nat.mod_eq_of_lt hx] at hv
          omega
        · have heq : x.val + 1 = L := by omega
          rw [heq, Nat.mod_self] at hv
          omega
      funext k
      by_cases hkx : k = x
      · subst k
        simp [a, glueBond]
      · by_cases hky : k = ringSucc x
        · subst k
          simp [a, glueBond, hxy.symm]
        · simp [glueBond, hkx, hky]
    have haction :=
      congrFun (bondSlice_bondSpin2ProjectionS_mulVec hL x Φ q) a
    have hker := hslice q
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
    rw [hker] at haction
    simpa only [bondSlice, hglue, Pi.zero_apply] using haction

/-- **Tasaki Lemma 7.4 (local VBS ground-state characterization), PROVED.**  A state `Φ` of the
`S = 1` chain is annihilated by the bond projection onto total spin 2 at the (periodic) bond
`{x, x+1}`, `P̂₂[Ŝ_x + Ŝ_{x+1}] Φ = 0` (eq. (7.1.19)), if and only if `Φ` has the valence-bond-solid
singlet-tensor form (7.1.20) on that bond (`IsVBSGroundForm`).

This is the local characterization that drives the Kennedy–Lieb–Tasaki uniqueness proof: a state
lies in the AKLT ground space iff it is annihilated by *every* bond projection, i.e. iff every bond
carries a singlet pair (the VBS state).  The concrete bond projection and the affine identity
(7.1.5) are proved above; the singlet form (7.1.20) is now the concrete predicate `IsVBSGroundForm`
(bond slices in the VBS subspace `W`).  The proof combines the global bond-slice equivalence with
the proved local identity `ker P̂₂^{loc} = W`.  The hypothesis
`1 < L` ensures the bond `{x, ringSucc x}` is genuinely two-site: on the degenerate one-site ring
`L = 1` one has `ringSucc x = x`, so the operator would be a single-site self-interaction rather
than the two-site bond projection of Lemma 7.4. -/
theorem tasaki_lemma_7_4 (hL : 1 < L) (x : Fin L) (Φ : (Fin L → Fin 3) → ℂ) :
    (bondSpin2ProjectionS x (ringSucc x)).mulVec Φ = 0 ↔ IsVBSGroundForm L x Φ := by
  simpa only [IsVBSGroundForm, bondLocal_ker_eq_vbsBondSubspace] using
    bondSpin2ProjectionS_mulVec_eq_zero_iff_bondSlice_mem_ker hL x Φ

end LatticeSystem.Quantum
