import LatticeSystem.Quantum.SpinS.AKLTKnabe.KnabeAggregationD6d
import LatticeSystem.Quantum.SpinS.AKLTKnabe.FrustrationFreeD7c
import LatticeSystem.Quantum.SpinS.AKLTKnabe.GenericSpectralD7b
import LatticeSystem.Quantum.SpinS.ManyBodySpectralGap
import LatticeSystem.Math.FrustrationFree

/-!
# Gate D7d (block ④-III): assembly of the Knabe spectral gap for the AKLT ring

This module belongs to Issue #5094 (Tasaki §7.1.4, Knabe's argument,
pp. 188–190).  It assembles the three finished blocks

* ③ (`AKLTKnabe.KnabeAggregationD6d`) — the Knabe operator inequality
  `(Ĥ′)² − (1/10) Ĥ′ ≥ 0` for the periodic chain `Fin L`, `5 ≤ L`, no parity restriction;
* ④-I (`AKLTKnabe.GenericSpectralD7b`) — the generic spectral infrastructure S1–S6;
* ④-II (`AKLTKnabe.FrustrationFreeD7c`) — frustration-freeness of the ring VBS state,

into the finite-volume gap theorem of §7.1.4, following the Gate D7a design items G1–G7:

* **G1** `posSemidef_ringBond` — a bond projection is `≥ 0` (Hermitian idempotent).
* **G2** `ringProjHamiltonianS_posSemidef_and_annihilates` — **one** call to Tasaki Lemma A.9
  (`LatticeSystem.Math.frustration_free_isGroundState`, `Math/FrustrationFree.lean:51`) with
  `ε ≡ 0` delivers *both* `Ĥ′ ≥ 0` and `Ĥ′ Φ_VBS = 0`.  There is deliberately **no** hand-written
  positive-semidefiniteness proof for `Ĥ′`.
* **G3** `ringProjHamiltonianS_ne_zero` — `Ĥ′ ≠ 0`, the existence obligation of the first excited
  state.  If `Ĥ′` vanished, Tasaki Lemma A.10 would make the all-`|+⟩` basis vector a
  simultaneous zero mode of every bond, hence (Lemma 7.4) its bond slice would lie in the VBS bond
  subspace `W` — but every generator `Ψ_{σσ′}` of `W` has vanishing `(+,+)` component.
* **G4** `isGroundEnergy_ringProjHamiltonianS` — the ground energy of `Ĥ′` is `0`.
* **G5** `exists_gap_ringProjHamiltonianS` — the gap of `Ĥ′` is `≥ 1/10` (S2 + S4 + ③).
* **G6** `akltHamiltonianS_eq_affine_ringProjHamiltonianS` — the **single** normalisation
  statement: `Ĥ_AKLT = 2 Ĥ′ − (2/3) L`, obtained from eq. (7.1.5) by collapsing the directed
  `ringCoupling` double sum.  Both constants `2` and `−(2/3)L` occur here and **only** here, so
  the factor cannot be applied twice and the shift cannot be dropped (exact negative controls N3
  and N4).
* **G7** `aklt_knabe_ring_gap` — the capstone: for every ring of length `L = n + 1 ≥ 5` the AKLT
  chain has the explicit VBS ground state at energy `−(2/3)L` and a spectral gap `≥ 1/5`.

**The three normalisation constants** are `2/5` (four-site window `ĥ`, Gate D5b), `1/10`
(projector sum `Ĥ′`, Gate D6d = Knabe's aggregation) and `1/5` (`Ĥ_AKLT`, here); the last step is
the factor `a = 2` of G6, applied through S5/S6, which multiply the gap by `a` and leave it
unaffected by the shift `b = −(2/3)L`.

Exact rational contrasts run before this file was written (`Fraction`, no floats): G6 holds at
`L = 3,4,5` with the negative controls N3 (shift `−(4/3)L`) and N4 (shift `0`) both firing;
`Ĥ′ ≠ 0` with all-`|+⟩` diagonal entry `L`; all four `Ψ_{σσ′}(+,+) = 0`; `Ĥ′ Φ_VBS = 0` and
`Ĥ_AKLT Φ_VBS = −(2/3)L Φ_VBS` at `L = 3,4,5`; and `(Ĥ′)² − γ Ĥ′ ≥ 0` at `L = 5` for
`γ = 1/10, 1/5, 3/10` but **not** for `γ = 1/2` (so small `L` does not discriminate `1/10`
against `3/10`; the Lean bound comes from ③, not from these probes).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4 (Knabe's argument), pp. 188–190, eqs. (7.1.1), (7.1.5), (7.1.7); S. Knabe,
J. Stat. Phys. **52**, 627 (1988).
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open scoped ComplexOrder

section Assembly

variable {L : ℕ} [NeZero L]

/-! ### G1 — a single bond projection is positive semidefinite -/

/-- **G1.**  Each ring bond projection `P̂₂[Ŝ_y + Ŝ_{y+1}]` is positive semidefinite: it is a
Hermitian idempotent, so `P = Pᴴ P ≥ 0`.  (`Matrix.conjTranspose` is spelled out because the `ᴴ`
postfix does not parse inside this namespace.) -/
theorem posSemidef_ringBond (hL : 2 ≤ L) (y : Fin L) :
    (ringBond y : ManyBodyOpS (Fin L) 2).PosSemidef := by
  have hone : ((1 : Fin L)).val = 1 := by
    change 1 % L = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hzero : ((0 : Fin L)).val = 0 := by simp
  have hne : y ≠ y + 1 := by
    intro h
    have h1 : (1 : Fin L) = 0 := left_eq_add.mp h
    have h2 := congrArg Fin.val h1
    rw [hone, hzero] at h2
    omega
  have hH := bondSpin2ProjectionS_isHermitian y (y + 1)
  have key : Matrix.conjTranspose (bondSpin2ProjectionS y (y + 1) : ManyBodyOpS (Fin L) 2)
      * bondSpin2ProjectionS y (y + 1) = bondSpin2ProjectionS y (y + 1) := by
    rw [hH.eq, bondSpin2ProjectionS_mul_self hne]
  change (bondSpin2ProjectionS y (y + 1) : ManyBodyOpS (Fin L) 2).PosSemidef
  exact key ▸ Matrix.posSemidef_conjTranspose_mul_self
    (bondSpin2ProjectionS y (y + 1) : ManyBodyOpS (Fin L) 2)

/-! ### G2 — positivity and the zero mode, in one call to Tasaki Lemma A.9 -/

/-- The local lower bounds `P̂_{y,y+1} − 0 ≥ 0` of every ring bond, in the shape consumed by
Tasaki Lemmas A.9 and A.10 with all local energies `ε_y ≡ 0`. -/
private theorem ringBond_sub_zero_posSemidef (hL : 2 ≤ L) :
    ∀ y ∈ (Finset.univ : Finset (Fin L)),
      (ringBond y - ((0 : ℝ) : ℂ) • (1 : ManyBodyOpS (Fin L) 2)).PosSemidef := by
  intro y _
  simpa using posSemidef_ringBond hL y

/-- **G2.**  The projector Hamiltonian `Ĥ′ = Σ_y P̂_{y,y+1}` of eq. (7.1.7) is positive
semidefinite **and** annihilates the ring VBS state.  Both facts come from a *single* application
of Tasaki Lemma A.9 (`frustration_free_isGroundState`) with all local bounds `ε_y ≡ 0`: the local
bounds are G1, and the simultaneous-eigenstate hypothesis is the frustration-freeness F8.  Writing
a separate positivity proof for `Ĥ′` would duplicate Lemma A.9. -/
theorem ringProjHamiltonianS_posSemidef_and_annihilates (hL : 2 ≤ L) :
    (ringProjHamiltonianS L).PosSemidef ∧
      (ringProjHamiltonianS L).mulVec (akltVBSState L) = 0 := by
  have heig : ∀ y ∈ (Finset.univ : Finset (Fin L)),
      (ringBond y).mulVec (akltVBSState L) = ((0 : ℝ) : ℂ) • akltVBSState L := by
    intro y _
    have hz := bondSpin2ProjectionS_mulVec_akltVBSState_eq_zero (by omega : 1 < L) y
    rw [ringSucc_eq_add_one] at hz
    simpa [ringBond] using hz
  obtain ⟨hpsd, hker⟩ :=
    LatticeSystem.Math.frustration_free_isGroundState Finset.univ
      (fun y : Fin L => ringBond y) (fun _ => (0 : ℝ)) (akltVBSState L)
      (ringBond_sub_zero_posSemidef hL) heig
  exact ⟨by simpa [ringProjHamiltonianS] using hpsd, by simpa [ringProjHamiltonianS] using hker⟩

/-! ### G3 — the projector Hamiltonian is nonzero -/

/-- **G3.**  The projector Hamiltonian is nonzero.  Suppose `Ĥ′ = 0`.  Then the all-`|+⟩` basis
vector `δ` is trivially at the (zero) ground energy, so Tasaki Lemma A.10
(`frustration_free_local_eigen`) makes it a zero mode of *every* bond projection; by Lemma 7.4 its
bond slice at the constant rest configuration lies in the VBS bond subspace `W`.  But evaluation at
the bond configuration `(+,+)` is a linear functional vanishing on all four generators `Ψ_{σσ′}`
of `W`, while `δ`'s slice has value `1` there.  This is the existence obligation of the first
excited state: without it `IsPositiveSpectralGap` is unprovable. -/
theorem ringProjHamiltonianS_ne_zero (hL : 2 ≤ L) : ringProjHamiltonianS L ≠ 0 := by
  intro hzero
  set δ : (Fin L → Fin 3) → ℂ := Pi.single (fun _ => 0) 1 with hδ
  have hgs : (∑ y ∈ (Finset.univ : Finset (Fin L)), ringBond y).mulVec δ
      = ((∑ _y ∈ (Finset.univ : Finset (Fin L)), (0 : ℝ) : ℝ) : ℂ) • δ := by
    have hsum : (∑ y ∈ (Finset.univ : Finset (Fin L)), ringBond y) = 0 := hzero
    rw [hsum]
    simp
  have hloc := LatticeSystem.Math.frustration_free_local_eigen Finset.univ
    (fun y : Fin L => ringBond y) (fun _ => (0 : ℝ)) δ (ringBond_sub_zero_posSemidef hL) hgs
  have h0 : (bondSpin2ProjectionS (0 : Fin L) (ringSucc 0)).mulVec δ = 0 := by
    have hb := hloc 0 (Finset.mem_univ _)
    rw [ringSucc_eq_add_one]
    simpa [ringBond] using hb
  have hmem := (tasaki_lemma_7_4 (by omega : 1 < L) (0 : Fin L) δ).mp h0 (fun _ => 0)
  have hker : vbsBondSubspace ≤ LinearMap.ker
      (LinearMap.proj (R := ℂ) (φ := fun _ : (Fin 2 → Fin 3) => ℂ) (fun _ => 0)) := by
    simp only [vbsBondSubspace]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨⟨p, q⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    fin_cases p <;> fin_cases q <;> simp +decide [vbsBondVec]
  have hglue : glueBond (0 : Fin L) (fun _ => 0) (fun _ => 0) = (fun _ => (0 : Fin 3)) := by
    funext k
    simp only [glueBond]
    split_ifs <;> rfl
  have hval := LinearMap.mem_ker.mp (hker hmem)
  rw [LinearMap.proj_apply] at hval
  simp only [bondSlice, hglue, hδ, Pi.single_eq_same] at hval
  exact one_ne_zero hval

/-! ### G4/G5 — ground energy `0` and the gap `1/10` of the projector Hamiltonian -/

/-- **G4.**  The ground energy of the projector Hamiltonian `Ĥ′` is `0`: the value is attained by
the (nonzero) ring VBS state, and no smaller value occurs because `Ĥ′ ≥ 0`. -/
theorem isGroundEnergy_ringProjHamiltonianS (hL : 2 ≤ L) :
    IsGroundEnergy (ringProjHamiltonianS L) 0 := by
  obtain ⟨hpsd, hker⟩ := ringProjHamiltonianS_posSemidef_and_annihilates hL
  refine ⟨⟨akltVBSState L, akltVBSState_ne_zero hL, ?_⟩, fun E hE => ?_⟩
  · rw [hker]
    simp
  · exact realSpectrum_nonneg_of_posSemidef hpsd hE

/-- **G5.**  The projector Hamiltonian `Ĥ′` of eq. (7.1.7) has a spectral gap of at least `1/10`,
uniformly in the ring length `L ≥ 5` and with no parity restriction.  The first excited energy
exists because `Ĥ′ ≠ 0` (G3), and it is `≥ 1/10` by Knabe's spectral step S4 applied to the
Gate D6d operator inequality `(Ĥ′)² ≥ (1/10) Ĥ′`. -/
theorem exists_gap_ringProjHamiltonianS (hL : 5 ≤ L) :
    ∃ gap : ℝ, (1 : ℝ) / 10 ≤ gap ∧ IsPositiveSpectralGap (ringProjHamiltonianS L) gap := by
  obtain ⟨hpsd, _⟩ := ringProjHamiltonianS_posSemidef_and_annihilates (L := L) (by omega)
  have hH : (ringProjHamiltonianS L).IsHermitian := hpsd.1
  have hgt : ∃ E ∈ realSpectrum (ringProjHamiltonianS L), (0 : ℝ) < E := by
    have hnz : hH.eigenvalues ≠ 0 := fun h =>
      ringProjHamiltonianS_ne_zero (L := L) (by omega) (hH.eigenvalues_eq_zero_iff.mp h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hnz
    have hi' : hH.eigenvalues i ≠ 0 := by simpa using hi
    exact ⟨hH.eigenvalues i, eigenvalues_mem_realSpectrum hH i,
      lt_of_le_of_ne (realSpectrum_nonneg_of_posSemidef hpsd
        (eigenvalues_mem_realSpectrum hH i)) (Ne.symm hi')⟩
  obtain ⟨E₁, hE₁spec, hE₁gt, _, hgap⟩ :=
    exists_isPositiveSpectralGap hH (isGroundEnergy_ringProjHamiltonianS (by omega)) hgt
  have hcast : (((1 : ℝ) / 10 : ℝ) : ℂ) = (1 : ℂ) / 10 := by norm_num
  have hknabe : ((ringProjHamiltonianS L) * (ringProjHamiltonianS L)
      - (((1 : ℝ) / 10 : ℝ) : ℂ) • ringProjHamiltonianS L).PosSemidef := by
    rw [hcast]
    exact ringProjHamiltonianS_knabe_posSemidef hL
  have h10 : (1 : ℝ) / 10 ≤ E₁ :=
    realSpectrum_ge_of_sq_sub_smul_posSemidef hpsd hknabe hE₁spec (ne_of_gt hE₁gt)
  exact ⟨E₁ - 0, by linarith, hgap⟩

/-! ### G6 — the normalisation of eq. (7.1.1) against eq. (7.1.7) -/

/-- The inner sum of `akltHamiltonianS` at a fixed left site: the *directed* `ringCoupling`
selects the single bond `{x, x+1}`, and eq. (7.1.5) turns the AKLT local term into
`2 P̂_{x,x+1} − 2/3`.  Because the coupling is directed, every bond is counted exactly once and no
factor of two can sneak in here. -/
private theorem akltHamiltonianS_inner_sum (x : Fin L) :
    (∑ y : Fin L, ringCoupling L x y •
        (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)))
      = (2 : ℂ) • ringBond x - ((2 : ℂ) / 3) • (1 : ManyBodyOpS (Fin L) 2) := by
  rw [Finset.sum_eq_single (ringSucc x)]
  · have hc : ringCoupling L x (ringSucc x) = 1 := by
      rw [ringCoupling]
      exact if_pos rfl
    rw [hc, one_smul, aklt_bond_term_eq_bondSpin2Projection]
    simp only [ringBond, ringSucc_eq_add_one]
  · intro y _ hy
    have hc : ringCoupling L x y = 0 := by
      rw [ringCoupling]
      exact if_neg fun hv => hy (Fin.ext hv)
    rw [hc, zero_smul]
  · intro hx
    exact absurd (Finset.mem_univ _) hx

omit [NeZero L] in
/-- The constant part of the collapsed double sum: `L` copies of `(2/3) · 1`. -/
private theorem akltHamiltonianS_const_sum :
    (∑ _x : Fin L, ((2 : ℂ) / 3) • (1 : ManyBodyOpS (Fin L) 2))
      = ((2 : ℂ) / 3 * (L : ℂ)) • (1 : ManyBodyOpS (Fin L) 2) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, mul_comm (L : ℂ) ((2 : ℂ) / 3)]

/-- **G6 (Tasaki eq. (7.1.1) vs eq. (7.1.7)).**  The AKLT ring Hamiltonian in its (7.1.1)
normalisation is the affine image `Ĥ_AKLT = 2 Ĥ′ − (2/3) L` of the projector sum (7.1.7).  Both
constants — the factor `2` and the shift `−(2/3)L` — occur in this one statement and nowhere else,
so the factor cannot be applied twice and the shift cannot be lost; the exact negative controls N3
(shift `−(4/3)L`) and N4 (shift `0`) both fire.  Stated in the affine shape `a • Ĥ′ + b • 1` with
real `a, b`, which is what the transport lemmas S5 and S6 consume. -/
theorem akltHamiltonianS_eq_affine_ringProjHamiltonianS :
    akltHamiltonianS L
      = ((2 : ℝ) : ℂ) • ringProjHamiltonianS L
        + ((-(2 : ℝ) / 3 * (L : ℝ) : ℝ) : ℂ) • (1 : ManyBodyOpS (Fin L) 2) := by
  have hcollapse : (∑ x : Fin L, ∑ y : Fin L, ringCoupling L x y •
      (spinSDot x y 2 + ((1 : ℂ) / 3) • (spinSDot x y 2 * spinSDot x y 2)))
      = ∑ x : Fin L, ((2 : ℂ) • ringBond x - ((2 : ℂ) / 3) • (1 : ManyBodyOpS (Fin L) 2)) :=
    Finset.sum_congr rfl fun x _ => akltHamiltonianS_inner_sum x
  have hc2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hcb : ((-(2 : ℝ) / 3 * (L : ℝ) : ℝ) : ℂ) = -((2 : ℂ) / 3 * (L : ℂ)) := by
    push_cast
    ring
  simp only [ringProjHamiltonianS]
  rw [akltHamiltonianS, hcollapse, Finset.sum_sub_distrib, ← Finset.smul_sum,
    akltHamiltonianS_const_sum, hc2, hcb, neg_smul, ← sub_eq_add_neg]

end Assembly

/-! ### G7 — the capstone: Tasaki §7.1.4 (Knabe) finite-volume gap theorem -/

/-- **Tasaki §7.1.4 (Knabe's argument), PROVED.**  For every ring of length `L = n + 1 ≥ 5` — with
**no parity restriction** — the `S = 1` AKLT chain `Ĥ_AKLT` of eq. (7.1.1) has the explicit
periodic valence-bond-solid matrix-product state `akltVBSState L` as a nonzero eigenvector at the
ground energy `−(2/3) L`, and a spectral gap bounded below by `1/5`, a constant **uniform in `L`**.

The threshold `n₀ = 4` (i.e. `L ≥ 5`) is exactly the range in which Knabe's aggregation
`(Ĥ′)² ≥ (1/10) Ĥ′` is proved (Gate D6d): that identity is false at `L = 3, 4` and true for every
`L ≥ 5`, odd or even.  The gap constant is `1/5 = 2 · (1/10)`, the factor `2` being the
normalisation of eq. (7.1.5) transported by S5; the shift `−(2/3)L` cancels in the energy
difference and only moves the ground energy.

This is Tasaki's own §7.1.4 theorem; it supplies the *existence* and *gap* conjuncts of
Theorem 7.1 but neither ground-state uniqueness (§7.1.3) nor the correlation function (7.1.2), so
the axiom `aklt_theorem_7_1` stays in place.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4, pp. 188–190; S. Knabe, J. Stat. Phys. **52**, 627 (1988). -/
theorem aklt_knabe_ring_gap :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      akltVBSState (n + 1) ≠ 0 ∧
      (akltHamiltonianS (n + 1)).mulVec (akltVBSState (n + 1))
          = ((-(2 : ℝ) / 3 * ((n : ℝ) + 1) : ℝ) : ℂ) • akltVBSState (n + 1) ∧
      IsGroundEnergy (akltHamiltonianS (n + 1)) (-(2 : ℝ) / 3 * ((n : ℝ) + 1)) ∧
      ∃ gap : ℝ, (1 : ℝ) / 5 ≤ gap ∧ IsPositiveSpectralGap (akltHamiltonianS (n + 1)) gap := by
  refine ⟨4, fun n hn => ?_⟩
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by norm_cast
  obtain ⟨_, hker⟩ := ringProjHamiltonianS_posSemidef_and_annihilates (L := n + 1) (by omega)
  have haff := akltHamiltonianS_eq_affine_ringProjHamiltonianS (L := n + 1)
  refine ⟨akltVBSState_ne_zero (by omega), ?_, ?_, ?_⟩
  · rw [haff, hcast]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hker, smul_zero,
      zero_add]
  · rw [haff, hcast]
    have hg := isGroundEnergy_affine (a := (2 : ℝ))
      (b := -(2 : ℝ) / 3 * ((n + 1 : ℕ) : ℝ)) (by norm_num)
      (isGroundEnergy_ringProjHamiltonianS (L := n + 1) (by omega))
    rw [show (2 : ℝ) * 0 + -(2 : ℝ) / 3 * ((n + 1 : ℕ) : ℝ)
      = -(2 : ℝ) / 3 * ((n + 1 : ℕ) : ℝ) from by ring] at hg
    exact hg
  · obtain ⟨gap, hgap10, hgapspec⟩ := exists_gap_ringProjHamiltonianS (L := n + 1) (by omega)
    refine ⟨2 * gap, by linarith, ?_⟩
    rw [haff]
    exact isPositiveSpectralGap_affine (by norm_num) hgapspec

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
