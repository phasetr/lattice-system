import LatticeSystem.Quantum.SpinS.AnisotropicEdgeEnergy
import LatticeSystem.Math.MatrixAnalysis.InvariantSubmoduleRayleigh

/-!
# Tasaki §8.1.3 Theorem 8.2: hidden order forces edge states

Assembly of the Koma–Tasaki argument.  The three trial states `Ô^{(α)}_string Φ` are nonzero by
hidden order, and by the character law (8.1.12) they sit in three *pairwise different* simultaneous
`Z₂ × Z₂` character sectors, all different from the sector of the ground state.  Each sector is
`Ĥ`-invariant, so a sector-restricted variational extraction produces an energy eigenvector inside
it whose energy is at most the trial Rayleigh energy `E₀ + C_ν / L`.  Distinct characters make the
three eigenvectors eigenvectors of `Θ + 2P` for three distinct eigenvalues, hence linearly
independent, and forbid any of them from being a multiple of the unique ground state, which turns
`E₀ ≤ E_ν` into `E₀ < E_ν`.

Two places where the Lean development is more than a transcription of the book are flagged in the
declarations below: the sector restriction (the book only says "repeat the argument of Theorem
3.1", which may return the same eigenstate three times) and the double-commutator support count
(supplied in `AnisotropicEdgeEnergy`).  The ground-state uniqueness of the *open* chain is a
hypothesis, exactly as in the source; it does not follow from Tasaki's Theorem 2.4, which concerns
the periodic even-`L` ring.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.2–§8.1.3, Theorem 8.2, eqs. (8.1.8)–(8.1.12) and footnotes 11–12, pp. 236–238;
T. Koma, H. Tasaki, J. Stat. Phys. **76**, 745 (1994).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-! ## Simultaneous character sectors -/

/-- The **simultaneous `Z₂ × Z₂` character sector** `{v | Θ v = s v ∧ P v = t v}`: the joint
eigenspace of the two global half turns for the character pair `(s, t)`. -/
private def edgeCharacterSector (L : ℕ) (s t : ℂ) : Submodule ℂ ((Fin L → Fin 3) → ℂ) where
  carrier := {v | (manyBodyReversalS (Fin L) 2).mulVec v = s • v ∧
    (magParityDiagS (Fin L) 2).mulVec v = t • v}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [Matrix.mulVec_add, ha1, hb1, smul_add],
      by rw [Matrix.mulVec_add, ha2, hb2, smul_add]⟩
  zero_mem' := by
    exact ⟨by rw [Matrix.mulVec_zero, smul_zero], by rw [Matrix.mulVec_zero, smul_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    exact ⟨by rw [Matrix.mulVec_smul, ha1, smul_comm],
      by rw [Matrix.mulVec_smul, ha2, smul_comm]⟩

/-- **Each character sector is `Ĥ`-invariant**, since both half turns commute with the
Hamiltonian.  This is what makes the sector-restricted variational extraction legitimate. -/
private theorem edgeCharacterSector_invariant (L : ℕ) (D : ℝ) (s t : ℂ) :
    ∀ v ∈ edgeCharacterSector L s t,
      (openAnisotropicChainHamiltonianS L D).mulVec v ∈ edgeCharacterSector L s t := by
  intro v hv
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Matrix.mulVec_mulVec,
      (manyBodyReversalS_commute_openAnisotropicChainHamiltonianS L D).eq,
      ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul]
  · rw [Matrix.mulVec_mulVec,
      (magParityDiagS_commute_openAnisotropicChainHamiltonianS L D).eq,
      ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul]

/-! ## Characters of the ground state and of the trial states -/

/-- **The unique ground state carries a `±1` character** under any involution commuting with the
Hamiltonian.  Footnote 12 (p. 238) explicitly allows the character to be `-1`, so the sign is never
assumed to be `+1`. -/
private theorem edgeGroundCharacter {H : ManyBodyOpS (Fin L) 2} {E0 : ℝ}
    {Phi : (Fin L → Fin 3) → ℂ} (hGS : IsUniqueChainGroundState H E0 Phi)
    {U : ManyBodyOpS (Fin L) 2} (hU : U * U = 1) (hcomm : Commute U H) :
    ∃ delta : ℂ, delta * delta = 1 ∧ U.mulVec Phi = delta • Phi := by
  obtain ⟨hPhi, hev, _, huniq⟩ := hGS
  have hinvol : U.mulVec (U.mulVec Phi) = Phi := by
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  have hne : U.mulVec Phi ≠ 0 := by
    intro hzero
    apply hPhi
    rw [← hinvol, hzero, Matrix.mulVec_zero]
  have hev' : H.mulVec (U.mulVec Phi) = (E0 : ℂ) • U.mulVec Phi := by
    rw [Matrix.mulVec_mulVec, ← hcomm.eq, ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := huniq _ hne hev'
  refine ⟨c, ?_, hc⟩
  have hcc : (c * c) • Phi = (1 : ℂ) • Phi := by
    have hstep := hinvol
    rw [hc, Matrix.mulVec_smul, hc, smul_smul] at hstep
    rw [one_smul]
    exact hstep
  have := sub_eq_zero.mpr hcc
  rw [← sub_smul, smul_eq_zero] at this
  rcases this with h | h
  · linear_combination h
  · exact absurd h hPhi

/-- **The character law of a trial state** (Tasaki (8.1.12), p. 238): if the involution `U`
conjugates `O` to `c O` and carries `Φ` to `δ Φ`, then `O Φ` carries the character `c δ`. -/
private theorem edgeTrialCharacter {U O : ManyBodyOpS (Fin L) 2} {c d : ℂ}
    {Phi : (Fin L → Fin 3) → ℂ} (hU : U * U = 1) (hconj : U * O * U = c • O)
    (hPhi : U.mulVec Phi = d • Phi) :
    U.mulVec (O.mulVec Phi) = (c * d) • O.mulVec Phi := by
  have hpast : U * O = c • (O * U) := by
    have hstep := congrArg (fun M => M * U) hconj
    simpa [mul_assoc, hU, Matrix.smul_mul] using hstep
  rw [Matrix.mulVec_mulVec, hpast, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hPhi,
    Matrix.mulVec_smul, smul_smul]

/-! ## The single-volume theorem -/

/-- **Theorem 8.2 at a fixed volume.**  For one chain length `L > 0`, hidden order at the unique
ground state produces three linearly independent strict excitations with `O(1/L)` energies.  The
public capstone `tasaki_theorem_8_2` is the eventual-`L` packaging of this statement. -/
private theorem tasaki_theorem_8_2_fixed_volume (L : ℕ) (hL : 0 < L) (D : ℝ) (hD : 0 ≤ D)
    (q : Fin 3 → ℝ) (hq : ∀ alpha : Fin 3, 0 < q alpha)
    (E0 : ℝ) (Phi : (Fin L → Fin 3) → ℂ)
    (hGS : IsUniqueChainGroundState (openAnisotropicChainHamiltonianS L D) E0 Phi)
    (hLRO : HasStringLRO L Phi q) :
    ∃ (E : Fin 3 → ℝ) (Psi : Fin 3 → ((Fin L → Fin 3) → ℂ)),
      LinearIndependent ℂ Psi ∧
      ∀ nu : Fin 3,
        Psi nu ≠ 0 ∧
        (openAnisotropicChainHamiltonianS L D).mulVec (Psi nu) = (E nu : ℂ) • Psi nu ∧
        E0 < E nu ∧ E nu ≤ E0 + 64 * (3 + D) / q nu / (L : ℝ) := by
  classical
  obtain ⟨hPhi, hev, hground, huniq⟩ := hGS
  have hGS' : IsUniqueChainGroundState (openAnisotropicChainHamiltonianS L D) E0 Phi :=
    ⟨hPhi, hev, hground, huniq⟩
  obtain ⟨d1, hd1sq, hd1⟩ := edgeGroundCharacter hGS' (manyBodyReversalS_mul_self (Fin L) 2)
    (manyBodyReversalS_commute_openAnisotropicChainHamiltonianS L D)
  obtain ⟨d3, hd3sq, hd3⟩ := edgeGroundCharacter hGS' magParityDiagS_mul_self
    (magParityDiagS_commute_openAnisotropicChainHamiltonianS L D)
  have hd1ne : d1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hd1sq; exact zero_ne_one hd1sq
  have hd3ne : d3 ≠ 0 := by
    intro h; rw [h, mul_zero] at hd3sq; exact zero_ne_one hd3sq
  set s : Fin 3 → ℂ := ![d1, -d1, -d1] with hsdef
  set t : Fin 3 → ℂ := ![-d3, -d3, d3] with htdef
  have hsval : ∀ nu : Fin 3, (if (0 : Fin 3) = nu then (1 : ℂ) else -1) * d1 = s nu := by
    intro nu; rw [hsdef]; fin_cases nu <;> simp +decide
  have htval : ∀ nu : Fin 3, (if (2 : Fin 3) = nu then (1 : ℂ) else -1) * d3 = t nu := by
    intro nu; rw [htdef]; fin_cases nu <;> simp +decide
  have hsne : ∀ nu : Fin 3, nu ≠ 0 → s nu = -d1 := by
    intro nu hnu
    rw [hsdef]
    fin_cases nu
    · exact absurd rfl hnu
    · simp
    · simp
  have htzero : t 0 = -d3 := by rw [htdef]; simp
  set v : Fin 3 → ((Fin L → Fin 3) → ℂ) :=
    fun nu => (edgeStringOrderOpS L nu).mulVec Phi with hvdef
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hPhiNorm : 0 < vecNormSqRe Phi := dotProduct_star_self_re_pos hPhi
  have hvne : ∀ nu : Fin 3, v nu ≠ 0 := by
    intro nu hzero
    have hb : q nu * (L : ℝ) ^ 2 * vecNormSqRe Phi ≤ vecNormSqRe (v nu) :=
      hasStringLRO_vecNormSqRe_bound L nu hPhi hLRO
    rw [hzero] at hb
    have h0 : vecNormSqRe (0 : (Fin L → Fin 3) → ℂ) = 0 := by
      simp [vecNormSqRe]
    rw [h0] at hb
    have hpos : 0 < q nu * (L : ℝ) ^ 2 * vecNormSqRe Phi := by
      have := hq nu; positivity
    linarith
  have hvmem : ∀ nu : Fin 3, v nu ∈ edgeCharacterSector L (s nu) (t nu) := by
    intro nu
    refine ⟨?_, ?_⟩
    · rw [← hsval nu]
      exact edgeTrialCharacter (manyBodyReversalS_mul_self (Fin L) 2)
        (manyBodyReversalS_conj_edgeStringOrderOpS L nu) hd1
    · rw [← htval nu]
      exact edgeTrialCharacter magParityDiagS_mul_self
        (magParityDiagS_conj_edgeStringOrderOpS L nu) hd3
  have hextract : ∀ nu : Fin 3, ∃ (En : ℝ) (Ps : (Fin L → Fin 3) → ℂ),
      Ps ∈ edgeCharacterSector L (s nu) (t nu) ∧ Ps ≠ 0 ∧
      (openAnisotropicChainHamiltonianS L D).mulVec Ps = (En : ℂ) • Ps ∧
      En ≤ E0 + 64 * (3 + D) / q nu / (L : ℝ) := by
    intro nu
    obtain ⟨En, Ps, hPs1, hPs2, hPs3, hPs4⟩ :=
      LatticeSystem.Math.exists_sector_eigenvector_energy_le_rayleigh
        (openAnisotropicChainHamiltonianS_isHermitian L D)
        (edgeCharacterSector L (s nu) (t nu))
        (edgeCharacterSector_invariant L D (s nu) (t nu)) (hvmem nu) (hvne nu)
    exact ⟨En, Ps, hPs1, hPs2, hPs3,
      le_trans hPs4 (edgeTrial_expectationRatioRe_le L hD nu (hq nu) hL hGS' hLRO)⟩
  choose E Psi hmem hne heig hle using hextract
  refine ⟨E, Psi, ?_, ?_⟩
  · -- linear independence via three distinct eigenvalues of `Θ + 2 P`
    have hinj : Function.Injective (fun nu : Fin 3 => s nu + 2 * t nu) := by
      have h1 : d1 = 1 ∨ d1 = -1 := mul_self_eq_one_iff.mp hd1sq
      have h3 : d3 = 1 ∨ d3 = -1 := mul_self_eq_one_iff.mp hd3sq
      intro a b hab
      simp only [hsdef, htdef] at hab
      fin_cases a <;> fin_cases b <;>
        first
          | rfl
          | (exfalso; rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;>
              rw [h1, h3] at hab <;> norm_num +decide at hab)
    refine Module.End.eigenvectors_linearIndependent'
      (Matrix.toLin' (manyBodyReversalS (Fin L) 2 + (2 : ℂ) • magParityDiagS (Fin L) 2))
      (fun nu => s nu + 2 * t nu) hinj Psi (fun nu => ⟨?_, hne nu⟩)
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.add_mulVec,
      Matrix.smul_mulVec, (hmem nu).1, (hmem nu).2, smul_smul, ← add_smul]
  · intro nu
    refine ⟨hne nu, heig nu, ?_, hle nu⟩
    have hge : E0 ≤ E nu := hground.2 _ ⟨Psi nu, hne nu, heig nu⟩
    rcases lt_or_eq_of_le hge with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨c, hc⟩ := huniq (Psi nu) (hne nu) (by rw [heig nu, ← heq])
      have hcne : c ≠ 0 := by
        intro h
        rw [h, zero_smul] at hc
        exact hne nu hc
      have h1 : (c * d1) • Phi = (s nu * c) • Phi := by
        have hstep : (manyBodyReversalS (Fin L) 2).mulVec (Psi nu) = s nu • Psi nu := (hmem nu).1
        rw [hc, Matrix.mulVec_smul, hd1, smul_smul, smul_smul] at hstep
        exact hstep
      have h3 : (c * d3) • Phi = (t nu * c) • Phi := by
        have hstep : (magParityDiagS (Fin L) 2).mulVec (Psi nu) = t nu • Psi nu := (hmem nu).2
        rw [hc, Matrix.mulVec_smul, hd3, smul_smul, smul_smul] at hstep
        exact hstep
      have hs1 : c * d1 = s nu * c := by
        have := sub_eq_zero.mpr h1
        rw [← sub_smul, smul_eq_zero] at this
        rcases this with h | h
        · linear_combination h
        · exact absurd h hPhi
      have hs3 : c * d3 = t nu * c := by
        have := sub_eq_zero.mpr h3
        rw [← sub_smul, smul_eq_zero] at this
        rcases this with h | h
        · linear_combination h
        · exact absurd h hPhi
      have hd1' : d1 = s nu := by
        rw [mul_comm c d1] at hs1
        exact mul_right_cancel₀ hcne hs1
      have hd3' : d3 = t nu := by
        rw [mul_comm c d3] at hs3
        exact mul_right_cancel₀ hcne hs3
      by_cases hnu0 : nu = 0
      · subst hnu0
        rw [htzero] at hd3'
        exact hd3ne (by linear_combination hd3' / 2)
      · rw [hsne nu hnu0] at hd1'
        exact hd1ne (by linear_combination hd1' / 2)

/-! ## The capstone -/

/-- **Tasaki Theorem 8.2 (hidden order forces edge states).**  Fix the anisotropy `D ≥ 0` and
hidden-order constants `q_α > 0`.  Then there is an eventual threshold `L₀` and **`L`-independent**
constants `C_ν > 0` such that: for every `L ≥ L₀`, whenever `Φ` is the **unique** ground state of
the *open-chain* Hamiltonian `Ĥ_D^open` at ground energy `E₀` (`IsUniqueChainGroundState`)
exhibiting hidden antiferromagnetic order (`HasStringLRO L Φ q`, the bound (8.1.10)), there exist
**three nonzero, mutually linearly independent excited states** `Ψ_ν` (`ν : Fin 3`) with energies
`E_ν` satisfying `Ĥ_D^open Ψ_ν = E_ν Ψ_ν` and `E₀ < E_ν ≤ E₀ + C_ν / L`.  Hidden antiferromagnetic
order thus forces a near four-fold degeneracy of low-lying states — the free `S = 1/2` spins at the
two open ends.

The constants `C_ν = 64 (3 + D) / q_ν` are chosen outside `∀ L`, so the `O(1/L)` splitting is
genuinely length-uniform; `0 ≤ D` enters through their positivity.  The eventual quantifier `∃ L₀`
matches the source's "at least for sufficiently large `L`" in (8.1.10); the source gives no
numerical threshold and none is needed here, so `L₀ = 1` is taken.  The conjunct `Ψ_ν ≠ 0` is
formally implied by `LinearIndependent ℂ Ψ` and is stated anyway, since an eigen-equation without
it is vacuous.

Proved by the Horsch–von der Linden / Koma–Tasaki variational argument, as in Theorem 3.1. -/
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
  refine ⟨1, fun nu => 64 * (3 + D) / q nu, fun nu => by have := hq nu; positivity, ?_⟩
  intro L hL E0 Phi hGS hLRO
  exact tasaki_theorem_8_2_fixed_volume L hL D hD q hq E0 Phi hGS hLRO

end LatticeSystem.Quantum
