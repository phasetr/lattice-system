/-
# Tasaki §7.1.3 (AKLT uniqueness), the capstone: uniqueness of the ring ground state

This file discharges the **uniqueness conjunct** of the AKLT main theorem (Tasaki Theorem 7.1,
`aklt_theorem_7_1`, conjunct (4)) as an independent theorem, mirroring the Knabe-gap precedent
`aklt_knabe_ring_gap`. This result now forms part of the theorem `aklt_theorem_7_1` (in
`AKLTTheorem71.lean`), composed together with the gap and correlation results.

Two ingredients are assembled:

* **Spectral bridge** (`ground_eigen_isVBSGroundForm`): a ground-energy eigenvector of the AKLT
  ring Hamiltonian lies in every bond kernel.  Via the affine identity
  `Ĥ_AKLT = 2 Ĥ' − (2/3)L` (`akltHamiltonianS_eq_affine_ringProjHamiltonianS`), eigenvalue
  `−(2/3)L` forces `Ĥ' Ψ = 0`; frustration-freeness (`frustration_free_local_eigen`, Tasaki
  Lemma A.10, with all local energies `0`) then annihilates every bond projection, and Lemma 7.4
  (`tasaki_lemma_7_4`) yields `IsVBSGroundForm L x Ψ` at every bond.

* **Polynomial one-dimensionality** (`weylMap_ground_form_eq_const_smul_prod`, Stage C): every such
  `Ψ` has `weylMap Ψ = C c · ∏_x f_x`.  Applying this to both `Ψ` and the explicit VBS state
  `akltVBSState (n+1)` (whose Weyl image is nonzero, hence `c₀ ≠ 0`) gives
  `weylMap Ψ = weylMap ((c/c₀) • akltVBSState (n+1))`; injectivity of `weylMap`
  (`weylMap_injective`) concludes `Ψ = (c/c₀) • akltVBSState (n+1)`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3 "The Uniqueness of the Ground State", pp. 186–188, Lemma 7.4, eqs. (7.1.22)–(7.1.25);
proof due to Kennedy–Lieb–Tasaki [41].
-/
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.ProductBondDivisibility
import LatticeSystem.Quantum.SpinS.AKLTKnabe.KnabeGapD7d

open MvPolynomial Matrix

namespace LatticeSystem.Quantum

open LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

variable {L : ℕ}

/-- **Spectral bridge (Tasaki §7.1.3, Lemma A.10 direction).**  A nonzero ground-energy eigenvector
`Ψ` of the AKLT ring Hamiltonian — eigenvalue `−(2/3)L` — has the VBS singlet form at every bond of
the ring.  The affine identity turns the eigen-equation into `Ĥ' Ψ = 0`, frustration-freeness makes
`Ψ` a zero mode of every bond projection (`frustration_free_local_eigen`), and Lemma 7.4 identifies
each zero mode with `IsVBSGroundForm L x Ψ`. -/
theorem ground_eigen_isVBSGroundForm [NeZero L] (hL : 2 ≤ L) (Ψ : (Fin L → Fin 3) → ℂ)
    (hev : (akltHamiltonianS L).mulVec Ψ = ((-(2 : ℝ) / 3 * (L : ℝ) : ℝ) : ℂ) • Ψ) :
    ∀ x : Fin L, IsVBSGroundForm L x Ψ := by
  have haff := akltHamiltonianS_eq_affine_ringProjHamiltonianS (L := L)
  rw [haff] at hev
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hev
  have h2 : ((2 : ℝ) : ℂ) • (ringProjHamiltonianS L).mulVec Ψ = 0 := by
    have h := congrArg (· - ((-(2 : ℝ) / 3 * (L : ℝ) : ℝ) : ℂ) • Ψ) hev
    simpa using h
  have hX0 : (ringProjHamiltonianS L).mulVec Ψ = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  simp only [ringProjHamiltonianS] at hX0
  have hgs : (∑ y ∈ (Finset.univ : Finset (Fin L)), ringBond y).mulVec Ψ
      = ((∑ _y ∈ (Finset.univ : Finset (Fin L)), (0 : ℝ) : ℝ) : ℂ) • Ψ := by
    rw [hX0]; simp
  have hloc := frustration_free_local_eigen Finset.univ (fun y : Fin L => ringBond y)
    (fun _ => (0 : ℝ)) Ψ (fun y _ => by simpa using posSemidef_ringBond hL y) hgs
  intro x
  have hb : (bondSpin2ProjectionS x (ringSucc x)).mulVec Ψ = 0 := by
    have hbx := hloc x (Finset.mem_univ x)
    rw [ringSucc_eq_add_one]
    simpa [ringBond] using hbx
  exact (tasaki_lemma_7_4 (by omega : 1 < L) x Ψ).mp hb

/-- **Tasaki Theorem 7.1, uniqueness conjunct (§7.1.3), PROVED.**  For every ring of length
`L = n + 1 ≥ 3`, any nonzero eigenvector `Ψ` of the AKLT ring Hamiltonian `Ĥ_AKLT` at the ground
energy `E₀ = −(2/3)(n+1)` is a scalar multiple of the explicit valence-bond-solid state
`akltVBSState (n+1)`: the ground space is one-dimensional.

This is exactly conjunct (4) of the theorem `aklt_theorem_7_1` (in `AKLTTheorem71.lean`), proved
independently and now composed together with the gap and correlation results (cf. the Knabe-gap
precedent `aklt_knabe_ring_gap`). The proof combines the spectral bridge
(`ground_eigen_isVBSGroundForm`) with polynomial one-dimensionality
(`weylMap_ground_form_eq_const_smul_prod`) and Weyl-map injectivity (`weylMap_injective`),
following Kennedy–Lieb–Tasaki [41].

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3, Lemma 7.4, eqs. (7.1.22)–(7.1.25), pp. 186–188. -/
theorem aklt_ring_ground_state_unique (n : ℕ) (hn : 2 ≤ n)
    (Ψ : (Fin (n + 1) → Fin 3) → ℂ) (hΨ0 : Ψ ≠ 0)
    (hev : (akltHamiltonianS (n + 1)).mulVec Ψ
        = ((-(2 : ℝ) / 3 * ((n : ℝ) + 1) : ℝ) : ℂ) • Ψ) :
    ∃ c : ℂ, Ψ = c • akltVBSState (n + 1) := by
  have hcast : (-(2 : ℝ) / 3 * ((n : ℝ) + 1)) = (-(2 : ℝ) / 3 * ((n + 1 : ℕ) : ℝ)) := by
    push_cast; ring
  rw [hcast] at hev
  have hΨvbs : ∀ x : Fin (n + 1), IsVBSGroundForm (n + 1) x Ψ :=
    ground_eigen_isVBSGroundForm (by omega) Ψ hev
  obtain ⟨c, hc⟩ := weylMap_ground_form_eq_const_smul_prod (by omega) Ψ hΨ0 hΨvbs
  have hΦvbs : ∀ x : Fin (n + 1), IsVBSGroundForm (n + 1) x (akltVBSState (n + 1)) :=
    fun x => akltVBSState_isVBSGroundForm (by omega) x
  have hΦ0 : akltVBSState (n + 1) ≠ 0 := akltVBSState_ne_zero (by omega)
  obtain ⟨c₀, hc₀⟩ :=
    weylMap_ground_form_eq_const_smul_prod (by omega) (akltVBSState (n + 1)) hΦ0 hΦvbs
  have hΦne : weylMap (akltVBSState (n + 1)) ≠ 0 := by
    have h := weylMap_injective.ne hΦ0
    simpa using h
  have hc₀0 : c₀ ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hc₀; exact hΦne hc₀
  refine ⟨c / c₀, ?_⟩
  apply weylMap_injective
  have hCeq : (C c : MvPolynomial (Fin (n + 1) × Fin 2) ℂ) = C (c / c₀) * C c₀ := by
    rw [← map_mul, div_mul_cancel₀ c hc₀0]
  rw [hc, map_smul, hc₀, smul_eq_C_mul, hCeq, mul_assoc]

end LatticeSystem.Quantum
