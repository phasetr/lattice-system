import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpanning
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMultiplet
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardKineticSpinBounds
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrial
import LatticeSystem.Math.MonotoneEnumeration

/-!
# Algebraic ingredients of the ferromagnetic energy floor (Tasaki §11.1.1)

The low-density impossibility argument compares the energy of a trial state against the energy a
fully spin-polarized state must at least have.  The lower bound is obtained by reading the energy
of a top-weight state as a *weighted* sum of the single-particle levels, with weights given by the
eigenmode occupations; the facts collected here are what makes that reading possible, and the
floor bound itself is assembled from them at the end of the module.

* **The occupation of an eigenmode never exceeds one**: `1 − n̂_{j,σ}` is positive-semidefinite,
  because the dual canonical anticommutation relation turns it into the Gram matrix `Ĉ·Ĉᴴ` of the
  eigenmode annihilator.  This is the Pauli exclusion input that caps each weight at `1`.
* **The on-site interaction annihilates a fully polarized state**: every term of `Ĥ_int` ends in a
  down annihilation, so a state without spin-down electrons has zero interaction energy — the
  reason the floor holds for every `U ≥ 0` with no `U`-dependent correction.
* **A top-weight state is fully polarized**: `N̂_tot = N̂_↑ + N̂_↓` and `Ŝᶻ_tot = (N̂_↑ − N̂_↓)/2`
  are operator identities, so an eigenvector with `N̂_tot = Ne` and `Ŝᶻ_tot = Ne/2` has `N̂_↓ = 0`
  outright, with no enumeration of the occupation configurations.
* **The floor itself**: the occupations are a `[0,1]`-valued weight family of total mass `Ne`, so
  the fractional-knapsack bound places the sum of the `Ne` lowest levels below the kinetic Rayleigh
  quotient — no enumeration of Slater determinants, and hence no restriction on the filling.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1, eqs. (11.1.5)/(11.1.6), p. 375, and §11.1.1, Theorem 11.4, eqs. (11.1.8)–(11.1.10),
p. 376; the underlying argument is Tasaki, Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3,
Appendix F, eqs. (F.12)/(F.13), p. 546.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math

open scoped BigOperators ComplexOrder

variable {M : ℕ}

open scoped ComplexOrder in
/-- **An eigenmode is occupied at most once**: `1 − n̂_{j,σ}` is positive-semidefinite.

Writing `A = Ĉ_σ(ē_j)` for the eigenmode annihilator, the dual canonical anticommutation relation
reads `A·Aᴴ + Aᴴ·A = 1`, and `n̂_{j,σ} = Aᴴ·A`, so `1 − n̂_{j,σ} = A·Aᴴ` is a Gram matrix.  This is
the Pauli exclusion bound complementing `eigenNumberOp_posSemidef`: together they confine the
expectation of `n̂_{j,σ}` to `[0, 1]`. -/
theorem one_sub_eigenNumberOp_posSemidef
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (j : Fin (M + 1)) (σ : Fin 2) :
    ((1 : ManyBodyOp (Fin (2 * M + 2))) - eigenNumberOp hT j σ).PosSemidef := by
  set A := spinfulAnnihilationFromVector M
    (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ with hA
  have hC : spinfulCreationFromVector M (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) σ = Aᴴ := by
    rw [hA, spinfulAnnihilationFromVector_conjTranspose, star_star]
  have hanti := eigenbasis_dual_annihilation_creation_anticomm hT j j σ σ
  rw [if_pos ⟨rfl, rfl⟩, one_smul, ← hA, hC] at hanti
  rw [eigenNumberOp, ← hA, hC, ← hanti, add_sub_cancel_right]
  exact Matrix.posSemidef_self_mul_conjTranspose A

/-- **The on-site interaction annihilates a fully polarized state**: `N̂_↓Φ = 0` implies
`Ĥ_intΦ = 0`.

Every summand of `Ĥ_int = U Σ_i n̂_{i,↑}n̂_{i,↓}` ends in the down annihilator `ĉ_{i,↓}`, which
kills `Φ` by `fermionDownAnnihilation_mulVec_eq_zero_of_downNumber_zero`.  This is the interaction
sibling of `hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero`, and is what makes the
ferromagnetic floor independent of `U`. -/
theorem hubbardOnSiteInteraction_mulVec_eq_zero_of_downNumber_zero (M : ℕ) (U : ℂ)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (hubbardOnSiteInteraction M U).mulVec Φ = 0 := by
  rw [hubbardOnSiteInteraction, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    show fermionDownNumber M i
        = fermionMultiCreation (2 * M + 1) (spinfulIndex M i 1) * fermionDownAnnihilation M i
      from rfl,
    ← Matrix.mulVec_mulVec, fermionDownAnnihilation_mulVec_eq_zero_of_downNumber_zero M i hΦ,
    Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]

/-- **A top-weight state is fully polarized**: an `Ne`-electron eigenvector of `Ŝᶻ_tot` with the
maximal weight `Ne/2` carries no spin-down electrons, `N̂_↓u = 0`.

`N̂_tot = N̂_↑ + N̂_↓` and `Ŝᶻ_tot = (N̂_↑ − N̂_↓)/2` are operator identities, so the two eigenvalue
equations say `N̂_↑u + N̂_↓u = Ne·u` and `N̂_↑u − N̂_↓u = Ne·u`; subtracting gives `2N̂_↓u = 0`.  No
enumeration of the occupation configurations is involved, so this holds at every electron
number. -/
theorem fermionTotalDownNumber_mulVec_eq_zero_of_topWeight {N Ne : ℕ}
    {u : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec u = ((Ne : ℕ) : ℂ) • u)
    (hZ : (fermionTotalSpinZ N).mulVec u = (((Ne : ℝ) / 2 : ℝ) : ℂ) • u) :
    (fermionTotalDownNumber N).mulVec u = 0 := by
  rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec] at hN
  rw [fermionTotalSpinZ, Matrix.smul_mulVec, Matrix.sub_mulVec] at hZ
  have hdiff : (fermionTotalUpNumber N).mulVec u - (fermionTotalDownNumber N).mulVec u
      = ((Ne : ℕ) : ℂ) • u := by
    have hscale := congrArg (fun x => (2 : ℂ) • x) hZ
    simp only [smul_smul] at hscale
    rw [show (2 : ℂ) * (1 / 2) = 1 by ring, one_smul] at hscale
    rw [hscale]
    congr 1
    push_cast
    ring
  funext w
  have hw := congrFun hN w
  have hw' := congrFun hdiff w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hw hw'
  change (fermionTotalDownNumber N).mulVec u w = 0
  linear_combination (hw - hw') / 2

/-- **The ferromagnetic energy floor**: a fully polarized `Ne`-electron state has kinetic energy at
least the sum of the `Ne` lowest single-particle levels,
`(∑_{i<Ne} ε_i)·‖u‖² ≤ ⟨u, Ĥ_kin u⟩`.

The weights are the eigenmode occupations `w_j = ⟨u, n̂_{j↑}u⟩/‖u‖²`.  They lie in `[0,1]` by
`eigenNumberOp_posSemidef` and `one_sub_eigenNumberOp_posSemidef`, and they sum to `Ne` because
`∑_j n̂_{j↑} = N̂_↑` and `N̂_↓u = 0` turns the total-number equation into `N̂_↑u = Ne·u`.  The
kinetic energy is `∑_j ε_j w_j ‖u‖²` since the spin-down kinetic block annihilates `u`, so the
bound is exactly the fractional-knapsack lemma
`sum_lowestLevels_le_sum_weighted_of_map_eq` read against the unsorted spectrum.

Because the weights are fractional occupations rather than a choice of occupied orbitals, no
enumeration of Slater determinants is needed and the bound holds at every filling `Ne ≤ M + 1`.
This is Tasaki's step (F.13) of Prog. Theor. Phys. **99** (1998) 489, Appendix F, p. 546. -/
theorem sum_lowestLevels_mul_le_rayleighOnVec_hubbardKinetic
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) {Ne : ℕ}
    (hk : Ne ≤ M + 1) {ε : Fin (M + 1) → ℝ} (hmono : Monotone ε)
    (hspec : (Finset.univ : Finset (Fin (M + 1))).val.map ε
      = (Finset.univ : Finset (Fin (M + 1))).val.map hT.eigenvalues)
    {u : (Fin (2 * M + 2) → Fin 2) → ℂ} (hu0 : u ≠ 0)
    (hdown : (fermionTotalDownNumber M).mulVec u = 0)
    (hnum : (fermionTotalNumber (2 * M + 1)).mulVec u = ((Ne : ℕ) : ℂ) • u) :
    (∑ i : Fin Ne, ε (Fin.castLE hk i)) * (star u ⬝ᵥ u).re
      ≤ rayleighOnVec (hubbardKinetic M t) u := by
  set P : ℝ := (star u ⬝ᵥ u).re with hPdef
  have hP : 0 < P := dotProduct_star_self_re_pos hu0
  set mm : Fin (M + 1) → ℝ := fun j => rayleighOnVec (eigenNumberOp hT j 0) u with hmmdef
  have hup : (fermionTotalUpNumber M).mulVec u = ((Ne : ℕ) : ℂ) • u := by
    rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec, hdown, add_zero] at hnum
    exact hnum
  have hmm0 : ∀ j, 0 ≤ mm j := by
    intro j
    have h := (eigenNumberOp_posSemidef hT j 0).re_dotProduct_nonneg u
    simpa [hmmdef, rayleighOnVec, RCLike.re_to_complex] using h
  have hmm1 : ∀ j, mm j ≤ P := by
    intro j
    have h := (one_sub_eigenNumberOp_posSemidef hT j 0).re_dotProduct_nonneg u
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec] at h
    simp only [RCLike.re_to_complex, Complex.sub_re] at h
    simp only [hmmdef, rayleighOnVec, hPdef]
    linarith
  set w : Fin (M + 1) → ℝ := fun j => mm j / P with hwdef
  have hw0 : ∀ j, 0 ≤ w j := fun j => div_nonneg (hmm0 j) (le_of_lt hP)
  have hw1 : ∀ j, w j ≤ 1 := fun j => (div_le_one hP).mpr (hmm1 j)
  have hsummm : ∑ j, mm j = (Ne : ℝ) * P := by
    have h1 : ∑ j, mm j = rayleighOnVec (∑ j : Fin (M + 1), eigenNumberOp hT j 0) u := by
      rw [rayleighOnVec_sum]
    rw [h1, show (∑ j : Fin (M + 1), eigenNumberOp hT j 0) = fermionTotalUpNumber M from
      (sum_eigenNumberOp_eq_sum_spinSiteNumber hT 0).trans rfl]
    unfold rayleighOnVec
    rw [hup, dotProduct_smul, smul_eq_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  have hsumw : ∑ j, w j = (Ne : ℝ) := by
    rw [hwdef]
    simp only
    rw [← Finset.sum_div, hsummm, mul_div_assoc, div_self (ne_of_gt hP), mul_one]
  have hkin : rayleighOnVec (hubbardKinetic M t) u = ∑ j, hT.eigenvalues j * mm j := by
    rw [hubbardKinetic_eq_hubbardKineticSpin_add, rayleighOnVec_add_matrix]
    have hzero : rayleighOnVec (hubbardKineticSpin M t 1) u = 0 := by
      unfold rayleighOnVec
      rw [hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero M t hdown, dotProduct_zero]
      exact Complex.zero_re
    rw [hzero, add_zero, hubbardKineticSpin_eq_sum_eigenNumberOp hT 0, rayleighOnVec_sum]
    exact Finset.sum_congr rfl fun j _ => rayleighOnVec_real_smul _ _ _
  have hW2 := sum_lowestLevels_le_sum_weighted_of_map_eq hk hmono hspec hw0 hw1 hsumw
  have hrw : ∑ j, hT.eigenvalues j * w j = (∑ j, hT.eigenvalues j * mm j) / P := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by rw [hwdef]; simp only; ring
  rw [hrw, le_div_iff₀ hP] at hW2
  rw [hkin]
  exact hW2

end LatticeSystem.Fermion
