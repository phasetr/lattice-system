import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismGroundTower
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCorrelation

/-!
# §10.2.3 (Theorem 10.6): the centered tower member carries Theorem 10.5's correlation signs

The ground multiplet of Lieb's half-filled repulsive Hubbard model is the lowering tower
`(Ŝ⁻_tot)^k w` (`k = 0, …, L`, `L := sublatticeImbalance A`) of a highest-weight ground vector `w`
(`LiebFerrimagnetismGroundTower.lean`).  Tasaki's ferrimagnetic bound (10.2.17) is evaluated on the
**centered** member of that tower, `k₀ := L / 2` (ℕ division), because that is where Tasaki proves
eq. (10.2.17): at the tower weight closest to `Ŝ³ = 0`, `L/2 − k₀ = (L % 2)/2`. Admissibility
for Theorem 10.5 (`theorem_10_5_shen_qiu_tian_transverse_sign`) is not what singles out `k₀`: the
`k`-th tower member's electron number `Ne_k := N + 1 + L − 2k` is even for *every* `k`
(`L` and `N + 1` have equal parity), and its sector `Ŝ³ = (Ne_k − (N+1))/2` is admissible whenever
`|L − 2k| < N + 1`, which holds for all `k` except the two extremes `k ∈ {0, L}` in the degenerate
case `L = N + 1`.

This module performs that identification and transports Theorem 10.5's sign pattern onto the
centered tower member:

* `liebRepulsive_groundEnergy_eq_ofReal` — the ground energy `E₀` of a nonzero `(N+1)`-electron
  ground submodule is real (Hermiticity of the symmetric repulsive Hamiltonian);
* `liebRepulsive_sectorGroundEnergy_eq_groundEnergy` — the sector ground energy `E` equals `E₀.re`,
  by a two-sided pinch: the sector ground state sits at half filling (so `E₀.re ≤ E`), while the
  centered tower member is an `E₀.re`-eigenvector inside the sector (so `E ≤ E₀.re`);
* `liebRepulsive_centered_eq_smul_sectorGround` — hence the centered tower member is a nonzero
  multiple of Theorem 10.5's unique sector ground state;
* `liebRepulsive_centered_transverse_sign` — the transverse correlation on the centered tower
  member is real, strictly positive on a sublattice and strictly negative across sublattices, the
  squared modulus of the rescaling factor being harmless;
* `liebRepulsive_exists_centered_transverse_sign` — the existential capstone that supplies a single
  highest-weight ground vector `w` carrying both the weight equation and the sign pattern.

Theorem 10.4's conclusions enter as hypotheses (`hne`, `hmin`, `hcas`) and Theorem 10.5's model
hypotheses (`hbip`, `hT_conn`, `hU`) are carried explicitly; the sector side conditions need only
`1 ≤ N` on top of them.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.2 (Theorems 10.4/10.5, pp. 350–353) and §10.2.3, p. 356,
eqs. (10.2.16)/(10.2.17).
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math

/-! ## Centered-weight arithmetic -/

/-- **Parity of the sublattice imbalance.**  `L := ||A| − |B||` has the parity of the site count
`N + 1`, since `|A| + |B| = N + 1` and `|A| − |B| ≡ |A| + |B| (mod 2)`.  Stated with `%` rather
than `Even` so that the downstream electron-number side conditions are `omega`-shaped. -/
private theorem liebRepulsive_sublatticeImbalance_mod_two {N : ℕ} (A : Finset (Fin (N + 1))) :
    sublatticeImbalance A % 2 = (N + 1) % 2 := by
  have hcard := bipartitionComplement_card_add N A
  rw [sublatticeImbalance]
  omega

/-- **The centered tower weight is Theorem 10.5's sector parameter.**  At the centered exponent
`k₀ = L / 2` (ℕ division) the tower weight `L/2 − k₀` equals the spin-`z` value
`(Ne₀ − (N+1))/2` of the electron number `Ne₀ = N + 1 + L % 2`: both sides are
`(L % 2)/2 ∈ {0, 1/2}`. -/
private theorem liebRepulsive_centeredWeight_eq {N : ℕ} (A : Finset (Fin (N + 1))) :
    (sublatticeImbalance A : ℂ) / 2 - ((sublatticeImbalance A / 2 : ℕ) : ℂ)
      = (((N + 1 + sublatticeImbalance A % 2 : ℕ) : ℂ) - ((N : ℂ) + 1)) / 2 := by
  have hdm : ((2 * (sublatticeImbalance A / 2) + sublatticeImbalance A % 2 : ℕ) : ℂ)
      = ((sublatticeImbalance A : ℕ) : ℂ) := by
    rw [Nat.div_add_mod]
  push_cast at hdm ⊢
  linear_combination -hdm / 2

/-- **State scaling of the raw expectation.**  `⟨c v| O |c v⟩ = (c* c) ⟨v| O |v⟩`: rescaling the
*state* multiplies `vectorExpectation` by the squared modulus of the factor (as opposed to
rescaling the *observable*, which is `euclideanExpectation_smul`). -/
private theorem vectorExpectation_smul_vector {N : ℕ} (O : ManyBodyOp (Fin (2 * N + 2))) (c : ℂ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    vectorExpectation O (c • v) = (star c * c) * vectorExpectation O v := by
  unfold vectorExpectation
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]

/-! ## Realification of the ground energy -/

/-- **The half-filling ground energy is real.**  If the `(N+1)`-electron ground submodule of the
symmetric repulsive Hubbard Hamiltonian at `E₀` is nonzero, then `E₀` is the complex cast of its
own real part, because the Hamiltonian is Hermitian for a symmetric hopping matrix
(`symmetricRepulsiveHubbardHamiltonian_isHermitian`) and a Hermitian matrix has real eigenvalues
(`isHermitian_mulVec_eigenvalue_eq_ofReal`).  This is what lets the ground energy be fed to the
`ℝ`-valued ground-state predicate `IsUniqueGroundStateOn`. -/
theorem liebRepulsive_groundEnergy_eq_ofReal (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥) :
    ((E₀.re : ℝ) : ℂ) = E₀ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
  obtain ⟨μ, hμ⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (symmetricRepulsiveHubbardHamiltonian_isHermitian N T hT U) hv0 hv.1
  rw [← hμ, Complex.ofReal_re]

/-! ## The centered tower member inside the spin-`z` sector -/

/-- **The centered tower member lies in Theorem 10.5's sector.**  Lowering a highest-weight vector
`k₀ = L/2` times produces a `Ŝ³_tot`-eigenvector of weight `L/2 − k₀`
(`fermionTotalSpinZ_mulVec_spinMinusPow_general`), which `liebRepulsive_centeredWeight_eq`
identifies with the sector parameter of the electron number `Ne₀ = N + 1 + L % 2`; the Pi carrier
is crossed to `EuclideanSpace` by `mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul`. -/
private theorem liebRepulsive_centered_mem_spinZSector {N : ℕ} (A : Finset (Fin (N + 1)))
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    (WithLp.toLp 2 (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)
        : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
      ∈ spinZSectorEuclidean N
        ((((N + 1 + sublatticeImbalance A % 2 : ℕ) : ℂ) - ((N : ℂ) + 1)) / 2) := by
  have hw := fermionTotalSpinZ_mulVec_spinMinusPow_general N w
    ((sublatticeImbalance A : ℂ) / 2) (sublatticeImbalance A / 2) hz
  rw [liebRepulsive_centeredWeight_eq A] at hw
  rw [spinZSectorEuclidean, Module.End.mem_eigenspace_iff,
    ← mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul]
  exact hw

/-! ## The sector ground energy is the half-filling ground energy -/

/-- **The centered sector's ground energy is the half-filling ground energy.**  Let `E` be the
ground energy on the centered spin-`z` sector `Ŝ³ = (Ne₀ − (N+1))/2` (`Ne₀ = N + 1 + L % 2`) and
`E₀` the `(N+1)`-electron ground energy.  Then `E = E₀.re`, by a two-sided pinch: the sector ground
state `φ` carries the half-filling number eigenvalue `hφN`, so it lies in the `(N+1)`-electron
`E`-ground submodule and `hmin` gives `E₀.re ≤ E`; conversely the centered tower member is a
nonzero `E₀.re`-eigenvector inside the sector (`liebRepulsive_ground_tower_ne_zero`,
`liebRepulsive_ground_spinMinusPow_mem`, `liebRepulsive_centered_mem_spinZSector`), so the
minimality clause of `IsGroundEigenvalueOn` gives `E ≤ E₀.re`. -/
theorem liebRepulsive_sectorGroundEnergy_eq_groundEnergy (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hE₀ : ((E₀.re : ℝ) : ℂ) = E₀)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn
      (spinZSectorEuclidean N
        ((((N + 1 + sublatticeImbalance A % 2 : ℕ) : ℂ) - ((N : ℂ) + 1)) / 2))
      (symmetricRepulsiveHubbardHamiltonian N T U) E φ)
    (hφN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ = ((N : ℂ) + 1) • φ) :
    E = E₀.re := by
  obtain ⟨-, hφnorm, hφeig, hφground, -⟩ := hGS
  have hφne : φ ≠ 0 := fun h => by rw [h, norm_zero] at hφnorm; exact one_ne_zero hφnorm.symm
  obtain ⟨u, rfl⟩ : ∃ u : (Fin (2 * N + 2) → Fin 2) → ℂ, φ = WithLp.toLp 2 u :=
    ⟨WithLp.ofLp φ, rfl⟩
  rw [← mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul] at hφeig hφN
  rw [ne_eq, WithLp.toLp_eq_zero] at hφne
  have htower := liebRepulsive_ground_spinMinusPow_mem N T hT U E₀ hwG (sublatticeImbalance A / 2)
  rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at htower
  refine le_antisymm (hφground.2 E₀.re ⟨WithLp.toLp 2 (((fermionTotalSpinMinus N) ^
    (sublatticeImbalance A / 2)).mulVec w), liebRepulsive_centered_mem_spinZSector A hz, ?_, ?_⟩) ?_
  · rw [ne_eq, WithLp.toLp_eq_zero]
    exact liebRepulsive_ground_tower_ne_zero N A T U E₀ hcas hw0 hwG hz _ (Nat.div_le_self _ _)
  · rw [← mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul, hE₀]
    exact htower.1
  · have humem : u ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) (E : ℂ) (N + 1) := by
      rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
        Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply]
      refine ⟨hφeig, ?_⟩
      push_cast
      exact hφN
    have hle := hmin (E : ℂ) ((Submodule.ne_bot_iff _).mpr ⟨u, humem, hφne⟩)
    rwa [Complex.ofReal_re] at hle

/-! ## Collinearity with the sector ground state -/

/-- **The centered tower member is a multiple of the sector ground state.**  Under the hypotheses
of `liebRepulsive_sectorGroundEnergy_eq_groundEnergy`, the centered tower member
`(Ŝ⁻_tot)^{k₀} w` (`k₀ = L/2`) is `c • φ` for a nonzero `c`: the energy match turns it into an
`E`-eigenvector inside the sector, so the uniqueness clause of `IsUniqueGroundStateOn` applies, and
`c ≠ 0` because the tower member itself is nonzero. -/
theorem liebRepulsive_centered_eq_smul_sectorGround (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hE₀ : ((E₀.re : ℝ) : ℂ) = E₀)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn
      (spinZSectorEuclidean N
        ((((N + 1 + sublatticeImbalance A % 2 : ℕ) : ℂ) - ((N : ℂ) + 1)) / 2))
      (symmetricRepulsiveHubbardHamiltonian N T U) E φ)
    (hφN : Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) φ = ((N : ℂ) + 1) • φ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (WithLp.toLp 2 (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)
          : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) = c • φ := by
  have hE := liebRepulsive_sectorGroundEnergy_eq_groundEnergy N A T hT U E₀ hmin hE₀ hcas hw0 hwG
    hz hGS hφN
  have hne0 : ((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w ≠ 0 :=
    liebRepulsive_ground_tower_ne_zero N A T U E₀ hcas hw0 hwG hz _ (Nat.div_le_self _ _)
  have htower := liebRepulsive_ground_spinMinusPow_mem N T hT U E₀ hwG (sublatticeImbalance A / 2)
  rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at htower
  have heig : Matrix.toEuclideanLin (symmetricRepulsiveHubbardHamiltonian N T U)
      (WithLp.toLp 2 (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w))
      = (E : ℂ) • (WithLp.toLp 2
        (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)) := by
    rw [← mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul, hE, hE₀]
    exact htower.1
  obtain ⟨c, hc⟩ := hGS.2.2.2.2 _ (liebRepulsive_centered_mem_spinZSector A hz) heig
  refine ⟨c, ?_, hc⟩
  intro hc0
  rw [hc0, zero_smul, WithLp.toLp_eq_zero] at hc
  exact hne0 hc

/-! ## Transport of Theorem 10.5's correlation signs -/

/-- **Theorem 10.5's transverse signs on the centered tower member.**  Under the hypotheses of
Theorem 10.4 (`hne`, `hmin`, `hcas`) and of Theorem 10.5 (symmetric bipartite connected hopping,
on-site repulsion) together with `1 ≤ N`, the transverse spin correlation
`⟨Ŝ⁽¹⁾_x Ŝ⁽¹⁾_y + Ŝ⁽²⁾_x Ŝ⁽²⁾_y⟩` evaluated on the centered tower member `(Ŝ⁻_tot)^{k₀} w`
(`k₀ = L/2`) is real, strictly positive when `x, y` share a sublattice and strictly negative
otherwise.

The electron number `Ne₀ = N + 1 + L % 2` is even by `liebRepulsive_sublatticeImbalance_mod_two`
and satisfies `0 < Ne₀ < 2(N+1)`, so Theorem 10.4's general-sector uniqueness supplies the sector
ground state `φ`; `liebRepulsive_centered_eq_smul_sectorGround` identifies the centered tower
member with `c • φ`, and the rescaling only multiplies the expectation by `|c|² > 0`. -/
theorem liebRepulsive_centered_transverse_sign (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (hN : 1 ≤ N) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y)
          (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).im = 0 ∧
        (SameSublattice A x y →
            0 < (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re < 0) := by
  have hpar := liebRepulsive_sublatticeImbalance_mod_two A
  obtain ⟨E, φ, φattr, hGS, -, -, hφN⟩ := repulsiveSpinZSector_ground_unique N
    (N + 1 + sublatticeImbalance A % 2) (Nat.even_iff.mpr (by omega)) (by omega) (by omega)
    T hT hbip hT_conn U hU
  have hsign := theorem_10_5_shen_qiu_tian_transverse_sign N
    (N + 1 + sublatticeImbalance A % 2) (Nat.even_iff.mpr (by omega)) (by omega) (by omega)
    T hT hbip hT_conn U hU hGS
  obtain ⟨c, hc0, hceq⟩ := liebRepulsive_centered_eq_smul_sectorGround N A T hT U E₀ hmin
    (liebRepulsive_groundEnergy_eq_ofReal N T hT U E₀ hne) hcas hw0 hwG hz hGS hφN
  have hvec : ((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w
      = c • WithLp.ofLp φ := by
    have h := congrArg WithLp.ofLp hceq
    rwa [WithLp.ofLp_toLp, WithLp.ofLp_smul] at h
  have hstar : star c * c = ((Complex.normSq c : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  have hq : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc0
  intro x y
  have hval : vectorExpectation (fermionSpinTransverse N x y)
      (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)
      = ((Complex.normSq c : ℝ) : ℂ)
        * euclideanExpectation (fermionSpinTransverse N x y) φ := by
    rw [hvec, vectorExpectation_smul_vector, hstar]
    rfl
  obtain ⟨him, hpos, hneg⟩ := hsign x y
  refine ⟨?_, fun hs => ?_, fun hns => ?_⟩
  · rw [hval, Complex.im_ofReal_mul, him, mul_zero]
  · rw [hval, Complex.re_ofReal_mul]
    exact mul_pos hq (hpos hs)
  · rw [hval, Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg hq (hneg hns)

/-- **A highest-weight ground vector whose centered tower member has Theorem 10.5's signs.**  The
existential form of `liebRepulsive_centered_transverse_sign`: the nonzero `(N+1)`-electron ground
submodule contains a highest-weight vector `w` (`liebRepulsive_ground_exists_topWeight`) which
simultaneously satisfies the weight equation `Ŝ³_tot w = (L/2) w` and carries the transverse-sign
pattern on its centered tower member.  Exposing the *same* `w` for both is what the ferrimagnetic
bound (10.2.17) consumes. -/
theorem liebRepulsive_exists_centered_transverse_sign (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (hN : 1 ≤ N) (E₀ : ℂ)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) :
    ∃ w : (Fin (2 * N + 2) → Fin 2) → ℂ, w ≠ 0 ∧
      w ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ∧
      (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w ∧
      ∀ x y : Fin (N + 1),
        (vectorExpectation (fermionSpinTransverse N x y)
            (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).im = 0 ∧
          (SameSublattice A x y →
              0 < (vectorExpectation (fermionSpinTransverse N x y)
                (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re) ∧
            (¬ SameSublattice A x y →
              (vectorExpectation (fermionSpinTransverse N x y)
                (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re < 0) := by
  obtain ⟨w, hw0, hwG, -, hz⟩ := liebRepulsive_ground_exists_topWeight N A T U E₀ hcas hne
  exact ⟨w, hw0, hwG, hz, liebRepulsive_centered_transverse_sign N A T hT hbip hT_conn U hU hN E₀
    hne hmin hcas hw0 hwG hz⟩

end LatticeSystem.Fermion
