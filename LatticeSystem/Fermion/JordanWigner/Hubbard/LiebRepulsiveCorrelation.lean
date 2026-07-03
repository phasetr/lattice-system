import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsive
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaSpinOp
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeBondSum

/-!
# Spin-correlation signs in the repulsive Hubbard ground states (Tasaki §10.2.2, Theorem 10.5)

This file **proves** **Tasaki Theorem 10.5** (Shen, Qiu, and Tian; Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.2, p. 351/353,
eqs. (10.2.7)/(10.2.8)/(10.2.13)) on the **balanced (`Ŝ³ = 0`) sector**: under the hypotheses of
Theorem 10.4 (odd `N`, connected real symmetric bipartite hopping `T`, on-site repulsion
`U_x > 0`), the transverse spin–spin correlation in the unique balanced-sector ground state is
**strictly positive for sites in the same sublattice and strictly negative for sites in different
sublattices**.

## The assembly (crux-free)

The Shiba unitary `Û` transports the balanced repulsive ground state `φ = Û φ_attr` to the
attractive Theorem-10.2 ground state `φ_attr` and (eq. (10.2.13)) sends the transverse spin
operators to the on-site pair (η-pairing) operators
(`shibaSignedUnitary_conj_spinPlusMinus`):
`Ûᴴ (Ŝ⁺_x Ŝ⁻_y) Û = (ε_x ε_y) · ĉ†_{x↑} ĉ†_{x↓} ĉ_{y↓} ĉ_{y↑}`, `ε_x = ±1` the sublattice gauge.
Hence the transverse correlation equals `½ ε_x ε_y` times a sum of Tian pair-transfer
correlations (Theorem 10.3, `theorem_10_3_tian_pair_correlation_positive`), each strictly
positive; the diagonal (`x = y`) contribution is `‖ĉ†_{x↑} ĉ†_{x↓} φ_attr‖² ≥ 0`.  The sign is
`ε_x ε_y = +1` iff `x, y` lie in the same sublattice.

## Scope (over-claim avoided)

Only the **balanced `Ŝ³ = 0` sector** is claimed, matching Theorem 10.4's
`repulsiveHalfFilling_balancedSector_ground_unique`.  The general `(N₁, N₂)` / `Ŝ³ = m ≠ 0`
sectors require the number ↔ spin-`z` sector transport for `m ≠ 0` and are deferred (not
axiomatized).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, Theorem 10.5, eqs. (10.2.7)/(10.2.8)/(10.2.13), pp. 351, 353; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201; S.-Q. Shen, Z.-M. Qiu, G.-S. Tian, *Phys. Rev. Lett.*
**72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The transverse spin–spin correlation operator
`Ŝ⁽¹⁾_x Ŝ⁽¹⁾_y + Ŝ⁽²⁾_x Ŝ⁽²⁾_y = ½ (Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)` of Theorem 10.5
(Tasaki eq. (10.2.7)). -/
noncomputable def fermionSpinTransverse (N : ℕ) (x y : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) •
    (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y +
      fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)

/-- The (raw) expectation `⟨v| O |v⟩` of an observable `O` in a state vector
`v`. -/
noncomputable def vectorExpectation {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  dotProduct (star v) (O.mulVec v)

/-- Two sites lie in the same sublattice of the bipartition `A ⊔ Aᶜ`. -/
def SameSublattice (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) : Prop :=
  x ∈ A ↔ y ∈ A

/-! ## Sign of the sublattice-gauge product -/

/-- The sublattice-gauge product is `+1` on the same sublattice. -/
private theorem gaugeSign_mul_sameSublattice (A : Finset (Fin (N + 1))) (x y : Fin (N + 1))
    (h : SameSublattice A x y) : gaugeSign A x * gaugeSign A y = 1 := by
  unfold gaugeSign SameSublattice at *
  by_cases hx : x ∈ A
  · rw [if_pos hx, if_pos (h.mp hx)]; ring
  · rw [if_neg hx, if_neg (fun hy => hx (h.mpr hy))]; ring

/-- The sublattice-gauge product is real (imaginary part zero). -/
private theorem gaugeSign_mul_im (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) :
    (gaugeSign A x * gaugeSign A y).im = 0 := by
  unfold gaugeSign
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx, hy]

/-- The sublattice-gauge product is `−1` across the two sublattices. -/
private theorem gaugeSign_mul_not_sameSublattice (A : Finset (Fin (N + 1))) (x y : Fin (N + 1))
    (h : ¬ SameSublattice A x y) : gaugeSign A x * gaugeSign A y = -1 := by
  unfold gaugeSign SameSublattice at *
  by_cases hx : x ∈ A
  · have hy : y ∉ A := fun hy => h ⟨fun _ => hy, fun _ => hx⟩
    rw [if_pos hx, if_neg hy]; ring
  · have hy : y ∈ A := by
      by_contra hy
      exact h ⟨fun hx' => absurd hx' hx, fun hy' => absurd hy' hy⟩
    rw [if_neg hx, if_pos hy]; ring

/-! ## Linearity and transport of the Euclidean expectation -/

/-- The Euclidean expectation is homogeneous in the observable. -/
private theorem euclideanExpectation_smul (a : ℂ) (O : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (a • O) φ = a * euclideanExpectation O φ := by
  unfold euclideanExpectation
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The Euclidean expectation is additive in the observable. -/
private theorem euclideanExpectation_add (O₁ O₂ : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (O₁ + O₂) φ
      = euclideanExpectation O₁ φ + euclideanExpectation O₂ φ := by
  unfold euclideanExpectation
  rw [Matrix.add_mulVec, dotProduct_add]

/-- **Shiba transport of the Euclidean expectation**: if `ψ = Û φ_attr` then
`⟨ψ| O |ψ⟩ = ⟨φ_attr| Ûᴴ O Û |φ_attr⟩`. -/
private theorem euclideanExpectation_shiba_conj (O : ManyBodyOp (Fin (2 * N + 2)))
    (Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ)
    (ψ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
    (hψ : ψ.ofLp = Ush.mulVec φattr.ofLp) :
    euclideanExpectation O ψ
      = euclideanExpectation (Matrix.conjTranspose Ush * O * Ush) φattr := by
  unfold euclideanExpectation
  rw [hψ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]

/-- The Euclidean `⟨v| Aᴴ A |v⟩` is the (nonnegative real) squared norm of `A v`. -/
private theorem euclideanExpectation_conjTranspose_mul_self
    (M : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (Matrix.conjTranspose M * M) φ
      = ((∑ j, Complex.normSq ((M.mulVec φ.ofLp) j) : ℝ) : ℂ) := by
  unfold euclideanExpectation
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-! ## Tasaki Theorem 10.5 (balanced sector) -/

/-- **Tasaki Theorem 10.5** (Shen–Qiu–Tian; 1st ed., Springer 2020, §10.2.2, p. 351/353,
eqs. (10.2.7)/(10.2.8)/(10.2.13); **PROVED** on the balanced `Ŝ³ = 0` sector, no axiom).
Under the hypotheses of Theorem 10.4 (odd `N`, connected real symmetric bipartite hopping `T`,
on-site repulsion `U_x > 0`), for the unique ground state `φ` on the balanced spin-`z` sector
`Ŝ³ = 0`, the transverse spin correlation
`⟨φ| Ŝ⁽¹⁾_x Ŝ⁽¹⁾_y + Ŝ⁽²⁾_x Ŝ⁽²⁾_y |φ⟩` is real, and is strictly positive when `x, y` lie in the
same sublattice and strictly negative otherwise.

Only the balanced `Ŝ³ = 0` sector is claimed (matching
`repulsiveHalfFilling_balancedSector_ground_unique`); the general `(N₁, N₂)` / `Ŝ³ = m ≠ 0`
sectors are deferred.  Proof: transport `φ = Û φ_attr` through the Shiba unitary
(`euclideanExpectation_shiba_conj`), send `Ŝ⁺_x Ŝ⁻_y` to the pair-transfer operator
(`shibaSignedUnitary_conj_spinPlusMinus`, eq. (10.2.13)), and apply Tian's positivity
(`theorem_10_3_tian_pair_correlation_positive`, Theorem 10.3). -/
theorem theorem_10_5_shen_qiu_tian_transverse_sign (N : ℕ) (hNodd : Odd N)
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (spinZSectorEuclidean N 0)
      (symmetricRepulsiveHubbardHamiltonian N T U) E φ) :
    ∀ x y : Fin (N + 1),
      (euclideanExpectation (fermionSpinTransverse N x y) φ).im = 0 ∧
        (SameSublattice A x y →
            0 < (euclideanExpectation (fermionSpinTransverse N x y) φ).re) ∧
          (¬ SameSublattice A x y →
            (euclideanExpectation (fermionSpinTransverse N x y) φ).re < 0) := by
  classical
  set Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ :=
    shibaSignedUnitary N (shibaSignFn A) with hUsh
  obtain ⟨Elem, ψ, φattr, huniqψ, hψeq, hpair⟩ :=
    repulsiveHalfFilling_balancedSector_ground_unique N hNodd T hT_symm hbip hT_conn U hU_pos
  obtain ⟨hφmem, hφnorm, hφeig, hφground, _⟩ := hGS
  obtain ⟨hψmem, hψnorm, hψeig, hψground, hψuniq⟩ := huniqψ
  have hφne : φ ≠ 0 := fun h => by rw [h, norm_zero] at hφnorm; exact one_ne_zero hφnorm.symm
  have hψne : ψ ≠ 0 := fun h => by rw [h, norm_zero] at hψnorm; exact one_ne_zero hψnorm.symm
  -- The two unique ground states share the ground eigenvalue `E = Elem`.
  have hEle : E ≤ Elem := hφground.2 Elem ⟨ψ, hψmem, hψne, hψeig⟩
  have hlemE : Elem ≤ E := hψground.2 E ⟨φ, hφmem, hφne, hφeig⟩
  have hEeq : E = Elem := le_antisymm hEle hlemE
  -- Collinearity `φ = c • ψ` with `|c| = 1`.
  obtain ⟨c, hc⟩ := hψuniq φ hφmem (by rw [← hEeq]; exact hφeig)
  have hcc : star c * c = 1 := by
    have hn : ‖c‖ = 1 := by
      have h := hc ▸ hφnorm
      rwa [norm_smul, hψnorm, mul_one] at h
    have hnc : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hn, one_pow]
    rw [Complex.star_def, mul_comm, Complex.mul_conj, hnc, Complex.ofReal_one]
  -- Phase invariance of the expectation.
  have hphase : ∀ O : ManyBodyOp (Fin (2 * N + 2)),
      euclideanExpectation O φ = euclideanExpectation O ψ := by
    intro O
    rw [hc]
    unfold euclideanExpectation
    rw [WithLp.ofLp_smul, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_smul, hcc, one_smul]
  -- Transport `⟨ψ| O |ψ⟩ = ⟨φ_attr| Ûᴴ O Û |φ_attr⟩`.
  have htrans : ∀ O : ManyBodyOp (Fin (2 * N + 2)),
      euclideanExpectation O ψ
        = euclideanExpectation (Matrix.conjTranspose Ush * O * Ush) φattr :=
    fun O => euclideanExpectation_shiba_conj O Ush ψ φattr (hUsh ▸ hψeq)
  intro x y
  -- Reduce to the transported pair-transfer expectations.
  have hbase : euclideanExpectation (fermionSpinTransverse N x y) φ
      = (1 / 2 : ℂ)
        * (euclideanExpectation (Matrix.conjTranspose Ush
              * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y) * Ush) φattr
          + euclideanExpectation (Matrix.conjTranspose Ush
              * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y) * Ush) φattr) := by
    rw [hphase, htrans, fermionSpinTransverse,
      show Matrix.conjTranspose Ush
            * ((1 / 2 : ℂ) • (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y
              + fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)) * Ush
          = (1 / 2 : ℂ) • (Matrix.conjTranspose Ush
              * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y) * Ush
            + Matrix.conjTranspose Ush
              * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y) * Ush) from by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul],
      euclideanExpectation_smul, euclideanExpectation_add]
  -- The first summand is `ε_x ε_y` times Tian's positive pair correlation.
  set r1 : ℂ := euclideanExpectation (hubbardPairCorrelationOp N x y) φattr with hr1
  have hterm1 : euclideanExpectation (Matrix.conjTranspose Ush
        * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y) * Ush) φattr
      = (gaugeSign A x * gaugeSign A y) * r1 := by
    rw [hUsh, shibaSignedUnitary_conj_spinPlusMinus, euclideanExpectation_smul]
  by_cases hxy : x = y
  · -- Diagonal: the second summand is `‖ĉ†_{x↑} ĉ†_{x↓} φ_attr‖² ≥ 0`.
    subst hxy
    set q : ℝ := ∑ j, Complex.normSq (((fermionUpCreation N x * fermionDownCreation N x).mulVec
      φattr.ofLp) j) with hq
    have hqnonneg : 0 ≤ q :=
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    have hgg : gaugeSign A x * gaugeSign A x = 1 :=
      gaugeSign_mul_sameSublattice A x x Iff.rfl
    have hPadj : Matrix.conjTranspose (fermionUpCreation N x * fermionDownCreation N x)
        = fermionDownAnnihilation N x * fermionUpAnnihilation N x := by
      rw [Matrix.conjTranspose_mul, fermionUpCreation, fermionDownCreation,
        fermionMultiCreation_conjTranspose, fermionMultiCreation_conjTranspose,
        fermionDownAnnihilation, fermionUpAnnihilation]
    have hterm2 : euclideanExpectation (Matrix.conjTranspose Ush
          * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N x) * Ush) φattr
        = (q : ℂ) := by
      have hsplit : Matrix.conjTranspose Ush
            * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N x) * Ush
          = (Matrix.conjTranspose Ush * fermionSiteSpinMinus N x * Ush)
            * (Matrix.conjTranspose Ush * fermionSiteSpinPlus N x * Ush) := by
        have hUUc : Ush * Matrix.conjTranspose Ush = 1 := by
          rw [hUsh]
          exact shibaSignedUnitary_self_mul_conjTranspose (shibaSignFn A)
            (fun d => shibaSignFn_star_mul_self A d)
        rw [show (Matrix.conjTranspose Ush * fermionSiteSpinMinus N x * Ush)
              * (Matrix.conjTranspose Ush * fermionSiteSpinPlus N x * Ush)
            = Matrix.conjTranspose Ush * fermionSiteSpinMinus N x
              * (Ush * Matrix.conjTranspose Ush) * fermionSiteSpinPlus N x * Ush from by
          noncomm_ring, hUUc, Matrix.mul_one]
        noncomm_ring
      rw [hsplit, hUsh, shibaSignedUnitary_conj_siteSpinMinus,
        shibaSignedUnitary_conj_siteSpinPlus, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgg,
        one_smul, ← hPadj, euclideanExpectation_conjTranspose_mul_self]
    -- Value `= ↑((r1.re + q)/2)`, real and strictly positive.
    obtain ⟨hr1pos, hr1im⟩ := hpair x x
    have hr1real : r1 = (r1.re : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact hr1im)
    have hval : euclideanExpectation (fermionSpinTransverse N x x) φ
        = (((r1.re + q) / 2 : ℝ) : ℂ) := by
      rw [hbase, hterm1, hgg, one_mul, hterm2, hr1real]; push_cast [Complex.ofReal_re]; ring
    refine ⟨by rw [hval, Complex.ofReal_im], fun _ => ?_, fun hns => absurd Iff.rfl hns⟩
    rw [hval, Complex.ofReal_re]; linarith [hr1pos, hqnonneg]
  · -- Off-diagonal: the second summand is `ε_x ε_y` times Tian's positive pair correlation.
    set r2 : ℂ := euclideanExpectation (hubbardPairCorrelationOp N y x) φattr with hr2
    have hterm2 : euclideanExpectation (Matrix.conjTranspose Ush
          * (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y) * Ush) φattr
        = (gaugeSign A x * gaugeSign A y) * r2 := by
      rw [fermionSiteSpinMinus_mul_Plus_comm N x y hxy, hUsh,
        shibaSignedUnitary_conj_spinPlusMinus, euclideanExpectation_smul, mul_comm (gaugeSign A y)]
    obtain ⟨hr1pos, hr1im⟩ := hpair x y
    obtain ⟨hr2pos, hr2im⟩ := hpair y x
    have hr1real : r1 = (r1.re : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact hr1im)
    have hr2real : r2 = (r2.re : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact hr2im)
    have hval : euclideanExpectation (fermionSpinTransverse N x y) φ
        = (gaugeSign A x * gaugeSign A y) * (((r1.re + r2.re) / 2 : ℝ) : ℂ) := by
      rw [hbase, hterm1, hterm2, hr1real, hr2real]; push_cast [Complex.ofReal_re]; ring
    have hposr : (0 : ℝ) < (r1.re + r2.re) / 2 := by linarith [hr1pos, hr2pos]
    refine ⟨?_, fun hs => ?_, fun hns => ?_⟩
    · rw [hval, Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add, gaugeSign_mul_im, zero_mul]
    · rw [hval, gaugeSign_mul_sameSublattice A x y hs, one_mul, Complex.ofReal_re]; exact hposr
    · rw [hval, gaugeSign_mul_not_sameSublattice A x y hns, neg_one_mul, Complex.neg_re,
        Complex.ofReal_re]; linarith [hposr]

end LatticeSystem.Fermion
