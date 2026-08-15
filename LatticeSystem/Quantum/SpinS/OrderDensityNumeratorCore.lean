/-
Hamiltonian-agnostic order-density algebra shared by the tower numerator estimates.

The declarations here scalarize an inserted order commutator `[ô⁺, ô⁻]` on a total-`Ŝ³` singlet,
telescope powers of the staggered order density into order words, and collect per-term expectation
bounds through triangle inequalities.  No statement or proof mentions a Hamiltonian, so both the
Anderson-tower numerator chain (Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §4.2.2 Theorem 4.6) and the Bose–Einstein-condensation XY numerator chain
(§5.3 Theorem 5.2) reuse them unchanged.

The order-word layer comes from `AndersonTowerLocality` and the generic power telescopes from
`LatticeSystem.Math.CommutatorTelescope`.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality
import LatticeSystem.Math.CommutatorTelescope

namespace LatticeSystem.Quantum

open Matrix

/-! ### Scalarization of an inserted `[ô⁺, ô⁻]` on an `Ŝ³`-singlet -/

/-- **Scalarization of an inserted `[ô⁺, ô⁻]` (S2/S3 core).**  On a total-`Ŝ³` singlet `Φ`, the
order commutator inserted between two order words collapses to a scalar (the suffix charge), since
`[ô⁺, ô⁻]` acts on any order-word state as `(V⁻² · 2 m(suf))`:
`(ô^{wₗ} [ô⁺,ô⁻] ô^{wᵣ}) Φ = (V⁻² · 2 m(wᵣ)) · (ô^{wₗ} ô^{wᵣ}) Φ`. -/
theorem orderWord_orderCommutator_insert_mulVec_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (wl wr : List Bool) :
    (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * orderWordProd d L N wr).mulVec Φ
      = ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr))
          • (orderWordProd d L N wl * orderWordProd d L N wr).mulVec Φ := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    orderCommutator_mulVec_orderWordProd d L N Φ hsing wr, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]

/-- **Scalarization of an inserted `[ô⁺,ô⁻]` with a left factor.**  Generalizes
`orderWord_orderCommutator_insert_mulVec_eq` to allow an arbitrary operator `X` to the left:
`(X · ô^{wₗ} [ô⁺,ô⁻] ô^{wᵣ}) Φ = (V⁻²·2 m(wᵣ)) · (X · ô^{wₗ} ô^{wᵣ}) Φ`. -/
theorem orderCommutator_insert_left_mulVec_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (X : ManyBodyOpS (HypercubicTorus d L) N) (wl wr : List Bool) :
    (X * (orderWordProd d L N wl
        * (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
        * orderWordProd d L N wr)).mulVec Φ
      = ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge wr))
          • (X * (orderWordProd d L N wl * orderWordProd d L N wr)).mulVec Φ := by
  rw [← Matrix.mulVec_mulVec, orderWord_orderCommutator_insert_mulVec_eq d L N Φ hsing wl wr,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]

/-- **Bra-side scalarization of a buried `Ŝ³`.**  Moving `Ŝ³` (`= [ô⁺,ô⁻]·V²/2`) onto the bra `Φ`
via Hermiticity: `(ô^{wₗ})†Φ` is an `Ŝ³` eigenstate (charge `m((wₗ)ʳ⁻)`), so
`⟨Φ, ô^{wₗ} Ŝ³ X Φ⟩ = conj(m((wₗ)ʳ⁻)) ⟨Φ, ô^{wₗ} X Φ⟩` for any right factor `X`. -/
theorem dotProduct_orderWord_totalSpinSOp3_mid_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (wl : List Bool)
    (X : ManyBodyOpS (HypercubicTorus d L) N) :
    star Φ ⬝ᵥ (orderWordProd d L N wl * totalSpinSOp3 (HypercubicTorus d L) N * X).mulVec Φ
      = (starRingEnd ℂ) (mCharge (wl.reverse.map not))
          * (star Φ ⬝ᵥ (orderWordProd d L N wl * X).mulVec Φ) := by
  have key : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((orderWordProd d L N (wl.reverse.map not)).mulVec Φ)
      = mCharge (wl.reverse.map not) • (orderWordProd d L N (wl.reverse.map not)).mulVec Φ :=
    totalSpinSOp3_mulVec_orderWordProd_eigenvec d L N _ hsing
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    star_dotProduct_mulVec_conjTranspose (orderWordProd d L N wl), orderWordProd_conjTranspose,
    star_dotProduct_mulVec_conjTranspose (totalSpinSOp3 (HypercubicTorus d L) N),
    (totalSpinSOp3_isHermitian (HypercubicTorus d L) N).eq, key, star_smul, smul_dotProduct,
    smul_eq_mul, ← orderWordProd_conjTranspose,
    ← star_dotProduct_mulVec_conjTranspose, Matrix.mulVec_mulVec, starRingEnd_apply]

/-- The order-commutator scalar coefficient is bounded by the word length:
`‖V⁻²·2·m(w)‖ ≤ V⁻²·2·|w|`. -/
theorem orderScalar_norm_le (d L : ℕ) [NeZero L] (w : List Bool) :
    ‖(((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge w)‖
      ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ * (2 * (w.length : ℝ)) := by
  rw [norm_mul, show ‖((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹‖
      = ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d)⁻¹ from by
    simp only [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
  exact mul_le_mul_of_nonneg_left (mCharge_norm_le w) (by norm_num)

/-! ### Order-density power telescopes and ring decompositions -/

/-- A power of a single order density is the order-word product over a constant word:
`(ô^b)^a = ô^{replicate a b}`.  Lets the numerator's order-density powers be fed to the R2-based
single-term bounds, which are phrased over `orderWordProd`. -/
theorem orderWordProd_replicate (d L N a : ℕ) [NeZero L] (b : Bool) :
    orderWordProd d L N (List.replicate a b) = staggeredOrderDensityOpS d L N b ^ a := by
  rw [orderWordProd, List.map_replicate, List.prod_replicate]

/-- **Anti-expansion of `(ô⁻)^M` against an operator.**  `(ô⁻)^M X − X (ô⁻)^M` telescopes into a
signed sum of single `[X, ô⁻]` insertions between powers of `ô⁻`. -/
theorem orderMinusPow_commutator_eq (d L N M : ℕ) [NeZero L]
    (X : ManyBodyOpS (HypercubicTorus d L) N) :
    staggeredOrderDensityOpS d L N false ^ M * X
        - X * staggeredOrderDensityOpS d L N false ^ M
      = - ∑ k ∈ Finset.range M, staggeredOrderDensityOpS d L N false ^ k
          * (X * staggeredOrderDensityOpS d L N false
            - staggeredOrderDensityOpS d L N false * X)
          * staggeredOrderDensityOpS d L N false ^ (M - 1 - k) := by
  rw [← neg_sub (X * staggeredOrderDensityOpS d L N false ^ M)
      (staggeredOrderDensityOpS d L N false ^ M * X), commutator_pow_eq_sum]

/-- **Right power commutator telescope.**  `A^r·B − B·A^r = ∑_l A^l (A·B−B·A) A^{r-1-l}`. -/
theorem pow_right_commutator_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (r : ℕ) :
    A ^ r * B - B * A ^ r
      = ∑ l ∈ Finset.range r, A ^ l * (A * B - B * A) * A ^ (r - 1 - l) := by
  have h : B * A ^ r - A ^ r * B
      = ∑ l ∈ Finset.range r, A ^ l * (B * A - A * B) * A ^ (r - 1 - l) :=
    commutator_pow_eq_sum B A r
  have key : (∑ l ∈ Finset.range r, A ^ l * (A * B - B * A) * A ^ (r - 1 - l))
      = -(∑ l ∈ Finset.range r, A ^ l * (B * A - A * B) * A ^ (r - 1 - l)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun l _ => by noncomm_ring)
  rw [key, ← h]; abel

/-- **Triple Leibniz decomposition.**  `[A·G·C, Z] = A·G·[C,Z] + A·[G,Z]·C + [A,Z]·G·C` (pure ring
identity).  In the typical application `A = (ô⁺)^j`, `G` is a Hamiltonian–order commutator,
`C = (ô⁺)^{M-1-j}` and `Z = ô⁻`: the middle term's `[G,Z]` gives the S1 contribution, the outer
two give the S2/S3 crossings. -/
theorem mul_mul_commutator_decomp {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (A G C Z : ManyBodyOpS Λ N) :
    A * G * C * Z - Z * (A * G * C)
      = A * G * (C * Z - Z * C) + A * (G * Z - Z * G) * C + (A * Z - Z * A) * G * C := by
  noncomm_ring

/-! ### Expectation triangle inequalities -/

/-- **Triangle inequality for a sum of sandwiched expectations.**  The real part of a finite-sum
operator's expectation is bounded by the sum of the per-term absolute real parts. -/
theorem abs_re_dotProduct_sum_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → ManyBodyOpS (HypercubicTorus d L) N) :
    |(star Φ ⬝ᵥ (∑ i ∈ s, f i).mulVec Φ).re| ≤ ∑ i ∈ s, |(star Φ ⬝ᵥ (f i).mulVec Φ).re| := by
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  exact Finset.abs_sum_le_sum_abs (fun i => (star Φ ⬝ᵥ (f i).mulVec Φ).re) s

/-- The same triangle bound for a negated finite sum (`|Re| = |Re of the un-negated sum|`). -/
theorem abs_re_dotProduct_neg_sum_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → ManyBodyOpS (HypercubicTorus d L) N) :
    |(star Φ ⬝ᵥ (- ∑ i ∈ s, f i).mulVec Φ).re| ≤ ∑ i ∈ s, |(star Φ ⬝ᵥ (f i).mulVec Φ).re| := by
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, abs_neg]
  exact abs_re_dotProduct_sum_le d L N Φ s f

end LatticeSystem.Quantum
