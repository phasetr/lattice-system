/-
Tasaki §4.2.2 Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), arc PR2 — the axis-1
spin-reversal (`Θ = manyBodyReversalS`) conjugation of the staggered order operators, the general
Ξ sandwich expansion, the charge-parity cross-term vanishing, and the transverse moments
(4.2.14) `⟨Ξ| Ô_L^{(α)} |Ξ⟩ = 0` for `α = 2, 3`.

The many-body spin reversal `Θ` (the `π`-rotation about axis 1, `SpinSReversal.lean`) conjugates the
staggered order operators componentwise: `Θ Ô^{(1)} Θ = Ô^{(1)}`, `Θ Ô^{(2)} Θ = -Ô^{(2)}`,
`Θ Ô^{(3)} Θ = -Ô^{(3)}` (from `F Ŝ^{(1)} F = Ŝ^{(1)}`, `F Ŝ^{(2)} F = -Ŝ^{(2)}`,
`F Ŝ^{(3)} F = -Ŝ^{(3)}` lifted site-by-site).  Since `Θ` commutes with `Ô^{(1)}` (its own fixed
axis) and `Θ Φ = Φ` (a hypothesis of the ground-state family, `IsTanakaFullSSBConstants`), it fixes
the whole Tanaka state, `Θ Ξ = Ξ`.  Together with `Θ` being a real symmetric involution
(`Θᴴ = Θ`), the anti-invariance `Θ Ô^{(α)} Θ = -Ô^{(α)}` (`α = 2, 3`) forces
`⟨Ξ| Ô^{(α)} |Ξ⟩ = ⟨Θ Ξ| Ô^{(α)} |Θ Ξ⟩ = ⟨Ξ| Θ Ô^{(α)} Θ |Ξ⟩ = -⟨Ξ| Ô^{(α)} |Ξ⟩ = 0` — the
transverse moments (4.2.14) vanish exactly at finite volume (Tasaki eq. (4.2.48)).

This file also records two pieces of shared infrastructure for the later relations
((4.2.12)/(4.2.13) lower bounds and (4.2.15) transverse fluctuation decay):
* the general sandwich expansion of `⟨Ξ| O |Ξ⟩` into the four two-term matrix elements (with the two
  cross terms merged for Hermitian `O`, Tasaki eqs. (4.2.45)/(4.2.49));
* the charge-parity cross-term vanishing for a charge-conserving `O` (commuting with the parity
  operator `Û = exp(iπ Ŝ_tot^{(3)})`), which kills the off-diagonal contribution of the two
  opposite-parity tower terms (the axis-`3` / squared-order-operator analogue of eq. (4.2.69)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.45)–(4.2.49), pp. 106–108 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerParityCrossTerm

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### The axis-1 spin reversal `Θ` conjugates the staggered order operators -/

/-- **`Θ` fixes the `1`-axis staggered order operator**: `Θ Ô_L^{(1)} Θ = Ô_L^{(1)}`.  The reversal
is the `π`-rotation about axis `1`, and `F Ŝ^{(1)} F = Ŝ^{(1)}`, lifted site-by-site. -/
theorem manyBodyReversalS_conj_staggeredOrderOp1S (A : Λ → Bool) :
    manyBodyReversalS Λ N * staggeredOrderOp1S A N * manyBodyReversalS Λ N
      = staggeredOrderOp1S A N := by
  rw [staggeredOrderOp1S, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  change manyBodyReversalS Λ N * onSiteS x (spinSOp1 N) * manyBodyReversalS Λ N
      = onSiteS x (spinSOp1 N)
  rw [manyBodyReversalS_conj_onSiteS, spinReversalS_conj_spinSOp1]

/-- **`Θ` reverses the `2`-axis staggered order operator**: `Θ Ô_L^{(2)} Θ = -Ô_L^{(2)}`
(`F Ŝ^{(2)} F = -Ŝ^{(2)}`, lifted site-by-site). -/
theorem manyBodyReversalS_conj_staggeredOrderOp2S (A : Λ → Bool) :
    manyBodyReversalS Λ N * staggeredOrderOp2S A N * manyBodyReversalS Λ N
      = -staggeredOrderOp2S A N := by
  rw [staggeredOrderOp2S, Matrix.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg]
  congr 1
  change manyBodyReversalS Λ N * onSiteS x (spinSOp2 N) * manyBodyReversalS Λ N
      = -onSiteS x (spinSOp2 N)
  rw [manyBodyReversalS_conj_onSiteS, spinReversalS_conj_spinSOp2, onSiteS_neg]

/-- **`Θ` reverses the `3`-axis staggered order operator**: `Θ Ô_L^{(3)} Θ = -Ô_L^{(3)}`
(`F Ŝ^{(3)} F = -Ŝ^{(3)}`, lifted site-by-site).  Here `Ô_L^{(3)}` is the existing
`staggeredOrderOpS`. -/
theorem manyBodyReversalS_conj_staggeredOrderOpS (A : Λ → Bool) :
    manyBodyReversalS Λ N * staggeredOrderOpS A N * manyBodyReversalS Λ N
      = -staggeredOrderOpS A N := by
  rw [staggeredOrderOpS, Matrix.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg]
  congr 1
  rw [spinSSiteOp3_def, manyBodyReversalS_conj_onSiteS, spinReversalS_conj_spinSOp3, onSiteS_neg]

/-! ### `Θ` fixes the Tanaka state -/

/-- **`Θ` commutes with the `1`-axis staggered order operator** (its own fixed axis): from
`Θ Ô^{(1)} Θ = Ô^{(1)}` and `Θ² = 1`. -/
theorem manyBodyReversalS_commute_staggeredOrderOp1S (A : Λ → Bool) :
    Commute (manyBodyReversalS Λ N) (staggeredOrderOp1S A N) := by
  have h3 : manyBodyReversalS Λ N * staggeredOrderOp1S A N * manyBodyReversalS Λ N
      * manyBodyReversalS Λ N = staggeredOrderOp1S A N * manyBodyReversalS Λ N :=
    congrArg (· * manyBodyReversalS Λ N) (manyBodyReversalS_conj_staggeredOrderOp1S A)
  rwa [mul_assoc (manyBodyReversalS Λ N * staggeredOrderOp1S A N), manyBodyReversalS_mul_self,
    mul_one] at h3

/-- **`Θ` fixes each Tanaka tower term** `(Ô_L^{(1)})^k Φ` when `Θ Φ = Φ`: `Θ` commutes with the
`1`-axis order operator, so it passes through the `k`-fold power and acts on `Φ` as the identity. -/
theorem manyBodyReversalS_mulVec_tanakaTowerTerm (A : Λ → Bool) (k : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΘΦ : (manyBodyReversalS Λ N).mulVec Φ = Φ) :
    (manyBodyReversalS Λ N).mulVec (tanakaTowerTerm A N k Φ) = tanakaTowerTerm A N k Φ := by
  have hce : manyBodyReversalS Λ N * (staggeredOrderOp1S A N) ^ k
      = (staggeredOrderOp1S A N) ^ k * manyBodyReversalS Λ N :=
    (manyBodyReversalS_commute_staggeredOrderOp1S A).pow_right k
  simp only [tanakaTowerTerm]
  rw [Matrix.mulVec_mulVec, hce, ← Matrix.mulVec_mulVec, hΘΦ]

/-- **`Θ` fixes the Tanaka symmetry-breaking state** `Ξ` when `Θ Φ = Φ` (Tasaki eq. (4.2.48),
`Û_π^{(1)} |Ξ_L^{(M)}⟩ = |Ξ_L^{(M)}⟩`): `Θ` fixes each unit-normalized tower term and commutes with
the scalar factors. -/
theorem manyBodyReversalS_mulVec_tanakaSSBState (A : Λ → Bool) (M : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΘΦ : (manyBodyReversalS Λ N).mulVec Φ = Φ) :
    (manyBodyReversalS Λ N).mulVec (tanakaSSBState A N M Φ) = tanakaSSBState A N M Φ := by
  have hM : (manyBodyReversalS Λ N).mulVec (unitNormalize (tanakaTowerTerm A N M Φ))
      = unitNormalize (tanakaTowerTerm A N M Φ) := by
    rw [unitNormalize, Matrix.mulVec_smul, manyBodyReversalS_mulVec_tanakaTowerTerm A M hΘΦ]
  have hM1 : (manyBodyReversalS Λ N).mulVec (unitNormalize (tanakaTowerTerm A N (M + 1) Φ))
      = unitNormalize (tanakaTowerTerm A N (M + 1) Φ) := by
    rw [unitNormalize, Matrix.mulVec_smul, manyBodyReversalS_mulVec_tanakaTowerTerm A (M + 1) hΘΦ]
  rw [tanakaSSBState, Matrix.mulVec_smul, Matrix.mulVec_add, hM, hM1]

/-! ### `Θ` is a real symmetric involution -/

/-- **`Θ` is symmetric** (real permutation matrix of an involution): `Θᴴ = Θ`. -/
theorem manyBodyReversalS_conjTranspose (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    Matrix.conjTranspose (manyBodyReversalS Λ N) = manyBodyReversalS Λ N := by
  ext σ' σ
  rw [Matrix.conjTranspose_apply, manyBodyReversalS_apply, manyBodyReversalS_apply]
  by_cases h : σ' = revConfigS σ
  · have h2 : σ = revConfigS σ' := by rw [h, revConfigS_involutive]
    rw [if_pos h2, if_pos h, star_one]
  · have h2 : ¬ σ = revConfigS σ' := fun hc => h (by rw [hc, revConfigS_involutive])
    rw [if_neg h2, if_neg h, star_zero]

/-! ### The transverse moments (4.2.14) vanish -/

/-- **Symmetry vanishing under a symmetric involution reversing `O`.**  If `Θᴴ = Θ`,
`Θ Ξ = δ • Ξ` with `δ` of unit modulus (`δ · δ̄ = 1`), and `Θ O Θ = -O`, then `⟨Ξ| O |Ξ⟩ = 0`:
conjugating by `Θ` sends the expectation to `(δ δ̄)·` its own negative `= -⟨Ξ|O|Ξ⟩`.  This is the
mechanism behind the vanishing transverse moments (4.2.14) and, at `δ = ±1`, the first-order
vanishing of the susceptibility perturbation (§4.1 Theorem 4.2, issue #4777). -/
theorem dotProduct_mulVec_eq_zero_of_conj_anti {ι : Type*} [Fintype ι]
    (Θ O : Matrix ι ι ℂ) (Ξ : ι → ℂ) {δ : ℂ} (hΘsym : Matrix.conjTranspose Θ = Θ)
    (hΘΞ : Θ.mulVec Ξ = δ • Ξ) (hδ : δ * star δ = 1) (hanti : Θ * O * Θ = -O) :
    star Ξ ⬝ᵥ O.mulVec Ξ = 0 := by
  have hR : star Ξ ⬝ᵥ (Θ * O * Θ).mulVec Ξ = (δ * star δ) * (star Ξ ⬝ᵥ O.mulVec Ξ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hΘΞ, Matrix.mulVec_smul,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      star_dotProduct_mulVec_conjTranspose, hΘsym, hΘΞ,
      star_smul, smul_dotProduct, smul_eq_mul, ← mul_assoc]
  have hL : star Ξ ⬝ᵥ (Θ * O * Θ).mulVec Ξ = -(star Ξ ⬝ᵥ O.mulVec Ξ) := by
    rw [hanti, Matrix.neg_mulVec, dotProduct_neg]
  have hfin : -(star Ξ ⬝ᵥ O.mulVec Ξ) = star Ξ ⬝ᵥ O.mulVec Ξ := by
    rw [← hL, hR, hδ, one_mul]
  linear_combination (-1 / 2 : ℂ) * hfin

/-- **Tasaki eq. (4.2.14) for `α = 2`: `⟨Ξ| Ô_L^{(2)} |Ξ⟩ = 0`.**  The axis-1 reversal `Θ` fixes `Ξ`
(`Θ Φ = Φ`) and reverses `Ô_L^{(2)}` (`Θ Ô^{(2)} Θ = -Ô^{(2)}`), so the per-site moment vanishes
exactly at finite volume. -/
theorem tanakaOrderMean2_eq_zero (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hΘΦ : (manyBodyReversalS (HypercubicTorus d L) N).mulVec Φ = Φ) :
    tanakaOrderMean2 d L N M Φ = 0 := by
  have hz : star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
        (tanakaSSBState (torusParitySublattice d L) N M Φ) = 0 :=
    dotProduct_mulVec_eq_zero_of_conj_anti _ _ _ (δ := 1)
      (manyBodyReversalS_conjTranspose (HypercubicTorus d L) N)
      (by rw [manyBodyReversalS_mulVec_tanakaSSBState (torusParitySublattice d L) M hΘΦ, one_smul])
      (by rw [star_one, mul_one])
      (manyBodyReversalS_conj_staggeredOrderOp2S (torusParitySublattice d L))
  rw [tanakaOrderMean2, expectationRatioRe, hz, Complex.zero_re, zero_div, zero_div]

/-- **Tasaki eq. (4.2.14) for `α = 3`: `⟨Ξ| Ô_L^{(3)} |Ξ⟩ = 0`.**  Same axis-1 reversal argument as
`tanakaOrderMean2_eq_zero`, using `Θ Ô^{(3)} Θ = -Ô^{(3)}`. -/
theorem tanakaOrderMean3_eq_zero (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hΘΦ : (manyBodyReversalS (HypercubicTorus d L) N).mulVec Φ = Φ) :
    tanakaOrderMean3 d L N M Φ = 0 := by
  have hz : star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N).mulVec
        (tanakaSSBState (torusParitySublattice d L) N M Φ) = 0 :=
    dotProduct_mulVec_eq_zero_of_conj_anti _ _ _ (δ := 1)
      (manyBodyReversalS_conjTranspose (HypercubicTorus d L) N)
      (by rw [manyBodyReversalS_mulVec_tanakaSSBState (torusParitySublattice d L) M hΘΦ, one_smul])
      (by rw [star_one, mul_one])
      (manyBodyReversalS_conj_staggeredOrderOpS (torusParitySublattice d L))
  rw [tanakaOrderMean3, expectationRatioRe, hz, Complex.zero_re, zero_div, zero_div]

/-! ### The general Ξ sandwich expansion -/

/-- **Real sandwich expansion of a `(1/√2)`-normalized two-vector sum.**  For Hermitian `O`,
`⟨(1/√2)(u+v)| O |(1/√2)(u+v)⟩.re = ½(⟨u|O|u⟩.re + ⟨v|O|v⟩.re) + ⟨u|O|v⟩.re`; the two cross terms
`⟨u|O|v⟩` and `⟨v|O|u⟩` are complex conjugates (Hermitian `O`), so their sum has real part
`2⟨u|O|v⟩.re`. -/
private theorem sqrtTwoInv_smul_add_re_sandwich {ι : Type*} [Fintype ι] (O : Matrix ι ι ℂ)
    (hHerm : O.IsHermitian) (u v : ι → ℂ) :
    (star ((Real.sqrt 2 : ℂ)⁻¹ • (u + v)) ⬝ᵥ
        O.mulVec ((Real.sqrt 2 : ℂ)⁻¹ • (u + v))).re
      = (1 / 2) * ((star u ⬝ᵥ O.mulVec u).re + (star v ⬝ᵥ O.mulVec v).re)
        + (star u ⬝ᵥ O.mulVec v).re := by
  have hcc : star ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hexp : star (u + v) ⬝ᵥ O.mulVec (u + v)
      = (star u ⬝ᵥ O.mulVec u + star v ⬝ᵥ O.mulVec v)
        + (star u ⬝ᵥ O.mulVec v + star v ⬝ᵥ O.mulVec u) := by
    rw [Matrix.mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hcross : star v ⬝ᵥ O.mulVec u = star (star u ⬝ᵥ O.mulVec v) := by
    rw [star_dotProduct_mulVec_conjTranspose O v u, hHerm.eq, Matrix.star_dotProduct]
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, hcc, hexp, hcross, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- **General Ξ sandwich expansion (Tasaki eqs. (4.2.45)/(4.2.49)).**  For Hermitian `O`, the Tanaka
state `Ξ = (1/√2)(u_M + u_{M+1})` (with `u_k` the unit-normalized tower terms) has
`⟨Ξ| O |Ξ⟩.re = ½(⟨u_M|O|u_M⟩.re + ⟨u_{M+1}|O|u_{M+1}⟩.re) + ⟨u_M|O|u_{M+1}⟩.re`.  Reduces each
relation's numerator to the two diagonal matrix elements plus one cross term. -/
theorem tanakaSSBState_dotProduct_mulVec_re_eq (A : Λ → Bool) (M : ℕ) (O : ManyBodyOpS Λ N)
    (hHerm : O.IsHermitian) (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (star (tanakaSSBState A N M Φ) ⬝ᵥ O.mulVec (tanakaSSBState A N M Φ)).re
      = (1 / 2) * ((star (unitNormalize (tanakaTowerTerm A N M Φ)) ⬝ᵥ
            O.mulVec (unitNormalize (tanakaTowerTerm A N M Φ))).re
          + (star (unitNormalize (tanakaTowerTerm A N (M + 1) Φ)) ⬝ᵥ
            O.mulVec (unitNormalize (tanakaTowerTerm A N (M + 1) Φ))).re)
        + (star (unitNormalize (tanakaTowerTerm A N M Φ)) ⬝ᵥ
          O.mulVec (unitNormalize (tanakaTowerTerm A N (M + 1) Φ))).re := by
  rw [tanakaSSBState]
  exact sqrtTwoInv_smul_add_re_sandwich O hHerm (unitNormalize (tanakaTowerTerm A N M Φ))
    (unitNormalize (tanakaTowerTerm A N (M + 1) Φ))

/-! ### Charge-parity cross-term vanishing for a charge-conserving operator -/

/-- **Charge-parity cross-term vanishing for a charge-conserving `O`.**  For a total-spin-`3`
singlet `Φ`, if `O` commutes with the parity operator `Û = exp(iπ Ŝ_tot^{(3)})`
(`O Û = Û O`, i.e. `O` conserves the magnetization parity), then the two adjacent Tanaka tower terms
are `O`-decoupled: `⟨(Ô_L^{(1)})^M Φ, O (Ô_L^{(1)})^{M+1} Φ⟩ = 0`.  They are `Û`-eigenvectors with
distinct eigenvalues `(-1)^M ≠ (-1)^{M+1}`, so `O` (preserving the eigenspaces) cannot connect them.
The axis-`3` / squared-order-operator analogue of the energy cross-term vanishing (eq. (4.2.69)). -/
theorem tanakaTowerTerm_cross_charge_conserving_eq_zero (A : Λ → Bool) (O : ManyBodyOpS Λ N) (M : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (hcomm : O * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
        = Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * O) :
    star (tanakaTowerTerm A N M Φ) ⬝ᵥ O.mulVec (tanakaTowerTerm A N (M + 1) Φ) = 0 := by
  refine dotProduct_eq_zero_of_diagonal_eigen (lam := (-1) ^ M) (mu := (-1) ^ (M + 1))
    (diagonal_magParitySignS_mulVec_tanakaTowerTerm A M hsing) ?_ ?_
  · rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec,
      diagonal_magParitySignS_mulVec_tanakaTowerTerm A (M + 1) hsing, Matrix.mulVec_smul]
  · intro h
    have hne : ((-1 : ℂ)) ^ M ≠ 0 := pow_ne_zero M (by norm_num)
    apply hne
    rw [pow_succ] at h
    exact (mul_eq_zero.mp (by linear_combination h : (2 : ℂ) * (-1) ^ M = 0)).resolve_left
      two_ne_zero

end LatticeSystem.Quantum
