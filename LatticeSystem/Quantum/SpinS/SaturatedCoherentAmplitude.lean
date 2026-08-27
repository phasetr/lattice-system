import LatticeSystem.Quantum.SpinS.AllAlignedStateCore
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Spin-`S` saturated-ferromagnet coherent state and its one-site amplitude

The coherent state of the saturated ferromagnet is
`Ξ_{θ,φ} = Û_φ^{(3)} Û_θ^{(2)} Φ↑` with `Û_α^{(a)} = exp(-i α Ŝ_tot^{(a)})` acting on the
all-aligned highest-weight state `Φ↑`.  This module defines that state through the matrix
exponential, defines the one-site amplitude

  `amp N θ j = √(binom N j) · cos(θ/2)^{N - j} · sin(θ/2)^j`,

and proves that at `φ = 0` the coherent state is the site-product of these amplitudes.

The product form is obtained from uniqueness for the linear ODE `ẋ = -i Ŝ_tot^{(2)} x`: both the
matrix-exponential state and the amplitude product solve it with the same value at `θ = 0`.

References: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020.
The coherent state `Ξ_{θ,φ} := Û_φ^{(3)} Û_θ^{(2)} Φ↑` is eq. (2.4.6), p. 33, and the global
rotation `Û_θ^{(α)} = exp(-iθ Ŝ_tot^{(α)})` is eq. (2.2.11), p. 22.  The site-product form of
`Ξ_{θ,φ}` is eq. (S.18) of the solution to Problem 2.4.c (statement p. 34, solution p. 497,
stated there for `S = 1/2`).  It is established here as the foundation for Problem 2.4.b
(statement p. 34, solution pp. 496-497, eq. (S.17)), whose solution expands
`Û_θ^{(2)} Φ↑ = Σ_M c_M Φ_M` and needs every `c_M` to be nonzero.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace

/-! ## Binomial square-root ladder identities -/

/-- Raising-step normalisation: `√((j+1)(N-j)) · √(binom N (j+1)) = (N-j) · √(binom N j)`.
This is the identity that makes `Ŝ^+` act on the one-site amplitudes of Tasaki's coherent state
(*Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.4.6), p. 33; site-product form
eq. (S.18) of the solution to Problem 2.4.c, p. 497) by a shift of the exponents alone. -/
private lemma sqrt_choose_raise (N : ℕ) {i : ℕ} (hi : i < N) :
    Real.sqrt (((i : ℝ) + 1) * ((N : ℝ) - ((i : ℝ) + 1) + 1)) *
        Real.sqrt ((N.choose (i + 1) : ℕ) : ℝ)
      = ((N : ℝ) - (i : ℝ)) * Real.sqrt ((N.choose i : ℕ) : ℝ) := by
  have hiN : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi.le
  have hNi : (0 : ℝ) ≤ (N : ℝ) - (i : ℝ) := by linarith
  have harg : ((i : ℝ) + 1) * ((N : ℝ) - ((i : ℝ) + 1) + 1)
      = ((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ)) := by ring
  have hcast : ((N.choose (i + 1) : ℕ) : ℝ) * ((i : ℝ) + 1)
      = ((N.choose i : ℕ) : ℝ) * ((N : ℝ) - (i : ℝ)) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.choose_succ_right_eq N i)
    push_cast [Nat.cast_sub hi.le] at h
    linarith
  have hR : ((N : ℝ) - (i : ℝ)) * Real.sqrt ((N.choose i : ℕ) : ℝ)
      = Real.sqrt ((((N : ℝ) - (i : ℝ)) ^ 2) * ((N.choose i : ℕ) : ℝ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hNi]
  rw [harg, hR, ← Real.sqrt_mul (mul_nonneg (by positivity) hNi)]
  congr 1
  linear_combination ((N : ℝ) - (i : ℝ)) * hcast

/-- Lowering-step normalisation: `√((N-k)(k+1)) · √(binom N k) = (k+1) · √(binom N (k+1))`.
Companion of `sqrt_choose_raise` for the action of `Ŝ^-` on the one-site amplitudes of Tasaki's
coherent state (*Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.4.6), p. 33;
site-product form eq. (S.18) of the solution to Problem 2.4.c, p. 497). -/
private lemma sqrt_choose_lower (N : ℕ) {k : ℕ} (hk : k + 1 ≤ N) :
    Real.sqrt (((N : ℝ) - (k : ℝ)) * ((k : ℝ) + 1)) * Real.sqrt ((N.choose k : ℕ) : ℝ)
      = ((k : ℝ) + 1) * Real.sqrt ((N.choose (k + 1) : ℕ) : ℝ) := by
  have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_succ_le hk
  have hNk : (0 : ℝ) ≤ (N : ℝ) - (k : ℝ) := by linarith
  have hcast : ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1)
      = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - (k : ℝ)) := by
    have h := congrArg (fun j : ℕ => (j : ℝ)) (Nat.choose_succ_right_eq N k)
    push_cast [Nat.cast_sub (Nat.le_of_succ_le hk)] at h
    linarith
  have hR : ((k : ℝ) + 1) * Real.sqrt ((N.choose (k + 1) : ℕ) : ℝ)
      = Real.sqrt ((((k : ℝ) + 1) ^ 2) * ((N.choose (k + 1) : ℕ) : ℝ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hR, ← Real.sqrt_mul (mul_nonneg hNk (by positivity))]
  congr 1
  linear_combination (-((k : ℝ) + 1)) * hcast

/-! ## One-site coherent amplitude -/

/-- **One-site coherent amplitude** `√(binom N j) · cos(θ/2)^{N-j} · sin(θ/2)^j` of the spin-`S`
saturated-ferromagnet coherent state, with `N = 2S` and basis index `j : Fin (N + 1)` (magnetic
quantum number `m = N/2 - j`).  For `N = 1` this is the pair `(cos(θ/2), sin(θ/2))` of the
one-site factor of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, eq. (S.18)
(solution to Problem 2.4.c, p. 497, stated there for `S = 1/2`), taken at `φ = 0`. -/
noncomputable def saturatedCoherentAmp (N : ℕ) (θ : ℝ) (j : Fin (N + 1)) : ℂ :=
  (Real.sqrt (N.choose (j : ℕ)) : ℂ) * (Real.cos (θ / 2) : ℂ) ^ (N - (j : ℕ)) *
    (Real.sin (θ / 2) : ℂ) ^ (j : ℕ)

/-- Action of `Ŝ^+` on the one-site coherent amplitudes: the raising operator shifts the
`cos`/`sin` exponents and replaces the binomial factor by `(N - j) √(binom N j)`. -/
private lemma spinSOpPlus_mulVec_saturatedCoherentAmp (N : ℕ) (θ : ℝ) (i : Fin (N + 1)) :
    (spinSOpPlus N *ᵥ saturatedCoherentAmp N θ) i
      = ((N : ℂ) - ((i : ℕ) : ℂ)) * (Real.sqrt (N.choose (i : ℕ)) : ℂ) *
          (Real.cos (θ / 2) : ℂ) ^ (N - (i : ℕ) - 1) *
          (Real.sin (θ / 2) : ℂ) ^ ((i : ℕ) + 1) := by
  have hiN : (i : ℕ) < N + 1 := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rcases Nat.lt_or_ge (i : ℕ) N with hlt | hge
  · have hsucc : (i : ℕ) + 1 < N + 1 := by omega
    rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hsucc⟩ : Fin (N + 1))]
    · rw [spinSOpPlus_apply_raise N (i := i) (j := ⟨(i : ℕ) + 1, hsucc⟩) rfl]
      have hk := sqrt_choose_raise N hlt
      have hk2 : ((Real.sqrt ((((i : ℕ) + 1 : ℕ) : ℝ) *
              ((N : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ) + 1)) : ℝ) : ℂ) *
            ((Real.sqrt ((N.choose ((i : ℕ) + 1) : ℕ) : ℝ) : ℝ) : ℂ)
          = ((N : ℂ) - ((i : ℕ) : ℂ)) * ((Real.sqrt ((N.choose (i : ℕ) : ℕ) : ℝ) : ℝ) : ℂ) := by
        push_cast at hk ⊢
        exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
      unfold saturatedCoherentAmp
      rw [show N - ((i : ℕ) + 1) = N - (i : ℕ) - 1 from by omega]
      linear_combination ((Real.cos (θ / 2) : ℂ) ^ (N - (i : ℕ) - 1) *
        (Real.sin (θ / 2) : ℂ) ^ ((i : ℕ) + 1)) * hk2
    · intro b _ hb
      rw [spinSOpPlus_apply_other N (fun hval => hb (Fin.ext hval.symm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hiEq : (i : ℕ) = N := by omega
    rw [Finset.sum_eq_zero]
    · rw [hiEq]; simp
    · intro b _
      have hb := b.isLt
      rw [spinSOpPlus_apply_other N (by omega), zero_mul]

/-- Action of `Ŝ^-` on the one-site coherent amplitudes: the lowering operator shifts the
`cos`/`sin` exponents the other way and replaces the binomial factor by `j √(binom N j)`. -/
private lemma spinSOpMinus_mulVec_saturatedCoherentAmp (N : ℕ) (θ : ℝ) (i : Fin (N + 1)) :
    (spinSOpMinus N *ᵥ saturatedCoherentAmp N θ) i
      = ((i : ℕ) : ℂ) * (Real.sqrt (N.choose (i : ℕ)) : ℂ) *
          (Real.cos (θ / 2) : ℂ) ^ (N - (i : ℕ) + 1) *
          (Real.sin (θ / 2) : ℂ) ^ ((i : ℕ) - 1) := by
  have hiN : (i : ℕ) < N + 1 := i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rcases Nat.eq_zero_or_pos (i : ℕ) with hzero | hpos
  · rw [Finset.sum_eq_zero]
    · rw [hzero]; simp
    · intro b _
      rw [spinSOpMinus_apply_other N (by omega), zero_mul]
  · obtain ⟨k, hk0⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hklt : k < N + 1 := by omega
    have hkle : k + 1 ≤ N := by omega
    rw [Finset.sum_eq_single (⟨k, hklt⟩ : Fin (N + 1))]
    · rw [spinSOpMinus_apply_lower N (i := i) (j := ⟨k, hklt⟩) (by simp [hk0])]
      have hk := sqrt_choose_lower N hkle
      have hk2 : ((Real.sqrt (((N : ℝ) - (k : ℝ)) * ((k : ℝ) + 1)) : ℝ) : ℂ) *
            ((Real.sqrt ((N.choose k : ℕ) : ℝ) : ℝ) : ℂ)
          = (((k + 1 : ℕ) : ℂ)) * ((Real.sqrt ((N.choose (k + 1) : ℕ) : ℝ) : ℝ) : ℂ) := by
        exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
      unfold saturatedCoherentAmp
      rw [hk0, show N - (k + 1) + 1 = N - k from by omega, show k + 1 - 1 = k from rfl]
      linear_combination ((Real.cos (θ / 2) : ℂ) ^ (N - k) *
        (Real.sin (θ / 2) : ℂ) ^ k) * hk2
    · intro b _ hb
      refine mul_eq_zero_of_left (spinSOpMinus_apply_other N ?_) _
      intro hval
      exact hb (Fin.ext (show (b : ℕ) = k from by omega))
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **One-site generator equation.** The one-site coherent amplitude solves
`d/dθ amp = -i Ŝ^{(2)} amp`, the single-site form of the rotation generator of Tasaki's coherent
state (*Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.4.6), p. 33, with the
rotation `Û_θ^{(α)} = exp(-iθ Ŝ_tot^{(α)})` of eq. (2.2.11), p. 22).  The half-angle `θ/2` of
the amplitude is exactly what this equation forces. -/
private lemma saturatedCoherentAmp_hasDerivAt (N : ℕ) (θ : ℝ) (j : Fin (N + 1)) :
    HasDerivAt (fun t : ℝ => saturatedCoherentAmp N t j)
      ((((-Complex.I) • spinSOp2 N) *ᵥ saturatedCoherentAmp N θ) j) θ := by
  have hjN : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  have hc : HasDerivAt (fun t : ℝ => (Real.cos (t / 2) : ℂ))
      (-(Real.sin (θ / 2) : ℂ) * (1 / 2)) θ := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using (((hasDerivAt_id θ).div_const 2).cos).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin (t / 2) : ℂ))
      ((Real.cos (θ / 2) : ℂ) * (1 / 2)) θ := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using (((hasDerivAt_id θ).div_const 2).sin).ofReal_comp
  have hI : (-Complex.I) * (1 / (2 * Complex.I)) = -(1 / 2 : ℂ) := by
    field_simp
  have hsplit : (((-Complex.I) • spinSOp2 N) *ᵥ saturatedCoherentAmp N θ) j
      = -(1 / 2 : ℂ) * ((spinSOpPlus N *ᵥ saturatedCoherentAmp N θ) j
          - (spinSOpMinus N *ᵥ saturatedCoherentAmp N θ) j) := by
    rw [Matrix.smul_mulVec]
    unfold spinSOp2
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((spinSOpPlus N *ᵥ saturatedCoherentAmp N θ) j
      - (spinSOpMinus N *ᵥ saturatedCoherentAmp N θ) j) * hI
  have hval : (((-Complex.I) • spinSOp2 N) *ᵥ saturatedCoherentAmp N θ) j
      = (Real.sqrt (N.choose (j : ℕ)) : ℂ) *
            (((N - (j : ℕ) : ℕ) : ℂ) * (Real.cos (θ / 2) : ℂ) ^ (N - (j : ℕ) - 1) *
              (-(Real.sin (θ / 2) : ℂ) * (1 / 2))) * (Real.sin (θ / 2) : ℂ) ^ (j : ℕ)
          + (Real.sqrt (N.choose (j : ℕ)) : ℂ) * (Real.cos (θ / 2) : ℂ) ^ (N - (j : ℕ)) *
              (((j : ℕ) : ℂ) * (Real.sin (θ / 2) : ℂ) ^ ((j : ℕ) - 1) *
                ((Real.cos (θ / 2) : ℂ) * (1 / 2))) := by
    rw [hsplit, spinSOpPlus_mulVec_saturatedCoherentAmp,
      spinSOpMinus_mulVec_saturatedCoherentAmp, Nat.cast_sub hjN, pow_succ, pow_succ]
    ring
  rw [hval]
  simp only [saturatedCoherentAmp]
  exact ((hc.fun_pow (N - (j : ℕ))).const_mul _).fun_mul (hs.fun_pow (j : ℕ))

/-! ## One-site operators acting on product states -/

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Leibniz action of a one-site operator on a product state.** Applying `onSiteS x A` to the
product vector `τ ↦ ∏ y, f y (τ y)` acts by `A` on the site-`x` factor and leaves the other
factors untouched. -/
theorem onSiteS_mulVec_prod (x : V) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (f : V → Fin (N + 1) → ℂ) (σ : V → Fin (N + 1)) :
    ((onSiteS x A : ManyBodyOpS V N) *ᵥ fun τ => ∏ y, f y (τ y)) σ
      = (A *ᵥ f x) (σ x) * ∏ y ∈ Finset.univ.erase x, f y (σ y) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  have hsupp : ∀ τ ∈ (Finset.univ : Finset (V → Fin (N + 1))),
      τ ∉ (Finset.univ : Finset (Fin (N + 1))).image (fun c => Function.update σ x c) →
      (onSiteS x A : ManyBodyOpS V N) σ τ * (∏ y, f y (τ y)) = 0 := by
    intro τ _ hτ
    have hne : ¬ (∀ k, k ≠ x → σ k = τ k) := by
      intro hall
      refine hτ (Finset.mem_image.2 ⟨τ x, Finset.mem_univ _, ?_⟩)
      funext k
      by_cases hk : k = x
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact hall k hk
    rw [onSiteS_apply_eq_zero_of_off_site_diff x A hne, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Fin (N + 1))).image (fun c => Function.update σ x c))) hsupp,
    Finset.sum_image (by
      intro a _ b _ hab
      have := congrFun hab x
      simpa using this)]
  have hprod : ∀ c : Fin (N + 1), (∏ y, f y (Function.update σ x c y))
      = f x c * ∏ y ∈ Finset.univ.erase x, f y (σ y) := by
    intro c
    rw [← Finset.mul_prod_erase Finset.univ (fun y => f y (Function.update σ x c y))
      (Finset.mem_univ x)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro y hy
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
  have hentry : ∀ c : Fin (N + 1),
      (onSiteS x A : ManyBodyOpS V N) σ (Function.update σ x c) = A (σ x) c := by
    intro c
    rw [onSiteS_apply_of_off_site_agree x A (fun k hk => (Function.update_of_ne hk _ _).symm)]
    simp
  simp only [hentry, hprod]
  simp only [Finset.sum_mul, mul_assoc]

/-! ## Coherent state -/

/-- **Global rotation about axis 2**, `Û_θ^{(2)} = exp(-iθ Ŝ_tot^{(2)})`, of Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.2.11), p. 22. -/
noncomputable def saturatedGlobalRot2 (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) (θ : ℝ) :
    ManyBodyOpS V N :=
  exp (θ • ((-Complex.I) • totalSpinSOp2 V N))

/-- **Global rotation about axis 3**, `Û_φ^{(3)} = exp(-iφ Ŝ_tot^{(3)})`, of Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.2.11), p. 22. -/
noncomputable def saturatedGlobalRot3 (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ) (φ : ℝ) :
    ManyBodyOpS V N :=
  exp (φ • ((-Complex.I) • totalSpinSOp3 V N))

/-- **Saturated-ferromagnet coherent state** `Ξ_{θ,φ} = Û_φ^{(3)} Û_θ^{(2)} Φ↑`, obtained by
rotating the all-aligned highest-weight state.  Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, eq. (2.4.6), p. 33. -/
noncomputable def saturatedCoherentState (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ)
    (θ φ : ℝ) : (V → Fin (N + 1)) → ℂ :=
  (saturatedGlobalRot3 V N φ * saturatedGlobalRot2 V N θ) *ᵥ allAlignedStateS V N 0

section ProductForm

open scoped Matrix.Norms.Operator

/-- Applying a fixed vector to a differentiable matrix path differentiates entrywise: the
derivative of `u ↦ A u *ᵥ Φ` is `A' *ᵥ Φ`.  Used to transport the derivative of the matrix
exponential to the coherent state. -/
private lemma hasDerivAt_mulVec_const {Φ : (V → Fin (N + 1)) → ℂ} {A : ℝ → ManyBodyOpS V N}
    {A' : ManyBodyOpS V N} {t : ℝ} (h : HasDerivAt A A' t) :
    HasDerivAt (fun u : ℝ => A u *ᵥ Φ) (A' *ᵥ Φ) t :=
  (LinearMap.mkContinuous
    ({ toFun := fun M : ManyBodyOpS V N => M *ᵥ Φ
       map_add' := fun M M' => by ext; simp [Matrix.add_mulVec]
       map_smul' := fun c M => by ext; simp [Matrix.smul_mulVec] } :
        ManyBodyOpS V N →ₗ[ℝ] ((V → Fin (N + 1)) → ℂ))
    ‖Φ‖ fun M => by rw [mul_comm]; exact Matrix.linfty_opNorm_mulVec M Φ).hasFDerivAt
      |>.comp_hasDerivAt t h

/-- At `φ = 0` only the axis-2 rotation acts, since `Û_0^{(3)} = 1`. -/
private lemma saturatedCoherentState_zero_eq_globalRot2 (θ : ℝ) :
    saturatedCoherentState V N θ 0 = saturatedGlobalRot2 V N θ *ᵥ allAlignedStateS V N 0 := by
  rw [saturatedCoherentState, saturatedGlobalRot3,
    show (0 : ℝ) • ((-Complex.I) • totalSpinSOp3 V N : ManyBodyOpS V N) = 0 from zero_smul _ _,
    NormedSpace.exp_zero, one_mul]

-- The matrix `NormedSpace.exp` derivative needs the operator-norm ring structure, whose uniformity
-- is only reducibly equal to the product uniformity carrying `CompleteSpace`; mathlib's own matrix
-- exponential lemmas relax the transparency check for the same reason.
set_option backward.isDefEq.respectTransparency false in
/-- **Generator equation for the coherent state.** The path `θ ↦ Ξ_{θ,0}` solves the linear ODE
`ẋ = -i Ŝ_tot^{(2)} x` generated by the axis-2 total spin, which is the defining property of the
rotation `Û_θ^{(2)}` in Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
eq. (2.2.11), p. 22. -/
private lemma saturatedCoherentState_zero_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun u : ℝ => saturatedCoherentState V N u 0)
      (((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) *ᵥ saturatedCoherentState V N θ 0)
      θ := by
  simp only [saturatedCoherentState_zero_eq_globalRot2, saturatedGlobalRot2]
  have hd := hasDerivAt_mulVec_const (Φ := allAlignedStateS V N 0)
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ)
      ((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) θ)
  rwa [← Matrix.mulVec_mulVec] at hd

/-- **Product form of the coherent state at `φ = 0`.** At every spin configuration `σ` the
coherent state `Ξ_{θ,0}` equals the product over sites of the one-site amplitudes
`√(binom N (σ x)) cos(θ/2)^{N - σ x} sin(θ/2)^{σ x}`.  This is the general-`S` form, at `φ = 0`,
of the site-product expression for `Ξ_{θ,φ}` in Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, eq. (S.18) of the solution to Problem 2.4.c (p. 497, stated there for
`S = 1/2`); it is the input to Problem 2.4.b (p. 34, solution pp. 496-497, eq. (S.17)).  Both
sides solve the linear ODE generated by `-i Ŝ_tot^{(2)}` and agree at `θ = 0`, so they agree
identically. -/
theorem saturatedCoherentState_zero_apply (θ : ℝ) (σ : V → Fin (N + 1)) :
    saturatedCoherentState V N θ 0 σ = ∏ x : V, saturatedCoherentAmp N θ (σ x) := by
  classical
  suffices h : (fun (t : ℝ) (τ : V → Fin (N + 1)) => ∏ x : V, saturatedCoherentAmp N t (τ x))
      = fun (t : ℝ) => saturatedCoherentState V N t 0 by
    exact (congrFun (congrFun h θ) σ).symm
  have hBsum : ((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N)
      = ∑ x : V, onSiteS x ((-Complex.I) • spinSOp2 N) := by
    simp only [totalSpinSOp2, Finset.smul_sum, onSiteS_smul]
  have hLip : ∀ _t : ℝ, LipschitzOnWith ‖((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N)‖₊
      (fun w : (V → Fin (N + 1)) → ℂ => ((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) *ᵥ w)
      Set.univ := by
    intro _
    refine (LipschitzWith.of_dist_le_mul ?_).lipschitzOnWith
    intro w₁ w₂
    rw [dist_eq_norm, dist_eq_norm, ← Matrix.mulVec_sub, coe_nnnorm]
    exact Matrix.linfty_opNorm_mulVec _ _
  have hFderiv : ∀ t : ℝ,
      HasDerivAt (fun (u : ℝ) (τ : V → Fin (N + 1)) => ∏ x : V, saturatedCoherentAmp N u (τ x))
        (((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) *ᵥ
          fun τ => ∏ x : V, saturatedCoherentAmp N t (τ x)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro τ
    have hB2 : (((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) *ᵥ
          fun ρ : V → Fin (N + 1) => ∏ x : V, saturatedCoherentAmp N t (ρ x)) τ
        = ∑ x : V, (∏ y ∈ Finset.univ.erase x, saturatedCoherentAmp N t (τ y)) •
            ((((-Complex.I) • spinSOp2 N) *ᵥ saturatedCoherentAmp N t) (τ x)) := by
      rw [hBsum, Matrix.sum_mulVec, Finset.sum_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [onSiteS_mulVec_prod x _ (fun _ => saturatedCoherentAmp N t) τ, smul_eq_mul, mul_comm]
    rw [hB2]
    exact HasDerivAt.fun_finset_prod fun x _ => saturatedCoherentAmp_hasDerivAt N t (τ x)
  have hinit : (fun (τ : V → Fin (N + 1)) => ∏ x : V, saturatedCoherentAmp N (0 : ℝ) (τ x))
      = saturatedCoherentState V N 0 0 := by
    rw [saturatedCoherentState_zero_eq_globalRot2, saturatedGlobalRot2,
      show (0 : ℝ) • ((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) = 0 from zero_smul _ _,
      NormedSpace.exp_zero, Matrix.one_mulVec]
    have hamp : ∀ j : Fin (N + 1),
        saturatedCoherentAmp N 0 j = if (j : ℕ) = 0 then 1 else 0 := by
      intro j
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
      · simp [saturatedCoherentAmp, h0]
      · have hj : (j : ℕ) ≠ 0 := by omega
        simp [saturatedCoherentAmp, hj, zero_pow hj]
    funext τ
    rw [Finset.prod_congr rfl (fun x _ => hamp (τ x)), Finset.prod_boole, allAlignedStateS,
      basisVecS_apply]
    have hiff : (∀ i ∈ (Finset.univ : Finset V), (τ i : ℕ) = 0)
        ↔ τ = allAlignedConfigS V N 0 := by
      constructor
      · intro h
        funext x
        exact Fin.val_eq_zero_iff.mp (h x (Finset.mem_univ x))
      · intro h x _
        rw [h]
        rfl
    simp only [hiff]
  exact ODE_solution_unique_univ hLip (fun t => ⟨hFderiv t, trivial⟩)
    (fun t => ⟨saturatedCoherentState_zero_hasDerivAt t, trivial⟩) hinit

end ProductForm

end LatticeSystem.Quantum
