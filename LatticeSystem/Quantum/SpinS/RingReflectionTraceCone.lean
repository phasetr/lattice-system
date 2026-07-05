/-
Trace reflection positivity: the `β = 0` base case of Gibbs reflection positivity
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 4).

The **trace functional** `X ↦ Tr X` on the even-ring operator algebra is reflection positive:
for every left-supported operator `A` (an element of `B(H_left) ⊗ I_right`),
`0 ≤ Re Tr(θ(A) · A)`.  In fact `Tr(θ(A) · A) = ‖∑_ℓ D ℓ‖²` is a perfect square, where the sum
runs over left-half configurations `ℓ` and `D` is the left-diagonal value of `A`.

The proof has two ingredients:

* **Support collapse.**  Both support conditions of `SupportedOnLeftS` force the only surviving
  term of `Tr(θ(A) · A) = ∑_{σ,μ} θ(A) σ μ · A μ σ` to be the diagonal `μ = σ`, so the trace
  equals `∑_σ conj (A (ρσ) (ρσ)) · A σ σ`.

* **Left/right factorization.**  Splitting the configuration space as a product of the left- and
  right-half configurations (`configSplitEquiv`, built from `finSumFinEquiv`), the diagonal value
  `A σ σ` depends only on the left half while `A (ρσ) (ρσ)` depends only on the right half; the
  sum factorizes into `(∑_ℓ D ℓ) · conj (∑_ℓ D ℓ) = ‖∑_ℓ D ℓ‖² ≥ 0`.

This trace cone is the `β = 0` building block on which a later layer mounts the Gibbs exponential
via the Trotter / Lie-product expansion.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionPositivity

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The index equivalence splitting the ring sites `Fin (2n)` into a left half and a right half,
`Fin (2n) ≃ Fin n ⊕ Fin n`, built from `finSumFinEquiv`.  The left sites `{0,…,n−1}` map to
`Sum.inl`, the right sites `{n,…,2n−1}` to `Sum.inr`. -/
def ringHalfEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
  (finCongr (two_mul n)).trans finSumFinEquiv.symm

/-- The left half of `Fin (2n)` under `ringHalfEquiv`: `Sum.inl i` corresponds to site `i`. -/
theorem ringHalfEquiv_symm_inl (i : Fin n) :
    ((ringHalfEquiv n).symm (Sum.inl i) : Fin (2 * n)) = ⟨(i : ℕ), by have := i.isLt; omega⟩ := by
  apply Fin.ext
  simp only [ringHalfEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
    finCongr_symm, finCongr_apply_coe, Fin.val_castAdd]

/-- The right half of `Fin (2n)` under `ringHalfEquiv`: `Sum.inr j` corresponds to site `n + j`. -/
theorem ringHalfEquiv_symm_inr (j : Fin n) :
    ((ringHalfEquiv n).symm (Sum.inr j) : Fin (2 * n))
      = ⟨n + (j : ℕ), by have := j.isLt; omega⟩ := by
  apply Fin.ext
  simp only [ringHalfEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, finSumFinEquiv_apply_right,
    finCongr_symm, finCongr_apply_coe, Fin.val_natAdd]

/-- Split a ring configuration into its left-half and right-half restrictions,
`(Fin (2n) → Fin (N+1)) ≃ (Fin n → Fin (N+1)) × (Fin n → Fin (N+1))`.  The first component is the
configuration restricted to the left sites, the second to the right sites. -/
def configSplitEquiv (n N : ℕ) :
    (Fin (2 * n) → Fin (N + 1)) ≃ ((Fin n → Fin (N + 1)) × (Fin n → Fin (N + 1))) :=
  (Equiv.arrowCongr (ringHalfEquiv n) (Equiv.refl (Fin (N + 1)))).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin n) (Fin (N + 1)))

/-- Left component of the configuration split: the value at left site `i`. -/
theorem configSplitEquiv_fst (σ : Fin (2 * n) → Fin (N + 1)) (i : Fin n) :
    (configSplitEquiv n N σ).1 i = σ ⟨(i : ℕ), by have := i.isLt; omega⟩ := by
  change (Equiv.sumArrowEquivProdArrow _ _ _ (fun x => σ ((ringHalfEquiv n).symm x))).1 i = _
  rw [Equiv.sumArrowEquivProdArrow_apply_fst, ringHalfEquiv_symm_inl]

/-- Right component of the configuration split: the value at right site `n + j`. -/
theorem configSplitEquiv_snd (σ : Fin (2 * n) → Fin (N + 1)) (j : Fin n) :
    (configSplitEquiv n N σ).2 j = σ ⟨n + (j : ℕ), by have := j.isLt; omega⟩ := by
  change (Equiv.sumArrowEquivProdArrow _ _ _ (fun x => σ ((ringHalfEquiv n).symm x))).2 j = _
  rw [Equiv.sumArrowEquivProdArrow_apply_snd, ringHalfEquiv_symm_inr]

/-- Value of a recombined configuration at a left site: `(configSplitEquiv).symm (ℓ, r)` agrees with
`ℓ` on the left half. -/
theorem configSplitEquiv_symm_apply_left (ℓ r : Fin n → Fin (N + 1)) (i : Fin (2 * n))
    (hi : (i : ℕ) < n) : (configSplitEquiv n N).symm (ℓ, r) i = ℓ ⟨(i : ℕ), hi⟩ := by
  have h := configSplitEquiv_fst ((configSplitEquiv n N).symm (ℓ, r)) ⟨(i : ℕ), hi⟩
  rw [Equiv.apply_symm_apply] at h
  rw [← h]

/-- For a left-supported operator the diagonal entry `A σ σ` depends only on the left half:
if `σ` and `τ` agree on every left site then `A σ σ = A τ τ`. -/
theorem SupportedOnLeftS.diag_eq {A : ManyBodyOpS (Fin (2 * n)) N} (hA : SupportedOnLeftS n N A)
    {σ τ : Fin (2 * n) → Fin (N + 1)} (h : ∀ i : Fin (2 * n), (i : ℕ) < n → σ i = τ i) :
    A σ σ = A τ τ :=
  hA.2 σ σ τ τ (fun _ _ => rfl) (fun _ _ => rfl) h h

/-- The left half of the reflected configuration `ρσ` equals the right half of `σ` read in reflected
order: `(configSplitEquiv (ρσ)).1 = (configSplitEquiv σ).2 ∘ Fin.rev`. -/
theorem configSplitEquiv_fst_ringConfigReflect (σ : Fin (2 * n) → Fin (N + 1)) (j : Fin n) :
    (configSplitEquiv n N (ringConfigReflect n N σ)).1 j
      = (configSplitEquiv n N σ).2 (Fin.rev j) := by
  rw [configSplitEquiv_fst, configSplitEquiv_snd]
  unfold ringConfigReflect
  congr 1
  apply Fin.ext
  rw [ringReflect_val]
  change 2 * n - 1 - (j : ℕ) = n + (Fin.rev j : ℕ)
  rw [Fin.val_rev]
  have := j.isLt
  omega

/-- Left-diagonal sum `S(A) = ∑_ℓ A_{(ℓ,ℓ),(ℓ,ℓ)}`, the cone "square-root" coordinate of a
left-supported operator: the scalar value that enters the reflection-positive factorization
`Tr(θ(A)·B) = conj(S A)·S B`. -/
noncomputable def refLeftSum (n N : ℕ) (A : ManyBodyOpS (Fin (2 * n)) N) : ℂ :=
  ∑ ℓ : Fin n → Fin (N + 1),
    A ((configSplitEquiv n N).symm (ℓ, ℓ)) ((configSplitEquiv n N).symm (ℓ, ℓ))

/-- **Bilinear reflection base identity (the `β = 0` cone).**  For left-supported operators `A`, `B`
the reflection trace form factorizes over the left-diagonal coordinate `refLeftSum`:
`Tr(θ(A)·B) = conj(S A)·S B`.  This is the genuine bilinear generalization of the diagonal
`traceFunctional_reflectionPositive` (recovered by `B := A`); it is the base identity on which the
Gibbs / doubled Cauchy–Schwarz layer of the Dyson–Lieb–Simon / Shastry argument is mounted
(Tasaki §4.1, Theorem 4.2). -/
theorem trace_theta_mul_eq_refLeftSum_mul {A B : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    (ringReflectionThetaS n N A * B).trace
      = starRingEnd ℂ (refLeftSum n N A) * refLeftSum n N B := by
  -- `DA`, `DB` are the left-diagonal summand functions of `A`, `B`; `refLeftSum` is their sum.
  set DA : (Fin n → Fin (N + 1)) → ℂ :=
    fun ℓ => A ((configSplitEquiv n N).symm (ℓ, ℓ)) ((configSplitEquiv n N).symm (ℓ, ℓ))
    with hDA
  set DB : (Fin n → Fin (N + 1)) → ℂ :=
    fun ℓ => B ((configSplitEquiv n N).symm (ℓ, ℓ)) ((configSplitEquiv n N).symm (ℓ, ℓ))
    with hDB
  have hrA : refLeftSum n N A = ∑ ℓ, DA ℓ := rfl
  have hrB : refLeftSum n N B = ∑ ℓ, DB ℓ := rfl
  rw [hrA, hrB]
  -- Each diagonal is a function of the left half alone.
  have hADA : ∀ τ : Fin (2 * n) → Fin (N + 1), A τ τ = DA (configSplitEquiv n N τ).1 := by
    intro τ
    simp only [hDA]
    apply hA.diag_eq
    intro i hi
    rw [configSplitEquiv_symm_apply_left _ _ i hi, configSplitEquiv_fst]
  have hADB : ∀ τ : Fin (2 * n) → Fin (N + 1), B τ τ = DB (configSplitEquiv n N τ).1 := by
    intro τ
    simp only [hDB]
    apply hB.diag_eq
    intro i hi
    rw [configSplitEquiv_symm_apply_left _ _ i hi, configSplitEquiv_fst]
  -- Step 1: support collapse.  Left agreement now comes from `hA.theta_right`, right from `hB.1`.
  have hcollapse : (ringReflectionThetaS n N A * B).trace
      = ∑ σ, ringReflectionThetaS n N A σ σ * B σ σ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.sum_eq_single σ]
    · intro μ _ hμ
      by_contra hprod
      obtain ⟨hθne, hBne⟩ := mul_ne_zero_iff.mp hprod
      have hL : ∀ i : Fin (2 * n), (i : ℕ) < n → σ i = μ i := hA.theta_right σ μ hθne
      have hR : ∀ i : Fin (2 * n), n ≤ (i : ℕ) → μ i = σ i := hB.1 μ σ hBne
      apply hμ
      funext x
      rcases lt_or_ge (x : ℕ) n with hx | hx
      · exact (hL x hx).symm
      · exact hR x hx
    · intro h; exact absurd (Finset.mem_univ σ) h
  -- Step 2: rewrite the `θ`-diagonal and `B`-diagonal, pass to `DA`, `DB`.
  have hsum : (ringReflectionThetaS n N A * B).trace
      = ∑ σ, starRingEnd ℂ (DA fun j => (configSplitEquiv n N σ).2 (Fin.rev j))
          * DB (configSplitEquiv n N σ).1 := by
    rw [hcollapse]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [ringReflectionThetaS_apply, hADA (ringConfigReflect n N σ), hADB σ]
    have he : (configSplitEquiv n N (ringConfigReflect n N σ)).1
        = fun j => (configSplitEquiv n N σ).2 (Fin.rev j) :=
      funext (configSplitEquiv_fst_ringConfigReflect σ)
    rw [he]
  -- Step 3: reindex the `r`-sum by `r ↦ r ∘ rev`.
  have hC : (∑ r : Fin n → Fin (N + 1), starRingEnd ℂ (DA fun j => r (Fin.rev j)))
      = starRingEnd ℂ (∑ r, DA r) := by
    have hsc : (∑ r : Fin n → Fin (N + 1), starRingEnd ℂ (DA fun j => r (Fin.rev j)))
        = ∑ r, starRingEnd ℂ (DA r) :=
      Fintype.sum_equiv (Equiv.arrowCongr (Function.Involutive.toPerm Fin.rev Fin.rev_rev)
          (Equiv.refl (Fin (N + 1))))
        (fun r : Fin n → Fin (N + 1) => starRingEnd ℂ (DA fun j => r (Fin.rev j)))
        (fun r : Fin n → Fin (N + 1) => starRingEnd ℂ (DA r)) (fun _ => rfl)
    rw [hsc, ← map_sum]
  -- Step 4: factorize the double sum into `conj(S A)·S B`.
  have hdouble : (∑ ℓ, ∑ r : Fin n → Fin (N + 1),
        starRingEnd ℂ (DA fun j => r (Fin.rev j)) * DB ℓ)
      = starRingEnd ℂ (∑ ℓ, DA ℓ) * ∑ ℓ, DB ℓ := by
    simp_rw [← Finset.sum_mul]
    rw [hC, ← Finset.mul_sum]
  -- Assemble.
  rw [hsum, ← Equiv.sum_comp (configSplitEquiv n N).symm
      (fun σ => starRingEnd ℂ (DA fun j => (configSplitEquiv n N σ).2 (Fin.rev j))
        * DB (configSplitEquiv n N σ).1)]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, hdouble]

/-- **Trace reflection positivity (the `β = 0` base case).**  The trace functional `X ↦ Tr X` on the
even-ring operator algebra is a reflection-positive functional: for every left-supported operator
`A`, `0 ≤ Re Tr(θ(A) · A)`.  The proof shows `Tr(θ(A)·A) = conj S · S = ‖S‖²` with
`S = ∑_ℓ D ℓ` the sum of the left-diagonal values of `A`, hence its real part is nonnegative.
This is the infinite-temperature base of the Dyson–Lieb–Simon / Shastry reflection-positivity
argument (Tasaki §4.1, Theorem 4.2). -/
theorem traceFunctional_reflectionPositive (n N : ℕ) :
    ReflectionPositiveFunctionalS n N (fun X => X.trace) := by
  intro A hA
  change 0 ≤ (ringReflectionThetaS n N A * A).trace.re
  rw [trace_theta_mul_eq_refLeftSum_mul hA hA, mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end LatticeSystem.Quantum
