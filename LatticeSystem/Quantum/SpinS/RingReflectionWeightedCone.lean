/-
Weighted trace reflection positivity: the algebraic completion of the trace cone
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 5).

Building on the `β = 0` trace cone (`RingReflectionTraceCone.lean`), this file records the algebraic
facts needed to mount the Gibbs exponential on the cone in a later layer:

* **Multiplicative closure** of the left-half subalgebra: a product of left-supported operators is
  left-supported (`SupportedOnLeftS.mul`).
* **Left/right commutation**: a left-supported `A` commutes with `θ(B)` for any left-supported `B`
  (since `θ(B)` acts on the right half), `SupportedOnLeftS.mul_theta_comm`.
* **Weighted trace cone**: the functional `X ↦ Tr((θ(C)·C)·X)` is reflection positive for every
  left-supported `C` (`weightedTraceFunctional_reflectionPositive`), and so is any nonnegative
  combination `∑ cᵢ θ(Cᵢ)·Cᵢ` (`weightedTraceFunctional_reflectionPositive_finsetSum`).

The weighted cone reduces to the trace cone via `Tr((θC·C)·(θA·A)) = Tr(θ(C·A)·(C·A))`, using `θ`'s
multiplicativity, the left/right commutation `C·θA = θA·C`, the trace's cyclicity, and the
multiplicative closure (`C·A` is left-supported).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTraceCone

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- Two configurations agree on the right half iff their right components under the split agree. -/
theorem right_agree_iff (σ τ : Fin (2 * n) → Fin (N + 1)) :
    (∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ i = τ i)
      ↔ (configSplitEquiv n N σ).2 = (configSplitEquiv n N τ).2 := by
  constructor
  · intro h
    funext j
    rw [configSplitEquiv_snd, configSplitEquiv_snd]
    exact h _ (Nat.le_add_right n _)
  · intro h i hi
    have hσ := configSplitEquiv_snd σ ⟨(i : ℕ) - n, by have := i.isLt; omega⟩
    have hτ := configSplitEquiv_snd τ ⟨(i : ℕ) - n, by have := i.isLt; omega⟩
    have key : σ ⟨n + ((i : ℕ) - n), by have := i.isLt; omega⟩
        = τ ⟨n + ((i : ℕ) - n), by have := i.isLt; omega⟩ := by
      rw [← hσ, ← hτ, h]
    have hidx : (⟨n + ((i : ℕ) - n), by have := i.isLt; omega⟩ : Fin (2 * n)) = i := by
      apply Fin.ext; change n + ((i : ℕ) - n) = (i : ℕ); omega
    rwa [hidx] at key

/-- Two configurations agree on the left half iff their left components under the split agree. -/
theorem left_agree_iff (σ τ : Fin (2 * n) → Fin (N + 1)) :
    (∀ i : Fin (2 * n), (i : ℕ) < n → σ i = τ i)
      ↔ (configSplitEquiv n N σ).1 = (configSplitEquiv n N τ).1 := by
  constructor
  · intro h
    funext j
    rw [configSplitEquiv_fst, configSplitEquiv_fst]
    exact h _ j.isLt
  · intro h i hi
    have hσ := configSplitEquiv_fst σ ⟨(i : ℕ), hi⟩
    have hτ := configSplitEquiv_fst τ ⟨(i : ℕ), hi⟩
    have key : σ ⟨(i : ℕ), by have := i.isLt; omega⟩ = τ ⟨(i : ℕ), by have := i.isLt; omega⟩ := by
      rw [← hσ, ← hτ, h]
    have hidx : (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin (2 * n)) = i := by apply Fin.ext; rfl
    rwa [hidx] at key

/-- A left-supported operator vanishes off the right-diagonal: if the right halves of `σ` and `τ`
differ then `A σ τ = 0`. -/
theorem SupportedOnLeftS.apply_eq_zero_of_snd_ne {A : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) {σ τ : Fin (2 * n) → Fin (N + 1)}
    (h : (configSplitEquiv n N σ).2 ≠ (configSplitEquiv n N τ).2) : A σ τ = 0 := by
  by_contra hne
  exact h ((right_agree_iff σ τ).1 (hA.1 σ τ hne))

/-- **Multiplicative closure of the left-half subalgebra.**  A product of two left-supported
operators is left-supported. -/
theorem SupportedOnLeftS.mul {A B : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    SupportedOnLeftS n N (A * B) := by
  refine ⟨fun σ τ h i hi => ?_, fun σ τ σ' τ' hσ hσ' hL hR => ?_⟩
  · rw [Matrix.mul_apply] at h
    obtain ⟨μ, _, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (hA.1 σ μ (left_ne_zero_of_mul hμ) i hi).trans (hB.1 μ τ (right_ne_zero_of_mul hμ) i hi)
  · rw [Matrix.mul_apply, Matrix.mul_apply,
      ← Equiv.sum_comp (configSplitEquiv n N).symm (fun μ => A σ μ * B μ τ),
      ← Equiv.sum_comp (configSplitEquiv n N).symm (fun μ => A σ' μ * B μ τ'),
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    -- the inner sum over the right half collapses to the single matching value
    have hcol : ∀ (ρ : Fin (2 * n) → Fin (N + 1)) (υ : Fin (2 * n) → Fin (N + 1)),
        (∑ q, A ρ ((configSplitEquiv n N).symm (p, q))
            * B ((configSplitEquiv n N).symm (p, q)) υ)
          = A ρ ((configSplitEquiv n N).symm (p, (configSplitEquiv n N ρ).2))
            * B ((configSplitEquiv n N).symm (p, (configSplitEquiv n N ρ).2)) υ := by
      intro ρ υ
      refine Finset.sum_eq_single (configSplitEquiv n N ρ).2 (fun q _ hq => ?_) (fun h => ?_)
      · apply mul_eq_zero_of_left
        apply hA.apply_eq_zero_of_snd_ne
        rw [Equiv.apply_symm_apply]
        exact fun hcontra => hq hcontra.symm
      · exact absurd (Finset.mem_univ _) h
    rw [hcol σ τ, hcol σ' τ']
    have hAeq : A σ ((configSplitEquiv n N).symm (p, (configSplitEquiv n N σ).2))
        = A σ' ((configSplitEquiv n N).symm (p, (configSplitEquiv n N σ').2)) :=
      hA.2 _ _ _ _
        ((right_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]))
        ((right_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]))
        hL
        ((left_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
    have hBeq : B ((configSplitEquiv n N).symm (p, (configSplitEquiv n N σ).2)) τ
        = B ((configSplitEquiv n N).symm (p, (configSplitEquiv n N σ').2)) τ' :=
      hB.2 _ _ _ _
        ((right_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]; exact (right_agree_iff σ τ).1 hσ))
        ((right_agree_iff _ _).2
          (by rw [Equiv.apply_symm_apply]; exact (right_agree_iff σ' τ').1 hσ'))
        ((left_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
        hR
    rw [hAeq, hBeq]

/-- The right half of the reflected configuration `ρσ` equals the left half of `σ` read in reflected
order: `(configSplitEquiv (ρσ)).2 = (configSplitEquiv σ).1 ∘ Fin.rev`. -/
theorem configSplitEquiv_snd_ringConfigReflect (σ : Fin (2 * n) → Fin (N + 1)) (j : Fin n) :
    (configSplitEquiv n N (ringConfigReflect n N σ)).2 j
      = (configSplitEquiv n N σ).1 (Fin.rev j) := by
  rw [configSplitEquiv_snd, configSplitEquiv_fst]
  unfold ringConfigReflect
  congr 1
  apply Fin.ext
  rw [ringReflect_val]
  change 2 * n - 1 - (n + (j : ℕ)) = (Fin.rev j : ℕ)
  rw [Fin.val_rev]
  have := j.isLt
  omega

/-- `θ(B)` vanishes off the left-diagonal: if the left halves of `μ` and `ν` differ then
`θ(B) μ ν = 0` (for any operator `B`, via condition (1) on `B` after reflection). -/
theorem SupportedOnLeftS.theta_apply_eq_zero_of_fst_ne {B : ManyBodyOpS (Fin (2 * n)) N}
    (hB : SupportedOnLeftS n N B) {μ ν : Fin (2 * n) → Fin (N + 1)}
    (h : (configSplitEquiv n N μ).1 ≠ (configSplitEquiv n N ν).1) :
    ringReflectionThetaS n N B μ ν = 0 := by
  rw [ringReflectionThetaS_apply]
  by_contra hne
  have hB0 : B (ringConfigReflect n N μ) (ringConfigReflect n N ν) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hne; exact hne rfl
  have hr := (right_agree_iff _ _).1 (hB.1 _ _ hB0)
  apply h
  funext j
  have hμ := configSplitEquiv_snd_ringConfigReflect μ (Fin.rev j)
  have hν := configSplitEquiv_snd_ringConfigReflect ν (Fin.rev j)
  rw [Fin.rev_rev] at hμ hν
  rw [← hμ, ← hν, hr]

/-- **Left/right commutation.**  A left-supported operator `A` commutes with `θ(B)` for any
left-supported `B`: `A` acts on the left half and `θ(B)` on the right half. -/
theorem SupportedOnLeftS.mul_theta_comm {A B : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    A * ringReflectionThetaS n N B = ringReflectionThetaS n N B * A := by
  ext σ τ
  rw [Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp (configSplitEquiv n N).symm
        (fun μ => A σ μ * ringReflectionThetaS n N B μ τ),
    ← Equiv.sum_comp (configSplitEquiv n N).symm
        (fun μ => ringReflectionThetaS n N B σ μ * A μ τ)]
  -- Both products collapse to a single surviving configuration.
  have hLHS : (∑ pq, A σ ((configSplitEquiv n N).symm pq)
        * ringReflectionThetaS n N B ((configSplitEquiv n N).symm pq) τ)
      = A σ ((configSplitEquiv n N).symm ((configSplitEquiv n N τ).1, (configSplitEquiv n N σ).2))
        * ringReflectionThetaS n N B
            ((configSplitEquiv n N).symm ((configSplitEquiv n N τ).1, (configSplitEquiv n N σ).2))
            τ := by
    refine Finset.sum_eq_single _ (fun pq _ hpq => ?_) (fun h => absurd (Finset.mem_univ _) h)
    obtain ⟨p, q⟩ := pq
    by_cases hq : q = (configSplitEquiv n N σ).2
    · subst hq
      apply mul_eq_zero_of_right
      apply hB.theta_apply_eq_zero_of_fst_ne
      rw [Equiv.apply_symm_apply]
      exact fun hcontra => hpq (Prod.ext hcontra rfl)
    · apply mul_eq_zero_of_left
      apply hA.apply_eq_zero_of_snd_ne
      rw [Equiv.apply_symm_apply]
      exact fun hcontra => hq hcontra.symm
  have hRHS : (∑ pq, ringReflectionThetaS n N B σ ((configSplitEquiv n N).symm pq)
        * A ((configSplitEquiv n N).symm pq) τ)
      = ringReflectionThetaS n N B σ
            ((configSplitEquiv n N).symm ((configSplitEquiv n N σ).1, (configSplitEquiv n N τ).2))
        * A ((configSplitEquiv n N).symm ((configSplitEquiv n N σ).1, (configSplitEquiv n N τ).2))
            τ := by
    refine Finset.sum_eq_single _ (fun pq _ hpq => ?_) (fun h => absurd (Finset.mem_univ _) h)
    obtain ⟨p, q⟩ := pq
    by_cases hq : q = (configSplitEquiv n N τ).2
    · subst hq
      apply mul_eq_zero_of_left
      apply hB.theta_apply_eq_zero_of_fst_ne
      rw [Equiv.apply_symm_apply]
      exact fun hcontra => hpq (Prod.ext hcontra.symm rfl)
    · apply mul_eq_zero_of_right
      apply hA.apply_eq_zero_of_snd_ne
      rw [Equiv.apply_symm_apply]
      exact hq
  rw [hLHS, hRHS]
  -- the two surviving terms coincide
  set μ₀ := (configSplitEquiv n N).symm ((configSplitEquiv n N τ).1, (configSplitEquiv n N σ).2)
  set μ₁ := (configSplitEquiv n N).symm ((configSplitEquiv n N σ).1, (configSplitEquiv n N τ).2)
  have hAeq : A σ μ₀ = A μ₁ τ :=
    hA.2 _ _ _ _
      ((right_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]))
      ((right_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]))
      ((left_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]))
      ((left_agree_iff _ _).2 (by rw [Equiv.apply_symm_apply]))
  have hθeq : ringReflectionThetaS n N B μ₀ τ = ringReflectionThetaS n N B σ μ₁ := by
    rw [ringReflectionThetaS_apply, ringReflectionThetaS_apply]
    congr 1
    apply hB.2
    · exact (right_agree_iff _ _).2 (by
        funext j
        rw [configSplitEquiv_snd_ringConfigReflect, configSplitEquiv_snd_ringConfigReflect,
          Equiv.apply_symm_apply])
    · exact (right_agree_iff _ _).2 (by
        funext j
        rw [configSplitEquiv_snd_ringConfigReflect, configSplitEquiv_snd_ringConfigReflect,
          Equiv.apply_symm_apply])
    · exact (left_agree_iff _ _).2 (by
        funext j
        rw [configSplitEquiv_fst_ringConfigReflect, configSplitEquiv_fst_ringConfigReflect,
          Equiv.apply_symm_apply])
    · exact (left_agree_iff _ _).2 (by
        funext j
        rw [configSplitEquiv_fst_ringConfigReflect, configSplitEquiv_fst_ringConfigReflect,
          Equiv.apply_symm_apply])
  rw [hAeq, hθeq, mul_comm]

/-- **Weighted trace cone.**  For a left-supported `C`, the functional `X ↦ Tr((θ(C)·C)·X)` is
reflection positive: `0 ≤ Re Tr((θ(C)·C)·(θ(A)·A))` for every left-supported `A`. -/
theorem weightedTraceFunctional_reflectionPositive {C : ManyBodyOpS (Fin (2 * n)) N}
    (hC : SupportedOnLeftS n N C) :
    ReflectionPositiveFunctionalS n N
      (fun X => ((ringReflectionThetaS n N C * C) * X).trace) := by
  intro A hA
  have hkey : (ringReflectionThetaS n N C * C) * (ringReflectionThetaS n N A * A)
      = ringReflectionThetaS n N (C * A) * (C * A) := by
    rw [ringReflectionThetaS_mul,
      show (ringReflectionThetaS n N C * C) * (ringReflectionThetaS n N A * A)
          = ringReflectionThetaS n N C * (C * ringReflectionThetaS n N A) * A by
        simp only [mul_assoc],
      hC.mul_theta_comm hA,
      show ringReflectionThetaS n N C * (ringReflectionThetaS n N A * C) * A
          = (ringReflectionThetaS n N C * ringReflectionThetaS n N A) * (C * A) by
        simp only [mul_assoc]]
  change 0 ≤ ((ringReflectionThetaS n N C * C) * (ringReflectionThetaS n N A * A)).trace.re
  rw [hkey]
  exact traceFunctional_reflectionPositive n N (C * A) (hC.mul hA)

/-- **Weighted trace cone, finite nonnegative combination.**  Any nonnegative finite combination
`∑ cᵢ θ(Cᵢ)·Cᵢ` of left-supported weights gives a reflection-positive trace functional. -/
theorem weightedTraceFunctional_reflectionPositive_finsetSum {ι : Type*} (s : Finset ι)
    (C : ι → ManyBodyOpS (Fin (2 * n)) N) (hC : ∀ i ∈ s, SupportedOnLeftS n N (C i))
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    ReflectionPositiveFunctionalS n N
      (fun X => (∑ i ∈ s, (c i : ℂ) • (ringReflectionThetaS n N (C i) * C i) * X).trace) := by
  intro A hA
  change 0 ≤ (∑ i ∈ s, (c i : ℂ) • (ringReflectionThetaS n N (C i) * C i)
    * (ringReflectionThetaS n N A * A)).trace.re
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg (fun i hi => ?_)
  rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_nonneg (hc i hi)
    (weightedTraceFunctional_reflectionPositive (hC i hi) A hA)

end LatticeSystem.Quantum
