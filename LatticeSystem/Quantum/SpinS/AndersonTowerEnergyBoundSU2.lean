import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundPhat

/-!
# Tasaki §4.2.1 Theorem 4.6: SU(2) rotation of the order operators and the LRO premise

The `SU(2)` covariance of the staggered order operators (P6) — the commutators
`[Ŝ³_tot, ô⁽¹⁾]`, `[Ŝ³_tot, ô⁽²⁾]`, `[Ŝ¹_tot, ô⁽²⁾]`, `[Ŝ¹_tot, ô]` and the resulting equality of
the squared-order expectations across the Cartesian axes — and the passage from the long-range-order
premise to the first-moment bound `⟨p̂⟩ ≥ 2 q₀` via the Cartesian ladder decomposition (P7),
including the moment recursion `phatMoment_succ_ratio`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, Theorem 4.6, eqs. (4.2.3)–(4.2.7), (4.2.35); cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### SU(2) rotation of the staggered order operators (P6) -/

/-- Per-site step of the rotation commutator `[Ŝ³_tot, Ô¹] = i Ô²`: the site-`x` `Ŝ³` commutes with
the staggered `Ô¹` except at its own site, contributing `ε_x · (i Ŝ²_x)`. -/
private theorem spinSSiteOp3_commutator_staggeredOrderOp1S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * spinSSiteOp3 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • (Complex.I • spinSSiteOp2 x N) := by
  unfold staggeredOrderOp1S spinSSiteOp3 spinSSiteOp1 spinSSiteOp2
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp3_commutator_spinSOp1, onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOp1 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ³_tot, Ô_L^{(1)}] = i Ô_L^{(2)}`: cross-site terms vanish; on-site
terms give the single-site `[Ŝ³, Ŝ¹] = i Ŝ²`. -/
theorem totalSpinSOp3_commutator_staggeredOrderOp1S (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * totalSpinSOp3 Λ N
      = Complex.I • staggeredOrderOp2S A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp2S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredOrderOp1S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- Per-site step of `[Ŝ³_tot, Ô²] = -i Ô¹`: on-site `[Ŝ³, Ŝ²] = -i Ŝ¹`. -/
private theorem spinSSiteOp3_commutator_staggeredOrderOp2S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * spinSSiteOp3 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • ((-Complex.I) • spinSSiteOp1 x N) := by
  unfold staggeredOrderOp2S spinSSiteOp3 spinSSiteOp2 spinSSiteOp1
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub,
      show spinSOp3 N * spinSOp2 N - spinSOp2 N * spinSOp3 N = (-Complex.I) • spinSOp1 N from by
        rw [← neg_sub, spinSOp2_commutator_spinSOp3, neg_smul], onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOp2 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ³_tot, Ô_L^{(2)}] = -i Ô_L^{(1)}`. -/
theorem totalSpinSOp3_commutator_staggeredOrderOp2S (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * totalSpinSOp3 Λ N
      = (-Complex.I) • staggeredOrderOp1S A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp1S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredOrderOp2S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- **Generic singlet component equality**: if `S` is Hermitian with `S Φ = 0` and rotates `A, B`
as `[S, A] = i B`, `[S, B] = −i A`, then `⟨Φ, A² Φ⟩ = ⟨Φ, B² Φ⟩`.  Via `[S, AB] = i(B²−A²)` and the
Hermitian shift killing both sides on the singlet. -/
theorem singlet_sq_expectation_eq {S A B : ManyBodyOpS Λ N} (hS : S.IsHermitian)
    (hcomm1 : S * A - A * S = Complex.I • B) (hcomm2 : S * B - B * S = (-Complex.I) • A)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hsing : S.mulVec Φ = 0) :
    star Φ ⬝ᵥ (A * A).mulVec Φ = star Φ ⬝ᵥ (B * B).mulVec Φ := by
  have hleib : S * (A * B) - A * B * S = Complex.I • (B * B - A * A) := by
    have e : S * (A * B) - A * B * S
        = (S * A - A * S) * B + A * (S * B - B * S) := by noncomm_ring
    rw [e, hcomm1, hcomm2, smul_mul_assoc, mul_smul_comm, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  have hcomm0 : star Φ ⬝ᵥ (S * (A * B) - A * B * S).mulVec Φ = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hermitian_dotProduct_shift hS, hsing, star_zero,
      zero_dotProduct, ← Matrix.mulVec_mulVec, hsing, Matrix.mulVec_zero, dotProduct_zero, sub_zero]
  rw [hleib, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hcomm0
  have h2 : star Φ ⬝ᵥ (B * B - A * A).mulVec Φ = 0 :=
    (mul_eq_zero.mp hcomm0).resolve_left Complex.I_ne_zero
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_eq_zero] at h2
  exact h2.symm

/-- **Transverse component equality** (P6, eq. 4.1.7): for a total-`Ŝ³`-singlet state,
`⟨Φ, (Ô¹)² Φ⟩ = ⟨Φ, (Ô²)² Φ⟩`. -/
theorem staggeredOrder_sq_expectation_eq_12 (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star Φ ⬝ᵥ (staggeredOrderOp1S A N * staggeredOrderOp1S A N).mulVec Φ
      = star Φ ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec Φ :=
  singlet_sq_expectation_eq (totalSpinSOp3_isHermitian Λ N)
    (totalSpinSOp3_commutator_staggeredOrderOp1S A)
    (totalSpinSOp3_commutator_staggeredOrderOp2S A) Φ hsing

/-- Per-site step of `[Ŝ¹_tot, Ô²] = i Ô³`: on-site `[Ŝ¹, Ŝ²] = i Ŝ³`. -/
private theorem spinSSiteOp1_commutator_staggeredOrderOp2S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp1 x N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * spinSSiteOp1 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • (Complex.I • spinSSiteOp3 x N) := by
  unfold staggeredOrderOp2S spinSSiteOp1 spinSSiteOp2 spinSSiteOp3
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp1_commutator_spinSOp2, onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp1 N) (spinSOp2 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ¹_tot, Ô_L^{(2)}] = i Ô_L^{(3)}`. -/
theorem totalSpinSOp1_commutator_staggeredOrderOp2S (A : Λ → Bool) :
    totalSpinSOp1 Λ N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * totalSpinSOp1 Λ N
      = Complex.I • staggeredOrderOpS A N := by
  have hsum : (totalSpinSOp1 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp1 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOpS,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp1_commutator_staggeredOrderOp2S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- Per-site step of `[Ŝ¹_tot, Ô³] = -i Ô²`: on-site `[Ŝ¹, Ŝ³] = -i Ŝ²`. -/
private theorem spinSSiteOp1_commutator_staggeredOrderOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp1 x N * staggeredOrderOpS A N - staggeredOrderOpS A N * spinSSiteOp1 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • ((-Complex.I) • spinSSiteOp2 x N) := by
  unfold staggeredOrderOpS spinSSiteOp1 spinSSiteOp3 spinSSiteOp2
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub,
      show spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N = (-Complex.I) • spinSOp2 N from by
        rw [← neg_sub, spinSOp3_commutator_spinSOp1, neg_smul], onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp1 N) (spinSOp3 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ¹_tot, Ô_L^{(3)}] = -i Ô_L^{(2)}`. -/
theorem totalSpinSOp1_commutator_staggeredOrderOpS (A : Λ → Bool) :
    totalSpinSOp1 Λ N * staggeredOrderOpS A N - staggeredOrderOpS A N * totalSpinSOp1 Λ N
      = (-Complex.I) • staggeredOrderOp2S A N := by
  have hsum : (totalSpinSOp1 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp1 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp2S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp1_commutator_staggeredOrderOpS, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- **Component equality** (P6): for a total-`Ŝ¹`-singlet state,
`⟨Φ, (Ô²)² Φ⟩ = ⟨Φ, (Ô³)² Φ⟩`. -/
theorem staggeredOrder_sq_expectation_eq_23 (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    star Φ ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec Φ
      = star Φ ⬝ᵥ (staggeredOrderOpS A N * staggeredOrderOpS A N).mulVec Φ :=
  singlet_sq_expectation_eq (totalSpinSOp1_isHermitian Λ N)
    (totalSpinSOp1_commutator_staggeredOrderOp2S A)
    (totalSpinSOp1_commutator_staggeredOrderOpS A) Φ hsing

/-! ### Order×order commutators `[Ô^{(α)}, Ô^{(β)}] = i ε_{αβγ} Ŝ^{(γ)}_tot` (Prop 4.10 arc)

The commutator of two staggered order operators is the **unstaggered** total spin: the two
staggering signs `ε_x` multiply to `ε_x² = 1`, so `[Ô^{(α)}, Ô^{(β)}] = Σ_x [Ŝ^{(α)}_x, Ŝ^{(β)}_x]
= i ε_{αβγ} Σ_x Ŝ^{(γ)}_x = i ε_{αβγ} Ŝ^{(γ)}_tot`.  These three identities feed the
commutator-contraction (swap-band) step that reduces the ordered product `∏_j Ô^{(f j)}` of Tasaki
eq. (4.2.59) to the grouped `(Ô²)^{M/2}` main part. -/

/-- Per-site step of `[Ŝ²_x, Ô³] = i Ŝ¹_x`: on-site `[Ŝ², Ŝ³] = i Ŝ¹`. -/
private theorem spinSSiteOp2_commutator_staggeredOrderOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp2 x N * staggeredOrderOpS A N - staggeredOrderOpS A N * spinSSiteOp2 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • (Complex.I • spinSSiteOp1 x N) := by
  unfold staggeredOrderOpS spinSSiteOp2 spinSSiteOp3 spinSSiteOp1
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp2_commutator_spinSOp3, onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp2 N) (spinSOp3 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Order×order commutator** `[Ô_L^{(1)}, Ô_L^{(2)}] = i Ŝ³_tot`.  Expanding the left factor
`Ô^{(1)} = Σ_x ε_x Ŝ^{(1)}_x` and applying `[Ŝ^{(1)}_x, Ô^{(2)}] = ε_x · i Ŝ^{(3)}_x`, the two
staggering signs cancel (`ε_x² = 1`), leaving the unstaggered total `Ŝ³_tot = Σ_x Ŝ^{(3)}_x`. -/
theorem staggeredOrderOp1S_commutator_staggeredOrderOp2S (A : Λ → Bool) :
    staggeredOrderOp1S A N * staggeredOrderOp2S A N
        - staggeredOrderOp2S A N * staggeredOrderOp1S A N
      = Complex.I • totalSpinSOp3 Λ N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [staggeredOrderOp1S, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hsum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, spinSSiteOp1_commutator_staggeredOrderOp2S,
    smul_smul]
  have hsq : (if A x then (1 : ℂ) else (-1 : ℂ)) * (if A x then (1 : ℂ) else (-1 : ℂ)) = 1 := by
    cases A x <;> norm_num
  rw [hsq, one_smul]

/-- **Order×order commutator** `[Ô_L^{(2)}, Ô_L^{(3)}] = i Ŝ¹_tot`.  Same mechanism via the
per-site `[Ŝ^{(2)}_x, Ô^{(3)}] = ε_x · i Ŝ^{(1)}_x`; the staggering squares to `1`. -/
theorem staggeredOrderOp2S_commutator_staggeredOrderOpS (A : Λ → Bool) :
    staggeredOrderOp2S A N * staggeredOrderOpS A N
        - staggeredOrderOpS A N * staggeredOrderOp2S A N
      = Complex.I • totalSpinSOp1 Λ N := by
  have hsum : (totalSpinSOp1 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp1 x N := rfl
  rw [staggeredOrderOp2S, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hsum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, spinSSiteOp2_commutator_staggeredOrderOpS,
    smul_smul]
  have hsq : (if A x then (1 : ℂ) else (-1 : ℂ)) * (if A x then (1 : ℂ) else (-1 : ℂ)) = 1 := by
    cases A x <;> norm_num
  rw [hsq, one_smul]

/-- **Order×order commutator** `[Ô_L^{(3)}, Ô_L^{(1)}] = i Ŝ²_tot`.  Same mechanism via the
per-site `[Ŝ^{(3)}_x, Ô^{(1)}] = ε_x · i Ŝ^{(2)}_x`; the staggering squares to `1`. -/
theorem staggeredOrderOpS_commutator_staggeredOrderOp1S (A : Λ → Bool) :
    staggeredOrderOpS A N * staggeredOrderOp1S A N
        - staggeredOrderOp1S A N * staggeredOrderOpS A N
      = Complex.I • totalSpinSOp2 Λ N := by
  have hsum : (totalSpinSOp2 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp2 x N := rfl
  rw [staggeredOrderOpS, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hsum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, spinSSiteOp3_commutator_staggeredOrderOp1S,
    smul_smul]
  have hsq : (if A x then (1 : ℂ) else (-1 : ℂ)) * (if A x then (1 : ℂ) else (-1 : ℂ)) = 1 := by
    cases A x <;> norm_num
  rw [hsq, one_smul]

/-! ### Missing total×order rotation commutators `[Ŝ²_tot, ô⁽¹⁾]`, `[Ŝ²_tot, ô⁽³⁾]` (Prop 4.10 arc)

The two `Ŝ²_tot` off-diagonal rotation commutators, completing the six off-diagonal total×order
commutators `[Ŝ^{(γ)}_tot, ô^{(β)}] = i ε_{γβδ} ô^{(δ)}` needed to push `Ŝ^{(γ)}_tot` through a
Cartesian order word in the swap-band telescoping (Prop 4.10 arc PR-3.2b).  Same per-site mechanism
as the `Ŝ³_tot`/`Ŝ¹_tot` cases above. -/

/-- Per-site step of `[Ŝ²_tot, Ô¹] = −i Ô³`: on-site `[Ŝ², Ŝ¹] = −i Ŝ³`. -/
private theorem spinSSiteOp2_commutator_staggeredOrderOp1S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp2 x N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * spinSSiteOp2 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • ((-Complex.I) • spinSSiteOp3 x N) := by
  unfold staggeredOrderOp1S spinSSiteOp2 spinSSiteOp1 spinSSiteOp3
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub,
      show spinSOp2 N * spinSOp1 N - spinSOp1 N * spinSOp2 N = (-Complex.I) • spinSOp3 N from by
        rw [← neg_sub, spinSOp1_commutator_spinSOp2, neg_smul], onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp2 N) (spinSOp1 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ²_tot, Ô_L^{(1)}] = −i Ô_L^{(3)}` (`ε_{213} = −1`). -/
theorem totalSpinSOp2_commutator_staggeredOrderOp1S (A : Λ → Bool) :
    totalSpinSOp2 Λ N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * totalSpinSOp2 Λ N
      = (-Complex.I) • staggeredOrderOpS A N := by
  have hsum : (totalSpinSOp2 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp2 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOpS,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp2_commutator_staggeredOrderOp1S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- **Rotation commutator** `[Ŝ²_tot, Ô_L^{(3)}] = i Ô_L^{(1)}` (`ε_{231} = +1`). -/
theorem totalSpinSOp2_commutator_staggeredOrderOpS (A : Λ → Bool) :
    totalSpinSOp2 Λ N * staggeredOrderOpS A N - staggeredOrderOpS A N * totalSpinSOp2 Λ N
      = Complex.I • staggeredOrderOp1S A N := by
  have hsum : (totalSpinSOp2 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp2 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp1S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp2_commutator_staggeredOrderOpS, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-! ### From the LRO premise to `⟨p̂⟩ ≥ 2 q₀` (P7) -/

/-- Cartesian decomposition of the raising operator: `Ŝ⁺ = Ŝ¹ + i Ŝ²`. -/
theorem spinSOpPlus_eq_cartesian (N : ℕ) :
    spinSOpPlus N = spinSOp1 N + Complex.I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by
    rw [mul_one_div]; field_simp]
  module

/-- Cartesian decomposition of the lowering operator: `Ŝ⁻ = Ŝ¹ − i Ŝ²`. -/
theorem spinSOpMinus_eq_cartesian (N : ℕ) :
    spinSOpMinus N = spinSOp1 N - Complex.I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by
    rw [mul_one_div]; field_simp]
  module

/-- Per-site Cartesian decomposition `Ŝ_x⁺ = Ŝ_x¹ + i Ŝ_x²`. -/
theorem spinSSiteOpPlus_eq_cartesian (x : Λ) :
    spinSSiteOpPlus x N = spinSSiteOp1 x N + Complex.I • spinSSiteOp2 x N := by
  unfold spinSSiteOpPlus spinSSiteOp1 spinSSiteOp2
  rw [spinSOpPlus_eq_cartesian, onSiteS_add, onSiteS_smul]

/-- Per-site Cartesian decomposition `Ŝ_x⁻ = Ŝ_x¹ − i Ŝ_x²`. -/
theorem spinSSiteOpMinus_eq_cartesian (x : Λ) :
    spinSSiteOpMinus x N = spinSSiteOp1 x N - Complex.I • spinSSiteOp2 x N := by
  unfold spinSSiteOpMinus spinSSiteOp1 spinSSiteOp2
  rw [spinSOpMinus_eq_cartesian, onSiteS_sub, onSiteS_smul]

/-- Cartesian decomposition of the staggered raising operator `Ô⁺ = Ô¹ + i Ô²`. -/
theorem staggeredRaisingOpS_eq_cartesian (A : Λ → Bool) :
    staggeredRaisingOpS A N = staggeredOrderOp1S A N + Complex.I • staggeredOrderOp2S A N := by
  unfold staggeredRaisingOpS staggeredOrderOp1S staggeredOrderOp2S
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOpPlus_eq_cartesian, smul_add, smul_comm Complex.I]

/-- Cartesian decomposition of the staggered lowering operator `Ô⁻ = Ô¹ − i Ô²`. -/
theorem staggeredLoweringOpS_eq_cartesian (A : Λ → Bool) :
    staggeredLoweringOpS A N = staggeredOrderOp1S A N - Complex.I • staggeredOrderOp2S A N := by
  unfold staggeredLoweringOpS staggeredOrderOp1S staggeredOrderOp2S
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOpMinus_eq_cartesian, smul_sub, smul_comm Complex.I]

/-- Algebraic expansion `(A + iB)(A − iB) + (A − iB)(A + iB) = 2(A² + B²)` (the imaginary cross
terms cancel; `i² = −1`). -/
theorem cartesian_ladder_anticomm_expand {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) :
    (A + Complex.I • B) * (A - Complex.I • B) + (A - Complex.I • B) * (A + Complex.I • B)
      = (2 : ℂ) • (A * A + B * B) := by
  have hI : (Complex.I • B) * (Complex.I • B) = -(B * B) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [add_mul, sub_mul, mul_sub, mul_sub, mul_add, mul_add, hI]
  module

/-- **`U(1)` order operator as transverse square sum** `p̂ = V⁻² (Ô¹² + Ô²²)` (eq. (4.2.31)). -/
theorem staggeredPhatS_eq_cartesian_sq (d L N : ℕ) [NeZero L] :
    staggeredPhatS d L N = (((L : ℂ) ^ d) ^ 2)⁻¹ •
      (staggeredOrderOp1S (torusParitySublattice d L) N
          * staggeredOrderOp1S (torusParitySublattice d L) N
        + staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N) := by
  rw [staggeredPhatS,
    show staggeredOrderDensityOpS d L N true
        = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl,
    show staggeredOrderDensityOpS d L N false
        = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl,
    staggeredRaisingOpS_eq_cartesian, staggeredLoweringOpS_eq_cartesian,
    smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, cartesian_ladder_anticomm_expand,
    smul_smul, smul_smul]
  congr 1
  ring

/-- The `p̂`-expectation in Cartesian form: `⟨Φ, p̂ Φ⟩ = V⁻² (⟨Ô¹² ⟩ + ⟨Ô²²⟩)`. -/
theorem staggeredPhatS_dotProduct_cartesian (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    star Φ ⬝ᵥ (staggeredPhatS d L N).mulVec Φ
      = (((L : ℂ) ^ d) ^ 2)⁻¹ *
          (star Φ ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
              * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec Φ
            + star Φ ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
              * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec Φ) := by
  rw [staggeredPhatS_eq_cartesian_sq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.add_mulVec, dotProduct_add]

/-- **P7 (eq. 4.1.7 → LRO bound):** for an `Ŝ³`- and `Ŝ¹`-singlet ground state with squared
staggered order parameter `≥ q₀`, the first `p̂`-moment obeys `2 q₀ ‖Φ‖² ≤ ⟨Φ, p̂ Φ⟩`.  By `SU(2)`
invariance
the three Cartesian order parameters are equal, so `⟨p̂⟩ = 2 ⟨(Ô³/V)²⟩ ≥ 2 q₀ ‖Φ‖²`. -/
theorem phatMoment_one_ge_of_lro (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (q₀ : ℝ) (hm0 : 0 < (star Φ ⬝ᵥ Φ).re) (hL : (0 : ℝ) < (L : ℝ) ^ d)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    2 * q₀ * (star Φ ⬝ᵥ Φ).re ≤ phatMoment d L N Φ 1 := by
  set V2 : ℝ := ((L : ℝ) ^ d) ^ 2 with hV2def
  have hV2 : 0 < V2 := pow_pos hL 2
  have hz12 := staggeredOrder_sq_expectation_eq_12 (torusParitySublattice d L) Φ hsing3
  have hz23 := staggeredOrder_sq_expectation_eq_23 (torusParitySublattice d L) Φ hsing1
  -- m₁ = V⁻² (⟨Ô¹²⟩.re + ⟨Ô²²⟩.re) = 2 V⁻² ⟨Ô³²⟩.re
  have hcast : (((L : ℂ) ^ d) ^ 2)⁻¹ = ((V2⁻¹ : ℝ) : ℂ) := by
    rw [hV2def]; push_cast; ring
  have hm1 : phatMoment d L N Φ 1
      = V2⁻¹ * ((star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
          * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        + (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
          * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re) := by
    rw [phatMoment, pow_one, staggeredPhatS_dotProduct_cartesian, hcast, hz12, hz23]
    simp [Complex.mul_re, Complex.add_re]
  rw [hm1]
  -- from LRO: q₀ * (m₀ * V2) ≤ ⟨Ô³²⟩.re
  rw [le_div_iff₀ (mul_pos hm0 hV2)] at hlro
  have hz3 : q₀ * ((star Φ ⬝ᵥ Φ).re * V2)
      ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re := hlro
  rw [← two_mul]
  -- 2 q₀ m₀ ≤ V⁻² · 2 · ⟨Ô³²⟩.re
  have key : 2 * q₀ * (star Φ ⬝ᵥ Φ).re
      = V2⁻¹ * (2 * (q₀ * ((star Φ ⬝ᵥ Φ).re * V2))) := by
    field_simp
  rw [key]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hV2))
  exact mul_le_mul_of_nonneg_left hz3 (by norm_num)

/-- The zeroth `p̂`-moment is the squared norm: `m₀ = ‖Φ‖²`. -/
theorem phatMoment_zero (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    phatMoment d L N Φ 0 = (star Φ ⬝ᵥ Φ).re := by
  rw [phatMoment, pow_zero, Matrix.one_mulVec]

/-- **Renormalized moment ratio** `2 q₀ mₙ ≤ mₙ₊₁` (the engine of Lemma R1): combining the
log-convexity cross inequality `m₁ mₙ ≤ m₀ mₙ₊₁` with the LRO entry `2 q₀ m₀ ≤ m₁` and cancelling
`m₀ > 0`.  Iterating recovers `(2 q₀)ⁿ m₀ ≤ mₙ`. -/
theorem phatMoment_succ_two_q0_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (q₀ : ℝ) (hm0 : 0 < (star Φ ⬝ᵥ Φ).re) (hL : (0 : ℝ) < (L : ℝ) ^ d)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) (n : ℕ) :
    2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1) := by
  have hP7 : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1 := by
    rw [phatMoment_zero]; exact phatMoment_one_ge_of_lro d L N Φ hsing3 hsing1 q₀ hm0 hL hlro
  have hcross := phatMoment_cross d L N Φ n
  have hm0' : 0 < phatMoment d L N Φ 0 := by rw [phatMoment_zero]; exact hm0
  have hmn : 0 ≤ phatMoment d L N Φ n := phatMoment_nonneg d L N Φ n
  have hkey : phatMoment d L N Φ 0 * (2 * q₀ * phatMoment d L N Φ n)
      ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) :=
    calc phatMoment d L N Φ 0 * (2 * q₀ * phatMoment d L N Φ n)
        = (2 * q₀ * phatMoment d L N Φ 0) * phatMoment d L N Φ n := by ring
      _ ≤ phatMoment d L N Φ 1 * phatMoment d L N Φ n :=
          mul_le_mul_of_nonneg_right hP7 hmn
      _ ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) := hcross
  exact le_of_mul_le_mul_left hkey hm0'

/-- **Renormalized moment ratio, processed form** `2 q₀ mₙ ≤ mₙ₊₁` taking the LRO entry
`2 q₀ m₀ ≤ m₁` directly (used inside the R1 induction). -/
theorem phatMoment_succ_ratio (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hP7 : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (n : ℕ) :
    2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1) := by
  have hcross := phatMoment_cross d L N Φ n
  have hmn : 0 ≤ phatMoment d L N Φ n := phatMoment_nonneg d L N Φ n
  have hkey : phatMoment d L N Φ 0 * (2 * q₀ * phatMoment d L N Φ n)
      ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) :=
    calc phatMoment d L N Φ 0 * (2 * q₀ * phatMoment d L N Φ n)
        = (2 * q₀ * phatMoment d L N Φ 0) * phatMoment d L N Φ n := by ring
      _ ≤ phatMoment d L N Φ 1 * phatMoment d L N Φ n :=
          mul_le_mul_of_nonneg_right hP7 hmn
      _ ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) := hcross
  exact le_of_mul_le_mul_left hkey hm0

end LatticeSystem.Quantum
