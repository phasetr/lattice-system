import LatticeSystem.Quantum.SpinS.MultiSiteCore
import LatticeSystem.Math.MvPolynomial.WeylSpinMap
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Per-site Weyl transport of the spin-`S` ladder/diagonal operators

`weylMap` (`LatticeSystem.Math.WeylSpinMap`) intertwines the single-site spin-`S` operators
`Ŝ^+`, `Ŝ^-`, `Ŝ^{(3)}` (`spinSOpPlus`, `spinSOpMinus`, `spinSOp3`) with the Weyl-variable
differential operators `X_x∂_{v_x}`, `X_x∂_{u_x}`, `½(X_x∂_{u_x} − X_x∂_{v_x})` (`u_x = (x,0)`,
`v_x = (x,1)`) at a single site `x : Fin L`, for any `L` and any `S`.  Transporting one site at a
time — rather than assembling a two-site matrix element directly, multi-site operators being
recovered afterwards from products of one-site ones — means the per-site statement is proved once
and reused unchanged at every bond, instead of once per bond.

Two ingredients carry the content:

* the Clebsch–Gordan step `√(binom(N,t+1))·√(t+1) = √(binom(N,t))·√(N−t)`, the `√`-form of
  `Nat.choose_succ_right_eq`, which is exactly the ladder matrix element `√((t+1)(N−t))` of
  `spinSOpPlus`/`spinSOpMinus`; the weights `cgSite` are therefore forced, not cosmetic;
* the one-site factorization `weylMono (Function.update σ x k) = M · weylSiteMono x k` with `M`
  free of the site-`x` variables (`exists_weylMono_site_factor`), which turns the column of the
  site embedding `onSiteS x A` into the single-site ladder sum multiplied by a constant.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3, eqs. (7.1.22)-(7.1.25); the per-site transport is the elementary building block consumed
by the two-site Casimir intertwiner.
-/

open MvPolynomial LatticeSystem.Math

namespace LatticeSystem.Quantum

variable {L N : ℕ}

/-! ## The Clebsch–Gordan step of the binomial weights -/

/-- **The single arithmetic fact behind both ladders.**  The `√`-form of
`Nat.choose_succ_right_eq` (`binom(n,t+1)·(t+1) = binom(n,t)·(n−t)`): the Clebsch–Gordan weights
`√(binom(n,·))` of neighbouring site states are related by the ladder matrix elements `√(t+1)` and
`√(n−t)`.  No hypothesis `t < n` is needed: above the top both sides vanish. -/
private theorem sqrt_choose_step (n t : ℕ) :
    Real.sqrt (n.choose (t + 1)) * Real.sqrt ((t : ℝ) + 1)
      = Real.sqrt (n.choose t) * Real.sqrt ((n - t : ℕ) : ℝ) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  congr 1
  exact_mod_cast Nat.choose_succ_right_eq n t

/-- Coefficient identity of the raising ladder: the `Ŝ^+` matrix element `√((t+1)(n−t))` times the
weight `√(binom(n,t))` of the target state equals the weight `√(binom(n,t+1))` of the source state
times the `v`-exponent `t+1` produced by `∂_v`.  The real subtraction `(n:ℝ) − (t+1) + 1` of
`spinSOpPlus` is bridged to the truncated `n − t` of `mdSite` by `t < n`. -/
private theorem sqrt_raise_coeff {n t : ℕ} (ht : t < n) :
    Real.sqrt (((t : ℝ) + 1) * ((n : ℝ) - ((t : ℝ) + 1) + 1)) * Real.sqrt (n.choose t)
      = Real.sqrt (n.choose (t + 1)) * ((t : ℝ) + 1) := by
  have hcast : (n : ℝ) - ((t : ℝ) + 1) + 1 = ((n - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub ht.le]
    ring
  have hsq : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  rw [hcast, Real.sqrt_mul (by positivity)]
  calc Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt (n.choose t)
      = Real.sqrt (n.choose t) * Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt ((t : ℝ) + 1) := by ring
    _ = Real.sqrt (n.choose (t + 1)) * Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) := by
        rw [sqrt_choose_step]
    _ = Real.sqrt (n.choose (t + 1)) * ((t : ℝ) + 1) := by rw [mul_assoc, hsq]

/-- Coefficient identity of the lowering ladder: the `Ŝ^-` matrix element `√((n−t)(t+1))` times the
weight `√(binom(n,t+1))` of the target state equals the weight `√(binom(n,t))` of the source state
times the `u`-exponent `n − t` produced by `∂_u`. -/
private theorem sqrt_lower_coeff {n t : ℕ} (ht : t < n) :
    Real.sqrt (((n : ℝ) - (t : ℝ)) * ((t : ℝ) + 1)) * Real.sqrt (n.choose (t + 1))
      = Real.sqrt (n.choose t) * ((n - t : ℕ) : ℝ) := by
  have hcast : (n : ℝ) - (t : ℝ) = ((n - t : ℕ) : ℝ) := (Nat.cast_sub ht.le).symm
  have hsq : Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt ((n - t : ℕ) : ℝ) = ((n - t : ℕ) : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [hcast, Real.sqrt_mul (Nat.cast_nonneg _)]
  calc Real.sqrt ((n - t : ℕ) : ℝ) * Real.sqrt ((t : ℝ) + 1) * Real.sqrt (n.choose (t + 1))
      = Real.sqrt (n.choose (t + 1)) * Real.sqrt ((t : ℝ) + 1)
          * Real.sqrt ((n - t : ℕ) : ℝ) := by ring
    _ = Real.sqrt (n.choose t) * Real.sqrt ((n - t : ℕ) : ℝ)
          * Real.sqrt ((n - t : ℕ) : ℝ) := by rw [sqrt_choose_step]
    _ = Real.sqrt (n.choose t) * ((n - t : ℕ) : ℝ) := by rw [mul_assoc, hsq]

/-! ## Multidegree bookkeeping of a single ladder step -/

/-- Multidegree of a raising step: removing one `v_x` and adding one `u_x` turns the site-`j`
multidegree into the site-`k` one whenever `k + 1 = j`.  The truncated subtractions are handled
algebraically (`mdSite x j` is split off as `… + single (x,1) 1` before cancelling), never by
`Finsupp.ext`. -/
private theorem mdSite_raise_multidegree {x : Fin L} {j k : Fin (N + 1)}
    (h : (k : ℕ) + 1 = (j : ℕ)) :
    Finsupp.single ((x, 0) : Fin L × Fin 2) 1
        + (mdSite x j - Finsupp.single ((x, 1) : Fin L × Fin 2) 1)
      = mdSite x k := by
  have hjN : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  have hsplit : mdSite (N := N) x j
      = (Finsupp.single ((x, 0) : Fin L × Fin 2) (N - (j : ℕ))
          + Finsupp.single ((x, 1) : Fin L × Fin 2) (k : ℕ))
        + Finsupp.single ((x, 1) : Fin L × Fin 2) 1 := by
    rw [add_assoc, ← Finsupp.single_add, h, mdSite]
  rw [hsplit, add_tsub_cancel_right, ← add_assoc, ← Finsupp.single_add,
    show 1 + (N - (j : ℕ)) = N - (k : ℕ) from by omega, mdSite]

/-- Multidegree of a lowering step: removing one `u_x` and adding one `v_x` turns the site-`j`
multidegree into the site-`k` one whenever `j + 1 = k`. -/
private theorem mdSite_lower_multidegree {x : Fin L} {j k : Fin (N + 1)}
    (h : (j : ℕ) + 1 = (k : ℕ)) :
    Finsupp.single ((x, 1) : Fin L × Fin 2) 1
        + (mdSite x j - Finsupp.single ((x, 0) : Fin L × Fin 2) 1)
      = mdSite x k := by
  have hkN : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
  have hsplit : mdSite (N := N) x j
      = (Finsupp.single ((x, 0) : Fin L × Fin 2) (N - (k : ℕ))
          + Finsupp.single ((x, 1) : Fin L × Fin 2) (j : ℕ))
        + Finsupp.single ((x, 0) : Fin L × Fin 2) 1 := by
    rw [add_right_comm, ← Finsupp.single_add,
      show N - (k : ℕ) + 1 = N - (j : ℕ) from by omega, mdSite]
  rw [hsplit, add_tsub_cancel_right,
    add_comm (Finsupp.single ((x, 0) : Fin L × Fin 2) (N - (k : ℕ))), ← add_assoc,
    ← Finsupp.single_add, show 1 + (j : ℕ) = (k : ℕ) from by omega, mdSite]
  exact add_comm _ _

/-! ## The three per-site column sums -/

/-- The per-site raising-ladder column sum: transporting `Ŝ^+` at site `x` through the single-site
Weyl monomials is the differential operator `X_x ∂_{v_x}` (`u_x = (x,0)`, `v_x = (x,1)`).  The
`spinSOpPlus`/`cgSite` weights must match *exactly* (not merely up to a constant) for this to hold;
`Tests.GeneralSWeylLadder` pins that Clebsch–Gordan normalization.  At the top state `j = 0` both
sides vanish, but for different reasons: the matrix column is empty, while the derivative side has
no `v_x` to differentiate. -/
theorem weylSiteMono_spinSOpPlus_sum (x : Fin L) (j : Fin (N + 1)) :
    ∑ k : Fin (N + 1), spinSOpPlus N k j • weylSiteMono x k
      = X (x, 0) * pderiv (x, 1) (weylSiteMono x j) := by
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · have hzero : ∀ k : Fin (N + 1), spinSOpPlus N k j • weylSiteMono (L := L) x k = 0 := by
      intro k
      rw [spinSOpPlus_apply_other N (by omega), zero_smul]
    rw [Finset.sum_congr rfl fun k _ => hzero k, Finset.sum_const_zero]
    simp [weylSiteMono, mdSite_apply_snd, hj]
  · have hjN : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (j : ℕ) = t + 1 := ⟨(j : ℕ) - 1, by omega⟩
    have hklt : t < N + 1 := by omega
    have hkj : ((⟨t, hklt⟩ : Fin (N + 1)) : ℕ) + 1 = (j : ℕ) := ht.symm
    have hne : ∀ b : Fin (N + 1), b ∈ (Finset.univ : Finset (Fin (N + 1))) →
        b ≠ (⟨t, hklt⟩ : Fin (N + 1)) → spinSOpPlus N b j • weylSiteMono (L := L) x b = 0 := by
      intro b _ hb
      have hval : (b : ℕ) + 1 ≠ (j : ℕ) := fun hcontra => hb (Fin.ext (by omega : (b : ℕ) = t))
      rw [spinSOpPlus_apply_other N hval, zero_smul]
    have hcoeff : (↑(Real.sqrt (((j : ℕ) : ℝ) * ((N : ℝ) - ((j : ℕ) : ℝ) + 1))) : ℂ)
        * cgSite (⟨t, hklt⟩ : Fin (N + 1)) = cgSite j * ((j : ℕ) : ℂ) := by
      rw [cgSite, cgSite, ht]
      exact_mod_cast sqrt_raise_coeff (n := N) (t := t) (by omega)
    rw [Finset.sum_eq_single (⟨t, hklt⟩ : Fin (N + 1)) hne (fun h => absurd (Finset.mem_univ _) h)]
    simp only [weylSiteMono, smul_monomial, smul_eq_mul, pderiv_monomial, mdSite_apply_snd]
    rw [spinSOpPlus_apply_raise N hkj, X, monomial_mul, one_mul,
      mdSite_raise_multidegree hkj, hcoeff]

/-- The per-site lowering-ladder column sum: transporting `Ŝ^-` at site `x` is the differential
operator `X_x ∂_{u_x}`.  At the bottom state `j = N` both sides vanish (empty matrix column on one
side, no `u_x` left to differentiate on the other). -/
theorem weylSiteMono_spinSOpMinus_sum (x : Fin L) (j : Fin (N + 1)) :
    ∑ k : Fin (N + 1), spinSOpMinus N k j • weylSiteMono x k
      = X (x, 1) * pderiv (x, 0) (weylSiteMono x j) := by
  have hjN : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  rcases eq_or_lt_of_le hjN with hj | hj
  · have hzero : ∀ k : Fin (N + 1), spinSOpMinus N k j • weylSiteMono (L := L) x k = 0 := by
      intro k
      have hk : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
      rw [spinSOpMinus_apply_other N (by omega), zero_smul]
    rw [Finset.sum_congr rfl fun k _ => hzero k, Finset.sum_const_zero]
    simp [weylSiteMono, mdSite_apply_self, ← hj]
  · have hklt : (j : ℕ) + 1 < N + 1 := by omega
    have hkj : (j : ℕ) + 1 = ((⟨(j : ℕ) + 1, hklt⟩ : Fin (N + 1)) : ℕ) := rfl
    have hne : ∀ b : Fin (N + 1), b ∈ (Finset.univ : Finset (Fin (N + 1))) →
        b ≠ (⟨(j : ℕ) + 1, hklt⟩ : Fin (N + 1)) →
        spinSOpMinus N b j • weylSiteMono (L := L) x b = 0 := by
      intro b _ hb
      have hval : (j : ℕ) + 1 ≠ (b : ℕ) := fun hcontra =>
        hb (Fin.ext (by omega : (b : ℕ) = (j : ℕ) + 1))
      rw [spinSOpMinus_apply_other N hval, zero_smul]
    have hcoeff : (↑(Real.sqrt (((N : ℝ) - ((j : ℕ) : ℝ)) * (((j : ℕ) : ℝ) + 1))) : ℂ)
        * cgSite (⟨(j : ℕ) + 1, hklt⟩ : Fin (N + 1)) = cgSite j * ((N - (j : ℕ) : ℕ) : ℂ) := by
      rw [cgSite, cgSite]
      exact_mod_cast sqrt_lower_coeff (n := N) (t := (j : ℕ)) hj
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hklt⟩ : Fin (N + 1)) hne
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [weylSiteMono, smul_monomial, smul_eq_mul, pderiv_monomial, mdSite_apply_self]
    rw [spinSOpMinus_apply_lower N hkj.symm, X, monomial_mul, one_mul,
      mdSite_lower_multidegree hkj, hcoeff]

/-- The per-site diagonal column sum: transporting `Ŝ^{(3)}` at site `x` is `½(a_x - b_x)` where
`a_x = X_x ∂_{u_x}`, `b_x = X_x ∂_{v_x}` are the two per-variable Euler operators of site `x`.
The eigenvalue `N/2 − j` of `spinSOp3` is exactly half the difference `(N − j) − j` of the two
exponents of `u_x^{N−j} v_x^j`. -/
theorem weylSiteMono_spinSOp3_sum (x : Fin L) (j : Fin (N + 1)) :
    ∑ k : Fin (N + 1), spinSOp3 N k j • weylSiteMono x k
      = (1 / 2 : ℂ) • (X (x, 0) * pderiv (x, 0) (weylSiteMono x j)
          - X (x, 1) * pderiv (x, 1) (weylSiteMono x j)) := by
  have hjN : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [spinSOp3_apply_offdiag N hb, zero_smul])
      (fun h => absurd (Finset.mem_univ j) h),
    spinSOp3_apply_diag]
  simp only [weylSiteMono, X_mul_pderiv_monomial, mdSite_apply_self, mdSite_apply_snd]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul, smul_smul]
  congr 1
  rw [Nat.cast_sub hjN]
  ring

/-! ## From per-site columns to the global Weyl transport -/

/-- **Column of a one-site embedding.**  Only the `L`-tuples that agree with `σ` away from `x`
contribute to the `σ`-column of `onSiteS x A`, so the column collapses to a sum over the site
state `k` at `x` alone, reindexed by `Function.update`. -/
theorem weylMono_onSiteS_column (x : Fin L) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ : Fin L → Fin (N + 1)) :
    ∑ σ' : Fin L → Fin (N + 1), (onSiteS x A : ManyBodyOpS (Fin L) N) σ' σ • weylMono σ'
      = ∑ k : Fin (N + 1), A k (σ x) • weylMono (Function.update σ x k) := by
  classical
  have hinj : Function.Injective (fun k : Fin (N + 1) => Function.update σ x k) := by
    intro a b hab
    simpa using congrFun hab x
  have hzero : ∀ τ ∈ (Finset.univ : Finset (Fin L → Fin (N + 1))),
      τ ∉ Finset.univ.image (fun k : Fin (N + 1) => Function.update σ x k) →
      (onSiteS x A : ManyBodyOpS (Fin L) N) τ σ • weylMono τ = 0 := by
    intro τ _ hτ
    have hdiff : ¬ (∀ y, y ≠ x → τ y = σ y) := by
      intro hagree
      refine hτ (Finset.mem_image.mpr ⟨τ x, Finset.mem_univ _, ?_⟩)
      funext y
      by_cases hyx : y = x
      · subst hyx
        rw [Function.update_self]
      · rw [Function.update_of_ne hyx]
        exact (hagree y hyx).symm
    rw [onSiteS_apply_eq_zero_of_off_site_diff x A hdiff, zero_smul]
  rw [← Finset.sum_subset
      (Finset.subset_univ
        (Finset.univ.image (fun k : Fin (N + 1) => Function.update σ x k))) hzero,
    Finset.sum_image hinj.injOn]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [onSiteS_apply_of_off_site_agree x A fun y hy => by rw [Function.update_of_ne hy],
    Function.update_self]

/-- **Columns determine the transport.**  If a many-body operator `A` sends every Weyl monomial
column to `D (weylMono σ)` for a fixed linear `D`, then `weylMap` intertwines `A` with `D` on all
states: expand `weylMap (A *ᵥ φ)`, exchange the two sums, and use linearity of `D`. -/
theorem weylMap_mulVec_of_column {A : ManyBodyOpS (Fin L) N}
    (D : MvPolynomial (Fin L × Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin L × Fin 2) ℂ)
    (hcol : ∀ σ : Fin L → Fin (N + 1),
      ∑ σ' : Fin L → Fin (N + 1), A σ' σ • weylMono σ' = D (weylMono σ))
    (φ : (Fin L → Fin (N + 1)) → ℂ) :
    weylMap (A.mulVec φ) = D (weylMap φ) := by
  have hswap : ∀ σ' : Fin L → Fin (N + 1),
      (A.mulVec φ) σ' • weylMono σ'
        = ∑ σ : Fin L → Fin (N + 1), φ σ • (A σ' σ • weylMono σ') := by
    intro σ'
    have hval : (A.mulVec φ) σ' = ∑ σ : Fin L → Fin (N + 1), A σ' σ * φ σ := rfl
    rw [hval, Finset.sum_smul]
    exact Finset.sum_congr rfl fun σ _ => by rw [smul_smul, mul_comm]
  simp only [weylMap, Fintype.linearCombination_apply, map_sum, map_smul]
  rw [Finset.sum_congr rfl fun σ' _ => hswap σ', Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ => by rw [← Finset.smul_sum, hcol σ]

/-- The bundled `ℂ`-linear operator `p ↦ X i * ∂_j p` on the Weyl polynomial ring: the three
per-site transports are `weylMap`-images of `onSiteS` embeddings under such operators (and, for
`Ŝ^{(3)}`, a scalar multiple of a difference of two of them), and bundling is what makes
`weylMap_mulVec_of_column` applicable. -/
private noncomputable def mulXPderiv (i j : Fin L × Fin 2) :
    MvPolynomial (Fin L × Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin L × Fin 2) ℂ :=
  (LinearMap.mulLeft ℂ (X i)).comp (pderiv j).toLinearMap

/-- Unfolding of the bundled site operator. -/
private theorem mulXPderiv_apply (i j : Fin L × Fin 2) (p : MvPolynomial (Fin L × Fin 2) ℂ) :
    mulXPderiv i j p = X i * pderiv j p := rfl

/-- Global raising transport: embedding `Ŝ^+` at site `x` into the many-body operator space and
pushing forward under `weylMap` is `X_x ∂_{v_x}` acting on `weylMap Φ` directly, for **any** `L`
and **any** `x : Fin L` — the per-site route makes this a single proof instead of one per bond. -/
theorem weylMap_mulVec_onSiteS_spinSOpPlus (x : Fin L) (φ : (Fin L → Fin (N + 1)) → ℂ) :
    weylMap ((onSiteS x (spinSOpPlus N)).mulVec φ) = X (x, 0) * pderiv (x, 1) (weylMap φ) := by
  have hcol : ∀ σ : Fin L → Fin (N + 1),
      ∑ σ' : Fin L → Fin (N + 1),
          (onSiteS x (spinSOpPlus N) : ManyBodyOpS (Fin L) N) σ' σ • weylMono σ'
        = mulXPderiv ((x, 0) : Fin L × Fin 2) (x, 1) (weylMono σ) := by
    intro σ
    obtain ⟨M, hM, hfac⟩ := exists_weylMono_site_factor x σ
    have hσ : weylMono σ = M * weylSiteMono x (σ x) := by
      have h := hfac (σ x)
      rwa [Function.update_eq_self] at h
    rw [weylMono_onSiteS_column, mulXPderiv_apply]
    calc ∑ k : Fin (N + 1), spinSOpPlus N k (σ x) • weylMono (Function.update σ x k)
        = ∑ k : Fin (N + 1), spinSOpPlus N k (σ x) • (M * weylSiteMono x k) :=
          Finset.sum_congr rfl fun k _ => by rw [hfac k]
      _ = M * ∑ k : Fin (N + 1), spinSOpPlus N k (σ x) • weylSiteMono x k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
      _ = M * (X (x, 0) * pderiv (x, 1) (weylSiteMono x (σ x))) := by
          rw [weylSiteMono_spinSOpPlus_sum]
      _ = X (x, 0) * pderiv (x, 1) (weylMono σ) := by
          rw [hσ, pderiv_mul, hM 1, zero_mul, zero_add]
          ring
  rw [weylMap_mulVec_of_column (mulXPderiv ((x, 0) : Fin L × Fin 2) (x, 1)) hcol φ,
    mulXPderiv_apply]

/-- Global lowering transport: `onSiteS x Ŝ^-` intertwines with `X_x ∂_{u_x}` under `weylMap`. -/
theorem weylMap_mulVec_onSiteS_spinSOpMinus (x : Fin L) (φ : (Fin L → Fin (N + 1)) → ℂ) :
    weylMap ((onSiteS x (spinSOpMinus N)).mulVec φ) = X (x, 1) * pderiv (x, 0) (weylMap φ) := by
  have hcol : ∀ σ : Fin L → Fin (N + 1),
      ∑ σ' : Fin L → Fin (N + 1),
          (onSiteS x (spinSOpMinus N) : ManyBodyOpS (Fin L) N) σ' σ • weylMono σ'
        = mulXPderiv ((x, 1) : Fin L × Fin 2) (x, 0) (weylMono σ) := by
    intro σ
    obtain ⟨M, hM, hfac⟩ := exists_weylMono_site_factor x σ
    have hσ : weylMono σ = M * weylSiteMono x (σ x) := by
      have h := hfac (σ x)
      rwa [Function.update_eq_self] at h
    rw [weylMono_onSiteS_column, mulXPderiv_apply]
    calc ∑ k : Fin (N + 1), spinSOpMinus N k (σ x) • weylMono (Function.update σ x k)
        = ∑ k : Fin (N + 1), spinSOpMinus N k (σ x) • (M * weylSiteMono x k) :=
          Finset.sum_congr rfl fun k _ => by rw [hfac k]
      _ = M * ∑ k : Fin (N + 1), spinSOpMinus N k (σ x) • weylSiteMono x k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
      _ = M * (X (x, 1) * pderiv (x, 0) (weylSiteMono x (σ x))) := by
          rw [weylSiteMono_spinSOpMinus_sum]
      _ = X (x, 1) * pderiv (x, 0) (weylMono σ) := by
          rw [hσ, pderiv_mul, hM 0, zero_mul, zero_add]
          ring
  rw [weylMap_mulVec_of_column (mulXPderiv ((x, 1) : Fin L × Fin 2) (x, 0)) hcol φ,
    mulXPderiv_apply]

/-- Global diagonal transport: `onSiteS x Ŝ^{(3)}` intertwines with `½(a_x - b_x)` under
`weylMap`. -/
theorem weylMap_mulVec_onSiteS_spinSOp3 (x : Fin L) (φ : (Fin L → Fin (N + 1)) → ℂ) :
    weylMap ((onSiteS x (spinSOp3 N)).mulVec φ)
      = (1 / 2 : ℂ) • (X (x, 0) * pderiv (x, 0) (weylMap φ)
          - X (x, 1) * pderiv (x, 1) (weylMap φ)) := by
  have happly : ∀ p : MvPolynomial (Fin L × Fin 2) ℂ,
      ((1 / 2 : ℂ) • (mulXPderiv ((x, 0) : Fin L × Fin 2) (x, 0)
          - mulXPderiv ((x, 1) : Fin L × Fin 2) (x, 1))) p
        = (1 / 2 : ℂ) • (X (x, 0) * pderiv (x, 0) p - X (x, 1) * pderiv (x, 1) p) := by
    intro p
    rw [LinearMap.smul_apply, LinearMap.sub_apply, mulXPderiv_apply, mulXPderiv_apply]
  have hcol : ∀ σ : Fin L → Fin (N + 1),
      ∑ σ' : Fin L → Fin (N + 1),
          (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N) σ' σ • weylMono σ'
        = ((1 / 2 : ℂ) • (mulXPderiv ((x, 0) : Fin L × Fin 2) (x, 0)
            - mulXPderiv ((x, 1) : Fin L × Fin 2) (x, 1))) (weylMono σ) := by
    intro σ
    obtain ⟨M, hM, hfac⟩ := exists_weylMono_site_factor x σ
    have hσ : weylMono σ = M * weylSiteMono x (σ x) := by
      have h := hfac (σ x)
      rwa [Function.update_eq_self] at h
    rw [weylMono_onSiteS_column, happly]
    calc ∑ k : Fin (N + 1), spinSOp3 N k (σ x) • weylMono (Function.update σ x k)
        = ∑ k : Fin (N + 1), spinSOp3 N k (σ x) • (M * weylSiteMono x k) :=
          Finset.sum_congr rfl fun k _ => by rw [hfac k]
      _ = M * ∑ k : Fin (N + 1), spinSOp3 N k (σ x) • weylSiteMono x k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
      _ = M * ((1 / 2 : ℂ) • (X (x, 0) * pderiv (x, 0) (weylSiteMono x (σ x))
            - X (x, 1) * pderiv (x, 1) (weylSiteMono x (σ x)))) := by
          rw [weylSiteMono_spinSOp3_sum]
      _ = (1 / 2 : ℂ) • (X (x, 0) * pderiv (x, 0) (weylMono σ)
            - X (x, 1) * pderiv (x, 1) (weylMono σ)) := by
          rw [hσ, pderiv_mul, pderiv_mul, hM 0, hM 1]
          simp only [zero_mul, zero_add]
          rw [mul_smul_comm]
          congr 1
          ring
  rw [weylMap_mulVec_of_column ((1 / 2 : ℂ) • (mulXPderiv ((x, 0) : Fin L × Fin 2) (x, 0)
      - mulXPderiv ((x, 1) : Fin L × Fin 2) (x, 1))) hcol φ, happly]

end LatticeSystem.Quantum
