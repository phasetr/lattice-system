import LatticeSystem.Quantum.SpinS.AKLTOpenChainWeylFactorization
import LatticeSystem.Math.MvPolynomial.WeylSpinMap

/-!
# General-`S` boundary shape of the open-chain cofactor

Regression gate for the general-`S` boundary layer of
`Quantum.SpinS.AKLTOpenChainWeylFactorization`: the `(S+1)²` boundary multidegrees `boundaryDeg`
(their per-site exponents, their injectivity and the resulting `(S+1)²` count), the weighted
homogeneity and nonvanishing of the divisor `∏_x f_x^S`, and the headline shape
`exists_boundary_factorization`.

Load-bearing controls: the `S = 0` degenerate case, which a wrong `S − a` truncation would get
wrong first; the `S = 1` oracle, pinning the general shape against the pre-existing
`weylMap_openGroundForm_eq_boundary_smul_prod` of eq. (S.77) so that the `u ↔ v` convention cannot
drift; and a shape-membership control pinning the image of `boundaryDeg` at `S = 1` against a
multidegree that divisibility alone would admit.
-/

open MvPolynomial
open LatticeSystem.Quantum LatticeSystem.Quantum.AKLTUniqueness LatticeSystem.Math

namespace LatticeSystem.Tests.GeneralSBoundaryShape

/-! ## 0. The boundary multidegree itself -/

/-- **Signature pin**: a boundary multidegree is the degree-`S` Weyl multidegree of the first site
times that of the last site, so it uses the Weyl map's own `0 ↦ u`, `1 ↦ v` convention. -/
example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab
      = mdSite (N := S) (0 : Fin (m + 2)) ab.1 + mdSite (N := S) (Fin.last (m + 1)) ab.2 :=
  rfl

/-! ## 1. Per-site exponents -/

example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab ((0 : Fin (m + 2)), 0) = S - (ab.1 : ℕ) :=
  boundaryDeg_apply_first_u ab

example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab ((0 : Fin (m + 2)), 1) = (ab.1 : ℕ) :=
  boundaryDeg_apply_first_v ab

example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab (Fin.last (m + 1), 0) = S - (ab.2 : ℕ) :=
  boundaryDeg_apply_last_u ab

example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab (Fin.last (m + 1), 1) = (ab.2 : ℕ) :=
  boundaryDeg_apply_last_v ab

/-- Interior sites (neither the first nor the last) carry degree `0` in both their variables — the
arithmetic that pins the shape's degree at the two ends only. -/
example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) {y : Fin (m + 2)} (h0 : y ≠ 0)
    (hl : y ≠ Fin.last (m + 1)) (j : Fin 2) : boundaryDeg m S ab (y, j) = 0 :=
  boundaryDeg_apply_interior ab h0 hl j

/-- Each end's two exponents split `S` — the arithmetic that `cofactor_support_shape` produces from
weighted homogeneity, checked here against `boundaryDeg`'s own values. -/
example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab ((0 : Fin (m + 2)), 0) + boundaryDeg m S ab ((0 : Fin (m + 2)), 1) = S := by
  rw [boundaryDeg_apply_first_u, boundaryDeg_apply_first_v]
  have := Nat.lt_succ_iff.mp ab.1.isLt
  omega

example (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDeg m S ab (Fin.last (m + 1), 0) + boundaryDeg m S ab (Fin.last (m + 1), 1) = S := by
  rw [boundaryDeg_apply_last_u, boundaryDeg_apply_last_v]
  have := Nat.lt_succ_iff.mp ab.2.isLt
  omega

/-! ## 2. Injectivity of the boundary multidegree map -/

/-- **The general-`S` boundary multidegree map is injective**: reading off the two `v`-coordinates
recovers `ab` exactly (the `(S+1)²` distinct boundary shapes of Tasaki §8.3.1, p. 252). -/
example (m S : ℕ) : Function.Injective (boundaryDeg m S) :=
  boundaryDeg_injective

/-! ## 3. Numeric bijection counts -/

/-- `S = 0` degenerate control: the unique boundary multidegree (`a = b = 0`) is the zero
multidegree, i.e. a constant monomial.  This is the case a wrong `S - a` truncation would get
wrong first (`0 - 0` vs. an off-by-one). -/
example (m : ℕ) : boundaryDeg m 0 (0, 0) = 0 := by
  ext e
  obtain ⟨y, j⟩ := e
  by_cases hy0 : y = 0
  · subst hy0; fin_cases j <;> simp [boundaryDeg_apply_first_u, boundaryDeg_apply_first_v]
  · by_cases hyl : y = Fin.last (m + 1)
    · subst hyl; fin_cases j <;> simp [boundaryDeg_apply_last_u, boundaryDeg_apply_last_v]
    · simp [boundaryDeg_apply_interior (0, 0) hy0 hyl]

/-- `S = 1` oracle: the general boundary multidegree at `S = 1` is *literally* the `S = 1` boundary
multidegree of eq. (S.77), one variable of the first site times one variable of the last site, so
the generalization involves no re-indexing. -/
example (m : ℕ) (ab : Fin 2 × Fin 2) :
    boundaryDeg m 1 ab
      = Finsupp.single ((0 : Fin (m + 2)), ab.1) 1 + Finsupp.single (Fin.last (m + 1), ab.2) 1 :=
  boundaryDeg_one ab

/-- **`S = 1` four-fold count**: the `(1+1)² = 4` boundary multidegrees are pairwise distinct. -/
example (m : ℕ) : Finset.card (Finset.image (boundaryDeg m 1) Finset.univ) = 4 := by
  rw [Finset.card_image_of_injective _ (boundaryDeg_injective (m := m) (S := 1))]
  simp

/-- **`S = 2`, `m = 0` (`L = 2`) nine-fold count**: Tasaki's `(S+1)² = 9`-fold boundary shape
named at §8.3.1, p. 252. -/
example : Finset.card (Finset.image (boundaryDeg 0 2) Finset.univ) = 9 := by
  rw [Finset.card_image_of_injective _ (boundaryDeg_injective (m := 0) (S := 2))]
  simp

/-! ## 4. The divisor `∏_x f_x^S` and the headline shape -/

/-- `prod_openBonds_fBond_pow_isWeightedHomogeneous`: the `S`-th power of the open-bond product is
`siteWeight`-homogeneous of the `S`-scaled per-bond degree. -/
example (L S : ℕ) :
    (∏ x ∈ openBonds L, fBond x ^ S).IsWeightedHomogeneous (siteWeight (L := L))
      (S • ∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1)) :=
  prod_openBonds_fBond_pow_isWeightedHomogeneous S

/-- `prod_openBonds_fBond_pow_ne_zero`: the `S`-th power of the open-bond product is nonzero for
`1 < L` — the load-bearing `q ≠ 0` hypothesis of the weighted cofactor lemma. -/
example (L S : ℕ) (hL : 1 < L) : (∏ x ∈ openBonds L, fBond x ^ S) ≠ 0 :=
  prod_openBonds_fBond_pow_ne_zero hL S

/-- **Headline `exists_boundary_factorization`**: a polynomial of per-site degree `2S` divisible by
`∏_x f_x^S` is that product times a boundary form supported on the `(S+1)²` boundary
multidegrees. -/
example {m S : ℕ} {p : MvPolynomial (Fin (m + 2) × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := m + 2))
            (∑ x : Fin (m + 2), Finsupp.single x (2 * S)))
    (hdvd : (∏ x ∈ openBonds (m + 2), fBond x ^ S) ∣ p) :
    ∃ c : Fin (S + 1) × Fin (S + 1) → ℂ,
      p = (∑ ab : Fin (S + 1) × Fin (S + 1), monomial (boundaryDeg m S ab) (c ab))
            * ∏ x ∈ openBonds (m + 2), fBond x ^ S :=
  exists_boundary_factorization hp hdvd

/-- **`S = 1` specialization control**: the pre-existing eq. (S.77) statement must still elaborate
verbatim after the generalization — it is now a corollary of the headline, and any drift of the
`u ↔ v` convention or of the boundary-index order would break it here. -/
example {m : ℕ} (Ψ : (Fin (m + 2) → Fin 3) → ℂ)
    (hΨ : ∀ x ∈ openBonds (m + 2), IsVBSGroundForm (m + 2) x Ψ) :
    ∃ c : Fin 2 × Fin 2 → ℂ,
      weylMap Ψ
        = (∑ ab : Fin 2 × Fin 2,
            MvPolynomial.C (c ab) * (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2)))
            * ∏ x ∈ openBonds (m + 2), fBond x :=
  weylMap_openGroundForm_eq_boundary_smul_prod Ψ hΨ

/-- **Shape-membership control**: the multidegree of `X (0,0) ^ 2` lies outside the `S = 1`
boundary shape, even though `(∏ f_x^1) * X (0,0) ^ 2` is divisible by `∏ f_x^1`.  The two halves
are established separately, so this pins the image of `boundaryDeg` — the two first-site exponents
of a boundary multidegree sum to `S`, here to `1`, whereas `X (0,0) ^ 2` sums to `2` — against a
multidegree that the divisibility hypothesis of `exists_boundary_factorization` would admit on its
own.  A wrong generalization of `boundaryDeg` allowing an end degree above `S` fails here.  This is
a statement about `boundaryDeg`, not a refutation of a factorization: ruling out a boundary
factorization of that `p` would additionally need the cancellation step in the integral domain. -/
example :
    (∏ x ∈ openBonds 2, fBond x ^ 1) ∣ (∏ x ∈ openBonds 2, fBond x ^ 1) * X ((0 : Fin 2), 0) ^ 2 ∧
      ¬ ∃ d ∈ Finset.image (boundaryDeg 0 1) Finset.univ,
          d = Finsupp.single ((0 : Fin 2), 0) 2 := by
  refine ⟨⟨X ((0 : Fin 2), 0) ^ 2, rfl⟩, ?_⟩
  rintro ⟨d, hd, rfl⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd
  obtain ⟨ab, hab⟩ := hd
  have h1 := congrArg (fun f : (Fin 2 × Fin 2) →₀ ℕ => f ((0 : Fin 2), 0)) hab
  simp [boundaryDeg_apply_first_u] at h1
  have hlt := ab.1.isLt
  omega

end LatticeSystem.Tests.GeneralSBoundaryShape
