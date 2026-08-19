import LatticeSystem.Quantum.SpinS.AKLTOpenChainWeylFactorization
import LatticeSystem.Quantum.SpinS.GeneralSOpenChainBondTerm
import LatticeSystem.Math.MvPolynomial.WeylSpinMap

/-!
# TDD Red: PR-5 of #5292 — general-`S` boundary shape of the open-chain cofactor

Design source: `.self-local/reports/design-5292-pr5-boundary-shape-round1-20260820.md`.  This file
is written **before** the general-`S` production declarations exist, per the design's §2/§3
skeleton (`boundaryDeg m S`, `exists_boundary_factorization`,
`prod_openBonds_fBond_pow_isWeightedHomogeneous`).  Two kinds of statements appear:

* Statements provable **now** from already-existing declarations (`mdSite`, `openBonds`, `fBond`,
  `siteWeight`) — these are genuine Red-phase tests and are proved outright, not `sorry`d.  Chief
  among them: `boundaryDegFixture`, a *test-only fixture* mirroring the design's intended
  `boundaryDeg m S ab := mdSite 0 ab.1 + mdSite (Fin.last (m+1)) ab.2`, used only to compute and pin
  the shape's numeric content (injectivity, the `S = 1` four-fold and `S = 2` nine-fold count, the
  `S = 0` degenerate case) ahead of the real `boundaryDeg` landing.  It must be **deleted** once the
  production `boundaryDeg` is public and every reference below switched to it directly — that switch
  is itself part of what makes this file's later green run a genuine regression check.
* Signature pins for declarations that do not exist yet (`exists_boundary_factorization`,
  `prod_openBonds_fBond_pow_isWeightedHomogeneous`) — these are `sorry`d on purpose: the goal is to
  fix the exact statement ahead of implementation, and `sorry` is this repo's build-error signal
  (`lakefile.toml` `mathlibStandardSet` + `warningAsError`) that the corresponding production
  declaration is still missing.  `lake build` on this file is expected to **fail** until PR-5 lands.
-/

open MvPolynomial
open LatticeSystem.Quantum LatticeSystem.Quantum.AKLTUniqueness LatticeSystem.Math

namespace LatticeSystem.Tests.GeneralSBoundaryShape

/-! ## 0. Fixture: the intended `boundaryDeg m S ab`, spelled out via the already-existing
`mdSite` (design §3), since the production declaration does not exist yet. -/

/-- Test-only stand-in for the future public `AKLTUniqueness.boundaryDeg m S ab`. -/
noncomputable def boundaryDegFixture (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    (Fin (m + 2) × Fin 2) →₀ ℕ :=
  mdSite (N := S) (0 : Fin (m + 2)) ab.1 + mdSite (N := S) (Fin.last (m + 1)) ab.2

/-! ## 1. Per-site apply lemmas (design §3, `boundaryDeg_apply_{first,last}_{u,v}` /
`_interior`) -/

private theorem zero_ne_last (m : ℕ) : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem boundaryDegFixture_apply_first_u (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDegFixture m S ab ((0 : Fin (m + 2)), 0) = S - (ab.1 : ℕ) := by
  simp [boundaryDegFixture, Finsupp.add_apply, mdSite_apply_self,
    mdSite_apply_ne (zero_ne_last m).symm]

theorem boundaryDegFixture_apply_first_v (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDegFixture m S ab ((0 : Fin (m + 2)), 1) = (ab.1 : ℕ) := by
  simp [boundaryDegFixture, Finsupp.add_apply, mdSite_apply_snd,
    mdSite_apply_ne (zero_ne_last m).symm]

theorem boundaryDegFixture_apply_last_u (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDegFixture m S ab (Fin.last (m + 1), 0) = S - (ab.2 : ℕ) := by
  simp [boundaryDegFixture, Finsupp.add_apply, mdSite_apply_self, mdSite_apply_ne (zero_ne_last m)]

theorem boundaryDegFixture_apply_last_v (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDegFixture m S ab (Fin.last (m + 1), 1) = (ab.2 : ℕ) := by
  simp [boundaryDegFixture, Finsupp.add_apply, mdSite_apply_snd, mdSite_apply_ne (zero_ne_last m)]

/-- Interior sites (neither the first nor the last) carry degree `0` in both their variables — the
arithmetic that pins the shape's total degree at the two ends only. -/
theorem boundaryDegFixture_apply_interior (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1))
    {y : Fin (m + 2)} (h0 : y ≠ 0) (hl : y ≠ Fin.last (m + 1)) (j : Fin 2) :
    boundaryDegFixture m S ab (y, j) = 0 := by
  simp [boundaryDegFixture, Finsupp.add_apply, mdSite_apply_ne (Ne.symm h0),
    mdSite_apply_ne (Ne.symm hl)]

/-- Each end's two exponents split `S` — the arithmetic `cofactor_support_shape` will produce from
weighted homogeneity, checked here directly against the fixture's definition. -/
theorem boundaryDegFixture_first_sum (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDegFixture m S ab ((0 : Fin (m + 2)), 0)
      + boundaryDegFixture m S ab ((0 : Fin (m + 2)), 1) = S := by
  rw [boundaryDegFixture_apply_first_u, boundaryDegFixture_apply_first_v]
  omega

theorem boundaryDegFixture_last_sum (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    boundaryDegFixture m S ab (Fin.last (m + 1), 0)
      + boundaryDegFixture m S ab (Fin.last (m + 1), 1) = S := by
  rw [boundaryDegFixture_apply_last_u, boundaryDegFixture_apply_last_v]
  omega

/-! ## 2. Injectivity of the boundary multidegree map (design §3, `boundaryDeg_injective`) -/

/-- **The general-`S` boundary multidegree map is injective**: reading off the two `v`-coordinates
recovers `ab` exactly (the `(S+1)²` distinct boundary shapes of Tasaki §8.3.1, p. 252). -/
theorem boundaryDegFixture_injective (m S : ℕ) : Function.Injective (boundaryDegFixture m S) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have ha := congrArg (fun f : (Fin (m + 2) × Fin 2) →₀ ℕ => f ((0 : Fin (m + 2)), 1)) h
  have hb := congrArg (fun f : (Fin (m + 2) × Fin 2) →₀ ℕ => f (Fin.last (m + 1), 1)) h
  simp only [boundaryDegFixture_apply_first_v, boundaryDegFixture_apply_last_v] at ha hb
  have ha' : a₁ = a₂ := Fin.ext ha
  have hb' : b₁ = b₂ := Fin.ext hb
  rw [ha', hb']

/-! ## 3. Numeric bijection counts -/

/-- `S = 0` degenerate control: the unique boundary multidegree (`a = b = 0`) is the zero
multidegree, i.e. a constant monomial.  This is the case a wrong `S - a` truncation would get
wrong first (`0 - 0` vs. an off-by-one). -/
example (m : ℕ) : boundaryDegFixture m 0 (0, 0) = 0 := by
  ext e
  obtain ⟨y, j⟩ := e
  by_cases hy0 : y = 0
  · subst hy0; fin_cases j <;>
      simp [boundaryDegFixture_apply_first_u, boundaryDegFixture_apply_first_v]
  · by_cases hyl : y = Fin.last (m + 1)
    · subst hyl; fin_cases j <;>
        simp [boundaryDegFixture_apply_last_u, boundaryDegFixture_apply_last_v]
    · simp [boundaryDegFixture_apply_interior m 0 (0, 0) hy0 hyl]

/-- `S = 1` oracle: the fixture's `S = 1` instance is *literally* the existing `S = 1` boundary
multidegree formula of `weylMap_openGroundForm_eq_boundary_smul_prod`'s proof
(`AKLTOpenChainWeylFactorization.lean:176`), so the eventual general `boundaryDeg` generalizes it
without any re-indexing (design §2, decision 3). -/
theorem boundaryDegFixture_one (m : ℕ) (ab : Fin 2 × Fin 2) :
    boundaryDegFixture m 1 ab
      = Finsupp.single ((0 : Fin (m + 2)), ab.1) 1 + Finsupp.single (Fin.last (m + 1), ab.2) 1 := by
  have hmd : ∀ (x : Fin (m + 2)) (k : Fin 2), mdSite (N := 1) x k = Finsupp.single (x, k) 1 := by
    intro x k
    fin_cases k <;> simp [mdSite]
  rw [boundaryDegFixture, hmd, hmd]

/-- **`S = 1` four-fold count**: the `(1+1)² = 4` boundary multidegrees are pairwise distinct. -/
example (m : ℕ) : Finset.card (Finset.image (boundaryDegFixture m 1) Finset.univ) = 4 := by
  rw [Finset.card_image_of_injective _ (boundaryDegFixture_injective m 1)]
  simp

/-- **`S = 2`, `m = 0` (`L = 2`) nine-fold count**: Tasaki's `(S+1)² = 9`-fold boundary shape
named at §8.3.1, p. 252. -/
example : Finset.card (Finset.image (boundaryDegFixture 0 2) Finset.univ) = 9 := by
  rw [Finset.card_image_of_injective _ (boundaryDegFixture_injective 0 2)]
  simp

/-! ## 4. Signature pins for not-yet-existing production declarations (`sorry`-marked Red) -/

/-- **Red pin — `prod_openBonds_fBond_pow_isWeightedHomogeneous`** (design §3): the `S`-th power of
the open-bond product is `siteWeight`-homogeneous of the `S`-scaled per-bond degree.  Not yet
implemented; `sorry` marks the missing production declaration. -/
example (L S : ℕ) :
    (∏ x ∈ openBonds L, fBond x ^ S).IsWeightedHomogeneous (siteWeight (L := L))
      (S • ∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1)) := by
  sorry

/-- **Red pin — `prod_openBonds_fBond_pow_ne_zero`** (design §3): the `S`-th power of the open-bond
product is nonzero, for `1 < L`.  Not yet implemented. -/
example (L S : ℕ) (hL : 1 < L) : (∏ x ∈ openBonds L, fBond x ^ S) ≠ 0 := by
  sorry

/-- **Red pin — headline `exists_boundary_factorization`** (design §2): the general-`S` boundary
shape of the cofactor.  Statement spelled out with `boundaryDegFixture` standing in for the future
public `boundaryDeg`; `sorry` marks the missing production declaration. -/
example {m S : ℕ} {p : MvPolynomial (Fin (m + 2) × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := m + 2))
            (∑ x : Fin (m + 2), Finsupp.single x (2 * S)))
    (hdvd : (∏ x ∈ openBonds (m + 2), fBond x ^ S) ∣ p) :
    ∃ c : Fin (S + 1) × Fin (S + 1) → ℂ,
      p = (∑ ab : Fin (S + 1) × Fin (S + 1), monomial (boundaryDegFixture m S ab) (c ab))
            * ∏ x ∈ openBonds (m + 2), fBond x ^ S := by
  sorry

/-- **`S = 1` specialization control**: the headline pin above, instantiated at `S = 1` via
`hp := weylMap_isWeightedHomogeneous Ψ` and `hdvd` from the existing bond-divisibility bridge, must
reduce (through `boundaryDegFixture_one` and `monomial`-to-`X * X` unfolding) to exactly the
existing `weylMap_openGroundForm_eq_boundary_smul_prod` conclusion.  `sorry`d until the headline
exists; this is the regression anchor of design pitfall 5 (the `S = 1` statement must not need to
change). -/
example {m : ℕ} (Ψ : (Fin (m + 2) → Fin 3) → ℂ)
    (hΨ : ∀ x ∈ openBonds (m + 2), IsVBSGroundForm (m + 2) x Ψ) :
    ∃ c : Fin 2 × Fin 2 → ℂ,
      weylMap Ψ
        = (∑ ab : Fin 2 × Fin 2,
            MvPolynomial.C (c ab) * (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2)))
            * ∏ x ∈ openBonds (m + 2), fBond x :=
  weylMap_openGroundForm_eq_boundary_smul_prod Ψ hΨ

/-- **Negative control**: the `hp` weighted-homogeneity hypothesis of
`exists_boundary_factorization` is load-bearing.  Without it, `hdvd` alone is too weak:
`p := (∏ f_x^S) * X (0,0) ^ (S + 1)` is divisible by `∏ f_x^S` but (already at `S = 1`, `m = 0`) its
cofactor `X (0,0) ^ 2` has degree `2` at the first site, not `1`, so it is not a sum of the
`boundaryDegFixture` monomials at `S = 1` (`boundaryDegFixture_first_sum` forces the two first-site
exponents to sum to `S`, but here they sum to `2 ≠ 1`). -/
example :
    (∏ x ∈ openBonds 2, fBond x ^ 1) ∣ (∏ x ∈ openBonds 2, fBond x ^ 1) * X ((0 : Fin 2), 0) ^ 2 ∧
      ¬ ∃ d ∈ Finset.image (boundaryDegFixture 0 1) Finset.univ,
          d = Finsupp.single ((0 : Fin 2), 0) 2 := by
  refine ⟨⟨X ((0 : Fin 2), 0) ^ 2, rfl⟩, ?_⟩
  rintro ⟨d, hd, rfl⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd
  obtain ⟨ab, hab⟩ := hd
  have h1 := congrArg (fun f : (Fin 2 × Fin 2) →₀ ℕ => f ((0 : Fin 2), 0)) hab
  simp [boundaryDegFixture_apply_first_u] at h1
  have hlt := ab.1.isLt
  omega

end LatticeSystem.Tests.GeneralSBoundaryShape
