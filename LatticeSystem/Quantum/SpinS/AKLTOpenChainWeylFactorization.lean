/-
# Tasaki §7.2.3 (Problem 7.2.3.b): the boundary-quadratic factorization (S.77)

The polynomial half of the completeness statement for the **open** `S = 1` AKLT chain: the Weyl
image of any open-chain ground form is a **boundary quadratic** in the two end sites times the
product of the `L − 1` open bond factors,

`weylMap Ψ = (Σ_{a,b} c_{ab} u/v_1^a u/v_L^b) · ∏_{x=1}^{L-1} (u_x v_{x+1} − v_x u_{x+1})`.

Structurally this repeats the ring argument of `AKLTUniqueness/ProductBondDivisibility.lean` with
`Finset.univ` replaced by `openBonds L`, with one genuine difference.  On the ring the `L` bond
factors already account for the whole degree `2L` of the Weyl image, so the cofactor is a
*constant* and the ground space is one-dimensional.  On the open chain there are only `L − 1`
bonds, total degree `2L − 2`, so the cofactor has degree `2` — and the total-degree grading is far
too coarse to pin a degree-`2` form in `2L` variables.  What does pin it is the **per-site**
grading of `Math/MvPolynomial/WeightedHomogeneousLayer.lean`: every site of the Weyl image carries
degree exactly `2`, the open bond product carries `1` at each end site and `2` in the bulk, so the
cofactor carries `1` at each end and `0` everywhere else.  Those are exactly the four monomials
`u_1 u_L, u_1 v_L, v_1 u_L, v_1 v_L` of eq. (S.77).

The bond factors are handled with the same UFD machinery as on the ring, but the separation
witness is produced by `exists_open_bond_var_witness`, which needs no hypothesis on `L` at all
(the cyclic `exists_bond_var_witness` needs `3 ≤ L`); this is what makes `2 ≤ L` — the same
hypothesis as the lower bound of Problem 7.2.3.a — sufficient here.

**Correction to the printed statement.**  The product in eq. (S.77) is printed with upper index
`L`; the correct upper index is `L − 1`.  The same solution states that eq. (7.1.24) holds for
`x = 1, …, L − 1`, the open chain has `L − 1` bonds, `u_{L+1}` does not exist, and the degree count
is `2 + 2(L − 1) = 2L`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.3, Problem 7.2.3.b, p. 207, solution (S.77), p. 508; §7.1.3, eqs. (7.1.22)–(7.1.25),
pp. 186–188; proof due to Kennedy–Lieb–Tasaki [41].
-/
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.ProductBondDivisibility
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer

open MvPolynomial

namespace LatticeSystem.Quantum.AKLTUniqueness

open LatticeSystem.Quantum LatticeSystem.Math

variable {L : ℕ}

/-! ### Separation and coprimality of distinct open bonds -/

/-- **Open bond-separation witness.**  Two distinct open bonds `{x, x+1} ≠ {y, y+1}` are separated
by a site `s ∈ {x, ringSucc x}` lying off `{y, ringSucc y}`: take the left endpoint `x` when the
bond `x` is to the left, the right endpoint `x+1` otherwise.  Unlike the cyclic
`exists_bond_var_witness`, this needs **no** hypothesis on `L`, because on the open chain the
successor never wraps (`ringSucc_val_of_mem_openBonds`) and the bonds are genuinely ordered. -/
theorem exists_open_bond_var_witness {x y : Fin L} (hx : x ∈ openBonds L) (hy : y ∈ openBonds L)
    (hxy : x ≠ y) : ∃ s : Fin L, (s = x ∨ s = ringSucc x) ∧ s ≠ y ∧ s ≠ ringSucc y := by
  have hxv : (ringSucc x).val = x.val + 1 := ringSucc_val_of_mem_openBonds hx
  have hyv : (ringSucc y).val = y.val + 1 := ringSucc_val_of_mem_openBonds hy
  have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  rcases lt_trichotomy x.val y.val with hlt | heq | hgt
  · exact ⟨x, Or.inl rfl, fun h => hne (congrArg Fin.val h),
      fun h => by have hv := congrArg Fin.val h; omega⟩
  · exact absurd heq hne
  · exact ⟨ringSucc x, Or.inr rfl, fun h => by have hv := congrArg Fin.val h; omega,
      fun h => by have hv := congrArg Fin.val h; omega⟩

/-- **Distinct open bonds are relatively prime.**  The exact hypothesis is `2 ≤ L`: at `L = 2`
there is a single open bond and the statement is vacuous, but the witness lemma feeding
`fBond_isRelPrime_of_witness` must still be available there — which the cyclic `fBond_isRelPrime`
(`3 ≤ L`) is not. -/
theorem fBond_isRelPrime_openBonds (hL : 2 ≤ L) {x y : Fin L} (hx : x ∈ openBonds L)
    (hy : y ∈ openBonds L) (hxy : x ≠ y) : IsRelPrime (fBond x) (fBond y) :=
  fBond_isRelPrime_of_witness (by omega) (exists_open_bond_var_witness hx hy hxy)

/-! ### Per-site homogeneity of the bond factors -/

/-- The bond factor `f_x = u_x v_{x+1} − v_x u_{x+1}` is `siteWeight`-homogeneous of the two-site
degree `single x 1 + single (ringSucc x) 1`: both of its monomials use one variable of site `x` and
one variable of site `x+1`.  This is the per-site refinement of `fBond_totalDegree`. -/
theorem fBond_isWeightedHomogeneous (x : Fin L) :
    (fBond x).IsWeightedHomogeneous (siteWeight (L := L))
      (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) := by
  unfold fBond
  exact bondFactor_isWeightedHomogeneous siteWeight (x, 0) (ringSucc x, 1) (x, 1)
    (ringSucc x, 0) rfl

/-- The product of the **open** bond factors is `siteWeight`-homogeneous of the summed per-bond
degree.  The sum ranges over `openBonds L` and never over `Finset.univ`: with the wrap bond every
site would carry degree `2` and the boundary quadratic of eq. (S.77) would collapse to a
constant. -/
theorem prod_openBonds_fBond_isWeightedHomogeneous :
    (∏ x ∈ openBonds L, fBond x).IsWeightedHomogeneous (siteWeight (L := L))
      (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1)) :=
  IsWeightedHomogeneous.prod _ _ _ fun x _ => fBond_isWeightedHomogeneous x

/-- The product of the open bond factors is nonzero (each factor is prime).  This discharges the
load-bearing `q ≠ 0` hypothesis of `isWeightedHomogeneous_cofactor_weight`, without which both
homogeneity hypotheses of that lemma are vacuous. -/
theorem prod_openBonds_fBond_ne_zero (hL : 1 < L) : (∏ x ∈ openBonds L, fBond x) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun x _ => (fBond_prime hL x).ne_zero

/-! ### Per-site bookkeeping: degree `1` at the two ends, `2` in the bulk -/

/-- The left endpoints of the open bonds contribute degree `1` to exactly the sites that carry a
bond to their right. -/
private theorem sum_openBonds_single_left_apply (y : Fin L) :
    (∑ x ∈ openBonds L, Finsupp.single x 1 : Fin L →₀ ℕ) y = if y ∈ openBonds L then 1 else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

/-- The right endpoints of the open bonds contribute degree `1` to exactly the sites that carry a
bond to their left, i.e. to every site but the first. -/
private theorem sum_openBonds_single_right_apply (y : Fin L) :
    (∑ x ∈ openBonds L, Finsupp.single (ringSucc x) 1 : Fin L →₀ ℕ) y
      = if 0 < y.val then 1 else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rcases Nat.eq_zero_or_pos y.val with hy | hy
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun x hx => ?_
    refine if_neg fun h => ?_
    have := ringSucc_val_of_mem_openBonds hx
    have hv := congrArg Fin.val h
    omega
  · rw [if_pos hy]
    have hyL : y.val < L := y.isLt
    have hzmem : (⟨y.val - 1, by omega⟩ : Fin L) ∈ openBonds L := by
      rw [mem_openBonds]
      change y.val - 1 + 1 < L
      omega
    have hzsucc : ringSucc (⟨y.val - 1, by omega⟩ : Fin L) = y :=
      Fin.ext (by
        rw [ringSucc_val_of_mem_openBonds hzmem]
        change y.val - 1 + 1 = y.val
        omega)
    rw [Finset.sum_eq_single_of_mem _ hzmem, if_pos hzsucc]
    intro b hb hbz
    refine if_neg fun h => hbz (Fin.ext ?_)
    have hbv := ringSucc_val_of_mem_openBonds hb
    have hv := congrArg Fin.val h
    change b.val = y.val - 1
    omega

/-- The per-site degree of the open bond product, split into the two endpoint contributions. -/
private theorem prodWeight_apply (y : Fin L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ) y
      = (if y ∈ openBonds L then 1 else 0) + (if 0 < y.val then 1 else 0) := by
  rw [Finset.sum_add_distrib, Finsupp.add_apply, sum_openBonds_single_left_apply,
    sum_openBonds_single_right_apply]

/-- **Bulk sites carry degree `2`**: an interior site has a bond on each side.  This is the value
that *every* site would carry if the product ran over `Finset.univ`, i.e. if the wrap bond leaked
back in — the boundary values below are what distinguish the open chain from the ring. -/
theorem prodWeight_apply_of_interior {y : Fin L} (h0 : 0 < y.val) (hl : y.val + 1 < L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ)
      y = 2 := by
  rw [prodWeight_apply, if_pos (mem_openBonds.mpr hl), if_pos h0]

/-- **The first site carries degree `1`**: it has a bond to its right only. -/
theorem prodWeight_apply_first (hL : 2 ≤ L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ)
      ⟨0, by omega⟩ = 1 := by
  rw [prodWeight_apply, if_pos (mem_openBonds.mpr (by simp; omega)), if_neg (by simp)]

/-- **The last site carries degree `1`**: it has a bond to its left only. -/
theorem prodWeight_apply_last (hL : 2 ≤ L) :
    (∑ x ∈ openBonds L, (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) : Fin L →₀ ℕ)
      ⟨L - 1, by omega⟩ = 1 := by
  rw [prodWeight_apply, if_neg (by rw [mem_openBonds]; simp; omega), if_pos (by simp; omega)]

/-! ### The shape of the cofactor -/

/-- The four boundary multidegrees of eq. (S.77): one variable of the first site and one variable
of the last site, indexed by the two free `S = 1/2` edge spins. -/
private noncomputable def boundaryDeg (m : ℕ) (ab : Fin 2 × Fin 2) : (Fin (m + 2) × Fin 2) →₀ ℕ :=
  Finsupp.single ((0 : Fin (m + 2)), ab.1) 1 + Finsupp.single (Fin.last (m + 1), ab.2) 1

/-- The first and last sites of a chain of length `≥ 2` are distinct. -/
private theorem first_ne_last (m : ℕ) : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

/-- Coefficientwise description of a boundary multidegree. -/
private theorem boundaryDeg_apply {m : ℕ} (ab : Fin 2 × Fin 2) (y : Fin (m + 2)) (j : Fin 2) :
    boundaryDeg m ab (y, j)
      = (if (0 : Fin (m + 2)) = y ∧ ab.1 = j then 1 else 0)
        + (if Fin.last (m + 1) = y ∧ ab.2 = j then 1 else 0) := by
  simp only [boundaryDeg, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]

/-- A boundary multidegree at the first site reads off its first index. -/
private theorem boundaryDeg_apply_first {m : ℕ} (ab : Fin 2 × Fin 2) (j : Fin 2) :
    boundaryDeg m ab ((0 : Fin (m + 2)), j) = if ab.1 = j then 1 else 0 := by
  rw [boundaryDeg_apply]
  simp [Ne.symm (first_ne_last m)]

/-- A boundary multidegree at the last site reads off its second index. -/
private theorem boundaryDeg_apply_last {m : ℕ} (ab : Fin 2 × Fin 2) (j : Fin 2) :
    boundaryDeg m ab (Fin.last (m + 1), j) = if ab.2 = j then 1 else 0 := by
  rw [boundaryDeg_apply]
  simp [first_ne_last m]

/-- The four boundary multidegrees are pairwise distinct, so the four monomials of eq. (S.77) are
genuinely four independent monomials. -/
private theorem boundaryDeg_injective {m : ℕ} : Function.Injective (boundaryDeg m) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have ha := congrArg (fun f : (Fin (m + 2) × Fin 2) →₀ ℕ => f ((0 : Fin (m + 2)), a₁)) h
  have hb := congrArg (fun f : (Fin (m + 2) × Fin 2) →₀ ℕ => f (Fin.last (m + 1), b₁)) h
  simp only [boundaryDeg_apply_first, boundaryDeg_apply_last] at ha hb
  have ha' : a₂ = a₁ := by
    by_contra hc
    simp only [if_neg hc] at ha
    simp at ha
  have hb' : b₂ = b₁ := by
    by_contra hc
    simp only [if_neg hc] at hb
    simp at hb
  rw [ha', hb']

/-- **The cofactor has per-site degree `1` at each end and `0` in the bulk.**  Writing
`weylMap Ψ = (∏_{openBonds} f_x) · r`, the weighted cofactor lemma applied at each site turns the
per-site identity `(bond product degree) + (cofactor degree) = 2` into exponent arithmetic: `2 + ?`
in the bulk forces `? = 0`, and `1 + ?` at the two ends forces `? = 1`. -/
private theorem cofactor_support_shape {m : ℕ} (Ψ : (Fin (m + 2) → Fin 3) → ℂ)
    {r : MvPolynomial (Fin (m + 2) × Fin 2) ℂ}
    (hqr : weylMap Ψ = (∏ x ∈ openBonds (m + 2), fBond x) * r)
    {d : (Fin (m + 2) × Fin 2) →₀ ℕ} (hd : d ∈ r.support) :
    (∀ y : Fin (m + 2), y ≠ 0 → y ≠ Fin.last (m + 1) → d (y, 0) = 0 ∧ d (y, 1) = 0)
      ∧ d ((0 : Fin (m + 2)), 0) + d ((0 : Fin (m + 2)), 1) = 1
      ∧ d (Fin.last (m + 1), 0) + d (Fin.last (m + 1), 1) = 1 := by
  have hn : ((∏ x ∈ openBonds (m + 2), fBond x) * r).IsWeightedHomogeneous
      (siteWeight (L := m + 2)) (∑ x : Fin (m + 2), Finsupp.single x 2) := by
    rw [← hqr]
    exact weylMap_isWeightedHomogeneous Ψ
  have hkey := isWeightedHomogeneous_cofactor_weight
    (prod_openBonds_fBond_isWeightedHomogeneous (L := m + 2))
    (prod_openBonds_fBond_ne_zero (by omega)) hn hd
  have happ : ∀ y : Fin (m + 2),
      (∑ x ∈ openBonds (m + 2), (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1) :
          Fin (m + 2) →₀ ℕ) y + (d (y, 0) + d (y, 1)) = 2 := by
    intro y
    have h := congrArg (fun f : Fin (m + 2) →₀ ℕ => f y) hkey
    simpa only [Finsupp.add_apply, weight_siteWeight_apply, weylMapWeight_apply] using h
  have hz : (⟨0, by omega⟩ : Fin (m + 2)) = (0 : Fin (m + 2)) := Fin.ext (by simp)
  have hl : (⟨m + 2 - 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp)
  refine ⟨fun y hy0 hyl => ?_, ?_, ?_⟩
  · have hyLt : y.val < m + 2 := y.isLt
    have hy0' : y.val ≠ 0 := fun h => hy0 (Fin.ext (by simp [h]))
    have hyl' : y.val ≠ m + 1 := fun h => hyl (Fin.ext (by simp [h]))
    have hbulk := prodWeight_apply_of_interior (L := m + 2) (y := y) (by omega) (by omega)
    have h := happ y
    rw [hbulk] at h
    omega
  · have hfst := prodWeight_apply_first (L := m + 2) (by omega)
    rw [hz] at hfst
    have h := happ 0
    rw [hfst] at h
    omega
  · have hlst := prodWeight_apply_last (L := m + 2) (by omega)
    rw [hl] at hlst
    have h := happ (Fin.last (m + 1))
    rw [hlst] at h
    omega

/-- Every multidegree of the shape produced by `cofactor_support_shape` is one of the four
boundary multidegrees: degree `1` split over a site's two variables selects exactly one of
them. -/
private theorem exists_boundary_shape {m : ℕ} {d : (Fin (m + 2) × Fin 2) →₀ ℕ}
    (hint : ∀ y : Fin (m + 2), y ≠ 0 → y ≠ Fin.last (m + 1) → d (y, 0) = 0 ∧ d (y, 1) = 0)
    (hfst : d ((0 : Fin (m + 2)), 0) + d ((0 : Fin (m + 2)), 1) = 1)
    (hlst : d (Fin.last (m + 1), 0) + d (Fin.last (m + 1), 1) = 1) :
    ∃ ab : Fin 2 × Fin 2, d = boundaryDeg m ab := by
  classical
  have hA : ∃ a : Fin 2, ∀ j : Fin 2, d ((0 : Fin (m + 2)), j) = if a = j then 1 else 0 := by
    rcases (by omega : d ((0 : Fin (m + 2)), 0) = 1 ∧ d ((0 : Fin (m + 2)), 1) = 0
        ∨ d ((0 : Fin (m + 2)), 0) = 0 ∧ d ((0 : Fin (m + 2)), 1) = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, fun j => by fin_cases j <;> simp [h1, h2]⟩
    · exact ⟨1, fun j => by fin_cases j <;> simp [h1, h2]⟩
  have hB : ∃ b : Fin 2, ∀ j : Fin 2, d (Fin.last (m + 1), j) = if b = j then 1 else 0 := by
    rcases (by omega : d (Fin.last (m + 1), 0) = 1 ∧ d (Fin.last (m + 1), 1) = 0
        ∨ d (Fin.last (m + 1), 0) = 0 ∧ d (Fin.last (m + 1), 1) = 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, fun j => by fin_cases j <;> simp [h1, h2]⟩
    · exact ⟨1, fun j => by fin_cases j <;> simp [h1, h2]⟩
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨(a, b), ?_⟩
  ext e
  obtain ⟨y, j⟩ := e
  by_cases hy0 : (0 : Fin (m + 2)) = y
  · subst hy0
    rw [ha j, boundaryDeg_apply_first]
  · by_cases hyl : Fin.last (m + 1) = y
    · subst hyl
      rw [hb j, boundaryDeg_apply_last]
    · rw [boundaryDeg_apply, if_neg (fun h => hy0 h.1), if_neg (fun h => hyl h.1), add_zero]
      have hzero := hint y (fun h => hy0 h.symm) (fun h => hyl h.symm)
      fin_cases j
      · exact hzero.1
      · exact hzero.2

/-! ### Eq. (S.77) -/

/-- A degree-`(1,1)` monomial in two variables is the corresponding scaled product. -/
private theorem monomial_pair_eq {σ : Type*} (i j : σ) (c : ℂ) :
    (monomial (Finsupp.single i 1 + Finsupp.single j 1) c : MvPolynomial σ ℂ)
      = C c * (X i * X j) := by
  rw [X, X, monomial_mul, C_mul_monomial, mul_one, mul_one]

/-- **Tasaki Problem 7.2.3.b, eq. (S.77), p. 508** (printed upper product index `L` corrected to
`L − 1`).  The Weyl image of any open-chain ground form factors as a **boundary quadratic** —
a linear combination of the four products `X_{(1,a)} X_{(L,b)}`, involving only the two end sites —
times the product of the `L − 1` open bond factors.

Proof: each open bond factor divides `weylMap Ψ` (the U3b bridge), distinct open bonds are
relatively prime, so the whole product divides (`prod_dvd_of_pairwise_isRelPrime`); the per-site
weighted cofactor lemma then confines the cofactor's support to the four boundary multidegrees.

Unlike the ring statement `weylMap_ground_form_eq_const_smul_prod` there is **no** `Ψ ≠ 0`
hypothesis: the four coefficients may all vanish, and the cofactor lemma needs the bond product,
not the cofactor, to be nonzero. -/
theorem weylMap_openGroundForm_eq_boundary_smul_prod {m : ℕ}
    (Ψ : (Fin (m + 2) → Fin 3) → ℂ)
    (hΨ : ∀ x ∈ openBonds (m + 2), IsVBSGroundForm (m + 2) x Ψ) :
    ∃ c : Fin 2 × Fin 2 → ℂ,
      weylMap Ψ
        = (∑ ab : Fin 2 × Fin 2,
            C (c ab) * (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2)))
            * ∏ x ∈ openBonds (m + 2), fBond x := by
  classical
  obtain ⟨r, hr⟩ : (∏ x ∈ openBonds (m + 2), fBond x) ∣ weylMap Ψ :=
    prod_dvd_of_pairwise_isRelPrime (openBonds (m + 2)) fBond (weylMap Ψ)
      (fun x hx => fBond_dvd_weylMap_of_isVBSGroundForm x (by omega) Ψ (hΨ x hx))
      (fun x hx y hy hxy => fBond_isRelPrime_openBonds (by omega)
        (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) hxy)
  have hsupp : r.support ⊆ Finset.image (boundaryDeg m) Finset.univ := by
    intro d hd
    obtain ⟨p, hp⟩ := cofactor_support_shape Ψ hr hd
    obtain ⟨ab, hab⟩ := exists_boundary_shape p hp.1 hp.2
    exact Finset.mem_image.mpr ⟨ab, Finset.mem_univ ab, hab.symm⟩
  refine ⟨fun ab => coeff (boundaryDeg m ab) r, ?_⟩
  have hexp : r = ∑ ab : Fin 2 × Fin 2,
      C (coeff (boundaryDeg m ab) r)
        * (X ((0 : Fin (m + 2)), ab.1) * X (Fin.last (m + 1), ab.2)) := by
    calc r = ∑ d ∈ r.support, monomial d (coeff d r) := as_sum r
      _ = ∑ d ∈ Finset.image (boundaryDeg m) Finset.univ, monomial d (coeff d r) := by
          refine Finset.sum_subset hsupp fun d _ hd => ?_
          rw [notMem_support_iff.mp hd, monomial_zero]
      _ = ∑ ab : Fin 2 × Fin 2, monomial (boundaryDeg m ab) (coeff (boundaryDeg m ab) r) :=
          Finset.sum_image fun _ _ _ _ h => boundaryDeg_injective h
      _ = _ := Finset.sum_congr rfl fun ab _ => monomial_pair_eq _ _ _
  rw [hr, mul_comm (∏ x ∈ openBonds (m + 2), fBond x) r]
  exact congrArg (fun p => p * ∏ x ∈ openBonds (m + 2), fBond x) hexp

end LatticeSystem.Quantum.AKLTUniqueness
