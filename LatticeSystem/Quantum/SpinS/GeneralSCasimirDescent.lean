import LatticeSystem.Quantum.SpinS.AKLTUniqueness.LocalBondDivisibility
import LatticeSystem.Math.MvPolynomial.BondFactorDerivation
import LatticeSystem.Math.MvPolynomial.WeightedHomogeneousLayer
import LatticeSystem.Math.MvPolynomial.BilinearFactorCoprime

/-!
# Casimir descent on the two-site Weyl polynomials

Under the Weyl (Schwinger-boson) map the two-site Casimir `Ĉ` acts as `N(N+1) − f₂ Ω`
(`LatticeSystem.Quantum.weylMap_mulVec_bondCasimirS`), so each factor `Ĉ − j(j+1)` of the
general-`S` AKLT bond term transports to the **descent step**

  `A_c(p) = c · p − f₂ · Ω p`,  `c = N(N+1) − j(j+1)`,

on `MvPolynomial (Fin 2 × Fin 2) ℂ`.  This file is the polynomial-algebra engine that turns a
vanishing composite of such steps into divisibility by a power of the bond factor `f₂`, with no
spectral theory and no harmonic (Clebsch–Gordan) decomposition:

* every step subtracts an explicitly `f₂`-divisible term, so a composite of the steps
  `A_{c_1}, …, A_{c_r}` is `(∏ c_i) · p` modulo `f₂`; a vanishing composite with `∏ c_i ≠ 0`
  therefore forces `f₂ ∣ p` (`bondFactor_dvd_of_casimirDescentFold_eq_zero`);
* dividing by `f₂` shifts the scalar of a step by the bidegree (`casimirDescentStep_bondFactor_mul`,
  the level shift carried by `bondOmega_bond_mul_of_isWeightedHomogeneous`), and the Casimir-penalty
  family `c_j = m(m+1) − j(j+1)` is *invariant* under that shift
  (`(m+1)(m+2) − j(j+1) − (2m+2) = m(m+1) − j(j+1)`).

Iterating the two gives the headline `bondFactor_pow_dvd_of_casimirDescentFold`: a polynomial of
bidegree `(S+k, S+k)` annihilated by the `S`-fold descent of level `S+k` is divisible by `f₂^k`.
Its consumer is the local kernel statement of the general-`S` open chain
(`LatticeSystem.Quantum.f2_pow_dvd_weylMap_of_localCasimirPenalty`), where the descent starts at the
Weyl bidegree `(2S, 2S)` of a two-site state and stops at level `S`, the last level at which the
scalar family is still nonvanishing.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.22)–(7.1.25); §7.3.1,
eqs. (7.3.1)–(7.3.3), pp. 208–209; polynomial representation due to Arovas–Auerbach–Haldane [10];
proof due to Kennedy–Lieb–Tasaki [41].
-/

open MvPolynomial

namespace LatticeSystem.Quantum

open LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness

/-- The **Casimir descent step** `A_c(p) = c · p − f₂ · Ω p` on the two-site Weyl polynomials, the
Weyl transport of a single Casimir factor `Ĉ − j(j+1)` at scalar `c = N(N+1) − j(j+1)`
(`weylMap_mulVec_bondCasimirS`). -/
noncomputable def casimirDescentStep (c : ℂ) (p : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    MvPolynomial (Fin 2 × Fin 2) ℂ :=
  c • p - f2 * bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) p

/-- The **Casimir-penalty scalars** at level `m`: the values `m(m+1) − j(j+1)`, `j = 0, …, S`, taken
by the Casimir factors of the general-`S` bond term `q_S(Ĉ) = ∏_{j=0}^{S}(Ĉ − j(j+1))` (Tasaki
eq. (7.3.3), p. 208) on a bond carrying total spin `m`. -/
noncomputable def casimirPenaltyScalars (m S : ℕ) : List ℂ :=
  List.ofFn fun j : Fin (S + 1) => (m : ℂ) * (m + 1) - ((j : ℕ) : ℂ) * (((j : ℕ) : ℂ) + 1)

/-- The bond factor `f₂` is `siteWeight`-homogeneous of bidegree `(1, 1)`: it is bilinear, one
variable from each of the two sites. -/
private theorem f2_isWeightedHomogeneous :
    (f2 : MvPolynomial (Fin 2 × Fin 2) ℂ).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  rw [f2]
  exact bondFactor_isWeightedHomogeneous _ _ _ _ _ rfl

/-- The bond factor `f₂` is nonzero (it is prime on its four distinct variables), which is what
makes it cancellable in the descent. -/
private theorem f2_ne_zero : (f2 : MvPolynomial (Fin 2 × Fin 2) ℂ) ≠ 0 := by
  rw [f2]
  exact (bondFactor_prime (by decide) (by decide) (by decide) (by decide) (by decide)).ne_zero

/-- Adding the bidegree `(1, 1)` of `f₂` to the bidegree `(m, m)` gives `(m+1, m+1)`: the
bookkeeping identity behind both the homogeneity of a descent step and the cofactor lemma. -/
private theorem single_succ_bidegree (m : ℕ) :
    (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m)
        + (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
      = Finsupp.single (0 : Fin 2) (m + 1) + Finsupp.single 1 (m + 1) := by
  simp only [Finsupp.single_add]
  abel

/-- The bundled cancellative structure on the per-site degree monoid `Fin 2 →₀ ℕ`.  Mathlib proves
`Finsupp.instIsCancelAdd` but has no bundled `AddCancelCommMonoid` instance for `ι →₀ ℕ`, while
`MvPolynomial.IsWeightedHomogeneous.pderiv` — hence `bondOmega_isWeightedHomogeneous` — demands the
bundled form.  It is introduced by `letI` at the single use site and never registered as an
instance, so every statement keeps elaborating with the canonical `AddCommMonoid` structure. -/
@[reducible] private noncomputable def siteDegreeAddCancelCommMonoid :
    AddCancelCommMonoid (Fin 2 →₀ ℕ) :=
  { (inferInstance : AddCommMonoid (Fin 2 →₀ ℕ)) with
    add_left_cancel := fun _ _ _ h => add_left_cancel h }

/-- **The descent step preserves the bidegree.**  `Ω` lowers the bidegree `(m+1, m+1)` to `(m, m)`
and multiplication by `f₂` raises it back, so `A_c` acts within the bidegree-`(m+1, m+1)` part.
The bottom level `m + 1 = 0` is excluded by the shape of the statement: at bidegree `(0,0)` there is
no lower level for `Ω` to land in. -/
theorem casimirDescentStep_isWeightedHomogeneous {m : ℕ} (c : ℂ)
    {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1))) :
    (casimirDescentStep c p).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1)) := by
  have hdeg := single_succ_bidegree m
  have hOm : (bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) p).IsWeightedHomogeneous
      (siteWeight (L := 2)) (Finsupp.single 0 m + Finsupp.single 1 m) := by
    letI := siteDegreeAddCancelCommMonoid
    exact bondOmega_isWeightedHomogeneous (w := siteWeight (L := 2))
      (a := ((0 : Fin 2), (0 : Fin 2))) (b := (1, 1)) (c := (0, 1)) (d := (1, 0)) hdeg hdeg hp
  have hmul := f2_isWeightedHomogeneous.mul hOm
  have hdeg' : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
      + (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m)
      = Finsupp.single (0 : Fin 2) (m + 1) + Finsupp.single 1 (m + 1) := by
    rw [← hdeg]; abel
  rw [hdeg'] at hmul
  exact (weightedHomogeneousSubmodule ℂ _ _).sub_mem (Submodule.smul_mem _ c hp) hmul

/-- **The level shift.**  Dividing by the bond factor lowers the scalar of a descent step by
`2m + 2`, the bidegree shift of `Ω (f₂ · q) = f₂ · Ω q + (D 0 + D 1 + 2) · q`
(`bondOmega_bond_mul_of_isWeightedHomogeneous`): on a `q` of bidegree `(m, m)`,

  `A_{c + (2m+2)}(f₂ · q) = f₂ · A_c(q)`.

This is the mechanism by which the Casimir eigenvalue changes when a singlet factor is split off
(Tasaki §7.1.3, eqs. (7.1.22)–(7.1.25), pp. 186–188). -/
theorem casimirDescentStep_bondFactor_mul {m : ℕ} (c : ℂ)
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    casimirDescentStep (c + (2 * m + 2 : ℕ)) (f2 * q) = f2 * casimirDescentStep c q := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hOm := bondOmega_bond_mul_of_isWeightedHomogeneous h01 hq
  have hD0 : (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m : Fin 2 →₀ ℕ) 0 = m := by simp
  have hD1 : (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m : Fin 2 →₀ ℕ) 1 = m := by simp
  rw [hD0, hD1] at hOm
  simp only [casimirDescentStep, f2]
  rw [hOm, mul_add, mul_smul_comm, mul_sub, mul_smul_comm, add_smul]
  push_cast
  module

/-- Homogeneity of a whole descent fold, the invariant that lets the level shift be iterated. -/
private theorem casimirDescentFold_isWeightedHomogeneous {m : ℕ} (cs : List ℂ)
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1))) :
    (List.foldr casimirDescentStep q cs).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1)) := by
  induction cs with
  | nil => exact hq
  | cons c cs ih => exact casimirDescentStep_isWeightedHomogeneous c ih

/-- **The level shift, folded over a whole scalar list.**  Shifting every scalar of a descent fold
by `2m + 2` is the same as splitting off one bond factor from the argument, provided the argument
has bidegree `(m, m)` with `m ≠ 0` (the intermediate folds must stay in a bidegree that `Ω` can
lower). -/
theorem casimirDescentFold_bondFactor_mul {m : ℕ} (hm : m ≠ 0) (cs : List ℂ)
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    List.foldr casimirDescentStep (f2 * q) (cs.map (· + (2 * m + 2 : ℕ)))
      = f2 * List.foldr casimirDescentStep q cs := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih,
      casimirDescentStep_bondFactor_mul c (casimirDescentFold_isWeightedHomogeneous cs hq)]

/-- **The descent is scalar multiplication modulo `f₂`.**  Every step subtracts an `f₂`-divisible
term, so a fold of steps with scalars `cs` acts as `(∏ cs) · p` plus a multiple of `f₂`, for every
`p` and with no grading hypothesis.  This is the engine of the divisibility argument. -/
private theorem casimirDescentFold_eq_prod_smul_add (cs : List ℂ)
    (p : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    ∃ w, List.foldr casimirDescentStep p cs = cs.prod • p + f2 * w := by
  induction cs with
  | nil => exact ⟨0, by simp⟩
  | cons c cs ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨c • w - bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
      (cs.prod • p + f2 * w), ?_⟩
    rw [List.foldr_cons, hw, casimirDescentStep, List.prod_cons, smul_add, smul_smul,
      ← mul_smul_comm, mul_sub]
    abel

/-- **Vanishing descent forces one bond factor.**  If a fold of descent steps whose scalars have
nonzero product annihilates `p`, then `f₂ ∣ p`: the fold equals `(∏ cs) · p` modulo `f₂`
(`casimirDescentFold_eq_prod_smul_add`), so `p` itself is `f₂` times a polynomial. -/
theorem bondFactor_dvd_of_casimirDescentFold_eq_zero {cs : List ℂ} (hcs : cs.prod ≠ 0)
    {p : MvPolynomial (Fin 2 × Fin 2) ℂ} (h : List.foldr casimirDescentStep p cs = 0) :
    f2 ∣ p := by
  obtain ⟨w, hw⟩ := casimirDescentFold_eq_prod_smul_add cs p
  rw [h] at hw
  have hp : cs.prod • p = -(f2 * w) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hw.symm
  refine ⟨-(cs.prod⁻¹ • w), ?_⟩
  calc p = cs.prod⁻¹ • cs.prod • p := (inv_smul_smul₀ hcs p).symm
    _ = cs.prod⁻¹ • -(f2 * w) := by rw [hp]
    _ = f2 * -(cs.prod⁻¹ • w) := by rw [smul_neg, ← mul_smul_comm, mul_neg]

/-- **The scalar family is invariant under the level shift.**  Raising the level by one shifts every
Casimir-penalty scalar by `2m + 2`, since `(m+1)(m+2) − j(j+1) = (m(m+1) − j(j+1)) + (2m+2)`. -/
private theorem casimirPenaltyScalars_succ (m S : ℕ) :
    casimirPenaltyScalars (m + 1) S
      = (casimirPenaltyScalars m S).map (· + ((2 * m + 2 : ℕ) : ℂ)) := by
  rw [casimirPenaltyScalars, casimirPenaltyScalars, List.map_ofFn]
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **The scalar family is nonvanishing below the top level.**  For `S < m` every Casimir-penalty
scalar `m(m+1) − j(j+1)`, `j ≤ S`, is nonzero, since `j ≤ S < m` gives `j(j+1) < m(m+1)`.  At
`m = S` the factor with `j = S` vanishes, which is exactly where the descent must stop. -/
theorem casimirPenaltyScalars_prod_ne_zero {m S : ℕ} (h : S < m) :
    (casimirPenaltyScalars m S).prod ≠ 0 := by
  rw [casimirPenaltyScalars, List.prod_ofFn]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_
  have hj : (j : ℕ) < m := lt_of_le_of_lt (Nat.lt_succ_iff.mp j.isLt) h
  have hnat : (j : ℕ) * ((j : ℕ) + 1) < m * (m + 1) := by nlinarith
  exact_mod_cast hnat.ne'

/-- **Headline: `k` levels of Casimir descent give `k` bond factors.**  A polynomial of bidegree
`(S+k, S+k)` annihilated by the fold of the Casimir-penalty steps of level `S+k` is divisible by
`f₂^k`.

Induction on `k`: at level `S+k+1 > S` the scalar product is nonzero
(`casimirPenaltyScalars_prod_ne_zero`), so one bond factor splits off; the cofactor has bidegree
`(S+k, S+k)`, and the shifted fold (`casimirPenaltyScalars_succ`,
`casimirDescentFold_bondFactor_mul`) annihilates it after cancelling the bond factor.  The
hypothesis `S ≠ 0` keeps every intermediate level nonzero, as required by the level shift. -/
theorem bondFactor_pow_dvd_of_casimirDescentFold {S : ℕ} (hS : S ≠ 0) (k : ℕ)
    {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (S + k) + Finsupp.single 1 (S + k)))
    (h : List.foldr casimirDescentStep p (casimirPenaltyScalars (S + k) S) = 0) :
    f2 ^ k ∣ p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    have hk : S + (k + 1) = S + k + 1 := by omega
    rw [hk] at hp h
    obtain ⟨q, rfl⟩ := bondFactor_dvd_of_casimirDescentFold_eq_zero
      (casimirPenaltyScalars_prod_ne_zero (by omega : S < S + k + 1)) h
    have hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
        (Finsupp.single 0 (S + k) + Finsupp.single 1 (S + k)) := by
      intro d hd
      have hcof := isWeightedHomogeneous_cofactor_weight f2_isWeightedHomogeneous f2_ne_zero hp
        (mem_support_iff.mpr hd)
      have hcancel : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
          + (Finsupp.single (0 : Fin 2) (S + k) + Finsupp.single 1 (S + k))
          = (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
            + Finsupp.weight (siteWeight (L := 2)) d := by
        rw [hcof, ← single_succ_bidegree (S + k)]
        abel
      exact (add_left_cancel hcancel).symm
    have hfold : List.foldr casimirDescentStep q (casimirPenaltyScalars (S + k) S) = 0 := by
      rw [casimirPenaltyScalars_succ,
        casimirDescentFold_bondFactor_mul (by omega : S + k ≠ 0) _ hq] at h
      exact (mul_eq_zero.mp h).resolve_left f2_ne_zero
    calc f2 ^ (k + 1) = f2 * f2 ^ k := by rw [pow_succ, mul_comm]
      _ ∣ f2 * q := mul_dvd_mul_left f2 (ih hq hfold)

end LatticeSystem.Quantum
