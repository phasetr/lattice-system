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

on `MvPolynomial (Fin 2 × Fin 2) ℂ`.  This file is the polynomial-algebra engine that identifies the
kernel of a composite of such steps with the multiples of a power of the bond factor `f₂`, with no
spectral theory and no harmonic (Clebsch–Gordan) decomposition:

* every step subtracts an explicitly `f₂`-divisible term, so a composite of the steps
  `A_{c_1}, …, A_{c_r}` is `(∏ c_i) · p` modulo `f₂`; a vanishing composite with `∏ c_i ≠ 0`
  therefore forces `f₂ ∣ p` (`bondFactor_dvd_of_casimirDescentFold_eq_zero`);
* dividing by `f₂` shifts the scalar of a step by the bidegree (`casimirDescentStep_bondFactor_mul`,
  the level shift carried by `bondOmega_bond_mul_of_isWeightedHomogeneous`), and the Casimir-penalty
  family `c_j = m(m+1) − j(j+1)` is *invariant* under that shift
  (`(m+1)(m+2) − j(j+1) − (2m+2) = m(m+1) − j(j+1)`);
* the family truncated at its own level ends in the scalar `m(m+1) − m(m+1) = 0`, which under
  `List.foldr` is the innermost factor, so the whole level is pushed into `f₂ · (level m−1)`; the
  level shift then reproduces the level-`(m−1)` family, and the induction stops at bidegree `(0,0)`,
  where a polynomial is constant and `Ω` annihilates it.  This is the **annihilating polynomial**
  `casimirDescentFold_self_eq_zero`, the Weyl transport of `∏_{J=0}^{m}(Ĉ − J(J+1)) = 0`.

Combining the three gives the headline `casimirDescentFold_eq_zero_iff_bondFactor_pow_dvd`: a
polynomial of bidegree `(2S, 2S)` is annihilated by the `(S+1)`-fold descent of level `2S` **iff**
it is divisible by `f₂^S` (the scalar family `casimirPenaltyScalars (2S) S` carries one step per
`j = 0, …, S`, hence `S+1` steps).  Its consumer is the local kernel statement of the general-`S`
open chain (`LatticeSystem.Quantum.localCasimirPenalty_mulVec_eq_zero_iff_f2_pow_dvd`), where the
descent starts at the Weyl bidegree `(2S, 2S)` of a two-site state and stops on arrival at level
`S`, the first level at which the scalar family acquires a zero factor (at `j = S` it is
`S(S+1) − S(S+1) = 0`); `S+1` is the last level at which the family is still nonvanishing.

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

/-- **The bottom level carries no variables.**  A polynomial of bidegree `(0, 0)` has every Weyl
exponent zero, hence is a constant and is killed by the second-order derivation `Ω`.  This is the
base case of the annihilating-polynomial induction: it is what stops the descent at bidegree
`(0, 0)`, where there is no lower level for `Ω` to land in. -/
private theorem bondOmega_eq_zero_of_isWeightedHomogeneous_zero
    {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 0 + Finsupp.single 1 0)) :
    bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) p = 0 := by
  obtain ⟨a, rfl⟩ : ∃ a : ℂ, p = C a := by
    refine ⟨coeff 0 p, ?_⟩
    ext d
    rw [coeff_C]
    rcases eq_or_ne (0 : (Fin 2 × Fin 2) →₀ ℕ) d with rfl | hd
    · rw [if_pos rfl]
    · rw [if_neg hd]
      by_contra hcoeff
      have hw := hp hcoeff
      have hsite : ∀ y : Fin 2, d (y, 0) + d (y, 1) = 0 := fun y => by
        have h1 : (Finsupp.weight (siteWeight (L := 2)) d) y
            = (Finsupp.single (0 : Fin 2) 0 + Finsupp.single 1 0 : Fin 2 →₀ ℕ) y :=
          congrArg (fun t : Fin 2 →₀ ℕ => t y) hw
        rw [weight_siteWeight_apply] at h1
        rw [h1]
        simp
      refine hd (Finsupp.ext fun e => ?_).symm
      obtain ⟨y, i⟩ := e
      have hy := hsite y
      rcases (by decide : ∀ b : Fin 2, b = 0 ∨ b = 1) i with rfl | rfl <;>
        · simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
  simp [bondOmega_apply]

/-- **The descent step preserves the bidegree.**  `Ω` lowers the bidegree `(m, m)` to `(m−1, m−1)`
and multiplication by `f₂` raises it back, so `A_c` acts within the bidegree-`(m, m)` part.  At the
bottom level `m = 0` the statement still holds, for the degenerate reason that `Ω` annihilates a
bidegree-`(0, 0)` polynomial altogether. -/
theorem casimirDescentStep_isWeightedHomogeneous {m : ℕ} (c : ℂ)
    {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    (casimirDescentStep c p).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m) := by
  have hmul : (f2 * bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
      p).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m) := by
    cases m with
    | zero =>
      rw [bondOmega_eq_zero_of_isWeightedHomogeneous_zero hp, mul_zero]
      exact isWeightedHomogeneous_zero ℂ _ _
    | succ m =>
      have hdeg := single_succ_bidegree m
      have hOm : (bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) p).IsWeightedHomogeneous
          (siteWeight (L := 2)) (Finsupp.single 0 m + Finsupp.single 1 m) := by
        letI := siteDegreeAddCancelCommMonoid
        exact bondOmega_isWeightedHomogeneous (w := siteWeight (L := 2))
          (a := ((0 : Fin 2), (0 : Fin 2))) (b := (1, 1)) (c := (0, 1)) (d := (1, 0)) hdeg hdeg hp
      have hdeg' : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
          + (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m)
          = Finsupp.single (0 : Fin 2) (m + 1) + Finsupp.single 1 (m + 1) := by
        rw [← hdeg]; abel
      have hmul := f2_isWeightedHomogeneous.mul hOm
      rwa [hdeg'] at hmul
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
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    (List.foldr casimirDescentStep q cs).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m) := by
  induction cs with
  | nil => exact hq
  | cons c cs ih => exact casimirDescentStep_isWeightedHomogeneous c ih

/-- **The level shift, folded over a whole scalar list.**  Shifting every scalar of a descent fold
by `2m + 2` is the same as splitting off one bond factor from an argument of bidegree `(m, m)`.  No
lower bound on `m` is needed: the intermediate folds stay in bidegree `(m, m)`, and at `m = 0` the
bond derivation annihilates them outright. -/
theorem casimirDescentFold_bondFactor_mul {m : ℕ} (cs : List ℂ)
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    List.foldr casimirDescentStep (f2 * q) (cs.map (· + (2 * m + 2 : ℕ)))
      = f2 * List.foldr casimirDescentStep q cs := by
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

/-- **The top level ends in a zero scalar.**  The Casimir-penalty family of level `m + 1` truncated
at `j = m + 1` is the family truncated at `j = m` followed by the single scalar
`(m+1)(m+2) − (m+1)(m+2) = 0`.  Under `List.foldr` that trailing zero is the *innermost* factor of
the ordered product, and it is what starts the descent. -/
private theorem casimirPenaltyScalars_self_succ (m : ℕ) :
    casimirPenaltyScalars (m + 1) (m + 1) = casimirPenaltyScalars (m + 1) m ++ [(0 : ℂ)] := by
  rw [casimirPenaltyScalars, casimirPenaltyScalars, List.ofFn_succ', List.concat_eq_append]
  congr 1
  all_goals simp

/-- **The Casimir polynomial of a layer annihilates that layer.**  For every `p` homogeneous of
bidegree `(m, m)` the fold of the descent steps with the level-`m` Casimir-penalty scalars
`m(m+1) − j(j+1)`, `j = 0, …, m`, vanishes — the Weyl transport of Tasaki's
`∏_{J=0}^{m}(Ĉ − J(J+1)) = 0` on a two-site layer (§7.3.1, eqs. (7.3.1)–(7.3.3), pp. 208–209), with
no side hypothesis whatsoever.

Induction on `m`.  The innermost factor is the one at `j = m`, whose scalar is `0`, so
`A_0(p) = f₂ · (−Ω p)` already lands in the image of multiplication by the bond factor; the
remaining `m` factors are the level-`m` family shifted by `2m + 2` (`casimirPenaltyScalars_succ`),
so the level shift `casimirDescentFold_bondFactor_mul` converts them verbatim into the level-`(m−1)`
family acting on `−Ω p`, which has bidegree `(m−1, m−1)`.  At the bottom, `Ω` annihilates a
bidegree-`(0, 0)` polynomial. -/
theorem casimirDescentFold_self_eq_zero {m : ℕ} {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    List.foldr casimirDescentStep p (casimirPenaltyScalars m m) = 0 := by
  induction m generalizing p with
  | zero =>
    have hlist : casimirPenaltyScalars 0 0 = [(0 : ℂ)] := by
      simp [casimirPenaltyScalars, List.ofFn_succ]
    rw [hlist, List.foldr_cons, List.foldr_nil, casimirDescentStep,
      bondOmega_eq_zero_of_isWeightedHomogeneous_zero hp, mul_zero, zero_smul, sub_zero]
  | succ m ih =>
    have hdeg := single_succ_bidegree m
    have hOm : (-(bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0)
        p)).IsWeightedHomogeneous (siteWeight (L := 2))
        (Finsupp.single 0 m + Finsupp.single 1 m) := by
      letI := siteDegreeAddCancelCommMonoid
      exact (weightedHomogeneousSubmodule ℂ _ _).neg_mem
        (bondOmega_isWeightedHomogeneous (w := siteWeight (L := 2))
          (a := ((0 : Fin 2), (0 : Fin 2))) (b := (1, 1)) (c := (0, 1)) (d := (1, 0))
          hdeg hdeg hp)
    have hstep : casimirDescentStep 0 p
        = f2 * -(bondOmega ((0 : Fin 2), (0 : Fin 2)) (1, 1) (0, 1) (1, 0) p) := by
      rw [casimirDescentStep, zero_smul, zero_sub, mul_neg]
    rw [casimirPenaltyScalars_self_succ, casimirPenaltyScalars_succ, List.foldr_append,
      List.foldr_cons, List.foldr_nil, hstep, casimirDescentFold_bondFactor_mul _ hOm, ih hOm,
      mul_zero]

/-- **The level shift, iterated `k` times.**  Splitting `k` bond factors off the argument of a
descent fold lowers the level of the scalar family by `k`: for `q` of bidegree `(m, m)` and any
truncation index `S`,

  `fold_{m+k,S}(f₂^k · q) = f₂^k · fold_{m,S}(q)`.

Induction on `k`, one application of `casimirDescentFold_bondFactor_mul` per step; the intermediate
arguments `f₂^j · q` never need a cofactor lemma, being manifestly homogeneous. -/
theorem casimirDescentFold_bondFactor_pow_mul {m : ℕ} (k S : ℕ)
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hq : q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m)) :
    List.foldr casimirDescentStep ((f2 : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ k * q)
        (casimirPenaltyScalars (m + k) S)
      = f2 ^ k * List.foldr casimirDescentStep q (casimirPenaltyScalars m S) := by
  induction k generalizing m q with
  | zero => simp
  | succ k ih =>
    have hdeg : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
        + (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m)
        = Finsupp.single (0 : Fin 2) (m + 1) + Finsupp.single 1 (m + 1) := by
      rw [← single_succ_bidegree m]; abel
    have hfq : (f2 * q).IsWeightedHomogeneous (siteWeight (L := 2))
        (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1)) := by
      have hmul := f2_isWeightedHomogeneous.mul hq
      rwa [hdeg] at hmul
    have hsplit : (f2 : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ (k + 1) * q = f2 ^ k * (f2 * q) := by
      ring
    have hlvl : m + (k + 1) = m + 1 + k := by omega
    rw [hsplit, hlvl, ih (m := m + 1) (q := f2 * q) hfq, casimirPenaltyScalars_succ,
      casimirDescentFold_bondFactor_mul _ hq, ← mul_assoc, ← pow_succ]

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

/-- **Dividing off one bond factor lowers the bidegree by one.**  The cofactor of `f₂` in a
bidegree-`(m+1, m+1)` polynomial has bidegree `(m, m)`, by the cofactor lemma
`isWeightedHomogeneous_cofactor_weight` and left cancellation in the per-site degree monoid. -/
private theorem isWeightedHomogeneous_of_bondFactor_mul {m : ℕ}
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (h : ((f2 : MvPolynomial (Fin 2 × Fin 2) ℂ) * q).IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (m + 1) + Finsupp.single 1 (m + 1))) :
    q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m) := by
  intro d hd
  have hcof := isWeightedHomogeneous_cofactor_weight f2_isWeightedHomogeneous f2_ne_zero h
    (mem_support_iff.mpr hd)
  have hcancel : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
      + (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 m)
      = (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
        + Finsupp.weight (siteWeight (L := 2)) d := by
    rw [hcof, ← single_succ_bidegree m]
    abel
  exact (add_left_cancel hcancel).symm

/-- **Dividing off `k` bond factors lowers the bidegree by `k`.**  Iterated
`isWeightedHomogeneous_of_bondFactor_mul`. -/
private theorem isWeightedHomogeneous_of_bondFactor_pow_mul {m k : ℕ}
    {q : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (h : ((f2 : MvPolynomial (Fin 2 × Fin 2) ℂ) ^ k * q).IsWeightedHomogeneous
      (siteWeight (L := 2)) (Finsupp.single 0 (m + k) + Finsupp.single 1 (m + k))) :
    q.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 m + Finsupp.single 1 m) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    refine ih (isWeightedHomogeneous_of_bondFactor_mul ?_)
    have hsplit : (f2 : MvPolynomial (Fin 2 × Fin 2) ℂ) * (f2 ^ k * q) = f2 ^ (k + 1) * q := by
      ring
    rw [hsplit]
    exact h

/-- **`k` levels of Casimir descent give `k` bond factors.**  A polynomial of bidegree
`(S+k, S+k)` annihilated by the fold of the Casimir-penalty steps of level `S+k` is divisible by
`f₂^k`.

Induction on `k`: at level `S+k+1 > S` the scalar product is nonzero
(`casimirPenaltyScalars_prod_ne_zero`), so one bond factor splits off; the cofactor has bidegree
`(S+k, S+k)` (`isWeightedHomogeneous_of_bondFactor_mul`), and the shifted fold
(`casimirPenaltyScalars_succ`, `casimirDescentFold_bondFactor_mul`) annihilates it after cancelling
the bond factor. -/
theorem bondFactor_pow_dvd_of_casimirDescentFold (S k : ℕ)
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
        (Finsupp.single 0 (S + k) + Finsupp.single 1 (S + k)) :=
      isWeightedHomogeneous_of_bondFactor_mul hp
    have hfold : List.foldr casimirDescentStep q (casimirPenaltyScalars (S + k) S) = 0 := by
      rw [casimirPenaltyScalars_succ, casimirDescentFold_bondFactor_mul _ hq] at h
      exact (mul_eq_zero.mp h).resolve_left f2_ne_zero
    calc f2 ^ (k + 1) = f2 * f2 ^ k := by rw [pow_succ, mul_comm]
      _ ∣ f2 * q := mul_dvd_mul_left f2 (ih hq hfold)

/-- **Headline: the kernel of the level-`2S` Casimir-penalty descent is exactly the `f₂^S`
multiples.**  For `p` of bidegree `(2S, 2S)` the fold of the `S+1` descent steps of level `2S`
vanishes iff `f₂^S ∣ p`.

`→` is `bondFactor_pow_dvd_of_casimirDescentFold` at `k = S`.  `←` writes `p = f₂^S · r` with `r` of
bidegree `(S, S)` (`isWeightedHomogeneous_of_bondFactor_pow_mul`), pushes the `S` bond factors out
of the fold (`casimirDescentFold_bondFactor_pow_mul`) and lands on the level-`S` self fold, which is
zero by the annihilating polynomial `casimirDescentFold_self_eq_zero`.  No side hypothesis is
needed; `S = 0` is the trivial instance. -/
theorem casimirDescentFold_eq_zero_iff_bondFactor_pow_dvd (S : ℕ)
    {p : MvPolynomial (Fin 2 × Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 (S + S) + Finsupp.single 1 (S + S))) :
    List.foldr casimirDescentStep p (casimirPenaltyScalars (S + S) S) = 0 ↔ f2 ^ S ∣ p := by
  refine ⟨bondFactor_pow_dvd_of_casimirDescentFold S S hp, fun hdvd => ?_⟩
  obtain ⟨r, rfl⟩ := hdvd
  have hr : r.IsWeightedHomogeneous (siteWeight (L := 2))
      (Finsupp.single 0 S + Finsupp.single 1 S) :=
    isWeightedHomogeneous_of_bondFactor_pow_mul (m := S) (k := S) hp
  rw [casimirDescentFold_bondFactor_pow_mul S S hr, casimirDescentFold_self_eq_zero hr, mul_zero]

end LatticeSystem.Quantum
