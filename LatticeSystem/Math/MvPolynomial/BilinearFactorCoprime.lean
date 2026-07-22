/-
Bilinear bond factors of a multivariate polynomial ring: irreducibility, relative
primality, variable sets, and the degree-matching divisibility argument.

This file isolates the purely polynomial-algebraic core ("Stage C") of the uniqueness of the
AKLT ground state (Tasaki §7.1.3, Kennedy–Lieb–Tasaki [41]).  In the Schwinger-boson (Weyl)
representation each site `x` carries two variables `u_x, v_x`, and a nearest-neighbour bond
contributes the degree-`2` homogeneous *bilinear factor*

  `bondFactor a b c d = X a * X b - X c * X d`   (`= u_x v_{x+1} - v_x u_{x+1}`).

We prove, over any domain `ℂ` and any variable type `σ` (so the results apply verbatim to the
cyclic chain `Fin L × Fin 2`):

* `bondFactor_irreducible` / `bondFactor_prime` — a bilinear factor on four distinct variables is
  irreducible, hence prime (the ring is a UFD).  Reduces directly to
  `MvPolynomial.irreducible_mul_X_add`.
* `bondFactor_totalDegree` — its total degree is `2`.
* `vars_bondFactor` — its variable set is exactly `{a, b, c, d}` (used to separate distinct bonds).
* `bondFactor_isRelPrime` — two prime factors of equal total degree, one of which contains a
  variable the other omits, are relatively prime (Stage C step 2': distinct bonds are coprime).
* `eq_const_smul_of_dvd_of_totalDegree_eq` — a divisor of a nonzero polynomial with matching total
  degree divides it up to a constant (the degree count `deg (∏ bond) = deg Φ = 2L` forcing
  one-dimensionality, Tasaki eq (7.1.25)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.22)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10], UFD property [89].
-/
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Degrees

open MvPolynomial

namespace LatticeSystem.Math

variable {σ : Type*}

/-- The bilinear bond factor `X a * X b - X c * X d` (Weyl form `u_x v_{x+1} - v_x u_{x+1}`,
Tasaki eq. (7.1.24)). -/
noncomputable def bondFactor (a b c d : σ) : MvPolynomial σ ℂ :=
  X a * X b - X c * X d

/-- On four distinct variables the bond factor is irreducible (Tasaki §7.1.3, the polynomial
factors (7.1.24) are irreducible).  Reduces to `MvPolynomial.irreducible_mul_X_add` by viewing
`bondFactor a b c d = (X b) * X a + (-(X c * X d))`. -/
theorem bondFactor_irreducible {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Irreducible (bondFactor a b c d) := by
  classical
  have hkey : bondFactor a b c d = X b * X a + (-(X c * X d)) := by
    unfold bondFactor; ring
  rw [hkey]
  apply irreducible_mul_X_add (X b) (-(X c * X d)) a
  · exact X_ne_zero b
  · simp only [vars_X, Finset.mem_singleton]
    exact hab
  · rw [vars_neg]
    intro ha
    have : a ∈ vars (X c) ∪ vars (X d) := vars_mul _ _ ha
    simp only [vars_X, Finset.mem_union, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hac h
    · exact had h
  · apply IsRelPrime.neg_right
    rw [(X_prime).irreducible.isRelPrime_iff_not_dvd, X_dvd_mul_iff, not_or]
    refine ⟨?_, ?_⟩
    · rw [X_dvd_X]; exact hbc
    · rw [X_dvd_X]; exact hbd

/-- On four distinct variables the bond factor is prime (`MvPolynomial σ ℂ` is a UFD, so
irreducible ⟹ prime). -/
theorem bondFactor_prime {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Prime (bondFactor a b c d) :=
  (bondFactor_irreducible hab hac had hbc hbd).prime

/-- The bond factor is homogeneous of total degree `2` (each bond contributes degree `2`,
so a chain of `L` bonds has total degree `2L`; Tasaki eq. (7.1.25)). -/
theorem bondFactor_totalDegree {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    (bondFactor a b c d).totalDegree = 2 := by
  classical
  set m1 : σ →₀ ℕ := Finsupp.single a 1 + Finsupp.single b 1 with hm1def
  set m2 : σ →₀ ℕ := Finsupp.single c 1 + Finsupp.single d 1 with hm2def
  have hXab : (X a * X b : MvPolynomial σ ℂ) = monomial m1 1 := by
    rw [hm1def]; simp only [MvPolynomial.X]; rw [monomial_mul, mul_one]
  have hXcd : (X c * X d : MvPolynomial σ ℂ) = monomial m2 1 := by
    rw [hm2def]; simp only [MvPolynomial.X]; rw [monomial_mul, mul_one]
  have hbond : bondFactor a b c d = monomial m1 1 - monomial m2 1 := by
    unfold bondFactor; rw [hXab, hXcd]
  have hne : m1 ≠ m2 := by
    intro h
    have h1 : m1 a = 1 := by simp [hm1def, Finsupp.add_apply, Ne.symm hab]
    have h2 : m2 a = 0 := by simp [hm2def, Finsupp.add_apply, Ne.symm hac, Ne.symm had]
    rw [h] at h1; omega
  have hm1sum : m1.sum (fun _ e => e) = 2 := by
    rw [hm1def, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  have hm2sum : m2.sum (fun _ e => e) = 2 := by
    rw [hm2def, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  refine le_antisymm ?_ ?_
  · rw [hbond]
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_monomial _ (one_ne_zero (α := ℂ)),
      totalDegree_monomial _ (one_ne_zero (α := ℂ)), hm1sum, hm2sum]
    simp
  · have hsupp : m1 ∈ (bondFactor a b c d).support := by
      rw [mem_support_iff, hbond, coeff_sub, coeff_monomial, coeff_monomial,
        if_pos rfl, if_neg (Ne.symm hne)]
      norm_num
    calc (2 : ℕ) = m1.sum (fun _ e => e) := hm1sum.symm
      _ ≤ _ := le_totalDegree hsupp

/-- The variable set of a bond factor on four distinct variables is exactly `{a, b, c, d}`.
Distinct cyclic bonds thus have different variable sets, which yields their relative primality
(Stage C step 2'). -/
theorem vars_bondFactor [DecidableEq σ] {a b c d : σ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (bondFactor a b c d).vars = {a, b, c, d} := by
  set m1 : σ →₀ ℕ := Finsupp.single a 1 + Finsupp.single b 1 with hm1def
  set m2 : σ →₀ ℕ := Finsupp.single c 1 + Finsupp.single d 1 with hm2def
  have hbond : bondFactor a b c d = monomial m1 1 - monomial m2 1 := by
    have hXab : (X a * X b : MvPolynomial σ ℂ) = monomial m1 1 := by
      rw [hm1def]; simp only [MvPolynomial.X]; rw [monomial_mul, mul_one]
    have hXcd : (X c * X d : MvPolynomial σ ℂ) = monomial m2 1 := by
      rw [hm2def]; simp only [MvPolynomial.X]; rw [monomial_mul, mul_one]
    unfold bondFactor; rw [hXab, hXcd]
  have hm1a : m1 a = 1 := by simp [hm1def, Finsupp.add_apply, Ne.symm hab]
  have hm2a : m2 a = 0 := by simp [hm2def, Finsupp.add_apply, Ne.symm hac, Ne.symm had]
  have hne : m1 ≠ m2 := by
    intro h
    have : (1 : ℕ) = 0 := by rw [← hm1a, h, hm2a]
    exact one_ne_zero this
  -- Coefficients of the two monomials are `1` and `-1`, so both lie in the support.
  have hm1supp : m1 ∈ (bondFactor a b c d).support := by
    rw [mem_support_iff, hbond, coeff_sub, coeff_monomial, coeff_monomial,
      if_pos rfl, if_neg (Ne.symm hne)]
    norm_num
  have hm2supp : m2 ∈ (bondFactor a b c d).support := by
    rw [mem_support_iff, hbond, coeff_sub, coeff_monomial, coeff_monomial,
      if_neg hne, if_pos rfl]
    norm_num
  -- Variable memberships in the two monomial supports.
  have ha_m1 : a ∈ m1.support :=
    Finsupp.mem_support_iff.mpr (by rw [hm1a]; exact one_ne_zero)
  have hb_m1 : b ∈ m1.support := by
    have : m1 b = 1 := by simp [hm1def, Finsupp.add_apply, hab]
    exact Finsupp.mem_support_iff.mpr (by rw [this]; exact one_ne_zero)
  have hc_m2 : c ∈ m2.support := by
    have : m2 c = 1 := by simp [hm2def, Finsupp.add_apply, Ne.symm hcd]
    exact Finsupp.mem_support_iff.mpr (by rw [this]; exact one_ne_zero)
  have hd_m2 : d ∈ m2.support := by
    have : m2 d = 1 := by simp [hm2def, Finsupp.add_apply, hcd]
    exact Finsupp.mem_support_iff.mpr (by rw [this]; exact one_ne_zero)
  have hin : ∀ {m : σ →₀ ℕ} {i : σ}, m ∈ (bondFactor a b c d).support →
      i ∈ m.support → i ∈ (bondFactor a b c d).vars :=
    fun hm hi => (mem_vars _).mpr ⟨_, hm, hi⟩
  refine Finset.Subset.antisymm ?_ ?_
  · -- `vars ⊆ {a, b, c, d}` from `vars_sub_subset`, `vars_mul`, `vars_X`.
    unfold bondFactor
    refine Finset.Subset.trans (vars_sub_subset (X a * X b)) (Finset.union_subset ?_ ?_)
    · refine Finset.Subset.trans (vars_mul _ _) ?_
      rw [vars_X, vars_X]
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · refine Finset.Subset.trans (vars_mul _ _) ?_
      rw [vars_X, vars_X]
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hin hm1supp ha_m1
    · exact hin hm1supp hb_m1
    · exact hin hm2supp hc_m2
    · exact hin hm2supp hd_m2

/-- Degree count (Tasaki eq. (7.1.25)): if `P ∣ Φ` with `Φ ≠ 0` and both have the same total
degree, then the quotient is a constant, so `Φ = C c * P`.  Applied with `P = ∏ bondFactor`
(total degree `2L`) and `Φ` the Weyl image of a ground form (total degree `2L`), this forces the
common-kernel space to be one-dimensional. -/
theorem eq_const_smul_of_dvd_of_totalDegree_eq
    {P Φ : MvPolynomial σ ℂ} (hdvd : P ∣ Φ) (hΦ0 : Φ ≠ 0)
    (hdeg : Φ.totalDegree = P.totalDegree) :
    ∃ c : ℂ, Φ = MvPolynomial.C c * P := by
  obtain ⟨q, rfl⟩ := hdvd
  have hP0 : P ≠ 0 := by rintro rfl; simp at hΦ0
  have hq0 : q ≠ 0 := by rintro rfl; simp at hΦ0
  rw [totalDegree_mul_of_isDomain hP0 hq0] at hdeg
  have hqdeg : q.totalDegree = 0 := by omega
  have hc : q = MvPolynomial.C (q.coeff 0) := (totalDegree_eq_zero_iff_eq_C (p := q)).mp hqdeg
  exact ⟨q.coeff 0, by rw [← hc]; exact mul_comm P q⟩

/-- Stage C step 2' (distinct bonds are coprime): two prime factors `p, q` of equal total degree,
where some variable occurs in `p` but not in `q`, are relatively prime.  If `p ∣ q` then, matching
total degrees, `q = C c * p` (`c ≠ 0`), whence `p` and `q` share the same variable set,
contradicting the witness `e`. -/
theorem bondFactor_isRelPrime {p q : MvPolynomial σ ℂ}
    (hp : Prime p) (hq0 : q ≠ 0) (hdeg : p.totalDegree = q.totalDegree)
    {e : σ} (hep : e ∈ p.vars) (heq : e ∉ q.vars) :
    IsRelPrime p q := by
  refine hp.irreducible.isRelPrime_iff_not_dvd.mpr ?_
  intro hdvd
  obtain ⟨c, hc⟩ := eq_const_smul_of_dvd_of_totalDegree_eq hdvd hq0 hdeg.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hc
    exact hq0 hc
  rw [hc, vars_C_mul c hc0] at heq
  exact heq hep

end LatticeSystem.Math
