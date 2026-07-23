/-
# Tasaki §7.1.3 (AKLT uniqueness), stage C4: the product of all bond factors divides the Weyl image

Building on the per-bond divisibility bridge `U3b`
(`fBond_dvd_weylMap_of_isVBSGroundForm`), this file assembles the *global* divisibility and
degree-count that force one-dimensionality of the common kernel `K_L` (Tasaki eq. (7.1.25)).

The mathematical content:

* **Cyclic combinatorics** (`exists_bond_var_witness`): on a ring of length `L ≥ 3`, two distinct
  sites `x ≠ y` have `{x, ringSucc x} ≠ {y, ringSucc y}`; concretely there is a site
  `s ∈ {x, ringSucc x}` off `{y, ringSucc y}`.  The obstruction `L ≤ 2` is detected by the
  double-shift lemma `ringSucc_ringSucc_ne` (`ringSucc (ringSucc y) ≠ y` for `L ≥ 3`).
* **Bond-factor invariants** (`fBond_prime`, `fBond_totalDegree`, `fBond_vars`): each global bond
  factor `f_x` is prime, has total degree `2`, and has variable set `{x, ringSucc x} × Fin 2`.
* **Pairwise coprimality** (`fBond_isRelPrime`): distinct bonds give relatively prime factors, using
  the witness variable `(s, 0)` present in `f_x.vars` but absent from `f_y.vars`.
* **Product divisibility and one-dimensionality** (`prod_fBond_dvd_weylMap`,
  `weylMap_ground_form_eq_const_smul_prod`): a common ground form `Ψ` (in every bond kernel) has
  `∏_x f_x ∣ weylMap Ψ`; matching total degrees `2L = 2L` then force
  `weylMap Ψ = C c · ∏_x f_x`, Tasaki eq. (7.1.25).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, 2020),
§7.1.3 "The Uniqueness of the Ground State", pp. 186–188, eqs. (7.1.24)–(7.1.25); polynomial
representation due to Arovas–Auerbach–Haldane [10]; proof due to Kennedy–Lieb–Tasaki [41].
-/
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.BondDivisibilityBridge
import LatticeSystem.Math.MvPolynomial.PairwiseCoprimeProd

open MvPolynomial

namespace LatticeSystem.Quantum.AKLTUniqueness

open LatticeSystem.Quantum LatticeSystem.Math

variable {L : ℕ}

/-! ### Cyclic combinatorics: distinct bonds occupy distinct site pairs -/

/-- On a ring of length `L ≥ 3` the double cyclic successor never returns to the start:
`ringSucc (ringSucc y) ≠ y`.  A return would mean the shift-by-two is the identity, i.e. `L ∣ 2`,
which fails for `L ≥ 3`.  This is the arithmetic obstruction that separates distinct cyclic bonds
(the coprimality of `f_x` and `f_y` breaks exactly at `L = 2`). -/
theorem ringSucc_ringSucc_ne (hL : 3 ≤ L) (y : Fin L) : ringSucc (ringSucc y) ≠ y := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ringSucc, Fin.val_mk] at hv
  have hy : y.val < L := y.isLt
  rcases lt_or_ge (y.val + 1) L with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    rcases lt_or_ge (y.val + 1 + 1) L with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have he : y.val + 1 + 1 = L := by omega
      rw [he, Nat.mod_self] at hv; omega
  · have he : y.val + 1 = L := by omega
    rw [he, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < L)] at hv
    omega

/-- **Cyclic bond-separation witness.**  For `L ≥ 3` and distinct sites `x ≠ y`, there is a site
`s ∈ {x, ringSucc x}` lying off the other bond, `s ≠ y` and `s ≠ ringSucc y`.  Hence the variable
`(s, 0)` occurs in `f_x` but not in `f_y`, which drives their relative primality. -/
theorem exists_bond_var_witness (hL : 3 ≤ L) {x y : Fin L} (hxy : x ≠ y) :
    ∃ s : Fin L, (s = x ∨ s = ringSucc x) ∧ s ≠ y ∧ s ≠ ringSucc y := by
  by_cases hx : x = y ∨ x = ringSucc y
  · have hxr : x = ringSucc y := hx.resolve_left hxy
    refine ⟨ringSucc x, Or.inr rfl, ?_, ?_⟩
    · intro h
      exact ringSucc_ringSucc_ne hL y ((congrArg ringSucc hxr.symm).trans h)
    · intro h
      exact ne_ringSucc (by omega : 1 < L) x (hxr.trans h.symm)
  · push Not at hx
    exact ⟨x, Or.inl rfl, hx.1, hx.2⟩

/-! ### Invariants of the global bond factor `f_x` -/

/-- The global bond factor `f_x` is prime on a ring of length `> 1`: its four variables
`(x,0), (ringSucc x,1), (x,1), (ringSucc x,0)` are pairwise distinct (`ne_ringSucc` handles the
same-component pairs), so `bondFactor_prime` applies. -/
theorem fBond_prime (hL : 1 < L) (x : Fin L) : Prime (fBond x) := by
  have hxr : x ≠ ringSucc x := ne_ringSucc hL x
  unfold fBond
  refine bondFactor_prime ?_ ?_ ?_ ?_ ?_
  · intro h; simp at h
  · intro h; simp at h
  · intro h; exact hxr (congrArg Prod.fst h)
  · intro h; exact hxr (congrArg Prod.fst h).symm
  · intro h; simp at h

/-- The global bond factor `f_x` has total degree `2` (it is a bilinear form); a ring of `L` bonds
thus has product degree `2L` (Tasaki eq. (7.1.25)). -/
theorem fBond_totalDegree (hL : 1 < L) (x : Fin L) : (fBond x).totalDegree = 2 := by
  have hxr : x ≠ ringSucc x := ne_ringSucc hL x
  unfold fBond
  refine bondFactor_totalDegree ?_ ?_ ?_
  · intro h; simp at h
  · intro h; simp at h
  · intro h; exact hxr (congrArg Prod.fst h)

/-- The variable set of the global bond factor `f_x` is exactly
`{(x,0), (ringSucc x,1), (x,1), (ringSucc x,0)}` — the four Weyl variables of the two bond sites.
Distinct cyclic bonds therefore have different variable sets, the mechanism behind their relative
primality. -/
theorem fBond_vars (hL : 1 < L) (x : Fin L) :
    (fBond x).vars = {(x, 0), (ringSucc x, 1), (x, 1), (ringSucc x, 0)} := by
  have hxr : x ≠ ringSucc x := ne_ringSucc hL x
  unfold fBond
  refine vars_bondFactor ?_ ?_ ?_ ?_ ?_ ?_
  · intro h; simp at h
  · intro h; simp at h
  · intro h; exact hxr (congrArg Prod.fst h)
  · intro h; exact hxr (congrArg Prod.fst h).symm
  · intro h; simp at h
  · intro h; simp at h

/-- **Distinct bonds are relatively prime** (Stage C step 2', Tasaki §7.1.3).  For `L ≥ 3` and
`x ≠ y`, the prime factors `f_x` and `f_y` are relatively prime: they have equal total degree `2`,
and the witness variable `(s, 0)` (`exists_bond_var_witness`) occurs in `f_x.vars` but not
`f_y.vars`, so `bondFactor_isRelPrime` applies. -/
theorem fBond_isRelPrime (hL : 3 ≤ L) {x y : Fin L} (hxy : x ≠ y) :
    IsRelPrime (fBond x) (fBond y) := by
  obtain ⟨s, hs, hsy, hsry⟩ := exists_bond_var_witness hL hxy
  refine bondFactor_isRelPrime (fBond_prime (by omega) x)
    (fBond_prime (by omega) y).ne_zero
    ((fBond_totalDegree (by omega) x).trans (fBond_totalDegree (by omega) y).symm)
    (e := (s, 0)) ?_ ?_
  · rw [fBond_vars (by omega) x]
    rcases hs with rfl | rfl <;> simp
  · rw [fBond_vars (by omega) y]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; exact hsy (congrArg Prod.fst h)
    · intro h; simp at h
    · intro h; simp at h
    · intro h; exact hsry (congrArg Prod.fst h)

/-! ### Product divisibility and the degree count (Tasaki eq. (7.1.25)) -/

/-- **The product of all bond factors divides the Weyl image of a common ground form.**  If `Ψ` has
the VBS singlet form at every bond of the ring (`∀ x, IsVBSGroundForm L x Ψ`), then each `f_x`
divides `weylMap Ψ` (U3b), and the pairwise coprimality of the `f_x` (`fBond_isRelPrime`) lifts this
to `∏_x f_x ∣ weylMap Ψ` via `prod_dvd_of_pairwise_isRelPrime`. -/
theorem prod_fBond_dvd_weylMap (hL : 3 ≤ L) (Ψ : (Fin L → Fin 3) → ℂ)
    (hΨ : ∀ x : Fin L, IsVBSGroundForm L x Ψ) :
    (∏ x : Fin L, fBond x) ∣ weylMap Ψ := by
  refine prod_dvd_of_pairwise_isRelPrime Finset.univ fBond (weylMap Ψ)
    (fun x _ => fBond_dvd_weylMap_of_isVBSGroundForm x (by omega) Ψ (hΨ x)) ?_
  intro x _ y _ hxy
  exact fBond_isRelPrime hL hxy

/-- The product of all `L` bond factors has total degree `2L` (each factor has degree `2`; the ring
is periodic so there are exactly `L` factors).  Uses `totalDegree_prod_of_isDomain` and
`fBond_totalDegree`. -/
theorem prod_fBond_totalDegree (hL : 1 < L) :
    (∏ x : Fin L, fBond x).totalDegree = 2 * L := by
  rw [totalDegree_prod_of_isDomain Finset.univ fBond
      (fun x _ => (fBond_prime hL x).ne_zero),
    Finset.sum_congr rfl (fun x _ => fBond_totalDegree hL x), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- **Stage C capstone (Tasaki eq. (7.1.25)): the polynomial side of one-dimensionality.**  A
nonzero common ground form `Ψ` (in every bond kernel) has Weyl image a constant multiple of the
product of all bond factors: `weylMap Ψ = C c · ∏_x f_x`.  Proof: `∏_x f_x ∣ weylMap Ψ`
(`prod_fBond_dvd_weylMap`) and both sides have total degree `2L` (`weylMap_isHomogeneous`,
`prod_fBond_totalDegree`), so the quotient is a constant (`eq_const_smul_of_dvd_of_totalDegree_eq`).
This is the explicit-scalar realization of `dim K_L ≤ 1`. -/
theorem weylMap_ground_form_eq_const_smul_prod (hL : 3 ≤ L)
    (Ψ : (Fin L → Fin 3) → ℂ) (hΨ0 : Ψ ≠ 0) (hΨ : ∀ x : Fin L, IsVBSGroundForm L x Ψ) :
    ∃ c : ℂ, weylMap Ψ = MvPolynomial.C c * ∏ x : Fin L, fBond x := by
  have hne : weylMap Ψ ≠ 0 := by
    have h := weylMap_injective.ne hΨ0
    simpa using h
  refine eq_const_smul_of_dvd_of_totalDegree_eq (prod_fBond_dvd_weylMap hL Ψ hΨ) hne ?_
  rw [(weylMap_isHomogeneous Ψ).totalDegree hne, prod_fBond_totalDegree (by omega)]

end LatticeSystem.Quantum.AKLTUniqueness
