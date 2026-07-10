/-
The ungauged Dyson–Lieb–Simon split of the bond-square field Hamiltonian
(Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS8a-i).

The physical bond-square field Hamiltonian `ringBondSquareFieldHamiltonian n N h` (Tasaki (4.1.48),
book p.86) couples its staggered field quadratically inside the directed bond-square running over
the `2n` cyclic bonds `(x, x+1)`.  Mirroring the linear ungauged DLS split
(`heisenbergHamiltonianS_ringCoupling_ungauged_dls`, `RingReflectionUngaugedDLS.lean`), this file
reorganises that directed bond sum — **without expanding any square** — by the geometric bond
classification of the even ring `Fin (2n)`:

* intra-left bonds `x+1 < n` (both endpoints in `{0,…,n−1}`),
* the crossing bond at `x = n−1` (the bond `(n−1, n)`),
* intra-right bonds `n ≤ x ∧ x+1 < 2n` (both endpoints in `{n,…,2n−1}`),
* the crossing bond at `x = 2n−1` (the bond `(2n−1, 0)`),

leaving the single-ion term `−∑_x (Ŝ³ₓ)²` whole.  The result
`ringBondSquareFieldHamiltonian_ungauged_dls` is the pre-gauge (bare-field, no staggered wrapper)
form on which the PR-BS8a-ii gauge conjugation fires: field-additivity is unavailable inside the
square, so unlike the linear route there is no field-free `H_L` to delegate to, and the split is
genuinely new.  It also records the directed-single-bond ↔ `ringLeftCoupling` double-sum bridge
`ringBondSquareLeftBondSum_eq_leftCouplingBulk` (the bond-square analogue of
`ringLeftHamiltonian_eq_leftBondSum`), aligning the intra-left directed sum with the bulk double sum
of the merged left-half Hamiltonian `ringBondSquareLeftFieldHamiltonian` (Tasaki (4.1.67), book
p.90).  The gauge crux, physical-field identification, and reflection step are deferred to
PR-BS8a-ii (new file, name to be chosen since `RingReflectionBondSquareFieldPartition.lean` is taken
by BS2) and PR-BS8b.

See `.self-local/docs/math-tasaki-4-1-51-bond-square-physical-field-reflection-step.md` (issue
#4777, §5 PR-BS8a-i).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareTwoFieldWeight
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareField
import LatticeSystem.Quantum.SpinS.RingReflectionBondSplit
import LatticeSystem.Quantum.SpinS.RingReflectionLeftBondSum

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Per-bond bond-square term** at the directed cyclic bond `(x, x+1)` with a bare per-site field
`f` (Tasaki §4.1 (4.1.48), book p.86): the kinetic pair `Ŝ¹ₓŜ¹_{x+1} + Ŝ²ₓŜ²_{x+1}` plus the
longitudinal bond-square `½(Ŝ³ₓ + Ŝ³_{x+1} − f_x − f_{x+1})²`.  This is the summand of
`ringBondSquareFieldHamiltonian` at `f = ringBondSquareStagField h`; naming it lets the ungauged DLS
split reorganise the directed bond sum without touching the square.  The field is taken **bare**
(no `(−1)ˣ` staggering), matching the merged left-half Hamiltonian's field convention. -/
noncomputable def ringBondSquareBondTermOf (n N : ℕ) (f : Fin (2 * n) → ℝ) (x : Fin (2 * n)) :
    ManyBodyOpS (Fin (2 * n)) N :=
  onSiteS x (spinSOp1 N) * onSiteS (ringBondSucc n x) (spinSOp1 N)
    + onSiteS x (spinSOp2 N) * onSiteS (ringBondSucc n x) (spinSOp2 N)
    + (1 / 2 : ℂ) • (onSiteS x (spinSOp3 N) + onSiteS (ringBondSucc n x) (spinSOp3 N)
        - (f x : ℂ) • 1 - (f (ringBondSucc n x) : ℂ) • 1) ^ 2

/-- **Intra-left directed bond-square sum**: the bond-square terms over the directed bonds
`(x, x+1)` entirely inside the left half `{0,…,n−1}` (`x+1 < n`), with bare field `f`.  The
bond-square analogue of `ringLeftHamiltonian`'s left bond form
(`ringLeftHamiltonian_eq_leftBondSum`); bridged to the bulk double sum of
`ringBondSquareLeftFieldHamiltonian` by `ringBondSquareLeftBondSum_eq_leftCouplingBulk`. -/
noncomputable def ringBondSquareLeftBondSum (n N : ℕ) (f : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  ∑ x : Fin (2 * n), if (x : ℕ) + 1 < n then ringBondSquareBondTermOf n N f x else 0

/-- **Intra-right directed bond-square sum**: the bond-square terms over the directed bonds
`(x, x+1)` entirely inside the right half `{n,…,2n−1}` (`n ≤ x ∧ x+1 < 2n`), with bare field `f`.
The bond-square analogue of `ringRightBondSum`; its identification with the `θ`-reflection of the
left half is part of the PR-BS8a-ii gauge conjugation, not of this ungauged split. -/
noncomputable def ringBondSquareRightBondSum (n N : ℕ) (f : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  ∑ x : Fin (2 * n),
    if n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n then ringBondSquareBondTermOf n N f x else 0

/-- **The physical bond-square field Hamiltonian as a bond-term sum minus the single-ion term.**  A
definitional repackaging of `ringBondSquareFieldHamiltonian` (Tasaki §4.1 (4.1.48), book p.86)
exhibiting its directed bond sum through the named per-bond term `ringBondSquareBondTermOf` at the
staggered field `ringBondSquareStagField h`, ready for the four-way bond classification. -/
theorem ringBondSquareFieldHamiltonian_eq_bondTermOf_sum (n N : ℕ) (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldHamiltonian n N h
      = (∑ x : Fin (2 * n), ringBondSquareBondTermOf n N (fun z => ringBondSquareStagField h z) x)
        - ∑ x : Fin (2 * n), onSiteS x (spinSOp3 N) ^ 2 := rfl

/-- **Generic four-way bond classification of a sum over the even ring.**  Every family `F` over the
directed bonds of `Fin (2n)` splits into the intra-left indicator sum (`x+1 < n`), the intra-right
indicator sum (`n ≤ x ∧ x+1 < 2n`), and the two crossing terms `F ⟨n−1⟩`, `F ⟨2n−1⟩`, since each
site falls into exactly one of the four classes.  The bond-square analogue of the routing inside
`heisenbergHamiltonianS_ringCoupling_bond_split` for the linear spin-dot family; here it is stated
generically in `F` so it can carry the whole bond-square term.  Reuses the existing single-condition
picker `sum_ite_val_eq` for the two crossing terms. -/
private theorem sum_four_way_split (n N : ℕ) [NeZero n]
    (F : Fin (2 * n) → ManyBodyOpS (Fin (2 * n)) N) :
    ∑ x : Fin (2 * n), F x
      = (∑ x : Fin (2 * n), if (x : ℕ) + 1 < n then F x else 0)
        + (∑ x : Fin (2 * n), if n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n then F x else 0)
        + F ⟨n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩
        + F ⟨2 * n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩ := by
  have key : ∀ x : Fin (2 * n), F x
      = (if (x : ℕ) + 1 < n then F x else 0) + (if (x : ℕ) = n - 1 then F x else 0)
        + (if n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n then F x else 0)
        + (if (x : ℕ) = 2 * n - 1 then F x else 0) := by
    intro x
    have hlt := x.isLt
    have hn := Nat.pos_of_ne_zero (NeZero.ne n)
    by_cases h1 : (x : ℕ) + 1 < n
    · rw [if_pos h1, if_neg (show ¬ (x : ℕ) = n - 1 by omega),
        if_neg (show ¬ (n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n) by omega),
        if_neg (show ¬ (x : ℕ) = 2 * n - 1 by omega)]
      simp
    · by_cases h2 : (x : ℕ) = n - 1
      · rw [if_neg h1, if_pos h2,
          if_neg (show ¬ (n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n) by omega),
          if_neg (show ¬ (x : ℕ) = 2 * n - 1 by omega)]
        simp
      · by_cases h4 : (x : ℕ) = 2 * n - 1
        · rw [if_neg h1, if_neg h2,
            if_neg (show ¬ (n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n) by omega), if_pos h4]
          simp
        · rw [if_neg h1, if_neg h2,
            if_pos (show n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n by omega), if_neg h4]
          simp
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_ite_val_eq (by have := Nat.pos_of_ne_zero (NeZero.ne n); omega),
    sum_ite_val_eq (by have := Nat.pos_of_ne_zero (NeZero.ne n); omega)]
  abel

/-- **The ungauged DLS split of the bond-square field Hamiltonian.**  The physical bond-square field
Hamiltonian reorganises — with no square expanded — into the intra-left and intra-right directed
bond-square sums, the two crossing bond-square terms, and the whole single-ion term (Tasaki §4.1
(4.1.48)/(4.1.69), book pp.86,90).  This is the bare-field pre-gauge form (no staggered wrapper)
the PR-BS8a-ii right-half Marshall gauge conjugates into the reflection-positive DLS form
`H_L(a) + θ(H_L(b)) − crossing(a,b)`; it mirrors the linear
`heisenbergHamiltonianS_ringCoupling_ungauged_dls`, the field now riding inside the un-expanded
squares. -/
theorem ringBondSquareFieldHamiltonian_ungauged_dls (n N : ℕ) [NeZero n] (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldHamiltonian n N h
      = ringBondSquareLeftBondSum n N (fun z => ringBondSquareStagField h z)
        + ringBondSquareRightBondSum n N (fun z => ringBondSquareStagField h z)
        + ringBondSquareBondTermOf n N (fun z => ringBondSquareStagField h z)
            ⟨n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩
        + ringBondSquareBondTermOf n N (fun z => ringBondSquareStagField h z)
            ⟨2 * n - 1, by have := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩
        - ∑ x : Fin (2 * n), onSiteS x (spinSOp3 N) ^ 2 := by
  rw [ringBondSquareFieldHamiltonian_eq_bondTermOf_sum,
    sum_four_way_split n N (ringBondSquareBondTermOf n N (fun z => ringBondSquareStagField h z))]
  rfl

/-- **Directed-bond ↔ `ringLeftCoupling` double-sum bridge.**  The intra-left directed bond-square
sum equals the bulk double sum of the merged left-half Hamiltonian
`ringBondSquareLeftFieldHamiltonian` (Tasaki §4.1 (4.1.67), book p.90): the left coupling
`ringLeftCoupling n x y` is nonzero only on a genuine left bond `y = x+1` with `x+1 < n`, collapsing
the inner sum, after which the two-factor square form `X·X` normalises to the bond-square `X²` and
the `+(−f)·1` shift to the `−f·1` slot.  The bond-square analogue of
`ringLeftHamiltonian_eq_leftBondSum`, aligning this ungauged split's intra-left piece with the
merged `H_L`'s bulk for the PR-BS8a-ii gauge conjugation. -/
theorem ringBondSquareLeftBondSum_eq_leftCouplingBulk (n N : ℕ) [NeZero n] (f : Fin (2 * n) → ℝ) :
    ringBondSquareLeftBondSum n N f
      = ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
          ∑ y ∈ Finset.univ.filter (fun y : Fin (2 * n) => (y : ℕ) < n),
            ringLeftCoupling n x y • (onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N)
              + onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)
              + (1 / 2 : ℂ) • ((onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
                    + (-(f x : ℂ)) • 1 + (-(f y : ℂ)) • 1)
                  * (onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
                    + (-(f x : ℂ)) • 1 + (-(f y : ℂ)) • 1))) := by
  rw [ringBondSquareLeftBondSum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Fin (2 * n) => (x : ℕ) < n)
      (fun x => if (x : ℕ) + 1 < n then ringBondSquareBondTermOf n N f x else 0)]
  have hnot : (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => ¬ (x : ℕ) < n),
        if (x : ℕ) + 1 < n then ringBondSquareBondTermOf n N f x else 0) = 0 :=
    Finset.sum_eq_zero (fun x hx => by
      rw [if_neg (by have := (Finset.mem_filter.mp hx).2; omega)])
  rw [hnot, add_zero]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hxn : (x : ℕ) < n := (Finset.mem_filter.mp hx).2
  by_cases hx1 : (x : ℕ) + 1 < n
  · rw [if_pos hx1, Finset.sum_eq_single (ringBondSucc n x)]
    · rw [ringLeftCoupling_succ_of_lt hx1, one_smul, ringBondSquareBondTermOf, pow_two]
      simp only [neg_smul, sub_eq_add_neg]
    · intro y hy hyne
      rw [ringLeftCoupling_eq_zero_of_ne hyne, zero_smul]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]; omega⟩) hmem
  · rw [if_neg hx1]
    refine (Finset.sum_eq_zero (fun y _ => ?_)).symm
    rw [ringLeftCoupling_eq_zero_of_not_lt hx1 y, zero_smul]

end LatticeSystem.Quantum
