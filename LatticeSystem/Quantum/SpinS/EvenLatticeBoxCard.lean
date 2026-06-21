import LatticeSystem.Quantum.SpinS.BulkDensity

/-!
# Tasaki §4.3.1: the even-sublattice cardinality `|Λ_n ∩ ℤᵈ_even| = (2n)ᵈ / 2`

This module computes the finite combinatorial coefficient left open by the
bulk-operator / bulk-density layer (`BulkOperator.lean`, `BulkDensity.lean`): for
`d ≥ 1` the centered box `Λ_n` splits into **equally many even and odd sites**, so
`|Λ_n ∩ ℤᵈ_even| = (2n)ᵈ / 2`.

The proof is a parity generating-function argument: the parity sign
`ε(m) = (−1)^m` is multiplicative on sums, and over the symmetric coordinate
interval `Ioc(−n, n]` the signs cancel (`n` evens and `n` odds), so the
`d`-dimensional sign sum vanishes when `d ≥ 1`; equal even/odd counts follow.

As a consequence, for a translation-invariant state and `n ≥ 1` the bulk density
has the clean value `ω(Â_n / Lᵈ) = ½ ω(Â)` (Tasaki §4.3.1).  Everything is proved
**axiom-free**; no new axiom and no existing axiom is touched.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, eqs. (4.3.2)–(4.3.6), pp. 112–115.
-/

namespace LatticeSystem.Quantum

namespace InfiniteSpinSystem

open Finset

/-- The **parity sign** `ε(m) = (−1)^m`: `+1` on even integers, `−1` on odd. -/
def paritySign (m : ℤ) : ℤ := if Even m then 1 else -1

/-- The parity sign is multiplicative on sums: `ε(a + b) = ε(a)·ε(b)`. -/
theorem paritySign_add (a b : ℤ) :
    paritySign (a + b) = paritySign a * paritySign b := by
  simp only [paritySign, Int.even_add]
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [ha, hb]

/-- The parity sign of a finite sum is the product of the parity signs. -/
theorem paritySign_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    paritySign (∑ i ∈ s, f i) = ∏ i ∈ s, paritySign (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [paritySign]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, paritySign_add, ih]

/-- Over the symmetric interval `Ioc(−n, n]` the parity signs cancel:
`Σ_{z ∈ Ioc(−n, n]} ε(z) = 0` (it contains `n` evens and `n` odds). -/
theorem sum_paritySign_Ioc_neg_nat (n : ℕ) :
    (∑ z ∈ Finset.Ioc (-(n : ℤ)) (n : ℤ), paritySign z) = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hset : Finset.Ioc (-((k : ℤ) + 1)) ((k : ℤ) + 1)
        = insert ((k : ℤ) + 1) (insert (-(k : ℤ)) (Finset.Ioc (-(k : ℤ)) (k : ℤ))) := by
      ext z
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hmem1 : (-(k : ℤ)) ∉ Finset.Ioc (-(k : ℤ)) (k : ℤ) := by
      simp [Finset.mem_Ioc]
    have hmem2 : ((k : ℤ) + 1) ∉ insert (-(k : ℤ)) (Finset.Ioc (-(k : ℤ)) (k : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
    have hcast : (-(((k : ℕ) + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) := by push_cast; ring
    have hcast2 : (((k : ℕ) + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    rw [hcast, hcast2, hset, Finset.sum_insert hmem2, Finset.sum_insert hmem1, ih]
    have hsign : paritySign ((k : ℤ) + 1) + paritySign (-(k : ℤ)) = 0 := by
      simp only [paritySign]
      rcases Int.even_or_odd (k : ℤ) with hk | hk
      · rw [if_neg (by simpa [Int.even_add_one] using hk),
          if_pos (by simpa using hk.neg)]
        ring
      · rw [if_pos (by simpa [Int.even_add_one, Int.not_even_iff_odd] using hk),
          if_neg (by simpa [Int.not_even_iff_odd] using hk.neg)]
        ring
    rw [add_zero] at *
    omega

variable {d : ℕ}

/-- The `d`-dimensional parity-sign sum over the box vanishes for `d ≥ 1`:
`Σ_{x ∈ Λ_n} ε(Σ_i xᵢ) = 0`. -/
theorem latticeBox_paritySign_sum_eq_zero (d n : ℕ) (hd : 0 < d) :
    (∑ x ∈ latticeBox d n, paritySign (∑ i, x i)) = 0 := by
  have hsplit : (∑ x ∈ latticeBox d n, paritySign (∑ i, x i))
      = ∏ _i : Fin d, (∑ z ∈ Finset.Ioc (-(n : ℤ)) (n : ℤ), paritySign z) := by
    rw [latticeBox_eq_hypercubicBox, LatticeSystem.Lattice.hypercubicBox]
    simp_rw [paritySign_sum]
    rw [Finset.prod_univ_sum]
  rw [hsplit]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hd⟩ : Fin d))
  exact sum_paritySign_Ioc_neg_nat n

/-- `evenSite` agrees with the evenness of the coordinate sum. -/
theorem evenSite_iff_even_sum {x : Fin d → ℤ} :
    evenSite x ↔ Even (∑ i, x i) := by
  rw [evenSite, Int.even_iff]

/-- The signed even/odd count over the box: `(#even) − (#odd) = Σ ε = 0` for
`d ≥ 1`, so the box has equally many even and odd sites. -/
theorem evenLatticeBox_card_eq_odd_card (d n : ℕ) (hd : 0 < d) :
    (evenLatticeBox d n).card =
      ((latticeBox d n).filter fun x : Fin d → ℤ => ¬ evenSite x).card := by
  classical
  have hsum : (∑ x ∈ latticeBox d n, paritySign (∑ i, x i))
      = ((evenLatticeBox d n).card : ℤ)
        - ((latticeBox d n).filter fun x : Fin d → ℤ => ¬ evenSite x).card := by
    rw [evenLatticeBox]
    rw [← Finset.sum_filter_add_sum_filter_not (latticeBox d n)
      (fun x => evenSite x) (fun x => paritySign (∑ i, x i))]
    have he : ∀ x ∈ (latticeBox d n).filter (fun x => evenSite x),
        paritySign (∑ i, x i) = 1 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      simp [paritySign, (evenSite_iff_even_sum.mp hx.2)]
    have ho : ∀ x ∈ (latticeBox d n).filter (fun x => ¬ evenSite x),
        paritySign (∑ i, x i) = -1 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have : ¬ Even (∑ i, x i) := fun h => hx.2 (evenSite_iff_even_sum.mpr h)
      simp [paritySign, this]
    rw [Finset.sum_congr rfl he, Finset.sum_congr rfl ho]
    simp [mul_comm]
    ring
  rw [latticeBox_paritySign_sum_eq_zero d n hd] at hsum
  have : ((evenLatticeBox d n).card : ℤ)
      = ((latticeBox d n).filter fun x : Fin d → ℤ => ¬ evenSite x).card := by omega
  exact_mod_cast this

/-- **Twice the even-site count equals the box volume**: `2·|Λ_n ∩ ℤᵈ_even| = (2n)ᵈ`
for `d ≥ 1`. -/
theorem two_mul_evenLatticeBox_card (d n : ℕ) (hd : 0 < d) :
    2 * (evenLatticeBox d n).card = (2 * n) ^ d := by
  classical
  have htot : (evenLatticeBox d n).card +
      ((latticeBox d n).filter fun x : Fin d → ℤ => ¬ evenSite x).card
      = (latticeBox d n).card := by
    rw [evenLatticeBox]
    exact Finset.card_filter_add_card_filter_not _
  have hcard : (latticeBox d n).card = (2 * n) ^ d := by
    rw [latticeBox_eq_hypercubicBox, LatticeSystem.Lattice.hypercubicBox_card]
  have heq := evenLatticeBox_card_eq_odd_card d n hd
  rw [hcard] at htot
  omega

/-- The real even-site count: `|Λ_n ∩ ℤᵈ_even| = (2n)ᵈ / 2` (`d ≥ 1`). -/
theorem evenLatticeBox_card_real (d n : ℕ) (hd : 0 < d) :
    ((evenLatticeBox d n).card : ℝ) = bulkVolume d n / 2 := by
  have h := two_mul_evenLatticeBox_card d n hd
  have hc : ((2 * (evenLatticeBox d n).card : ℕ) : ℝ) = (((2 * n) ^ d : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  rw [bulkVolume]
  push_cast at hc ⊢
  linarith

/-- The complex even-site count: `|Λ_n ∩ ℤᵈ_even| = (2n)ᵈ / 2` (`d ≥ 1`). -/
theorem evenLatticeBox_card_complex (d n : ℕ) (hd : 0 < d) :
    ((evenLatticeBox d n).card : ℂ) = (bulkVolume d n : ℂ) / 2 := by
  have hr := evenLatticeBox_card_real d n hd
  rw [show ((evenLatticeBox d n).card : ℂ)
      = (((evenLatticeBox d n).card : ℝ) : ℂ) by push_cast; ring, hr]
  push_cast
  ring

/-- The box volume is positive once `0 < n`. -/
theorem bulkVolume_pos_of_pos (d : ℕ) {n : ℕ} (hn : 0 < n) : 0 < bulkVolume d n := by
  rw [bulkVolume]
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  positivity

/-- The complex box volume is nonzero once `0 < n`. -/
theorem bulkVolume_ne_zero_complex_of_pos (d : ℕ) {n : ℕ} (hn : 0 < n) :
    (bulkVolume d n : ℂ) ≠ 0 := by
  have := (bulkVolume_pos_of_pos d hn).ne'
  exact_mod_cast this

variable {A : Type*} [CStarAlgebra A]

namespace TranslationInvariant

/-- **Half-filling of the even sublattice**: for a translation-invariant state and
`n ≥ 1`, the bulk density of any observable is `ω(Â_n / Lᵈ) = ½ ω(Â)` (`d ≥ 1`),
since exactly half the box sites are even. -/
theorem bulkDensity_apply_eq_half_mul {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (a : A) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    ω (bulkDensity S a n) = (1 / 2 : ℂ) * ω a := by
  have hbv := bulkVolume_ne_zero_complex_of_pos d hn
  rw [hω.bulkDensity_apply_eq_card_mul, evenLatticeBox_card_complex d n hd]
  field_simp

/-- Real first-moment form of the half-filling value: `Re ω(Â_n)/Lᵈ = ½ Re ω(Â)`. -/
theorem bulkDensityMean_eq_half_mul {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (a : A) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    bulkDensityMean S ω a n = (ω a).re / 2 := by
  have hbv := (bulkVolume_pos_of_pos d hn).ne'
  rw [hω.bulkDensityMean_eq_card_mul, evenLatticeBox_card_real d n hd]
  field_simp

end TranslationInvariant

end InfiniteSpinSystem

end LatticeSystem.Quantum
