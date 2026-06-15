import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval

/-!
# The infinite hypercubic lattice `ℤᵈ` and its finite-volume exhaustion

This module fixes the **graph-centric** datum underlying the project's central
long-term goal — the thermodynamic (infinite-volume) limit on the
`d`-dimensional hypercubic lattice `ℤᵈ`.  Finite-volume systems are the starting
point; the infinite system is obtained as the limit along an increasing sequence
of finite boxes `Λ_n ⊆ Λ_{n+1} ⊆ ⋯` that exhaust `ℤᵈ`.

It provides, with no quantum / C*-algebra dependencies:

* `hypercubicLatticeGraph d : SimpleGraph (Fin d → ℤ)` — the infinite hypercubic
  lattice as a `SimpleGraph`, with two sites adjacent iff they differ in exactly
  one coordinate by `±1` (the nearest-neighbor bond set `B∞`, cf. Tasaki
  eq. (4.3.1));
* `hypercubicBox d n : Finset (Fin d → ℤ)` — the centered finite box
  `Λ_n = {x ∈ ℤᵈ : −n < xᵢ ≤ n}` of even side length `2n` (Tasaki eq. (3.1.2));
* the **monotone exhaustion** of `ℤᵈ` by the boxes: `Λ_n ⊆ Λ_{n+1}`
  (`hypercubicBox_subset_succ`, `hypercubicBox_monotone`) and
  `⋃ₙ Λ_n = ℤᵈ` (`iUnion_hypercubicBox`, `exists_mem_hypercubicBox`).

The box `hypercubicBox d n` is definitionally the same `Fintype.piFinset` as
`LatticeSystem.Quantum.InfiniteSpinSystem.latticeBox d n`; this model-agnostic
copy lives in `Lattice/` so the increasing-region API is available without the
quantum layer.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §3.1 (eq. (3.1.2)) and §4.3 (eq. (4.3.1)).
-/

namespace LatticeSystem.Lattice

open Finset

variable (d : ℕ)

/-- The **infinite hypercubic lattice** `ℤᵈ` as a `SimpleGraph (Fin d → ℤ)`: two
sites `x, y` are adjacent iff they differ in exactly one coordinate by `±1`,
i.e. there is a coordinate `i` with `|xᵢ − yᵢ| = 1` and `xⱼ = yⱼ` for every
`j ≠ i`.  This is the nearest-neighbor bond set `B∞` of Tasaki eq. (4.3.1). -/
def hypercubicLatticeGraph : SimpleGraph (Fin d → ℤ) where
  Adj x y := ∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j
  symm := by
    rintro x y ⟨i, hi, hj⟩
    exact ⟨i, by rw [abs_sub_comm]; exact hi, fun j hjne => (hj j hjne).symm⟩
  loopless := ⟨by rintro x ⟨i, hi, -⟩; simp at hi⟩

variable {d}

/-- Adjacency in `hypercubicLatticeGraph d` unfolds to the nearest-neighbor bond
condition: `x` and `y` differ in exactly one coordinate by `±1`. -/
theorem hypercubicLatticeGraph_adj {x y : Fin d → ℤ} :
    (hypercubicLatticeGraph d).Adj x y ↔
      ∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j :=
  Iff.rfl

instance : DecidableRel (hypercubicLatticeGraph d).Adj := fun x y =>
  decidable_of_iff (∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j)
    hypercubicLatticeGraph_adj.symm

variable (d)

/-- The centered finite **hypercubic box** `Λ_n = {x ∈ ℤᵈ : −n < xᵢ ≤ n}` of even
side length `2n` and volume `(2n)ᵈ` (Tasaki eq. (3.1.2)), as a `Finset`.  This is
definitionally equal to `Quantum.InfiniteSpinSystem.latticeBox d n`. -/
noncomputable def hypercubicBox (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ioc (-(n : ℤ)) (n : ℤ)

variable {d}

/-- Membership in the hypercubic box: `x ∈ Λ_n` iff every coordinate satisfies
`−n < xᵢ ≤ n`. -/
@[simp]
theorem mem_hypercubicBox {n : ℕ} {x : Fin d → ℤ} :
    x ∈ hypercubicBox d n ↔ ∀ i, -(n : ℤ) < x i ∧ x i ≤ (n : ℤ) := by
  simp [hypercubicBox, Fintype.mem_piFinset, Finset.mem_Ioc]

/-- The boxes are **nested**: `Λ_n ⊆ Λ_{n+1}`. -/
theorem hypercubicBox_subset_succ (n : ℕ) :
    hypercubicBox d n ⊆ hypercubicBox d (n + 1) := by
  apply Fintype.piFinset_subset
  intro _
  apply Finset.Ioc_subset_Ioc
  · push_cast; omega
  · push_cast; omega

/-- The box family is **monotone** in the side index `n` (as a function to
`Finset`s under `⊆`). -/
theorem hypercubicBox_monotone : Monotone (hypercubicBox d) := by
  apply monotone_nat_of_le_succ
  intro n
  exact hypercubicBox_subset_succ n

/-- Every site of `ℤᵈ` lies in some box: the boxes **exhaust** `ℤᵈ`.  Concretely
`x ∈ Λ_n` for any `n` exceeding every `|xᵢ|`. -/
theorem exists_mem_hypercubicBox (x : Fin d → ℤ) :
    ∃ n : ℕ, x ∈ hypercubicBox d n := by
  refine ⟨(Finset.univ.sup fun i => (x i).natAbs) + 1, ?_⟩
  rw [mem_hypercubicBox]
  intro i
  have hle : (x i).natAbs ≤ Finset.univ.sup fun i => (x i).natAbs :=
    Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  constructor <;> push_cast <;> omega

/-- The boxes **exhaust** `ℤᵈ`: `⋃ₙ Λ_n = ℤᵈ`. -/
theorem iUnion_hypercubicBox :
    ⋃ n : ℕ, (hypercubicBox d n : Set (Fin d → ℤ)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨n, hn⟩ := exists_mem_hypercubicBox x
  exact Set.mem_iUnion.mpr ⟨n, hn⟩

end LatticeSystem.Lattice
