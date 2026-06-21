import LatticeSystem.Quantum.SpinS.BoxLocalTranslation

/-!
# Tasaki §4.3.1: algebra of the bulk operator `Â_n`

Tasaki's **bulk operator** `Â_n = Σ_{x ∈ Λ_n ∩ ℤᵈ_even} τ_x(Â)` (eq. (4.3.5))
averages an observable `Â` over the even sites of the box `Λ_n`; its density
`Â_n / Lᵈ` is the macroscopic observable whose fluctuation defines ergodicity
(Definition 4.18, eq. (4.3.6)).

This module records the **constructive algebra** of `Â ↦ Â_n`, all proved
**axiom-free**: it is `ℂ`-linear (`bulkOp_zero/add/smul/finset_sum`), the bulk of
a spin / bond operator expands as a sum over the shifted even sites
(`bulkOp_spin_eq_sum`, `bulkOp_spinDot_eq_sum`), these bulk observables are local
(supported in a translated box), and for a translation-invariant state the bulk
expectation is `ω(Â_n) = |Λ_n ∩ ℤᵈ_even| · ω(Â)`.

No new axiom is introduced and no existing axiom is touched.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, eqs. (4.3.5)–(4.3.6), pp. 112–115;
  Appendix A.7, pp. 530–533.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

namespace InfiniteSpinSystem

/-- The **even sites of the box** `Λ_n ∩ ℤᵈ_even`, the index set of the bulk
operator (Tasaki eq. (4.3.5)). -/
noncomputable def evenLatticeBox (d n : ℕ) : Finset (Fin d → ℤ) :=
  (latticeBox d n).filter evenSite

/-- Membership in `evenLatticeBox`: an even site of the box. -/
@[simp]
theorem mem_evenLatticeBox {x : Fin d → ℤ} {n : ℕ} :
    x ∈ evenLatticeBox d n ↔ x ∈ latticeBox d n ∧ evenSite x := by
  simp [evenLatticeBox]

/-- The even box sites are box sites. -/
theorem evenLatticeBox_subset_latticeBox (d n : ℕ) :
    evenLatticeBox d n ⊆ latticeBox d n :=
  Finset.filter_subset _ _

/-- The bulk operator as a sum over the even box sites:
`Â_n = Σ_{x ∈ Λ_n ∩ ℤᵈ_even} τ_x Â`. -/
theorem bulkOp_eq_sum_evenLatticeBox (S : InfiniteSpinSystem d A) (a : A) (n : ℕ) :
    bulkOp S a n = ∑ x ∈ evenLatticeBox d n, S.transl x a :=
  rfl

/-- The bulk operator annihilates `0`. -/
@[simp]
theorem bulkOp_zero (S : InfiniteSpinSystem d A) (n : ℕ) :
    bulkOp S (0 : A) n = 0 := by
  simp [bulkOp_eq_sum_evenLatticeBox]

/-- The bulk operator is additive. -/
theorem bulkOp_add (S : InfiniteSpinSystem d A) (a b : A) (n : ℕ) :
    bulkOp S (a + b) n = bulkOp S a n + bulkOp S b n := by
  simp [bulkOp_eq_sum_evenLatticeBox, map_add, Finset.sum_add_distrib]

/-- The bulk operator is `ℂ`-homogeneous. -/
theorem bulkOp_smul (S : InfiniteSpinSystem d A) (c : ℂ) (a : A) (n : ℕ) :
    bulkOp S (c • a) n = c • bulkOp S a n := by
  simp [bulkOp_eq_sum_evenLatticeBox, map_smul, Finset.smul_sum]

/-- The bulk operator commutes with finite sums. -/
theorem bulkOp_finset_sum {ι : Type*} (S : InfiniteSpinSystem d A)
    (t : Finset ι) (f : ι → A) (n : ℕ) :
    bulkOp S (∑ i ∈ t, f i) n = ∑ i ∈ t, bulkOp S (f i) n := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bulkOp_add, ih]

/-- The bulk of a per-site spin operator expands over the shifted even sites:
`(Ŝ_y^{(α)})_n = Σ_{x ∈ Λ_n ∩ ℤᵈ_even} Ŝ_{y+x}^{(α)}`. -/
theorem bulkOp_spin_eq_sum (S : InfiniteSpinSystem d A) (y : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    bulkOp S (S.spin y α) n = ∑ x ∈ evenLatticeBox d n, S.spin (y + x) α := by
  rw [bulkOp_eq_sum_evenLatticeBox]
  exact Finset.sum_congr rfl fun x _ => S.transl_spin x y α

/-- The bulk of a bond spin–spin operator expands over the shifted even sites:
`(Ŝ_y · Ŝ_z)_n = Σ_{x ∈ Λ_n ∩ ℤᵈ_even} Ŝ_{y+x} · Ŝ_{z+x}`. -/
theorem bulkOp_spinDot_eq_sum (S : InfiniteSpinSystem d A) (y z : Fin d → ℤ) (n : ℕ) :
    bulkOp S (spinDot S y z) n = ∑ x ∈ evenLatticeBox d n, spinDot S (y + x) (z + x) := by
  rw [bulkOp_eq_sum_evenLatticeBox]
  exact Finset.sum_congr rfl fun x _ => S.transl_spinDot x y z

end InfiniteSpinSystem

namespace LocalSupportData

variable {S : InfiniteSpinSystem d A} (D : LocalSupportData S)

/-- The bulk of a per-site spin operator is local: supported in the translated
box `Λ_n + y`. -/
theorem bulkOp_spin_mem_localSubalgebra (y : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    InfiniteSpinSystem.bulkOp S (S.spin y α) n ∈
      D.localSubalgebra (InfiniteSpinSystem.translatedLatticeBox d y n) := by
  rw [InfiniteSpinSystem.bulkOp_spin_eq_sum]
  refine sum_mem fun x hx => ?_
  refine D.spin_mem_localSubalgebra_of_mem α ?_
  refine InfiniteSpinSystem.mem_translatedLatticeBox.mpr
    ⟨x, ?_, add_comm x y⟩
  exact InfiniteSpinSystem.evenLatticeBox_subset_latticeBox d n hx

include D in
/-- The bulk of a per-site spin operator is a local observable. -/
theorem bulkOp_spin_mem_localAlg (y : Fin d → ℤ) (α : Fin 3) (n : ℕ) :
    InfiniteSpinSystem.bulkOp S (S.spin y α) n ∈ S.localAlg :=
  D.localSubalgebra_le_localAlg _ (D.bulkOp_spin_mem_localSubalgebra y α n)

/-- The bulk of a bond spin–spin operator is local: supported in the union of the
two translated boxes `(Λ_n + y) ∪ (Λ_n + z)`. -/
theorem bulkOp_spinDot_mem_localSubalgebra (y z : Fin d → ℤ) (n : ℕ) :
    InfiniteSpinSystem.bulkOp S (InfiniteSpinSystem.spinDot S y z) n ∈
      D.localSubalgebra
        (InfiniteSpinSystem.translatedLatticeBox d y n ∪
          InfiniteSpinSystem.translatedLatticeBox d z n) := by
  rw [InfiniteSpinSystem.bulkOp_spinDot_eq_sum]
  refine sum_mem fun x hx => ?_
  have hxlat : x ∈ InfiniteSpinSystem.latticeBox d n :=
    InfiniteSpinSystem.evenLatticeBox_subset_latticeBox d n hx
  refine D.spinDot_mem_localSubalgebra_of_mem ?_ ?_
  · exact Finset.mem_union_left _
      (InfiniteSpinSystem.mem_translatedLatticeBox.mpr ⟨x, hxlat, add_comm x y⟩)
  · exact Finset.mem_union_right _
      (InfiniteSpinSystem.mem_translatedLatticeBox.mpr ⟨x, hxlat, add_comm x z⟩)

include D in
/-- The bulk of a bond spin–spin operator is a local observable. -/
theorem bulkOp_spinDot_mem_localAlg (y z : Fin d → ℤ) (n : ℕ) :
    InfiniteSpinSystem.bulkOp S (InfiniteSpinSystem.spinDot S y z) n ∈ S.localAlg :=
  D.localSubalgebra_le_localAlg _ (D.bulkOp_spinDot_mem_localSubalgebra y z n)

end LocalSupportData

namespace InfiniteSpinSystem.TranslationInvariant

/-- **Bulk expectation in a translation-invariant state**: every even translation
preserves the expectation, so `ω(Â_n) = |Λ_n ∩ ℤᵈ_even| · ω(Â)`. -/
theorem bulkOp_apply_eq_card_mul {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (a : A) (n : ℕ) :
    ω (InfiniteSpinSystem.bulkOp S a n) =
      ((InfiniteSpinSystem.evenLatticeBox d n).card : ℂ) * ω a := by
  rw [InfiniteSpinSystem.bulkOp_eq_sum_evenLatticeBox, map_sum]
  rw [Finset.sum_congr rfl fun x hx =>
    hω a x (InfiniteSpinSystem.mem_evenLatticeBox.mp hx).2]
  rw [Finset.sum_const, nsmul_eq_mul]

end InfiniteSpinSystem.TranslationInvariant

end LatticeSystem.Quantum
