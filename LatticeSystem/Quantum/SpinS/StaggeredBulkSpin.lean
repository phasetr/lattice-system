import LatticeSystem.Quantum.SpinS.EvenLatticeBoxCard
import LatticeSystem.Quantum.SpinS.PhysicalGroundStateConsequences

/-!
# Tasaki §4.3.1: the staggered (Néel) bulk observable

The order parameter of the antiferromagnetic Heisenberg model is the **staggered**
magnetization.  Restricting the translation average to the even sublattice (as in
Tasaki's bulk operator `Â_n`, eq. (4.3.5)), the relevant cell observable is the
even-cell difference `Ŝ_0^{(α)} − Ŝ_u^{(α)}` between the A-site `0` and an odd
neighbour `u` (`staggeredSign u = −1`).  Its bulk average and density detect Néel
order:

* on the symmetric ground state `ω_0` (zero single-site magnetization, eq. (4.3.9))
  the staggered bulk density vanishes;
* on a symmetry-breaking ground state `ω_n` with Néel magnetization
  `ω(Ŝ_x^{(α)}) = (−1)^x m_* n_α` (eq. (4.3.10)) the staggered bulk density equals
  `m_* n_α`.

Everything is proved **axiom-free**: the magnetization values enter as
*hypotheses* (matching the conclusions of Theorem 4.20, but not asserting them),
so no axiom is added or discharged.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1, eqs. (4.3.5), (4.3.9), (4.3.10), pp. 112–115.
-/

namespace LatticeSystem.Quantum

variable {d : ℕ} {A : Type*} [CStarAlgebra A]

namespace InfiniteSpinSystem

/-- The support of the staggered cell observable: the two sites `{0, u}`. -/
def staggeredCellSupport (u : Fin d → ℤ) : Finset (Fin d → ℤ) := {0, u}

/-- The **staggered cell observable** `Ŝ_0^{(α)} − Ŝ_u^{(α)}`: the difference of
the spin at the A-site `0` and at the (odd) site `u` (Tasaki §4.3.1, the Néel
order-parameter cell). -/
noncomputable def staggeredCellSpin (S : InfiniteSpinSystem d A) (u : Fin d → ℤ) (α : Fin 3) : A :=
  S.spin 0 α - S.spin u α

/-- The **staggered bulk observable** `(Ŝ_0^{(α)} − Ŝ_u^{(α)})_n`: the bulk average
of the staggered cell observable over the even sites of `Λ_n`. -/
noncomputable def staggeredBulkSpin (S : InfiniteSpinSystem d A) (u : Fin d → ℤ)
    (α : Fin 3) (n : ℕ) : A :=
  bulkOp S (staggeredCellSpin S u α) n

/-- The **staggered bulk density** `(Ŝ_0^{(α)} − Ŝ_u^{(α)})_n / Lᵈ`. -/
noncomputable def staggeredBulkSpinDensity (S : InfiniteSpinSystem d A) (u : Fin d → ℤ)
    (α : Fin 3) (n : ℕ) : A :=
  bulkDensity S (staggeredCellSpin S u α) n

/-- The staggered bulk observable splits as a difference of single-site bulks. -/
theorem staggeredBulkSpin_eq_bulkOp_sub (S : InfiniteSpinSystem d A) (u : Fin d → ℤ)
    (α : Fin 3) (n : ℕ) :
    staggeredBulkSpin S u α n = bulkOp S (S.spin 0 α) n - bulkOp S (S.spin u α) n := by
  simp [staggeredBulkSpin, staggeredCellSpin, bulkOp_eq_sum_evenLatticeBox, map_sub,
    Finset.sum_sub_distrib]

/-- The staggered bulk observable expands over the shifted even sites:
`Σ_{x ∈ Λ_n ∩ ℤᵈ_even} (Ŝ_x^{(α)} − Ŝ_{u+x}^{(α)})`. -/
theorem staggeredBulkSpin_eq_sum (S : InfiniteSpinSystem d A) (u : Fin d → ℤ)
    (α : Fin 3) (n : ℕ) :
    staggeredBulkSpin S u α n =
      ∑ x ∈ evenLatticeBox d n, (S.spin x α - S.spin (u + x) α) := by
  rw [staggeredBulkSpin, staggeredCellSpin, bulkOp_eq_sum_evenLatticeBox]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sub, S.transl_spin, S.transl_spin, zero_add]

/-- `staggeredSign` of the origin is `+1` (the A-site). -/
theorem staggeredSign_zero : staggeredSign (0 : Fin d → ℤ) = 1 := by
  simp [staggeredSign]

namespace TranslationInvariant

variable {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}

/-- In a translation-invariant state and `n ≥ 1`, the staggered bulk density is
half the cell expectation. -/
theorem staggeredBulkSpinDensity_apply_eq_half_mul
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (u : Fin d → ℤ) (α : Fin 3) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n) :
    ω (staggeredBulkSpinDensity S u α n) = (1 / 2 : ℂ) * ω (staggeredCellSpin S u α) :=
  hω.bulkDensity_apply_eq_half_mul (staggeredCellSpin S u α) hd hn

end TranslationInvariant

/-- **Symmetric case (eq. (4.3.9))**: if the state has vanishing single-site
magnetization, the staggered cell observable has zero expectation. -/
theorem staggeredCellSpin_apply_of_zero_magnetization {S : InfiniteSpinSystem d A}
    {ω : WeakDual ℂ A} (u : Fin d → ℤ) (α : Fin 3)
    (hzero : ∀ (x : Fin d → ℤ) (β : Fin 3), ω (S.spin x β) = 0) :
    ω (staggeredCellSpin S u α) = 0 := by
  simp [staggeredCellSpin, map_sub, hzero]

/-- **Néel case (eq. (4.3.10))**: with `staggeredSign u = −1` and the Néel
single-site magnetization, the staggered cell observable has expectation
`2 m_* n_α`. -/
theorem staggeredCellSpin_apply_of_staggered_magnetization {S : InfiniteSpinSystem d A}
    {ω : WeakDual ℂ A} {mStar : ℝ} {nvec : Fin 3 → ℝ} {u : Fin d → ℤ}
    (hu : staggeredSign u = -1) (α : Fin 3)
    (hmag : ∀ (x : Fin d → ℤ) (β : Fin 3),
      ω (S.spin x β) = ((staggeredSign x : ℝ) : ℂ) * (mStar : ℂ) * (nvec β : ℂ)) :
    ω (staggeredCellSpin S u α) = 2 * (mStar : ℂ) * (nvec α : ℂ) := by
  rw [staggeredCellSpin, map_sub, hmag 0 α, hmag u α, hu, staggeredSign_zero]
  push_cast
  ring

namespace TranslationInvariant

variable {S : InfiniteSpinSystem d A} {ω : WeakDual ℂ A}

/-- The staggered bulk density vanishes on a symmetric (zero-magnetization)
translation-invariant state (`n ≥ 1`). -/
theorem staggeredBulkSpinDensity_apply_of_zero_magnetization
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) (u : Fin d → ℤ) (α : Fin 3) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n)
    (hzero : ∀ (x : Fin d → ℤ) (β : Fin 3), ω (S.spin x β) = 0) :
    ω (staggeredBulkSpinDensity S u α n) = 0 := by
  rw [hω.staggeredBulkSpinDensity_apply_eq_half_mul u α hd hn,
    staggeredCellSpin_apply_of_zero_magnetization u α hzero, mul_zero]

/-- The staggered bulk density equals the Néel order parameter `m_* n_α` on a
symmetry-breaking translation-invariant state (`staggeredSign u = −1`, `n ≥ 1`). -/
theorem staggeredBulkSpinDensity_apply_of_staggered_magnetization
    (hω : InfiniteSpinSystem.TranslationInvariant S ω) {mStar : ℝ} {nvec : Fin 3 → ℝ}
    {u : Fin d → ℤ} (hu : staggeredSign u = -1) (α : Fin 3) {n : ℕ}
    (hd : 0 < d) (hn : 0 < n)
    (hmag : ∀ (x : Fin d → ℤ) (β : Fin 3),
      ω (S.spin x β) = ((staggeredSign x : ℝ) : ℂ) * (mStar : ℂ) * (nvec β : ℂ)) :
    ω (staggeredBulkSpinDensity S u α n) = (mStar : ℂ) * (nvec α : ℂ) := by
  rw [hω.staggeredBulkSpinDensity_apply_eq_half_mul u α hd hn,
    staggeredCellSpin_apply_of_staggered_magnetization hu α hmag]
  ring

end TranslationInvariant

end InfiniteSpinSystem

namespace LocalSupportData

variable {S : InfiniteSpinSystem d A} (D : LocalSupportData S)

/-- The staggered cell observable is supported on `{0, u}`. -/
theorem staggeredCellSpin_mem_localSubalgebra (u : Fin d → ℤ) (α : Fin 3) :
    InfiniteSpinSystem.staggeredCellSpin S u α ∈
      D.localSubalgebra (InfiniteSpinSystem.staggeredCellSupport u) := by
  rw [InfiniteSpinSystem.staggeredCellSpin]
  refine sub_mem (D.spin_mem_localSubalgebra_of_mem α ?_) (D.spin_mem_localSubalgebra_of_mem α ?_)
  · exact Finset.mem_insert_self 0 {u}
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self u)

include D in
/-- The staggered cell observable is a local observable. -/
theorem staggeredCellSpin_mem_localAlg (u : Fin d → ℤ) (α : Fin 3) :
    InfiniteSpinSystem.staggeredCellSpin S u α ∈ S.localAlg :=
  D.localSubalgebra_le_localAlg _ (D.staggeredCellSpin_mem_localSubalgebra u α)

end LocalSupportData

namespace InfiniteSpinSystem.IsPhysicalGroundState

variable {S : InfiniteSpinSystem d A} {εGS : ℝ} {ω : WeakDual ℂ A}

/-- In a physical ground state the staggered-cell bulk-density fluctuation vanishes
(conditional on self-adjointness of the cell observable). -/
theorem tendsto_staggeredCellSpin_bulkDensityFluctuation
    (hω : InfiniteSpinSystem.IsPhysicalGroundState S εGS ω) (D : LocalSupportData S)
    (u : Fin d → ℤ) (α : Fin 3)
    (hsa : IsSelfAdjoint (InfiniteSpinSystem.staggeredCellSpin S u α)) :
    Filter.Tendsto (fun n : ℕ =>
      InfiniteSpinSystem.bulkDensityFluctuation S ω
        (InfiniteSpinSystem.staggeredCellSpin S u α) (n + 1))
      Filter.atTop (nhds 0) :=
  hω.tendsto_bulkDensityFluctuation (D.staggeredCellSpin_mem_localAlg u α) hsa

end InfiniteSpinSystem.IsPhysicalGroundState

end LatticeSystem.Quantum
