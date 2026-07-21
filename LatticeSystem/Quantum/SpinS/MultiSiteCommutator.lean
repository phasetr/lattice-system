import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.CyclicCommutator

/-!
# Multi-site spin-`S` same-site commutators
(Tasaki §2.5 Phase B-β β-3k)

Lifts the single-site SU(2) cyclic commutators (Issue #458 β-20/21/22)

  `[Ŝ^{(1)}, Ŝ^{(2)}] = i Ŝ^{(3)}`,
  `[Ŝ^{(2)}, Ŝ^{(3)}] = i Ŝ^{(1)}`,
  `[Ŝ^{(3)}, Ŝ^{(1)}] = i Ŝ^{(2)}`,

to the multi-site Hilbert space at a single site `x : Λ`:

  `[Ŝ_x^{(1)}, Ŝ_x^{(2)}] = i Ŝ_x^{(3)}`, etc.

Also exposes the general "same-site lifting" identity

  `[onSiteS i A, onSiteS i B] = onSiteS i [A, B]`,

which is an immediate corollary of `onSiteS_mul_onSiteS_same` (β-3d).
This is the diagonal (`x = y`) case of Tasaki eq. (2.2.6) for general spin.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Same-site commutator: `[onSiteS i A, onSiteS i B] = onSiteS i [A, B]`. -/
theorem onSiteS_commutator_same (i : Λ)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS i B - onSiteS i B * onSiteS i A : ManyBodyOpS Λ N) =
      onSiteS i (A * B - B * A) := by
  rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same, ← onSiteS_sub]

/-- Same-site SU(2) cyclic commutator at axis `(1, 2) → 3`. -/
theorem spinSOp1_onSiteS_commutator_spinSOp2_onSiteS (x : Λ) :
    (onSiteS x (spinSOp1 N) * onSiteS x (spinSOp2 N)
        - onSiteS x (spinSOp2 N) * onSiteS x (spinSOp1 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp3 N) := by
  rw [onSiteS_commutator_same, spinSOp1_commutator_spinSOp2, onSiteS_smul]

/-- Same-site SU(2) cyclic commutator at axis `(2, 3) → 1`. -/
theorem spinSOp2_onSiteS_commutator_spinSOp3_onSiteS (x : Λ) :
    (onSiteS x (spinSOp2 N) * onSiteS x (spinSOp3 N)
        - onSiteS x (spinSOp3 N) * onSiteS x (spinSOp2 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp1 N) := by
  rw [onSiteS_commutator_same, spinSOp2_commutator_spinSOp3, onSiteS_smul]

/-- Same-site SU(2) cyclic commutator at axis `(3, 1) → 2`. -/
theorem spinSOp3_onSiteS_commutator_spinSOp1_onSiteS (x : Λ) :
    (onSiteS x (spinSOp3 N) * onSiteS x (spinSOp1 N)
        - onSiteS x (spinSOp1 N) * onSiteS x (spinSOp3 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp2 N) := by
  rw [onSiteS_commutator_same, spinSOp3_commutator_spinSOp1, onSiteS_smul]

/-! ## Total-spin commutators for arbitrary spin -/

/-- General total-spin commutator: if `[A, B] = I • C` then
`[Σ_x onSiteS x A, Σ_x onSiteS x B] = I • Σ_x onSiteS x C`. -/
theorem totalSpinS_commutator_general
    {N : ℕ} {A B C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hab : A * B - B * A = Complex.I • C) :
    ((∑ x : Λ, onSiteS x A : ManyBodyOpS Λ N) * (∑ x : Λ, onSiteS x B)
        - (∑ x : Λ, onSiteS x B) * (∑ x : Λ, onSiteS x A)) =
      Complex.I • ∑ x : Λ, onSiteS x C := by
  calc (∑ x : Λ, onSiteS x A : ManyBodyOpS Λ N) * (∑ x : Λ, onSiteS x B)
          - (∑ x : Λ, onSiteS x B) * (∑ x : Λ, onSiteS x A)
      = ∑ x : Λ, ∑ y : Λ,
          (onSiteS x A * onSiteS y B - onSiteS y B * onSiteS x A) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm
            (f := fun y x => (onSiteS y B : ManyBodyOpS Λ N) * onSiteS x A)
            (s := Finset.univ) (t := Finset.univ)]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
    _ = ∑ x : Λ, (Complex.I • onSiteS x C : ManyBodyOpS Λ N) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single x]
        · rw [onSiteS_commutator_same, hab, onSiteS_smul]
        · intros y _ hyx
          rw [onSiteS_mul_onSiteS_of_ne hyx.symm]
          simp
        · intro h; exact absurd (Finset.mem_univ x) h
    _ = Complex.I • ∑ x : Λ, (onSiteS x C : ManyBodyOpS Λ N) := by
        rw [← Finset.smul_sum]

/-- Total-spin SU(2) commutator: `[Ŝ_tot^{(1)}, Ŝ_tot^{(2)}] = i Ŝ_tot^{(3)}`. -/
theorem totalSpinSOp1_commutator_totalSpinSOp2 (N : ℕ) :
    ((∑ x : Λ, onSiteS x (spinSOp1 N) : ManyBodyOpS Λ N) *
        (∑ x : Λ, onSiteS x (spinSOp2 N))
        - (∑ x : Λ, onSiteS x (spinSOp2 N)) *
            (∑ x : Λ, onSiteS x (spinSOp1 N))) =
      Complex.I • ∑ x : Λ, onSiteS x (spinSOp3 N) :=
  totalSpinS_commutator_general (Λ := Λ) (spinSOp1_commutator_spinSOp2 N)

/-- Total-spin SU(2) commutator: `[Ŝ_tot^{(2)}, Ŝ_tot^{(3)}] = i Ŝ_tot^{(1)}`. -/
theorem totalSpinSOp2_commutator_totalSpinSOp3 (N : ℕ) :
    ((∑ x : Λ, onSiteS x (spinSOp2 N) : ManyBodyOpS Λ N) *
        (∑ x : Λ, onSiteS x (spinSOp3 N))
        - (∑ x : Λ, onSiteS x (spinSOp3 N)) *
            (∑ x : Λ, onSiteS x (spinSOp2 N))) =
      Complex.I • ∑ x : Λ, onSiteS x (spinSOp1 N) :=
  totalSpinS_commutator_general (Λ := Λ) (spinSOp2_commutator_spinSOp3 N)

/-- Total-spin SU(2) commutator: `[Ŝ_tot^{(3)}, Ŝ_tot^{(1)}] = i Ŝ_tot^{(2)}`. -/
theorem totalSpinSOp3_commutator_totalSpinSOp1 (N : ℕ) :
    ((∑ x : Λ, onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N) *
        (∑ x : Λ, onSiteS x (spinSOp1 N))
        - (∑ x : Λ, onSiteS x (spinSOp1 N)) *
            (∑ x : Λ, onSiteS x (spinSOp3 N))) =
      Complex.I • ∑ x : Λ, onSiteS x (spinSOp2 N) :=
  totalSpinS_commutator_general (Λ := Λ) (spinSOp3_commutator_spinSOp1 N)

/-- For any single-site operator `onSiteS x A` and any
total-spin-like sum `Σ_z onSiteS z B`, the commutator concentrates
at site `x`:

  `[onSiteS x A, Σ_z onSiteS z B] = onSiteS x [A, B]`.

The off-site terms vanish by `onSiteS_mul_onSiteS_of_ne` (β-3b),
and the on-site term collapses via `onSiteS_mul_onSiteS_same` (β-3d). -/
theorem onSiteS_commutator_totalOnSiteS
    (x : Λ) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS x A : ManyBodyOpS Λ N) * (∑ z : Λ, onSiteS z B)
        - (∑ z : Λ, onSiteS z B) * onSiteS x A =
      onSiteS x (A * B - B * A) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single x]
  · rw [onSiteS_mul_onSiteS_same, onSiteS_mul_onSiteS_same, ← onSiteS_sub]
  · intros z _ hzx
    rw [onSiteS_mul_onSiteS_of_ne hzx.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ x) h

end LatticeSystem.Quantum
