import LatticeSystem.Math.PosSemidef.Kernel

/-!
# Kernel propagation for PSD solutions of a ground-state Lyapunov equation

This is the analytic heart of Tasaki Lemma 10.10 (Lieb's spin-reflection-positivity
proof for the attractive Hubbard model). A positive-semidefinite matrix `R` that
solves the minimal-energy equation

  `A·R + R·Aᴴ − Σ_x U_x·(I_x·R·I_x) = E·R`     (`U_x > 0`, `I_x`, `A` Hermitian)

has a kernel that is **invariant under each `I_x` and under `A`**: if `R v = 0` then
`R (I_x v) = 0` for every `x` and `R (A v) = 0`.

The mechanism is purely a positive-semidefinite argument: sandwiching the equation by
`v` annihilates the kinetic part (`R v = 0`), leaving `Σ_x U_x ⟨I_x v, R I_x v⟩ = 0`;
since each summand is nonnegative and `U_x > 0`, each `⟨I_x v, R I_x v⟩ = 0`, hence
`R (I_x v) = 0` (Tasaki Lemma A.11). Feeding this back into the equation applied to `v`
gives `R (Aᴴ v) = 0`, i.e. `R (A v) = 0` for Hermitian `A`.

## Main result

* `posSemidef_ground_kernel_propagation` — `R v = 0 ⟹ (∀ x, R (I_x v) = 0) ∧ R (A v) = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Math

open Matrix
open scoped BigOperators ComplexOrder

variable {S ι : Type*} [Fintype S] [Fintype ι]

/-- For a Hermitian `M`, the sesquilinear form is self-adjoint:
`⟨v, M w⟩ = ⟨M v, w⟩`. -/
private theorem hermitian_dotProduct_swap {M : Matrix S S ℂ} (hM : M.IsHermitian)
    (v w : S → ℂ) :
    star v ⬝ᵥ M.mulVec w = star (M.mulVec v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, Matrix.star_mulVec, hM.eq]

/-- **Kernel propagation for PSD solutions of the ground-state Lyapunov equation.**
If `R ≥ 0` solves `A·R + R·Aᴴ − Σ_x U_x·(I_x·R·I_x) = E·R` with `U_x > 0`, `A` and each
`I_x` Hermitian, and `R v = 0`, then `R (I_x v) = 0` for every `x` and `R (A v) = 0`. -/
theorem posSemidef_ground_kernel_propagation
    {A R : Matrix S S ℂ} {I : ι → Matrix S S ℂ} {U : ι → ℝ} {E : ℝ}
    (hA : A.IsHermitian) (hI : ∀ x, (I x).IsHermitian) (hR : R.PosSemidef)
    (hU : ∀ x, 0 < U x)
    (hEq : A * R + R * Aᴴ - ∑ x, (U x : ℂ) • (I x * R * I x) = (E : ℂ) • R)
    {v : S → ℂ} (hv : R.mulVec v = 0) :
    (∀ x, R.mulVec ((I x).mulVec v) = 0) ∧ R.mulVec (A.mulVec v) = 0 := by
  -- The equation applied to `v` as a vector.
  have hvec : R.mulVec (Aᴴ.mulVec v)
      - ∑ x, (U x : ℂ) • (I x).mulVec (R.mulVec ((I x).mulVec v)) = 0 := by
    have h := congrArg (fun M : Matrix S S ℂ => M.mulVec v) hEq
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, smul_zero, zero_add] at h
    exact h
  -- Each interaction summand's energy vanishes.
  have hquad : ∀ x, star ((I x).mulVec v) ⬝ᵥ R.mulVec ((I x).mulVec v) = 0 := by
    have hsand : ∑ x, (U x : ℂ) *
        (star ((I x).mulVec v) ⬝ᵥ R.mulVec ((I x).mulVec v)) = 0 := by
      have hLHS := congrArg (fun w => star v ⬝ᵥ w) hvec
      simp only [dotProduct_zero, dotProduct_sub, dotProduct_sum, dotProduct_smul,
        smul_eq_mul] at hLHS
      rw [hermitian_dotProduct_swap hR.1, hv, star_zero, zero_dotProduct, zero_sub,
        neg_eq_zero] at hLHS
      rw [← hLHS]
      exact Finset.sum_congr rfl (fun x _ => by rw [hermitian_dotProduct_swap (hI x)])
    have hnonneg : ∀ x ∈ Finset.univ, (0 : ℂ) ≤ (U x : ℂ) *
        (star ((I x).mulVec v) ⬝ᵥ R.mulVec ((I x).mulVec v)) := fun x _ =>
      mul_nonneg (by exact_mod_cast (hU x).le) (hR.dotProduct_mulVec_nonneg _)
    intro x
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsand x (Finset.mem_univ x)
    exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast (hU x).ne')
  -- PSD ⟹ the kernel contains each `I_x v`.
  have hIker : ∀ x, R.mulVec ((I x).mulVec v) = 0 := fun x =>
    posSemidef_mulVec_eq_zero_of_inner_zero hR (hquad x)
  refine ⟨hIker, ?_⟩
  -- Feed back into `hvec`: the interaction sum vanishes, leaving `R (Aᴴ v) = 0`.
  have hAH : R.mulVec (Aᴴ.mulVec v) = 0 := by
    have hsum0 : ∑ x, (U x : ℂ) • (I x).mulVec (R.mulVec ((I x).mulVec v)) = 0 :=
      Finset.sum_eq_zero (fun x _ => by rw [hIker x, Matrix.mulVec_zero, smul_zero])
    rw [hsum0, sub_zero] at hvec
    exact hvec
  rwa [hA.eq] at hAH

end LatticeSystem.Math
