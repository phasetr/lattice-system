import LatticeSystem.Quantum.SpinS.SublatticeSpin
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Sublattice magnetization eigenvalue bound (`|M_z^A| ≤ s_A`)

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

`Ŝ_A^(3)` is diagonal in the basis with eigenvalue
`∑_{x ∈ A} (N/2 − σ_x)` on `|σ⟩`.  Each term lies in `[−N/2, N/2]`, so the
sublattice magnetization lies in `[−s_A, s_A]` with `s_A = |A|·N/2 = |A|·S`
the maximal `A`-sublattice spin.  This is the elementary bound underlying the
highest-weight argument for the sublattice Casimir `(Ŝ_A)²`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The sublattice spin `Ŝ_A^(3)` acts diagonally on a basis state with
eigenvalue `∑_{x ∈ A} (N/2 − σ_x)`. -/
theorem sublatticeSpinSOp3_mulVec_basisVecS (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    (sublatticeSpinSOp3 N A).mulVec (basisVecS σ) =
      (∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
          ((N : ℂ) / 2 - ((σ x).val : ℂ))) • basisVecS σ := by
  classical
  unfold sublatticeSpinSOp3
  rw [Matrix.sum_mulVec]
  rw [Finset.sum_smul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Λ => A x = true)]
  have hzero :
      (∑ x ∈ Finset.univ.filter (fun x : Λ => ¬ A x = true),
          (if A x then (onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N) else 0).mulVec
            (basisVecS σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxnot : ¬ A x = true := (Finset.mem_filter.mp hx).2
    simp [if_neg hxnot]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro x hx
  have hxA : A x = true := (Finset.mem_filter.mp hx).2
  rw [if_pos hxA, onSiteS_spinSOp3_mulVec_basisVecS]

omit [DecidableEq Λ] in
/-- The sublattice magnetization eigenvalue `M_z^A = ∑_{x∈A} (N/2 − σ_x)` is real,
with real part `∑_{x∈A} (N/2 − σ_x)`. -/
theorem sublatticeSpinSOp3_eigenvalue_re (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    (∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))).re =
      ∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
        ((N : ℝ) / 2 - ((σ x).val : ℝ)) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Complex.sub_re]

omit [DecidableEq Λ] in
/-- **Sublattice magnetization bound**: `|M_z^A| ≤ s_A = |A|·N/2`. -/
theorem sublatticeSpinSOp3_eigenvalue_re_abs_le_sA (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    |(∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))).re| ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 := by
  rw [sublatticeSpinSOp3_eigenvalue_re]
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
      |(N : ℝ) / 2 - ((σ x).val : ℝ)| ≤ (N : ℝ) / 2 := by
    intro x _
    have h1 : (0 : ℝ) ≤ ((σ x).val : ℝ) := by positivity
    have h2 : ((σ x).val : ℝ) ≤ (N : ℝ) := by
      have := (σ x).2
      have : (σ x).val ≤ N := by omega
      exact_mod_cast this
    rw [abs_le]
    constructor <;> linarith
  calc
    |∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
        ((N : ℝ) / 2 - ((σ x).val : ℝ))|
        ≤ ∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
            |(N : ℝ) / 2 - ((σ x).val : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : Λ => A x = true), (N : ℝ) / 2 :=
          Finset.sum_le_sum hterm
    _ = ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * ((N : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2 := by ring

end LatticeSystem.Quantum
