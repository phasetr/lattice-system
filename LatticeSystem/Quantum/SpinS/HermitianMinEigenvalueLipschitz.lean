import LatticeSystem.Quantum.SpinS.RayleighRitzEquality
import LatticeSystem.Quantum.SpinS.RayleighOnVecBddBelow

/-!
# Lipschitz continuity of `hermitianMinEigenvalue` in matrix entries

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

For Hermitian matrices `A, B`, the minimum eigenvalue is Lipschitz in the
sum-of-entry-norms metric:
`|hermitianMinEigenvalue hA - hermitianMinEigenvalue hB| ≤ Σ_{i,j} ‖(A - B)_{ij}‖`.

Proof: by Rayleigh-Ritz (PR #3951), `hermitianMinEigenvalue = rayleighInfMatrix`.
Use additivity of `rayleighOnVec` (PR #3940) and the entry-norm bound (PR #3947)
to get `rayleighInfMatrix B ≤ rayleighInfMatrix A + Σ ‖(B - A)_{ij}‖`, then
symmetrise.

This Lipschitz bound directly implies continuity of `hermitianMinEigenvalue`
in `M`, the analytic ingredient needed by the obligation (2) deformation
argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Helper: for Hermitian `A` and `B`, the upper bound
`rayleighInfMatrix B ≤ rayleighInfMatrix A + Σ ‖(B - A)_{ij}‖`. -/
theorem rayleighInfMatrix_le_add_sum_entryNorms
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) :
    rayleighInfMatrix B ≤ rayleighInfMatrix A + ∑ i, ∑ j, ‖(B - A) i j‖ := by
  -- For each p in unit sphere:
  --   rayleighOnVec B p.val = rayleighOnVec A p.val + rayleighOnVec (B-A) p.val (additive)
  --                        ≤ rayleighOnVec A p.val + Σ ‖(B-A)_ij‖.
  -- Hence rayleighInfMatrix B ≤ rayleighOnVec B p.val ≤ rayleighOnVec A p.val + Σ ‖(B-A)_ij‖.
  -- Taking iInf over p in unit sphere: rayleighInfMatrix B ≤ rayleighInfMatrix A + Σ ‖(B-A)_ij‖.
  haveI : Nonempty {v : n → ℂ // dotProduct (star v) v = 1} :=
    nonempty_unit_dotProduct_subtype hA
  -- For each p, rayleighInfMatrix B - Σ ‖(B-A)_ij‖ ≤ rayleighOnVec A p.val
  have key : ∀ p : {v : n → ℂ // dotProduct (star v) v = 1},
      rayleighInfMatrix B - (∑ i, ∑ j, ‖(B - A) i j‖) ≤ rayleighOnVec A p.val := by
    intro p
    have h1 : rayleighInfMatrix B ≤ rayleighOnVec B p.val :=
      rayleighInfMatrix_le_rayleighOnVec_of_bddBelow B
        (rayleighOnVec_bddBelow_on_unit_sphere B) p.property
    -- rayleighOnVec B = rayleighOnVec A + rayleighOnVec (B - A)
    have hadd : rayleighOnVec B p.val =
        rayleighOnVec A p.val + rayleighOnVec (B - A) p.val := by
      conv_lhs => rw [show B = A + (B - A) from by abel]
      exact rayleighOnVec_add_matrix _ _ _
    have h2 : rayleighOnVec (B - A) p.val ≤ ∑ i, ∑ j, ‖(B - A) i j‖ :=
      le_of_abs_le (abs_rayleighOnVec_le_sum_entryNorms_of_unit (B - A) p.property)
    linarith
  -- Take iInf over p
  have hinf : rayleighInfMatrix B - (∑ i, ∑ j, ‖(B - A) i j‖) ≤ rayleighInfMatrix A := by
    unfold rayleighInfMatrix
    exact le_ciInf key
  linarith

/-- **Lipschitz continuity** of `rayleighInfMatrix` in the entry-norm sum:
`|rayleighInfMatrix A - rayleighInfMatrix B| ≤ Σ ‖(A - B)_{ij}‖`. -/
theorem abs_rayleighInfMatrix_sub_le_sum_entryNorms
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |rayleighInfMatrix A - rayleighInfMatrix B| ≤ ∑ i, ∑ j, ‖(A - B) i j‖ := by
  have hAB := rayleighInfMatrix_le_add_sum_entryNorms (A := A) (B := B) hA
  have hBA := rayleighInfMatrix_le_add_sum_entryNorms (A := B) (B := A) hB
  -- Σ ‖(B - A)_ij‖ = Σ ‖(A - B)_ij‖
  have hsym : (∑ i, ∑ j, ‖(B - A) i j‖) = ∑ i, ∑ j, ‖(A - B) i j‖ := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show (B - A) i j = -((A - B) i j) from by rw [Matrix.sub_apply, Matrix.sub_apply]; ring,
        norm_neg]
  rw [hsym] at hAB
  -- |x - y| ≤ c iff x - y ≤ c ∧ y - x ≤ c
  apply abs_sub_le_iff.mpr
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **Lipschitz continuity of `hermitianMinEigenvalue`** in the entry-norm sum, via
the Rayleigh-Ritz equality (PR #3951):
`|hermitianMinEigenvalue hA - hermitianMinEigenvalue hB| ≤ Σ ‖(A - B)_{ij}‖`. -/
theorem abs_hermitianMinEigenvalue_sub_le_sum_entryNorms
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |hermitianMinEigenvalue hA - hermitianMinEigenvalue hB| ≤ ∑ i, ∑ j, ‖(A - B) i j‖ := by
  rw [← rayleighInfMatrix_eq_hermitianMinEigenvalue hA,
      ← rayleighInfMatrix_eq_hermitianMinEigenvalue hB]
  exact abs_rayleighInfMatrix_sub_le_sum_entryNorms hA hB

end LatticeSystem.Quantum
