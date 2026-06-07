import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity

/-!
# Tasaki 11.5: the raising operator preserves the hard-core subspace (Prop 11.24 E3b PR5c)

`Ŝ⁺_tot` maps the hard-core subspace into itself (mirror of the `Ŝ⁻_tot` version), and so does the
iterated `(Ŝ⁺_tot)^k`.  This keeps every state of the raising tower
`(Ŝ⁺)^k Φ₀` hard-core, a prerequisite for applying the coefficient-sum recursion
(`coeffSum_fermionTotalSpinPlus_eq_of_downEigen`) along the tower.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- **`Ŝ⁺_tot` preserves the hard-core subspace.** -/
theorem fermionTotalSpinPlus_mulVec_mem_hardcore (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    (fermionTotalSpinPlus N).mulVec v ∈ hubbardHardcoreSubspace N := by
  have hself : (hubbardHardcoreProjection N).mulVec ((fermionTotalSpinPlus N).mulVec v)
      = (fermionTotalSpinPlus N).mulVec v := by
    rw [Matrix.mulVec_mulVec,
      (fermionTotalSpinPlus_commute_hubbardHardcoreProjection N).symm.eq,
      ← Matrix.mulVec_mulVec, hubbardHardcoreProjection_mulVec_eq_self_of_mem N hv]
  rw [← hself]
  exact hubbardHardcoreProjection_mulVec_mem N _

/-- The tower `(Ŝ⁺)^k v` stays in the hard-core subspace. -/
theorem fermionTotalSpinPlus_pow_mulVec_mem_hardcore (N : ℕ) (k : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    ((fermionTotalSpinPlus N) ^ k).mulVec v ∈ hubbardHardcoreSubspace N := by
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact fermionTotalSpinPlus_mulVec_mem_hardcore N ih

end LatticeSystem.Fermion
