import LatticeSystem.Fermion.JordanWigner.StringBasisVecAction
import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Action of Jordan–Wigner annihilation/creation operators on basis states

Building on `jwString_mulVec_basisVec`, this file computes the action of the
single-mode Jordan–Wigner annihilation and creation operators on a
computational basis state `basisVec c`, the next ingredient for the Tasaki
§11.2 hopping matrix elements (eq. (11.2.4)/(11.2.5)).

With `c_j = J_j σ^+_j` and `c†_j = J_j σ^-_j` (where `σ^+ = !![0,1;0,0]`,
`σ^- = !![0,0;1,0]` flip the site-`j` occupation) and the diagonal string sign

  `jwSign N j c = ∏_{k < j} (if c k = 0 then 1 else -1)`,

one gets

  `c_j  |c⟩ = if c j = 1 then jwSign N j c • |c with j ↦ 0⟩ else 0`,
  `c†_j |c⟩ = if c j = 0 then jwSign N j c • |c with j ↦ 1⟩ else 0`.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, pp. 382-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## The Jordan–Wigner string sign -/

/-- The Jordan–Wigner string sign at mode `j` for the configuration `c`: the
fermion-parity sign `∏_{k < j} (-1)^{c k}` of the occupied modes below `j`. -/
noncomputable def jwSign (N : ℕ) (j : Fin (N + 1)) (c : Fin (N + 1) → Fin 2) :
    ℂ :=
  ∏ k ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun k => k.val < j.val),
    (if c k = 0 then (1 : ℂ) else -1)

/-- The string sign only depends on the configuration below `j`, so updating
`c` at `j` itself leaves it unchanged. -/
theorem jwSign_update_eq (N : ℕ) (j : Fin (N + 1)) (c : Fin (N + 1) → Fin 2)
    (v : Fin 2) : jwSign N j (Function.update c j v) = jwSign N j c := by
  unfold jwSign
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hkj : k ≠ j := by
    intro h
    simp only [Finset.mem_filter] at hk
    exact absurd (h ▸ hk.2) (by omega)
  rw [Function.update_of_ne hkj]

/-! ## Action of `σ^±` on a basis state -/

/-- The raising matrix `σ^+ = !![0,1;0,0]` lowers the site-`j` occupation:
`σ^+_j |c⟩ = |c with j ↦ 0⟩` if `c j = 1`, else `0`. -/
theorem onSite_spinHalfOpPlus_mulVec_basisVec (N : ℕ) (j : Fin (N + 1))
    (c : Fin (N + 1) → Fin 2) :
    (onSite j spinHalfOpPlus).mulVec (basisVec c) =
      if c j = 1 then basisVec (Function.update c j 0) else 0 := by
  rw [onSite_mulVec_basisVec]
  funext τ
  by_cases hcj : c j = 1
  · rw [hcj, if_pos rfl]
    rw [Fintype.sum_eq_single (0 : Fin 2) (fun k hk => by
      fin_cases k <;> simp_all [spinHalfOpPlus])]
    simp [spinHalfOpPlus]
  · rw [if_neg hcj]
    have hcj0 : c j = 0 := by
      have h2 := (c j).isLt
      exact Fin.ext (by have : (c j).val ≠ 1 := fun h => hcj (Fin.ext h); omega)
    apply Finset.sum_eq_zero
    intro k _
    rw [hcj0]
    fin_cases k <;> simp [spinHalfOpPlus]

/-- The lowering matrix `σ^- = !![0,0;1,0]` raises the site-`j` occupation:
`σ^-_j |c⟩ = |c with j ↦ 1⟩` if `c j = 0`, else `0`. -/
theorem onSite_spinHalfOpMinus_mulVec_basisVec (N : ℕ) (j : Fin (N + 1))
    (c : Fin (N + 1) → Fin 2) :
    (onSite j spinHalfOpMinus).mulVec (basisVec c) =
      if c j = 0 then basisVec (Function.update c j 1) else 0 := by
  rw [onSite_mulVec_basisVec]
  funext τ
  by_cases hcj : c j = 0
  · rw [hcj, if_pos rfl]
    rw [Fintype.sum_eq_single (1 : Fin 2) (fun k hk => by
      fin_cases k <;> simp_all [spinHalfOpMinus])]
    simp [spinHalfOpMinus]
  · rw [if_neg hcj]
    have hcj1 : c j = 1 := by
      have h2 := (c j).isLt
      exact Fin.ext (by have : (c j).val ≠ 0 := fun h => hcj (Fin.ext h); omega)
    apply Finset.sum_eq_zero
    intro k _
    rw [hcj1]
    fin_cases k <;> simp [spinHalfOpMinus]

/-! ## Action of annihilation/creation on a basis state -/

/-- Action of the annihilation operator on a basis state:
`c_j |c⟩ = jwSign N j c • |c with j ↦ 0⟩` if `c j = 1`, else `0`. -/
theorem fermionMultiAnnihilation_mulVec_basisVec (N : ℕ) (j : Fin (N + 1))
    (c : Fin (N + 1) → Fin 2) :
    (fermionMultiAnnihilation N j).mulVec (basisVec c) =
      if c j = 1 then jwSign N j c • basisVec (Function.update c j 0) else 0 := by
  unfold fermionMultiAnnihilation
  rw [← Matrix.mulVec_mulVec, onSite_spinHalfOpPlus_mulVec_basisVec]
  by_cases hcj : c j = 1
  · rw [if_pos hcj, if_pos hcj, jwString_mulVec_basisVec]
    congr 1
    exact jwSign_update_eq N j c 0
  · rw [if_neg hcj, if_neg hcj, Matrix.mulVec_zero]

/-- Action of the creation operator on a basis state:
`c†_j |c⟩ = jwSign N j c • |c with j ↦ 1⟩` if `c j = 0`, else `0`. -/
theorem fermionMultiCreation_mulVec_basisVec (N : ℕ) (j : Fin (N + 1))
    (c : Fin (N + 1) → Fin 2) :
    (fermionMultiCreation N j).mulVec (basisVec c) =
      if c j = 0 then jwSign N j c • basisVec (Function.update c j 1) else 0 := by
  unfold fermionMultiCreation
  rw [← Matrix.mulVec_mulVec, onSite_spinHalfOpMinus_mulVec_basisVec]
  by_cases hcj : c j = 0
  · rw [if_pos hcj, if_pos hcj, jwString_mulVec_basisVec]
    congr 1
    exact jwSign_update_eq N j c 1
  · rw [if_neg hcj, if_neg hcj, Matrix.mulVec_zero]

end LatticeSystem.Fermion
