import LatticeSystem.Fermion.JordanWigner.String

/-!
# Diagonal action of the Jordan–Wigner string on computational basis states

This file provides the foundational infrastructure for computing the action of
Jordan–Wigner operators on computational basis states `basisVec c`, needed for
the Tasaki §11.2 hopping matrix elements (eq. (11.2.4)/(11.2.5)).

The Jordan–Wigner string `jwString N i` is the product of `σ^z` over all modes
below `i`. Since `σ^z = diag(1, -1)` is diagonal in the computational basis,
each factor acts on `basisVec c` by the parity sign `(-1)^{c j}`, and the whole
string acts as the scalar

  `∏_{j < i} (if c j = 0 then 1 else -1)`,

the fermion-parity sign of the occupied modes below `i`. This is the source of
the fermion signs in the hopping matrix elements.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, pp. 382-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-! ## Diagonal Pauli-`Z` action -/

/-- Diagonal entry of `σ^z`: `pauliZ m m = 1` if `m = 0` and `-1` otherwise. -/
private theorem pauliZ_diag (m : Fin 2) :
    pauliZ m m = if m = 0 then (1 : ℂ) else -1 := by
  fin_cases m <;> simp [pauliZ]

/-- Off-diagonal entries of `σ^z` vanish: `pauliZ k m = 0` for `k ≠ m`. -/
private theorem pauliZ_offdiag {k m : Fin 2} (h : k ≠ m) : pauliZ k m = 0 := by
  fin_cases k <;> fin_cases m <;> simp_all [pauliZ]

omit [LinearOrder Λ] in
/-- A single `σ^z` at mode `j` acts on a computational basis state by the
parity sign at `j`: `σ^z_j · |c⟩ = (-1)^{c j} |c⟩`. -/
theorem onSite_pauliZ_mulVec_basisVec (j : Λ) (c : Λ → Fin 2) :
    (onSite j pauliZ).mulVec (basisVec c) =
      (if c j = 0 then (1 : ℂ) else -1) • basisVec c := by
  rw [onSite_mulVec_basisVec]
  funext τ
  rw [Fintype.sum_eq_single (c j) (fun k hk => by
    rw [pauliZ_offdiag hk, zero_mul])]
  rw [Function.update_eq_self, pauliZ_diag]
  simp only [Pi.smul_apply, smul_eq_mul]

/-! ## Diagonal action of a commuting product on a basis state -/

omit [LinearOrder Λ] in
/-- If every factor of a non-commutative product acts on `basisVec c` by a
scalar, the product acts by the product of those scalars. -/
private theorem noncommProd_mulVec_basisVec_of_diagonal
    {ι : Type*} (s : Finset ι) (f : ι → ManyBodyOp Λ)
    (hcomm : (s : Set ι).Pairwise (fun a b => Commute (f a) (f b)))
    (c : Λ → Fin 2) (g : ι → ℂ)
    (hf : ∀ a ∈ s, (f a).mulVec (basisVec c) = g a • basisVec c) :
    (s.noncommProd f hcomm).mulVec (basisVec c) =
      (∏ a ∈ s, g a) • basisVec c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.noncommProd_empty, Finset.prod_empty, one_smul,
      Matrix.one_mulVec]
  | @insert a t hat ih =>
    have hcomm_t : (t : Set ι).Pairwise (fun a b => Commute (f a) (f b)) :=
      hcomm.mono fun x hx => Finset.mem_insert_of_mem hx
    have hf_t : ∀ b ∈ t, (f b).mulVec (basisVec c) = g b • basisVec c :=
      fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hat, Finset.prod_insert hat,
      ← Matrix.mulVec_mulVec, ih hcomm_t hf_t, Matrix.mulVec_smul,
      hf a (Finset.mem_insert_self a t), smul_smul, mul_comm]

/-! ## Diagonal action of the Jordan–Wigner string -/

/-- The Jordan–Wigner string acts on a computational basis state by the
fermion-parity sign of the occupied modes below `i`:
`jwString N i · |c⟩ = (∏_{j < i} (-1)^{c j}) |c⟩`. -/
theorem jwString_mulVec_basisVec (N : ℕ) (i : Fin (N + 1))
    (c : Fin (N + 1) → Fin 2) :
    (jwString N i).mulVec (basisVec c) =
      (∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).filter (fun j => j.val < i.val),
        (if c j = 0 then (1 : ℂ) else -1)) • basisVec c := by
  unfold jwString
  exact noncommProd_mulVec_basisVec_of_diagonal _ _ _ c _
    (fun j _ => onSite_pauliZ_mulVec_basisVec j c)

end LatticeSystem.Fermion
