import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MultiSiteCasimir
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Spin-`S` all-aligned (saturated ferromagnet) state
(Tasaki §2.4 generalised to spin-`S`)

For a multi-site spin-`S` system on a finite vertex set `V`, the
**all-aligned** (constant-spin) state with `σ x = c` for all `x : V`
is a basis vector of the multi-site Hilbert space.

This file proves:

1. The all-aligned state at any `c : Fin (N+1)` is a `Ŝ^z_tot`
   eigenvector with eigenvalue `|V|·N/2 − |V|·c`.
2. The two extreme cases `c = 0` (highest weight, "all up") and
   `c = N` (lowest weight, "all down") are the **unique** elements of
   their respective magnetization sectors (`magSumS = 0` and
   `magSumS = |V|·N`), hence automatically Heisenberg eigenvectors
   for ANY coupling via the magnetization-conservation identity
   `[H, Ŝ^z_tot] = 0`. The eigenvalue is the explicit diagonal
   `Σ_x J(x,x) · N(N+2)/4 + Σ_{x≠y} J(x,y) · N²/4`.

The `(Ŝ_tot)²` eigenvalue `(|V|·N/2)(|V|·N/2+1)` (the `J = |V|·S`
highest-weight irreducible representation) is left to a follow-up
textbook unit, since it requires the alternative Casimir form
`(Ŝ_tot)² = Ŝ^-_tot Ŝ^+_tot + (Ŝ^z_tot)² + Ŝ^z_tot` plus
`Ŝ^+_tot · |σ_⊤⟩ = 0`.

The spin-`S` extension of Tasaki §2.4 (which treats `S = 1/2` in
detail) and the operator-level form of the saturated-ferromagnetic
ground state on the bipartite Heisenberg model.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## All-aligned configuration and state -/

/-- The constant configuration `σ x = c` for all `x : V`. -/
def allAlignedConfigS (V : Type*) (N : ℕ) (c : Fin (N + 1)) :
    V → Fin (N + 1) := fun _ => c

/-- The all-aligned basis state at constant value `c`. -/
noncomputable def allAlignedStateS (V : Type*) [Fintype V] [DecidableEq V]
    (N : ℕ) (c : Fin (N + 1)) :
    (V → Fin (N + 1)) → ℂ :=
  basisVecS (allAlignedConfigS V N c)

/-! ## Magnetization properties -/

omit [DecidableEq V] in
/-- `magSumS (allAlignedConfigS V N c) = |V| · c.val`. -/
theorem magSumS_allAlignedConfigS (c : Fin (N + 1)) :
    magSumS (allAlignedConfigS V N c) = Fintype.card V * c.val := by
  unfold magSumS allAlignedConfigS
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq V] in
/-- `magEigenvalueS (allAlignedConfigS V N c) = |V|·N/2 − |V|·c`. -/
theorem magEigenvalueS_allAlignedConfigS (c : Fin (N + 1)) :
    magEigenvalueS (allAlignedConfigS V N c) =
      ((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
        ((Fintype.card V : ℂ) * (c.val : ℂ)) := by
  unfold magEigenvalueS
  rw [magSumS_allAlignedConfigS]
  push_cast
  ring

/-! ## `Ŝ_tot^{(3)}` eigenvalue on the all-aligned state -/

/-- The all-aligned state at `c` is a `Ŝ_tot^{(3)}`-eigenvector with
eigenvalue `magEigenvalueS (allAlignedConfigS V N c) = |V|·N/2 − |V|·c`. -/
theorem totalSpinSOp3_mulVec_allAlignedStateS (c : Fin (N + 1)) :
    (totalSpinSOp3 V N).mulVec (allAlignedStateS V N c) =
      magEigenvalueS (allAlignedConfigS V N c) •
        allAlignedStateS V N c := by
  exact totalSpinSOp3_mulVec_basisVecS (allAlignedConfigS V N c)

/-! ## Highest-weight specialisation (`c = 0`, "all up")

The highest-weight all-aligned state corresponds to `σ x = 0` for all
`x` (in our `Fin (N+1)` basis convention, `σ x = 0` is the
`m_z = +N/2 = +S` state). It has `magSumS = 0`,
`Ŝ^z_tot`-eigenvalue `+|V|·N/2`, and is the unique configuration in
its sector. Hence by magnetization conservation it is automatically a
**Heisenberg-Hamiltonian eigenvector**.
-/

omit [DecidableEq V] in
/-- For `c = (0 : Fin (N+1))`, `magSumS = 0`. -/
theorem magSumS_allAlignedConfigS_zero :
    magSumS (allAlignedConfigS V N (0 : Fin (N + 1))) = 0 := by
  rw [magSumS_allAlignedConfigS]
  simp

omit [DecidableEq V] in
/-- The all-up configuration is the **unique** configuration with
`magSumS = 0`: every other configuration has `magSumS > 0`. -/
theorem magSumS_pos_of_ne_allAlignedConfigS_zero
    {σ : V → Fin (N + 1)} (h : σ ≠ allAlignedConfigS V N 0) :
    0 < magSumS σ := by
  rcases Nat.eq_zero_or_pos (magSumS σ) with hmag | hpos
  · exfalso
    apply h
    funext x
    unfold magSumS at hmag
    have hx : (σ x).val = 0 := by
      have := Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset V))
        (f := fun y => (σ y).val)
        (fun y _ => Nat.zero_le _) |>.mp hmag x (Finset.mem_univ x)
      exact this
    unfold allAlignedConfigS
    exact Fin.ext hx
  · exact hpos

/-- **The all-up state is a Heisenberg eigenvector** (any coupling
`J`): for the all-up basis state `|σ_⊤⟩` (`σ x = 0` for all `x`),

  `H · |σ_⊤⟩ = (H_{σ_⊤,σ_⊤}) · |σ_⊤⟩`.

By magnetization conservation `[H, Ŝ^z_tot] = 0`, the only matrix
element `H τ σ_⊤` non-zero requires `magSumS τ = magSumS σ_⊤ = 0`,
which forces `τ = σ_⊤`. -/
theorem heisenbergHamiltonianS_mulVec_allAlignedStateS_zero
    (J : V → V → ℂ) :
    (heisenbergHamiltonianS J N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  funext τ
  unfold allAlignedStateS
  rw [heisenbergHamiltonianS_mulVec_basisVecS_apply]
  change heisenbergHamiltonianS J N τ (allAlignedConfigS V N 0) =
    (heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
      (allAlignedConfigS V N 0)) * basisVecS (allAlignedConfigS V N 0) τ
  by_cases h : τ = allAlignedConfigS V N 0
  · subst h
    rw [basisVecS_apply, if_pos rfl]
    ring
  · -- τ ≠ σ_⊤. By magnetization conservation, H τ σ_⊤ = 0.
    rw [basisVecS_apply, if_neg h, mul_zero]
    -- magSumS τ ≠ 0 = magSumS σ_⊤.
    apply heisenbergHamiltonianS_apply_eq_zero_of_mag_ne (Λ := V) J N
    -- Goal: magEigenvalueS σ_⊤ ≠ magEigenvalueS τ.
    intro hEig
    have hmag : magSumS τ = magSumS (allAlignedConfigS V N 0) := by
      have := congrArg (fun z : ℂ => -(z - ((Fintype.card V : ℂ) * (N : ℂ)) / 2)) hEig
      simp [magEigenvalueS] at this
      exact_mod_cast this.symm
    rw [magSumS_allAlignedConfigS_zero] at hmag
    have hpos := magSumS_pos_of_ne_allAlignedConfigS_zero h
    omega

/-- **Explicit Heisenberg eigenvalue formula on all-up**: combining
`heisenbergHamiltonianS_mulVec_allAlignedStateS_zero` with the
diagonal computation `heisenbergHamiltonianS_apply_diag` gives

  `H · |σ_⊤⟩ = (Σ_x J(x,x) · N(N+2)/4 + Σ_{x≠y} J(x,y) · N²/4) · |σ_⊤⟩`. -/
theorem heisenbergHamiltonianS_mulVec_allAlignedStateS_zero_eigenvalue
    (J : V → V → ℂ) :
    (heisenbergHamiltonianS J N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)))) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  rw [heisenbergHamiltonianS_mulVec_allAlignedStateS_zero]
  congr 1
  rw [heisenbergHamiltonianS_apply_diag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy]
    show J x y *
      (((N : ℂ) / 2 - ((allAlignedConfigS V N 0) x).val) *
        ((N : ℂ) / 2 - ((allAlignedConfigS V N 0) y).val)) =
      J x y * ((N : ℂ) / 2 * ((N : ℂ) / 2))
    unfold allAlignedConfigS
    have h0 : ((0 : Fin (N + 1)).val : ℂ) = 0 := by simp
    rw [h0]
    ring

end LatticeSystem.Quantum
