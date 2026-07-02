import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDotOffDiag
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Lattice.Graph
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Spin-`S` Heisenberg-type Hamiltonian
(Tasaki §2.5 Phase B-β β-3h)

The general Heisenberg-type Hamiltonian on the multi-site spin-`S`
Hilbert space:

  `Ĥ_J := Σ_{x, y : Λ} J(x, y) • Ŝ_x · Ŝ_y`.

This is the spin-`S` analogue of `heisenbergHamiltonian`
(`Quantum/SpinDot/Hamiltonian.lean`) and the foundation for the
single-cluster (Problem 2.5.a) and Marshall–Lieb–Mattis (Theorem 2.2)
machinery for general spin (Issue #412 Phase B-γ).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The spin-`S` Heisenberg-type Hamiltonian on `Λ` with coupling
`J : Λ → Λ → ℂ`. -/
noncomputable def heisenbergHamiltonianS (J : Λ → Λ → ℂ) (N : ℕ) :
    ManyBodyOpS Λ N :=
  ∑ x : Λ, ∑ y : Λ, J x y • spinSDot x y N

/-- Definitional unfolding of `heisenbergHamiltonianS`. -/
theorem heisenbergHamiltonianS_def (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS (Λ := Λ) J N =
      ∑ x : Λ, ∑ y : Λ, J x y • spinSDot x y N := rfl

/-- A spin-`S` Heisenberg Hamiltonian with **real** coupling
(`star (J x y) = J x y`) is Hermitian. No symmetry of `J` is needed,
since `Ŝ_x · Ŝ_y` is always Hermitian (β-3g) — symmetry of the
coupling is automatically symmetrised by the doubled sum
`∑_{x, y} J(x, y) Ŝ_x · Ŝ_y`. -/
theorem heisenbergHamiltonianS_isHermitian_of_real
    {J : Λ → Λ → ℂ} (hreal : ∀ x y, star (J x y) = J x y) (N : ℕ) :
    (heisenbergHamiltonianS (Λ := Λ) J N).IsHermitian := by
  unfold heisenbergHamiltonianS Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  congr 1; funext x
  rw [Matrix.conjTranspose_sum]
  congr 1; funext y
  rw [Matrix.conjTranspose_smul, (spinSDot_isHermitian x y N).eq]
  rw [hreal]


/-! ## SU(2) invariance (Tasaki §2.2 (2.2.13) general S) -/

/-- SU(2) invariance, axis 1: the spin-`S` Heisenberg Hamiltonian
commutes with `Ŝ_tot^{(1)}`. -/
theorem heisenbergHamiltonianS_commutator_totalSpinSOp1
    (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp1 Λ N -
        totalSpinSOp1 Λ N * heisenbergHamiltonianS J N = 0 := by
  unfold heisenbergHamiltonianS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp1, smul_zero]

/-- SU(2) invariance, axis 2: `[Ĥ_J, Ŝ_tot^{(2)}] = 0`. -/
theorem heisenbergHamiltonianS_commutator_totalSpinSOp2
    (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp2 Λ N -
        totalSpinSOp2 Λ N * heisenbergHamiltonianS J N = 0 := by
  unfold heisenbergHamiltonianS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp2, smul_zero]

/-- SU(2) invariance, axis 3: `[Ĥ_J, Ŝ_tot^{(3)}] = 0`. -/
theorem heisenbergHamiltonianS_commutator_totalSpinSOp3
    (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS J N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * heisenbergHamiltonianS J N = 0 := by
  unfold heisenbergHamiltonianS
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
  rw [spinSDot_commutator_totalSpinSOp3, smul_zero]

/-- The Heisenberg Hamiltonian commutes with the Casimir `(Ŝ_tot)²`:
operator-level SU(2) invariance at the Casimir level. Follows from
`[Ĥ_J, Ŝ_tot^{(α)}] = 0` for each axis (β-3o) via `Commute.mul_right`
and `Commute.add_right`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSSquared
    (J : Λ → Λ → ℂ) (N : ℕ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSSquared Λ N) := by
  unfold totalSpinSSquared
  have h1 : Commute (heisenbergHamiltonianS J N) (totalSpinSOp1 Λ N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp1 J N)
  have h2 : Commute (heisenbergHamiltonianS J N) (totalSpinSOp2 Λ N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp2 J N)
  have h3 : Commute (heisenbergHamiltonianS J N) (totalSpinSOp3 Λ N) :=
    sub_eq_zero.mp (heisenbergHamiltonianS_commutator_totalSpinSOp3 J N)
  exact ((h1.mul_right h1).add_right (h2.mul_right h2)).add_right
    (h3.mul_right h3)

/-! ## Linearity in the coupling -/

/-- The Heisenberg Hamiltonian is additive in the coupling: -/
theorem heisenbergHamiltonianS_add (J J' : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS (Λ := Λ) (fun x y => J x y + J' x y) N =
      heisenbergHamiltonianS J N + heisenbergHamiltonianS J' N := by
  unfold heisenbergHamiltonianS
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [add_smul]

/-- The Heisenberg Hamiltonian is zero when the coupling is zero
(every term in the double sum vanishes). -/
theorem heisenbergHamiltonianS_zero (N : ℕ) :
    heisenbergHamiltonianS (Λ := Λ) (fun _ _ => (0 : ℂ)) N = 0 := by
  unfold heisenbergHamiltonianS
  refine Finset.sum_eq_zero (fun x _ => ?_)
  refine Finset.sum_eq_zero (fun y _ => ?_)
  simp

/-- For the trivial spin parameter `N = 0` (`S = 0`), every Heisenberg
matrix element on the multi-site space is the same-site Casimir
contribution, which equals zero. So the Heisenberg Hamiltonian is the
zero operator. -/
theorem heisenbergHamiltonianS_N_zero (J : Λ → Λ → ℂ) :
    heisenbergHamiltonianS (Λ := Λ) J 0 = 0 := by
  unfold heisenbergHamiltonianS
  refine Finset.sum_eq_zero (fun x _ => ?_)
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hxy : x = y
  · subst hxy
    rw [show spinSDot x x 0 = (0 : ManyBodyOpS Λ 0) from spinSDot_self_N_zero x]
    simp
  · rw [spinSDot_N_zero_of_ne hxy]
    simp

/-- The Heisenberg Hamiltonian negates with the coupling: -/
theorem heisenbergHamiltonianS_neg (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS (Λ := Λ) (fun x y => -(J x y)) N =
      -(heisenbergHamiltonianS J N) := by
  unfold heisenbergHamiltonianS
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [neg_smul]

/-- The Heisenberg Hamiltonian matrix element formula:
`(heisenbergHamiltonianS J N) σ τ = ∑_{x,y} J(x,y) (Ŝ_x · Ŝ_y) σ τ`. -/
theorem heisenbergHamiltonianS_apply (J : Λ → Λ → ℂ) (N : ℕ)
    (σ τ : Λ → Fin (N + 1)) :
    (heisenbergHamiltonianS J N) σ τ =
      ∑ x : Λ, ∑ y : Λ, J x y * (spinSDot x y N) σ τ := by
  unfold heisenbergHamiltonianS
  simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- `totalSpinSSquared Λ N` is the Heisenberg Hamiltonian with
constant unit coupling: `(Ŝ_tot)² = ∑_{x,y} (Ŝ_x · Ŝ_y)`. -/
theorem totalSpinSSquared_eq_heisenbergHamiltonianS_unit :
    (totalSpinSSquared Λ N : ManyBodyOpS Λ N) =
      heisenbergHamiltonianS (Λ := Λ) (fun _ _ => (1 : ℂ)) N := by
  rw [totalSpinSSquared_eq_sum_spinSDot]
  unfold heisenbergHamiltonianS
  simp

/-- The diagonal Heisenberg matrix element on a configuration `σ`:
splits into a same-site Casimir contribution `∑_x J(x,x) (N(N+2)/4)`
and a distinct-site `Ŝ^{(3)}_x Ŝ^{(3)}_y` contribution
`∑_{x≠y} J(x,y) m_x m_y` where `m_z = N/2 - σ_z.val`. -/
theorem heisenbergHamiltonianS_apply_diag (J : Λ → Λ → ℂ) (N : ℕ)
    (σ : Λ → Fin (N + 1)) :
    (heisenbergHamiltonianS J N) σ σ =
      ∑ x : Λ, ∑ y : Λ,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else ((N : ℂ) / 2 - (σ x).val) *
                      ((N : ℂ) / 2 - (σ y).val)) := by
  rw [heisenbergHamiltonianS_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, spinSDot_self_apply_diag]
  · rw [if_neg hxy, spinSDot_apply_diag_of_ne hxy]

/-- The Heisenberg Hamiltonian is homogeneous in the coupling: -/
theorem heisenbergHamiltonianS_smul (c : ℂ) (J : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS (Λ := Λ) (fun x y => c * J x y) N =
      c • heisenbergHamiltonianS J N := by
  unfold heisenbergHamiltonianS
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [smul_smul]

/-! ## Heisenberg on a `SimpleGraph` -/

/-- Canonical named wrapper for the spin-`S` Heisenberg Hamiltonian
with hopping pattern derived from a `SimpleGraph G` and uniform
complex edge weight `J`. Spin-`S` analogue of
`heisenbergHamiltonianOnGraph` (`Quantum/HeisenbergChain.lean`). -/
noncomputable def heisenbergHamiltonianOnGraphS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (N : ℕ) :
    ManyBodyOpS Λ N :=
  heisenbergHamiltonianS (LatticeSystem.Lattice.couplingOf G J) N

/-- The Heisenberg Hamiltonian on a graph is Hermitian for any real
complex edge weight `J` (i.e. `star J = J`). Direct corollary of
`heisenbergHamiltonianS_isHermitian_of_real` and
`couplingOf_real`. -/
theorem heisenbergHamiltonianOnGraphS_isHermitian
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {J : ℂ}
    (hJ : star J = J) (N : ℕ) :
    (heisenbergHamiltonianOnGraphS G J N : ManyBodyOpS Λ N).IsHermitian :=
  heisenbergHamiltonianS_isHermitian_of_real
    (LatticeSystem.Lattice.couplingOf_real G hJ) N

/-- Spin-`S` Heisenberg Hamiltonian on the open chain `pathGraph (M + 1)`. -/
noncomputable def heisenbergHamiltonianChainS
    (M : ℕ) (J : ℝ) (N : ℕ) :
    ManyBodyOpS (Fin (M + 1)) N :=
  heisenbergHamiltonianOnGraphS (SimpleGraph.pathGraph (M + 1))
    (-(J : ℂ)) N

/-- Hermiticity of the chain spin-`S` Heisenberg Hamiltonian (for real
coupling `J : ℝ`). -/
theorem heisenbergHamiltonianChainS_isHermitian (M : ℕ) (J : ℝ) (N : ℕ) :
    (heisenbergHamiltonianChainS M J N).IsHermitian :=
  heisenbergHamiltonianOnGraphS_isHermitian _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- Spin-`S` Heisenberg Hamiltonian on the periodic chain `cycleGraph (M + 2)`. -/
noncomputable def heisenbergHamiltonianPeriodicChainS
    (M : ℕ) (J : ℝ) (N : ℕ) :
    ManyBodyOpS (Fin (M + 2)) N :=
  heisenbergHamiltonianOnGraphS (SimpleGraph.cycleGraph (M + 2))
    (-(J : ℂ)) N

/-- Hermiticity of the periodic chain spin-`S` Heisenberg Hamiltonian. -/
theorem heisenbergHamiltonianPeriodicChainS_isHermitian
    (M : ℕ) (J : ℝ) (N : ℕ) :
    (heisenbergHamiltonianPeriodicChainS M J N).IsHermitian :=
  heisenbergHamiltonianOnGraphS_isHermitian _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- The Heisenberg Hamiltonian preserves each magnetization subspace:
`v ∈ magSubspaceS Λ N M ⇒ (Ĥ · v) ∈ magSubspaceS Λ N M`.
Direct corollary of the `Ŝ_tot^{(3)}` commutativity. -/
theorem heisenbergHamiltonianS_mulVec_mem_magSubspaceS
    (J : Λ → Λ → ℂ) (N : ℕ) (M : ℂ)
    {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (heisenbergHamiltonianS J N).mulVec v ∈ magSubspaceS Λ N M :=
  mem_magSubspaceS_of_commute M (heisenbergHamiltonianS J N)
    (sub_eq_zero.mp
      (heisenbergHamiltonianS_commutator_totalSpinSOp3 J N)).symm hv

/-- Applying the Heisenberg Hamiltonian to a basis vector and reading
the result at configuration `τ` yields the matrix element
`H τ σ`. The basis-vector mulVec collapses to a single matrix entry. -/
theorem heisenbergHamiltonianS_mulVec_basisVecS_apply
    (J : Λ → Λ → ℂ) (N : ℕ) (σ τ : Λ → Fin (N + 1)) :
    (heisenbergHamiltonianS J N).mulVec (basisVecS σ) τ =
      (heisenbergHamiltonianS J N) τ σ := by
  classical
  change ∑ σ' : Λ → Fin (N + 1),
      (heisenbergHamiltonianS J N) τ σ' * basisVecS σ σ' =
        (heisenbergHamiltonianS J N) τ σ
  simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ σ
      (fun σ' => (heisenbergHamiltonianS J N) τ σ')]
  simp

/-- The Heisenberg Hamiltonian applied to a basis state stays in the
same magnetization subspace: `Ĥ |σ⟩ ∈ magSubspaceS Λ N (magEigenvalueS σ)`.
Direct corollary of `basisVecS_mem_magSubspaceS` and the magnetization
preservation property. -/
theorem heisenbergHamiltonianS_mulVec_basisVecS_mem_magSubspaceS
    (J : Λ → Λ → ℂ) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    (heisenbergHamiltonianS J N).mulVec (basisVecS σ) ∈
      magSubspaceS Λ N (magEigenvalueS σ) :=
  heisenbergHamiltonianS_mulVec_mem_magSubspaceS _ N _
    (basisVecS_mem_basisVec_magSubspaceS σ)
where
  basisVecS_mem_basisVec_magSubspaceS := basisVecS_mem_magSubspaceS


end LatticeSystem.Quantum
