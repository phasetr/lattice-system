import LatticeSystem.Quantum.SpinS.Magnetization
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

/-- The Heisenberg Hamiltonian is anti-distributive over subtraction
in the coupling: -/
theorem heisenbergHamiltonianS_sub (J J' : Λ → Λ → ℂ) (N : ℕ) :
    heisenbergHamiltonianS (Λ := Λ) (fun x y => J x y - J' x y) N =
      heisenbergHamiltonianS J N - heisenbergHamiltonianS J' N := by
  have h : (fun x y : Λ => J x y - J' x y) =
      (fun x y => J x y + (-(J' x y))) := by
    ext x y; ring
  rw [h]
  rw [heisenbergHamiltonianS_add]
  rw [heisenbergHamiltonianS_neg]
  abel

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

/-- Definitional unfolding of `heisenbergHamiltonianChainS`. -/
theorem heisenbergHamiltonianChainS_def (M : ℕ) (J : ℝ) (N : ℕ) :
    heisenbergHamiltonianChainS M J N =
      heisenbergHamiltonianOnGraphS (SimpleGraph.pathGraph (M + 1))
        (-(J : ℂ)) N := rfl

/-- Definitional unfolding of `heisenbergHamiltonianPeriodicChainS`. -/
theorem heisenbergHamiltonianPeriodicChainS_def (M : ℕ) (J : ℝ) (N : ℕ) :
    heisenbergHamiltonianPeriodicChainS M J N =
      heisenbergHamiltonianOnGraphS (SimpleGraph.cycleGraph (M + 2))
        (-(J : ℂ)) N := rfl

/-- Hermiticity of the periodic chain spin-`S` Heisenberg Hamiltonian. -/
theorem heisenbergHamiltonianPeriodicChainS_isHermitian
    (M : ℕ) (J : ℝ) (N : ℕ) :
    (heisenbergHamiltonianPeriodicChainS M J N).IsHermitian :=
  heisenbergHamiltonianOnGraphS_isHermitian _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- The Heisenberg-on-graph Hamiltonian commutes with `Ŝ_tot^{(α)}`
for every axis (specialised SU(2) invariance for graph-derived
couplings). -/
theorem heisenbergHamiltonianOnGraphS_commute_totalSpinSOp1
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (N : ℕ) :
    heisenbergHamiltonianOnGraphS G J N * totalSpinSOp1 Λ N -
        totalSpinSOp1 Λ N * heisenbergHamiltonianOnGraphS G J N = 0 :=
  heisenbergHamiltonianS_commutator_totalSpinSOp1 _ N

theorem heisenbergHamiltonianOnGraphS_commute_totalSpinSOp2
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (N : ℕ) :
    heisenbergHamiltonianOnGraphS G J N * totalSpinSOp2 Λ N -
        totalSpinSOp2 Λ N * heisenbergHamiltonianOnGraphS G J N = 0 :=
  heisenbergHamiltonianS_commutator_totalSpinSOp2 _ N

theorem heisenbergHamiltonianOnGraphS_commute_totalSpinSOp3
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (N : ℕ) :
    heisenbergHamiltonianOnGraphS G J N * totalSpinSOp3 Λ N -
        totalSpinSOp3 Λ N * heisenbergHamiltonianOnGraphS G J N = 0 :=
  heisenbergHamiltonianS_commutator_totalSpinSOp3 _ N

/-- The Heisenberg-on-graph Hamiltonian commutes with `(Ŝ_tot)²`. -/
theorem heisenbergHamiltonianOnGraphS_commute_totalSpinSSquared
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (N : ℕ) :
    Commute (heisenbergHamiltonianOnGraphS G J N)
      (totalSpinSSquared Λ N) :=
  heisenbergHamiltonianS_commute_totalSpinSSquared _ N

/-- The Heisenberg Hamiltonian preserves `(Ŝ_tot)²` eigenvalues:
if `(Ŝ_tot)² · v = S · v`, then `(Ŝ_tot)² · (Ĥ · v) = S · (Ĥ · v)`.
Operator-level simultaneous diagonalisation. -/
theorem heisenbergHamiltonianS_mulVec_preserves_totalSpinSSquared_eigenvalue
    (J : Λ → Λ → ℂ) (N : ℕ)
    {S : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : (totalSpinSSquared Λ N).mulVec v = S • v) :
    (totalSpinSSquared Λ N).mulVec
        ((heisenbergHamiltonianS J N).mulVec v) =
      S • (heisenbergHamiltonianS J N).mulVec v := by
  have hcomm : totalSpinSSquared Λ N * heisenbergHamiltonianS J N =
      heisenbergHamiltonianS J N * totalSpinSSquared Λ N :=
    (heisenbergHamiltonianS_commute_totalSpinSSquared J N).symm
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

/-- The Heisenberg Hamiltonian preserves `Ŝ_tot^{(3)}` eigenvalues:
if `Ŝ_tot^{(3)} · v = M · v`, then `Ŝ_tot^{(3)} · (Ĥ · v) = M · (Ĥ · v)`.
The `(Ŝ_tot)^{(3)}`-analogue of the Casimir version. -/
theorem heisenbergHamiltonianS_mulVec_preserves_totalSpinSOp3_eigenvalue
    (J : Λ → Λ → ℂ) (N : ℕ)
    {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : (totalSpinSOp3 Λ N).mulVec v = M • v) :
    (totalSpinSOp3 Λ N).mulVec
        ((heisenbergHamiltonianS J N).mulVec v) =
      M • (heisenbergHamiltonianS J N).mulVec v := by
  have hcomm : totalSpinSOp3 Λ N * heisenbergHamiltonianS J N =
      heisenbergHamiltonianS J N * totalSpinSOp3 Λ N :=
    (sub_eq_zero.mp
      (heisenbergHamiltonianS_commutator_totalSpinSOp3 J N)).symm
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

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

/-- The Heisenberg-on-graph Hamiltonian preserves magnetization subspaces. -/
theorem heisenbergHamiltonianOnGraphS_mulVec_mem_magSubspaceS
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (J : ℂ) (N : ℕ) (M : ℂ)
    {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (heisenbergHamiltonianOnGraphS G J N).mulVec v ∈ magSubspaceS Λ N M :=
  heisenbergHamiltonianS_mulVec_mem_magSubspaceS _ N M hv

/-- For real coupling, the diagonal entries of the Heisenberg
Hamiltonian have zero imaginary part. (Since the Hamiltonian is
Hermitian for real coupling, its diagonal is real.) -/
theorem heisenbergHamiltonianS_apply_diag_im_zero
    {J : Λ → Λ → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y)
    (σ : Λ → Fin (N + 1)) :
    ((heisenbergHamiltonianS J N) σ σ).im = 0 := by
  have hH := heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hreal N
  have := hH.apply σ σ
  exact Complex.conj_eq_iff_im.mp this

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

/-! ## Heisenberg Hamiltonian symmetry for symmetric coupling -/

/-- For real-valued symmetric matrix `spinSDot x y` the matrix
element is symmetric in the configuration arguments:
`(Ŝ_x · Ŝ_y) σ' σ = (Ŝ_x · Ŝ_y) σ σ'`. Combines Hermiticity and
the real-valuedness of all spinSDot entries. -/
theorem spinSDot_apply_swap (x y : Λ) (N : ℕ)
    (σ' σ : Λ → Fin (N + 1)) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ =
      (spinSDot x y N : ManyBodyOpS Λ N) σ σ' := by
  have hH := spinSDot_isHermitian (Λ := Λ) x y N
  have happ := hH.apply σ σ'
  have him : ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ).im = 0 :=
    spinSDot_apply_im_zero x y N σ' σ
  have hreal : star ((spinSDot x y N : ManyBodyOpS Λ N) σ' σ) =
      (spinSDot x y N : ManyBodyOpS Λ N) σ' σ :=
    Complex.conj_eq_iff_im.mpr him
  exact (happ.symm.trans hreal).symm

/-- For symmetric coupling `J x y = J y x`, the Heisenberg matrix
element `H σ' σ` equals `H σ σ'`. The Heisenberg matrix is symmetric
on the configuration basis. -/
theorem heisenbergHamiltonianS_apply_swap_of_symm
    {J : Λ → Λ → ℂ} (_hsym : ∀ x y, J x y = J y x) (N : ℕ)
    (σ' σ : Λ → Fin (N + 1)) :
    (heisenbergHamiltonianS J N) σ' σ =
      (heisenbergHamiltonianS J N) σ σ' := by
  rw [heisenbergHamiltonianS_apply, heisenbergHamiltonianS_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [spinSDot_apply_swap]

/-- **Heisenberg matrix vanishes on three-site differences**: if
`σ', σ` differ at three pairwise-distinct sites `z₁, z₂, z₃`, the
Heisenberg matrix element `H σ' σ` vanishes (every spinSDot term in
the double sum vanishes by pigeonhole). -/
theorem heisenbergHamiltonianS_apply_eq_zero_of_three_diff
    (J : Λ → Λ → ℂ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z₁ z₂ z₃ : Λ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    (heisenbergHamiltonianS J N) σ' σ = 0 := by
  rw [heisenbergHamiltonianS_apply]
  refine Finset.sum_eq_zero (fun x' _ => ?_)
  refine Finset.sum_eq_zero (fun y' _ => ?_)
  by_cases hxy' : x' = y'
  · subst hxy'
    rw [show (spinSDot x' x' N : ManyBodyOpS Λ N) σ' σ = 0 from
      spinSDot_self_apply_eq_zero_of_diff_at x' N hz1]
    ring
  · rw [show (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 from
      spinSDot_apply_eq_zero_of_three_diff hxy' N h12 h13 h23 hz1 hz2 hz3]
    ring

/-- **Magnetization conservation, matrix-element form**: if `σ', σ`
differ at exactly one site `z` (i.e., agree everywhere off `{z}`),
the Heisenberg matrix element `H σ' σ` vanishes.

Every term in the double sum vanishes: `(x' = y')` gives the
diagonal Casimir times `δ_{σ',σ} = 0`; `(x' ≠ y')` gives a two-site
spinSDot entry which vanishes on one-site differences. -/
theorem heisenbergHamiltonianS_apply_eq_zero_of_one_site_diff
    (J : Λ → Λ → ℂ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    (heisenbergHamiltonianS J N) σ' σ = 0 := by
  rw [heisenbergHamiltonianS_apply]
  refine Finset.sum_eq_zero (fun x' _ => ?_)
  refine Finset.sum_eq_zero (fun y' _ => ?_)
  by_cases hxy' : x' = y'
  · subst hxy'
    rw [show (spinSDot x' x' N : ManyBodyOpS Λ N) σ' σ = 0 from
      spinSDot_self_apply_eq_zero_of_diff_at x' N hz]
    ring
  · rw [show (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ = 0 from
      spinSDot_apply_eq_zero_of_one_site_diff hxy' N hagree hz]
    ring



/-- For real coupling `J`, the Heisenberg matrix entries have zero
imaginary part. (Each `Ŝ_x · Ŝ_y` matrix element is real, and a real
coupling preserves this.) -/
theorem heisenbergHamiltonianS_apply_im_zero
    {J : Λ → Λ → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0)
    (σ' σ : Λ → Fin (N + 1)) :
    ((heisenbergHamiltonianS J N) σ' σ).im = 0 := by
  rw [heisenbergHamiltonianS_apply]
  -- Sum of products of (J x y) (real) with (spinSDot x y N σ' σ) (real)
  rw [show ((∑ x : Λ, ∑ y : Λ, J x y * (spinSDot x y N) σ' σ).im : ℝ) =
        ∑ x : Λ, ∑ y : Λ, (J x y * (spinSDot x y N) σ' σ).im from by
    rw [Complex.im_sum]; refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Complex.im_sum]]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  refine Finset.sum_eq_zero (fun y _ => ?_)
  rw [Complex.mul_im]
  rw [hreal x y, spinSDot_apply_im_zero]
  ring

/-- For real coupling `J`, each Heisenberg matrix entry equals its
real-part embedding. -/
theorem heisenbergHamiltonianS_apply_eq_ofReal_re
    {J : Λ → Λ → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0)
    (σ' σ : Λ → Fin (N + 1)) :
    (heisenbergHamiltonianS J N) σ' σ =
      (((heisenbergHamiltonianS J N) σ' σ).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact heisenbergHamiltonianS_apply_im_zero (Λ := Λ) N hreal σ' σ

/-- The matrix element `H σ' σ` vanishes when the two configurations
have different magnetization quantum numbers. This is the matrix-level
expression of `[H, S^z_tot] = 0`. -/
theorem heisenbergHamiltonianS_apply_eq_zero_of_mag_ne
    (J : Λ → Λ → ℂ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : magEigenvalueS σ ≠ magEigenvalueS σ') :
    (heisenbergHamiltonianS J N) σ' σ = 0 := by
  -- Apply H to |σ⟩: result is in magSubspaceS Λ N (magEig σ).
  have hH := heisenbergHamiltonianS_mulVec_basisVecS_mem_magSubspaceS
    (Λ := Λ) J N σ
  rw [mem_magSubspaceS_iff] at hH
  -- Read at row σ': S^z_tot · (H · |σ⟩) σ' = (magEig σ) · (H · |σ⟩) σ'.
  have hentry := congrFun hH σ'
  -- LHS: (S^z · H · |σ⟩) σ' = magEig σ' · (H · |σ⟩) σ' (using S^z diagonal).
  classical
  have hLHS :
      (totalSpinSOp3 Λ N).mulVec
        ((heisenbergHamiltonianS J N).mulVec (basisVecS σ)) σ' =
      magEigenvalueS σ' *
        ((heisenbergHamiltonianS J N).mulVec (basisVecS σ)) σ' := by
    change ∑ τ, (totalSpinSOp3 Λ N) σ' τ *
        ((heisenbergHamiltonianS J N).mulVec (basisVecS σ)) τ = _
    rw [Finset.sum_eq_single σ']
    · rw [totalSpinSOp3_apply_diag]
    · intro τ _ hτne
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hτne), zero_mul]
    · intro hσ; exact (hσ (Finset.mem_univ σ')).elim
  rw [hLHS, Pi.smul_apply, smul_eq_mul] at hentry
  -- hentry : magEig σ' · X = magEig σ · X, where X = (H · |σ⟩) σ' = H σ' σ.
  have hHapply : (heisenbergHamiltonianS J N).mulVec (basisVecS σ) σ' =
      (heisenbergHamiltonianS J N) σ' σ :=
    heisenbergHamiltonianS_mulVec_basisVecS_apply (Λ := Λ) J N σ σ'
  rw [hHapply] at hentry
  have hzero :
      (magEigenvalueS σ' - magEigenvalueS σ) *
        (heisenbergHamiltonianS J N) σ' σ = 0 := by
    linear_combination hentry
  rcases mul_eq_zero.mp hzero with hmag | hH
  · exact (h (sub_eq_zero.mp hmag).symm).elim
  · exact hH

end LatticeSystem.Quantum
