import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDotOffDiag
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Lattice.Graph
import Mathlib.Combinatorics.SimpleGraph.Basic
import LatticeSystem.Quantum.SpinS.HeisenbergCore

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

/-- **Two-site matrix-element formula**: for `x ≠ y` and configurations
`σ', σ` agreeing off `{x, y}` with `σ' ≠ σ`, the Heisenberg matrix
element factorises as

    `H σ' σ = (J(x, y) + J(y, x)) · (Ŝ_x · Ŝ_y) σ' σ`.

In the double sum `∑_{x', y'} J(x', y') (Ŝ_{x'} · Ŝ_{y'}) σ' σ`,
exactly two terms contribute (at `(x', y') = (x, y)` and `(y, x)`)
because all other pairs give zero by `spinSDot_apply_eq_zero_of_*`
(same-site Casimir vanishes on `σ' ≠ σ`; off-pair entries are killed
by the outside-pair lemmas). The two surviving terms combine via
`spinSDot_comm` (`Ŝ_y · Ŝ_x = Ŝ_x · Ŝ_y`). -/
theorem heisenbergHamiltonianS_apply_of_off_two_site_agree
    {J : Λ → Λ → ℂ} {x y : Λ} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (heisenbergHamiltonianS J N) σ' σ =
      (J x y + J y x) * (spinSDot x y N : ManyBodyOpS Λ N) σ' σ := by
  classical
  rw [heisenbergHamiltonianS_apply]
  -- Step 1: Outer terms x' ∉ {x, y} vanish.
  have hfxy_zero : ∀ x' ∈ (Finset.univ : Finset Λ),
      x' ∉ ({x, y} : Finset Λ) →
      (∑ y' : Λ, J x' y' *
        (spinSDot x' y' N : ManyBodyOpS Λ N) σ' σ) = 0 := by
    intro x' _ hx'
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
    obtain ⟨hxx', hyx'⟩ := hx'
    refine Finset.sum_eq_zero (fun y' _ => ?_)
    by_cases hxy' : x' = y'
    · subst hxy'
      obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
      rw [spinSDot_self_apply_eq_zero_of_diff_at x' N hz]
      ring
    · rw [spinSDot_apply_eq_zero_of_x_outside_pair hxy N hne h hxy'
        hxx' hyx']
      ring
  rw [← Finset.sum_subset
    (Finset.subset_univ ({x, y} : Finset Λ)) hfxy_zero]
  rw [Finset.sum_insert (Finset.notMem_singleton.mpr hxy),
    Finset.sum_singleton]
  -- Step 2: Inner sum at outer site `x` reduces to the `y'` = `y` term.
  have hf_x : (∑ y' : Λ, J x y' *
      (spinSDot x y' N : ManyBodyOpS Λ N) σ' σ) =
      J x y * (spinSDot x y N : ManyBodyOpS Λ N) σ' σ := by
    rw [Finset.sum_eq_single y]
    · intro y' _ hy'ne
      by_cases hxy' : x = y'
      · subst hxy'
        obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
        rw [spinSDot_self_apply_eq_zero_of_diff_at x N hz]
        ring
      · rw [spinSDot_apply_eq_zero_of_y_outside_pair hxy N hne h hxy'
          (fun heq => hxy' heq.symm) hy'ne]
        ring
    · intro hyu; exact (hyu (Finset.mem_univ y)).elim
  -- Step 3: Inner sum at outer site `y` reduces to the `y'` = `x` term.
  have hf_y : (∑ y' : Λ, J y y' *
      (spinSDot y y' N : ManyBodyOpS Λ N) σ' σ) =
      J y x * (spinSDot x y N : ManyBodyOpS Λ N) σ' σ := by
    rw [Finset.sum_eq_single x]
    · rw [show (spinSDot y x N : ManyBodyOpS Λ N) σ' σ =
            (spinSDot x y N : ManyBodyOpS Λ N) σ' σ from by
        rw [spinSDot_comm]]
    · intro y' _ hy'ne
      by_cases hyy' : y = y'
      · subst hyy'
        obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
        rw [spinSDot_self_apply_eq_zero_of_diff_at y N hz]
        ring
      · rw [spinSDot_apply_eq_zero_of_y_outside_pair hxy N hne h hyy'
          hy'ne (fun heq => hyy' heq.symm)]
        ring
    · intro hxu; exact (hxu (Finset.mem_univ x)).elim
  rw [hf_x, hf_y]
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

/-- **Magnetization conservation, spinSDot matrix-element form**: the
two-site `Ŝ_x · Ŝ_y` matrix element vanishes when `σ', σ` carry
different magnetization quantum numbers.

This is the matrix-level expression of `[Ŝ_x · Ŝ_y, Ŝ^{(3)}_tot] = 0`
(`spinSDot_commutator_totalSpinSOp3`). The proof structure mirrors the
Heisenberg analogue (`heisenbergHamiltonianS_apply_eq_zero_of_mag_ne`)
since both rely on commutativity with `Ŝ^{(3)}_tot`. -/
theorem spinSDot_apply_eq_zero_of_mag_ne
    (x y : Λ) (N : ℕ)
    {σ' σ : Λ → Fin (N + 1)}
    (h : magEigenvalueS σ ≠ magEigenvalueS σ') :
    (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
  classical
  -- Apply spinSDot to |σ⟩: result is in magSubspaceS Λ N (magEig σ).
  have hcomm : Commute (totalSpinSOp3 Λ N)
      (spinSDot x y N : ManyBodyOpS Λ N) :=
    (sub_eq_zero.mp (spinSDot_commutator_totalSpinSOp3 x y N)).symm
  have hH : (spinSDot x y N : ManyBodyOpS Λ N).mulVec (basisVecS σ) ∈
      magSubspaceS Λ N (magEigenvalueS σ) :=
    mem_magSubspaceS_of_commute _ _ hcomm
      (basisVecS_mem_magSubspaceS σ)
  rw [mem_magSubspaceS_iff] at hH
  have hentry := congrFun hH σ'
  have hLHS :
      (totalSpinSOp3 Λ N).mulVec
        ((spinSDot x y N : ManyBodyOpS Λ N).mulVec (basisVecS σ)) σ' =
      magEigenvalueS σ' *
        ((spinSDot x y N : ManyBodyOpS Λ N).mulVec (basisVecS σ)) σ' := by
    change ∑ τ, (totalSpinSOp3 Λ N) σ' τ *
        ((spinSDot x y N : ManyBodyOpS Λ N).mulVec (basisVecS σ)) τ = _
    rw [Finset.sum_eq_single σ']
    · rw [totalSpinSOp3_apply_diag]
    · intro τ _ hτne
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hτne), zero_mul]
    · intro hσ; exact (hσ (Finset.mem_univ σ')).elim
  rw [hLHS, Pi.smul_apply, smul_eq_mul] at hentry
  -- Identify (spinSDot · |σ⟩) σ' with the matrix entry spinSDot σ' σ.
  have hSapply :
      (spinSDot x y N : ManyBodyOpS Λ N).mulVec (basisVecS σ) σ' =
        (spinSDot x y N : ManyBodyOpS Λ N) σ' σ := by
    change ∑ σ'' : Λ → Fin (N + 1),
        (spinSDot x y N : ManyBodyOpS Λ N) σ' σ'' * basisVecS σ σ'' =
          (spinSDot x y N : ManyBodyOpS Λ N) σ' σ
    simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ σ
        (fun σ'' => (spinSDot x y N : ManyBodyOpS Λ N) σ' σ'')]
    simp
  rw [hSapply] at hentry
  have hzero :
      (magEigenvalueS σ' - magEigenvalueS σ) *
        (spinSDot x y N : ManyBodyOpS Λ N) σ' σ = 0 := by
    linear_combination hentry
  rcases mul_eq_zero.mp hzero with hmag | hS
  · exact (h (sub_eq_zero.mp hmag).symm).elim
  · exact hS

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

/-! ## Real-valued Heisenberg matrix (for real coupling) -/

/-- The real-part of the Heisenberg Hamiltonian as a real-valued
matrix on the multi-site Hilbert space. For real-coupled `J`, this
matrix completely determines the Hermitian Hamiltonian. -/
noncomputable def heisenbergHamiltonianSReMatrix
    (J : Λ → Λ → ℂ) (N : ℕ) :
    Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℝ :=
  fun σ τ => ((heisenbergHamiltonianS J N) σ τ).re

/-- Component-wise unfolding of `heisenbergHamiltonianSReMatrix`. -/
theorem heisenbergHamiltonianSReMatrix_apply
    (J : Λ → Λ → ℂ) (N : ℕ) (σ τ : Λ → Fin (N + 1)) :
    heisenbergHamiltonianSReMatrix J N σ τ =
      ((heisenbergHamiltonianS J N) σ τ).re := rfl

/-- A spin-`S` Heisenberg Hamiltonian with real coupling is matrix-symmetric.
Direct corollary of Hermiticity plus realness of matrix entries
(`heisenbergHamiltonianS_apply_im_zero`).

For a Hermitian complex matrix with real entries, conjTranspose = transpose,
so IsHermitian implies IsSymm. -/
theorem heisenbergHamiltonianS_isSymm_of_real
    {J : Λ → Λ → ℂ} (hreal_star : ∀ x y, star (J x y) = J x y) (N : ℕ) :
    (heisenbergHamiltonianS (Λ := Λ) J N).IsSymm := by
  have hH := heisenbergHamiltonianS_isHermitian_of_real (Λ := Λ) hreal_star N
  have hreal_im : ∀ x y, (J x y).im = 0 := fun x y => by
    have := hreal_star x y
    rw [Complex.star_def] at this
    have him := congrArg Complex.im this
    rw [Complex.conj_im] at him
    linarith
  ext σ σ'
  rw [Matrix.transpose_apply]
  have hH_apply : (heisenbergHamiltonianS (Λ := Λ) J N) σ σ' =
      star ((heisenbergHamiltonianS (Λ := Λ) J N) σ' σ) := by
    have := congrFun (congrFun hH.eq σ) σ'
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  rw [hH_apply]
  rw [Complex.star_def]
  apply Complex.ext
  · rw [Complex.conj_re]
  · rw [Complex.conj_im,
      heisenbergHamiltonianS_apply_im_zero N hreal_im σ' σ, neg_zero]

end LatticeSystem.Quantum
