import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundState
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge

/-!
# Tasaki Theorem 11.5: the all-up minimum is the global one-hole ground energy

`weakNagaoka_theorem_11_5` (`WeakNagaokaGroundState.lean`) produces the
`(2 S_max + 1)`-degenerate multiplet at the *all-up sector* minimum energy
`E = hermitianMinEigenvalue M_↑`. To match Tasaki's statement ("among the
*ground states* …") we upgrade this to the *global* one-hole sector minimum:
`hermitianMinEigenvalue M_↑ = hermitianMinEigenvalue M`.

The `≤` direction (`hermitianMinEigenvalue M ≤ hermitianMinEigenvalue M_↑`) is
the trivial principal-submatrix inequality (via `upEmbed`). The `≥` direction is
Tasaki's Schwarz bound (11.2.9): ferromagnetizing any one-hole state lowers its
energy. Since the Tasaki matrix `M` is real (its entries are `-t_{x,y}` times an
indicator, `tasakiEffReMatrix`), a global minimum eigenvector can be taken real
(`RealComplexEigenspaceBridge`), letting us apply the existing real Schwarz bound
`tasakiQuadForm_ferro_le`.

This file records the real form of `M` and that `M = M_ℝ.map ofReal`.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, eq. (11.2.9), pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The one-hole Tasaki index is nonempty (the hole can sit at site `0`, all-up). -/
instance instNonemptyHoleSpinSigma (N : ℕ) :
    Nonempty ((x : Fin (N + 1)) × HoleSpin N x) :=
  ⟨⟨0, holeSpinUp N 0⟩⟩

/-- The real Tasaki matrix: the `(11.2.5)` matrix elements of `Ĥ_eff` as real
numbers. `M_ℝ ⟨y,τ⟩ ⟨x,σ⟩ = -t_{x,y} · [σ_{x→y} = τ]` for `x ≠ y`, `0` on the
diagonal. -/
noncomputable def tasakiEffReMatrix (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) :
    Matrix ((x : Fin (N + 1)) × HoleSpin N x) ((x : Fin (N + 1)) × HoleSpin N x) ℝ :=
  fun q p =>
    if p.1 = q.1 then 0
    else -t p.1 q.1 *
      (if hubbardOneHoleConfig N q.1 (hubbardSpinMove N p.2.val p.1 q.1) =
          hubbardOneHoleConfig N q.1 q.2.val then 1 else 0)

/-- The (complex) Tasaki matrix of `Ĥ_eff` is the real Tasaki matrix cast to `ℂ`:
`M = M_ℝ.map (ofReal)`. So `M` is a real matrix in disguise, and its eigenvectors
can be taken real. -/
theorem tasakiEffMatrix_eq_map_tasakiEffReMatrix (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (U : ℝ) (htdiag : ∀ i, t i i = 0) :
    tasakiEffMatrix N (fun i j => (t i j : ℂ)) (U : ℂ) =
      (tasakiEffReMatrix N t).map (Complex.ofReal) := by
  ext q p
  obtain ⟨y, τ⟩ := q
  obtain ⟨x, σ⟩ := p
  rw [tasakiEffMatrix_apply, Matrix.map_apply]
  simp only [tasakiEffReMatrix, tasakiState]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Complex.ofReal_zero]
    exact hubbardEffective_tasaki_matrixElement_diag N x σ.val τ.val (fun i j => (t i j : ℂ))
      (U : ℂ) (fun i => by simp [htdiag i])
  · rw [hubbardEffective_tasaki_matrixElement N x y σ.val τ.val (fun i j => (t i j : ℂ))
      (U : ℂ) hxy, if_neg hxy]
    split <;> push_cast <;> ring

/-- For real symmetric hopping, the complex-cast Hermitian hypotheses of the
Tasaki matrix hold. -/
theorem tasakiEffMatrix_hJ_of_real {N : ℕ} {t : Fin (N + 1) → Fin (N + 1) → ℝ}
    (htsym : ∀ i j, t i j = t j i) :
    ∀ i j, star ((t i j : ℂ)) = (t j i : ℂ) :=
  fun i j => by rw [Complex.star_def, Complex.conj_ofReal, htsym i j]

/-- The Tasaki matrix has a **real** minimum eigenvector: since `M = M_ℝ.map ofReal`
is a real matrix in disguise, a complex minimum eigenvector has a nonzero real or
imaginary part that is a real eigenvector of `M_ℝ` at the same (real) eigenvalue. -/
theorem exists_real_min_eigenvector_tasakiEffReMatrix (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (U : ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    ∃ φ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ, φ ≠ 0 ∧
      (tasakiEffReMatrix N t).mulVec φ =
        (hermitianMinEigenvalue (tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ))
          (U : ℂ) (tasakiEffMatrix_hJ_of_real htsym) (by rw [Complex.star_def,
            Complex.conj_ofReal]))) • φ := by
  classical
  set hM := tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) (U : ℂ)
    (tasakiEffMatrix_hJ_of_real htsym)
    (by rw [Complex.star_def, Complex.conj_ofReal]) with hMdef
  obtain ⟨v, hv_ne, hv_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hM
  have hv_map : (tasakiEffReMatrix N t).map (Complex.ofReal) *ᵥ v =
      ((hermitianMinEigenvalue hM : ℝ) : ℂ) • v := by
    rw [← tasakiEffMatrix_eq_map_tasakiEffReMatrix N t U htdiag]; exact hv_eig
  by_cases hre : (fun i => (v i).re) = 0
  · refine ⟨fun i => (v i).im, ?_, matrix_eigenvec_im_of_complex hv_map⟩
    intro him
    apply hv_ne
    funext i
    have hr := congrFun hre i
    have hi := congrFun him i
    simp only [Pi.zero_apply] at hr hi ⊢
    exact Complex.ext hr hi
  · exact ⟨fun i => (v i).re, hre, matrix_eigenvec_re_of_complex hv_map⟩

end LatticeSystem.Fermion
