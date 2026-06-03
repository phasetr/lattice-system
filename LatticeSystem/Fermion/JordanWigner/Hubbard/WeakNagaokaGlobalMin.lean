import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGroundState
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Quantum.SpinS.RayleighRitzEquality
import LatticeSystem.Quantum.SpinS.RayleighOnEigenvector

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

/-! ## Rayleigh quotient transports between `M` and the all-up block `M_↑` -/

/-- The squared norm is preserved by the all-up embedding:
`⟨upEmbed ξ, upEmbed ξ⟩ = ⟨ξ, ξ⟩`. -/
theorem dotProduct_star_upEmbed (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    dotProduct (star (upEmbed N ξ)) (upEmbed N ξ) = dotProduct (star ξ) ξ := by
  classical
  simp only [dotProduct, Pi.star_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (holeSpinUp N x)
    (fun σ _ hσ => by simp [upEmbed, if_neg hσ])
    (fun hmem => absurd (Finset.mem_univ _) hmem)]
  simp [upEmbed]

/-- The Rayleigh quotient transports along the all-up embedding:
`rayleighOnVec M (upEmbed ξ) = rayleighOnVec M_↑ ξ`. -/
theorem rayleighOnVec_upEmbed (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (htdiag : ∀ i, t i i = 0) (ξ : Fin (N + 1) → ℂ) :
    rayleighOnVec (tasakiEffMatrix N t U) (upEmbed N ξ) =
      rayleighOnVec (tasakiEffMatrixUp N t U) ξ := by
  classical
  unfold rayleighOnVec
  rw [tasakiEffMatrix_mulVec_upEmbed N t U htdiag]
  congr 1
  simp only [dotProduct, Pi.star_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (holeSpinUp N x)
    (fun σ _ hσ => by simp [upEmbed, if_neg hσ])
    (fun hmem => absurd (Finset.mem_univ _) hmem)]
  simp [upEmbed]

/-! ## The all-up minimum dominates the full one-hole minimum -/

/-- `min(M) ≤ min(M_↑)`: the all-up block is a principal submatrix, so its minimum
eigenvalue is at least the full minimum (witnessed by embedding a unit all-up
eigenvector). -/
theorem hermitianMinEigenvalue_le_tasakiEffMatrixUp (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) (htdiag : ∀ i, t i i = 0) :
    hermitianMinEigenvalue (tasakiEffMatrix_isHermitian N t U hJ hU) ≤
      hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N t U hJ hU) := by
  obtain ⟨ξ, hξ_unit, hξ_eig⟩ :=
    exists_unit_eigenvector_hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N t U hJ hU)
  have hupunit : dotProduct (star (upEmbed N ξ)) (upEmbed N ξ) = 1 := by
    rw [dotProduct_star_upEmbed]; exact hξ_unit
  have hle := hermitianMinEigenvalue_le_rayleighOnVec_of_unit
    (tasakiEffMatrix_isHermitian N t U hJ hU) hupunit
  rwa [rayleighOnVec_upEmbed N t U htdiag,
    rayleighOnVec_eq_re_of_eigenvector _ ξ _ hξ_eig hξ_unit, Complex.ofReal_re] at hle

/-! ## The all-up minimum is dominated by the full minimum (Schwarz bound) -/

/-- `star` commutes with the all-up embedding. -/
theorem star_upEmbed (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    star (upEmbed N ξ) = upEmbed N (star ξ) := by
  funext p
  simp only [Pi.star_apply, upEmbed]
  split <;> simp

/-- The all-up block Rayleigh quotient of a real weight vector equals the real
part of the effective-Hamiltonian energy of the corresponding all-up state. -/
theorem rayleighOnVec_tasakiEffMatrixUp_eq (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (htdiag : ∀ i, t i i = 0) (ξ : Fin (N + 1) → ℂ) (hξ : star ξ = ξ) :
    rayleighOnVec (tasakiEffMatrixUp N t U) ξ =
      (hubbardEffEnergy N t U (pfFerroState N ξ)).re := by
  rw [← rayleighOnVec_upEmbed N t U htdiag,
    rayleighOnVec_tasakiEffMatrix_of_real N t U (upEmbed N ξ) (by rw [star_upEmbed, hξ]),
    ← pfFerroState_eq_tasakiExpansion]

/-- `upEmbed` of the ferromagnetized weights equals the ferromagnetic Tasaki
coefficients. -/
theorem upEmbed_ferroXi (N : ℕ) (φ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ) :
    upEmbed N (fun x => (ferroXi N φ x : ℂ)) = fun p => ((ferroCoeff N φ p : ℝ) : ℂ) := by
  funext p
  simp only [upEmbed, ferroCoeff]
  split <;> simp

/-- `min(M_↑) ≤ min(M)` (Tasaki's Schwarz bound (11.2.9)): ferromagnetizing a
real minimum eigenvector of `M` lowers the energy into the all-up sector, so the
all-up minimum is no larger than the full minimum. -/
theorem hermitianMinEigenvalue_tasakiEffMatrixUp_le (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (U : ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) (hpos : ∀ i j, 0 ≤ t i j) :
    hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N (fun i j => (t i j : ℂ))
        (U : ℂ) (tasakiEffMatrix_hJ_of_real htsym)
        (by rw [Complex.star_def, Complex.conj_ofReal])) ≤
      hermitianMinEigenvalue (tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ))
        (U : ℂ) (tasakiEffMatrix_hJ_of_real htsym)
        (by rw [Complex.star_def, Complex.conj_ofReal])) := by
  classical
  have hJ := tasakiEffMatrix_hJ_of_real (t := t) htsym
  have hU : star (U : ℂ) = (U : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  have hM := tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) (U : ℂ) hJ hU
  have hMup := tasakiEffMatrixUp_isHermitian N (fun i j => (t i j : ℂ)) (U : ℂ) hJ hU
  set μ := hermitianMinEigenvalue hM with hμ
  set μup := hermitianMinEigenvalue hMup with hμup
  obtain ⟨φ, hφ_ne, hφ_eig⟩ := exists_real_min_eigenvector_tasakiEffReMatrix N t U htsym htdiag
  have hφ_eigμ : (tasakiEffReMatrix N t).mulVec φ = μ • φ := hφ_eig
  have hnorm_pos : 0 < ∑ p, (φ p) ^ 2 := by
    obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hφ_ne
    rw [Pi.zero_apply] at hp₀
    exact Finset.sum_pos' (fun p _ => sq_nonneg _)
      ⟨p₀, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hp₀))⟩
  have hA : rayleighOnVec (tasakiEffMatrixUp N (fun i j => (t i j : ℂ)) (U : ℂ))
        (fun x => (ferroXi N φ x : ℂ)) =
      tasakiQuadForm N t (ferroCoeff N φ) := by
    rw [rayleighOnVec_tasakiEffMatrixUp_eq N (fun i j => (t i j : ℂ)) (U : ℂ)
        (fun i => by simp [htdiag i]) _
      (by funext x; rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]),
      pfFerroState_eq_tasakiExpansion, upEmbed_ferroXi,
      hubbardEffEnergy_eq_quadForm N t (U : ℂ) htdiag, Complex.ofReal_re]
  have hMφ : (tasakiEffMatrix N (fun i j => (t i j : ℂ)) (U : ℂ)).mulVec (fun p => (φ p : ℂ)) =
      (μ : ℂ) • (fun p => (φ p : ℂ)) := by
    rw [tasakiEffMatrix_eq_map_tasakiEffReMatrix N t U htdiag]
    exact matrix_eigenvec_map_ofReal hφ_eigμ
  have hE : rayleighOnVec (tasakiEffMatrix N (fun i j => (t i j : ℂ)) (U : ℂ))
        (fun p => (φ p : ℂ)) = μ * ∑ p, (φ p) ^ 2 := by
    unfold rayleighOnVec
    rw [hMφ, dotProduct_smul, smul_eq_mul,
      show dotProduct (star (fun p => ((φ p : ℝ) : ℂ))) (fun p => ((φ p : ℝ) : ℂ)) =
          ((∑ p, (φ p) ^ 2 : ℝ) : ℂ) from by
        simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
        push_cast
        exact Finset.sum_congr rfl (fun p _ => by ring),
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hQ : tasakiQuadForm N t φ =
      rayleighOnVec (tasakiEffMatrix N (fun i j => (t i j : ℂ)) (U : ℂ)) (fun p => (φ p : ℂ)) := by
    have hcr : star (fun p => ((φ p : ℝ) : ℂ)) = fun p => ((φ p : ℝ) : ℂ) := by
      funext p; rw [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [rayleighOnVec_tasakiEffMatrix_of_real N (fun i j => (t i j : ℂ)) (U : ℂ)
        (fun p => (φ p : ℂ)) hcr,
      hubbardEffEnergy_eq_quadForm N t (U : ℂ) htdiag, Complex.ofReal_re]
  have hlow := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hMup
    (fun x => (ferroXi N φ x : ℂ))
  have hdot : (dotProduct (star (fun x => ((ferroXi N φ x : ℝ) : ℂ)))
      (fun x => ((ferroXi N φ x : ℝ) : ℂ))).re = ∑ p, (φ p) ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← ferroCoeff_normSq_eq N φ,
      show (∑ p, (ferroCoeff N φ p) ^ 2) = ∑ x, (ferroXi N φ x) ^ 2 from by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_eq_single (holeSpinUp N x)
          (fun σ _ hσ => by simp [ferroCoeff, if_neg hσ])
          (fun hmem => absurd (Finset.mem_univ _) hmem)]
        simp [ferroCoeff]]
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun x _ => by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring)
  rw [hdot, hA] at hlow
  have hchain : μup * ∑ p, (φ p) ^ 2 ≤ μ * ∑ p, (φ p) ^ 2 :=
    le_trans hlow (le_trans (tasakiQuadForm_ferro_le N t hpos φ) (le_of_eq (hQ.trans hE)))
  exact le_of_mul_le_mul_right hchain hnorm_pos

end LatticeSystem.Fermion
