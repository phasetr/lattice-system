import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpanning
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralBasisHN
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState

/-!
# Hubbard low-`U` impossibility, trial-state inputs: spectral foundation

Foundational layer extracted from `HubbardImpossibilityLowUTrial.lean` for build speed.
This file collects the combinatorial fact that the maximally up-filled configuration is
the all-up configuration, the spectral-coordinate form of the hopping matrix, and the
site expansion of the eigenmode number operator.

The kinetic operator as a sum of eigenmode number operators and the kinetic energy of an
eigenmode Slater determinant are kept in the capstone module
`HubbardImpossibilityLowUTrial.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-! ## Combinatorial: the maximally up-filled configuration is the all-up configuration -/

/-- **A maximally up-filled configuration is the all-up configuration.**  If a configuration `w` has
`M + 1` up-occupied sites (out of `M + 1`) and `0` down-occupied sites, then it is the all-up
configuration `k ↦ if k even then 1 else 0`.  (Public copy of the combinatorial support lemma
used by the §11.1.1 ground-state structure.) -/
theorem hubbardImpossibilityLowU_config_eq_allUp (w : Fin (2 * M + 2) → Fin 2)
    (hup : (∑ i : Fin (M + 1), (w (spinfulIndex M i 0)).val) = M + 1)
    (hdown : (∑ i : Fin (M + 1), (w (spinfulIndex M i 1)).val) = 0) :
    w = (fun k : Fin (2 * M + 2) => if k.val % 2 = 0 then 1 else 0) := by
  have hupOne : ∀ i : Fin (M + 1), w (spinfulIndex M i 0) = 1 := by
    intro i
    have hle : ∀ j : Fin (M + 1), (w (spinfulIndex M j 0)).val ≤ 1 := fun j =>
      Nat.lt_succ_iff.mp (w (spinfulIndex M j 0)).isLt
    have hcard : (∑ _j : Fin (M + 1), 1) = M + 1 := by simp
    have heq : ∀ j : Fin (M + 1), (w (spinfulIndex M j 0)).val = 1 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j₀, hj₀⟩ := hcon
      have hj₀lt : (w (spinfulIndex M j₀ 0)).val < 1 := lt_of_le_of_ne (hle j₀) hj₀
      have : (∑ j : Fin (M + 1), (w (spinfulIndex M j 0)).val) < ∑ _j : Fin (M + 1), 1 :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨j₀, Finset.mem_univ _, hj₀lt⟩
      rw [hcard, hup] at this
      exact lt_irrefl _ this
    exact Fin.ext (by rw [heq i, Fin.val_one])
  have hdownZero : ∀ i : Fin (M + 1), w (spinfulIndex M i 1) = 0 := by
    intro i
    have : (w (spinfulIndex M i 1)).val = 0 := by
      by_contra hcon
      have hpos : 0 < (w (spinfulIndex M i 1)).val := Nat.pos_of_ne_zero hcon
      have : 0 < (∑ j : Fin (M + 1), (w (spinfulIndex M j 1)).val) :=
        Finset.sum_pos' (fun j _ => Nat.zero_le _) ⟨i, Finset.mem_univ _, hpos⟩
      rw [hdown] at this
      exact lt_irrefl _ this
    exact Fin.ext this
  funext k
  obtain ⟨i, r, hir⟩ : ∃ (i : Fin (M + 1)) (r : Fin 2), k = spinfulIndex M i r := by
    refine ⟨⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by have := k.isLt; omega)⟩,
      ⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    apply Fin.ext; simp only [spinfulIndex]; omega
  subst hir
  by_cases hr : r = 0
  · subst hr
    rw [hupOne i, if_pos (by simp [spinfulIndex])]
  · have hr1 : r = 1 := by omega
    subst hr1
    have hodd : (spinfulIndex M i 1).val % 2 = 1 := by simp [spinfulIndex]
    rw [hdownZero i, if_neg (by omega)]

/-! ## Spectral coordinate form of the hopping matrix -/

/-- **Spectral coordinate form of a Hermitian matrix in its eigenbasis**:
`t_{yx} = Σ_j ε_j · e_j(y) · conj(e_j(x))`, where `e_j = eigenbasisAsBasis hT j` and
`ε_j = hT.eigenvalues j`.  Proven by checking that the right-hand side matrix acts as `ε_k`
on each eigenvector `e_k` (orthonormality collapses the inner sum to a Kronecker delta), so it
agrees with `t` on the spanning eigenbasis, hence equals `t`. -/
theorem hubbardSpectral_entry {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (y x : Fin (M + 1)) :
    (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
        * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y
        * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)) = t y x := by
  classical
  -- The candidate matrix `Mmat y x = Σ_j ε_j e_j(y) conj(e_j(x))`.
  set Mmat : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ :=
    Matrix.of (fun y x => ∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
        * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y
        * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)) with hMmat
  -- `Mmat` acts as `ε_k` on each eigenvector `e_k`.
  have hact : ∀ k : Fin (M + 1),
      Mmat.mulVec (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ)
        = (hT.eigenvalues k : ℂ) • (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) := by
    intro k
    funext yv
    rw [Pi.smul_apply, smul_eq_mul]
    simp only [hMmat, Matrix.mulVec, Matrix.of_apply, dotProduct]
    -- `Σ_x (Σ_j ε_j e_j(yv) conj(e_j(x))) e_k(x)`
    rw [show (∑ xv : Fin (M + 1),
          (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
              * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) yv
              * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) xv))
            * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) xv)
        = ∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
            * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) yv
            * (∑ xv : Fin (M + 1),
                star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) xv)
                  * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) xv) from by
      rw [show (∑ xv : Fin (M + 1),
            (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
                * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) yv
                * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) xv))
              * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) xv)
          = ∑ xv : Fin (M + 1), ∑ j : Fin (M + 1),
              ((hT.eigenvalues j : ℂ) * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) yv
                  * star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) xv))
                * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) xv from by
        refine Finset.sum_congr rfl fun xv _ => ?_
        rw [Finset.sum_mul]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun xv _ => ?_
      ring]
    rw [show (∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
          * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) yv
          * (∑ xv : Fin (M + 1),
              star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) xv)
                * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) xv))
        = ∑ j : Fin (M + 1), (hT.eigenvalues j : ℂ)
            * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) yv
            * (if j = k then (1 : ℂ) else 0) from by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eigenbasisAsBasis_orthonormal_sum hT j k]]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro j _ hjk
      rw [if_neg hjk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  -- `Mmat` and `t` agree on all eigenvectors, hence on the whole space, hence as matrices.
  have hmulVec : ∀ v : Fin (M + 1) → ℂ, Mmat.mulVec v = t.mulVec v := by
    intro v
    -- expand `v` in the eigenbasis
    have hexp : v = ∑ k : Fin (M + 1),
        (eigenbasisAsBasis hT).repr v k • (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) := by
      conv_lhs => rw [← (eigenbasisAsBasis hT).sum_repr v]
    rw [hexp, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hact k, eigenbasisAsBasis_mulVec hT k]
  -- conclude `Mmat = t`
  have hMeq : Mmat = t := by
    ext yv xv
    have := congrFun (hmulVec (Pi.single xv 1)) yv
    rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  have := congrFun (congrFun hMeq y) x
  rw [hMmat] at this
  simpa only [Matrix.of_apply] using this

/-! ## Eigenmode number operator: site expansion -/

/-- **Site expansion of the eigenmode number operator**
`n̂_{j,σ} = Σ_x Σ_y (conj(e_j(x))·e_j(y)) • (ĉ†_{yσ}ĉ_{xσ})`: expand both smeared factors of
`eigenNumberOp = Ĉ†_σ(e_j)·Ĉ_σ(ē_j)` into site operators and distribute (annihilation index `x`
outer, creation index `y` inner — matching the natural smul-product expansion). -/
theorem eigenNumberOp_eq_site_sum {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (j : Fin (M + 1)) (σ : Fin 2) :
    eigenNumberOp hT j σ
      = ∑ x : Fin (M + 1), ∑ y : Fin (M + 1),
          (star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)
              * (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) y) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M y σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) := by
  rw [eigenNumberOp]
  simp only [spinfulCreationFromVector, spinfulAnnihilationFromVector, Finset.sum_mul,
    Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, Pi.star_apply]

end LatticeSystem.Fermion
