import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetryRaising
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulNumberHermitian

/-!
# Hermiticity and total-`Ŝ⁻` invariance of the ferromagnetic t-J model (Tasaki §11.5)

`Ĥ_tJ` is self-adjoint, and `[Ĥ_tJ, Ŝ⁻_tot] = 0`.  With the total-`Ŝ³` conservation
(`TJSpinSymmetry.lean`) and the total-`Ŝ⁺` invariance (`TJSpinSymmetryRaising.lean`), this completes
the **full SU(2) invariance** of the t-J Hamiltonian (Issue #4230 PR1), feeding the spin-½ sector
reduction (Theorem A.17) for the discharge of Proposition 11.24.  Hermiticity is also what makes the
sector matrix real symmetric for the Perron–Frobenius step (Theorem A.18).

The interaction `J Σ_{⟨x,y⟩}(n̂_x n̂_y/4 − Ŝ_x·Ŝ_y)` is self-adjoint *as a sum*: each bond term has
`(f x y)ᴴ = f y x` (since `(Ŝ_x·Ŝ_y)ᴴ = Ŝ_y·Ŝ_x`), and the ordered double sum over the symmetric
adjacency is invariant under `Finset.sum_comm`.  The lowering invariance follows from the raising
one by adjoints, using `Ĥ_tJ` Hermitian and `(Ŝ⁺_tot)ᴴ = Ŝ⁻_tot`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, eq. (11.5.4), p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ### Adjoints of the site spin operators -/

/-- `(Ŝ⁺_x)ᴴ = Ŝ⁻_x`. -/
theorem fermionSiteSpinPlus_conjTranspose (N : ℕ) (x : Fin (N + 1)) :
    (fermionSiteSpinPlus N x)ᴴ = fermionSiteSpinMinus N x := by
  unfold fermionSiteSpinPlus fermionSiteSpinMinus
  rw [Matrix.conjTranspose_mul, fermionDownAnnihilation_conjTranspose,
    fermionUpCreation_conjTranspose]

/-- `(Ŝ⁻_x)ᴴ = Ŝ⁺_x`. -/
theorem fermionSiteSpinMinus_conjTranspose (N : ℕ) (x : Fin (N + 1)) :
    (fermionSiteSpinMinus N x)ᴴ = fermionSiteSpinPlus N x := by
  unfold fermionSiteSpinPlus fermionSiteSpinMinus
  rw [Matrix.conjTranspose_mul, fermionUpAnnihilation_conjTranspose,
    fermionDownCreation_conjTranspose]

/-- `Ŝ³_x` is self-adjoint. -/
theorem fermionSiteSpinZ_isHermitian (N : ℕ) (x : Fin (N + 1)) :
    (fermionSiteSpinZ N x).IsHermitian := by
  unfold fermionSiteSpinZ
  refine (Matrix.IsHermitian.sub ?_ ?_).smul
    (by rw [isSelfAdjoint_iff]; norm_num [Complex.ext_iff])
  · rw [show fermionUpCreation N x * fermionUpAnnihilation N x = fermionUpNumber N x from rfl]
    exact fermionUpNumber_isHermitian N x
  · rw [show fermionDownCreation N x * fermionDownAnnihilation N x = fermionDownNumber N x from rfl]
    exact fermionDownNumber_isHermitian N x

/-- `(Ŝ_x · Ŝ_y)ᴴ = Ŝ_y · Ŝ_x` (the dot product is *not* self-adjoint termwise; its adjoint swaps
the two sites). -/
theorem fermionSpinDot_conjTranspose (N : ℕ) (x y : Fin (N + 1)) :
    (fermionSpinDot N x y)ᴴ = fermionSpinDot N y x := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff, Complex.star_def]
  unfold fermionSpinDot
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    fermionSiteSpinPlus_conjTranspose, fermionSiteSpinMinus_conjTranspose,
    fermionSiteSpinMinus_conjTranspose, fermionSiteSpinPlus_conjTranspose,
    (fermionSiteSpinZ_isHermitian N x).eq, (fermionSiteSpinZ_isHermitian N y).eq, h2]

/-- The per-site total number `n̂_x` is self-adjoint. -/
theorem fermionSiteNumber_isHermitian (N : ℕ) (x : Fin (N + 1)) :
    (fermionSiteNumber N x).IsHermitian := by
  unfold fermionSiteNumber
  exact (fermionUpNumber_isHermitian N x).add (fermionDownNumber_isHermitian N x)

/-! ### Hermiticity of the t-J Hamiltonian -/

/-- **`Ĥ_tJ` is self-adjoint.** -/
theorem tJHamiltonian_isHermitian (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) : (tJHamiltonian N G τ J).IsHermitian := by
  unfold tJHamiltonian
  refine Matrix.IsHermitian.add ?_ ?_
  · -- `−τ · (P̂hc K̂ P̂hc)` self-adjoint.
    refine Matrix.IsHermitian.smul ?_
      (by rw [isSelfAdjoint_iff, star_neg, Complex.star_def, Complex.conj_ofReal])
    have hP : (hubbardHardcoreProjection N)ᴴ = hubbardHardcoreProjection N :=
      (hubbardHardcoreProjection_isHermitian N).eq
    have h := Matrix.isHermitian_conjTranspose_mul_mul (hubbardHardcoreProjection N)
      (hubbardKineticOnGraph_isHermitian N G (by rw [star_one]))
    rwa [hP] at h
  · -- `J · Σ (n̂n̂/4 − Ŝ·Ŝ)` self-adjoint (sum-level symmetry).
    refine Matrix.IsHermitian.smul ?_
      (by rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal])
    have key : ∀ a b : Fin (N + 1),
        (if G.Adj a b then (1 / 4 : ℂ) • (fermionSiteNumber N a * fermionSiteNumber N b) -
            fermionSpinDot N a b else 0)ᴴ
          = if G.Adj b a then (1 / 4 : ℂ) • (fermionSiteNumber N b * fermionSiteNumber N a) -
              fermionSpinDot N b a else 0 := by
      intro a b
      have h4 : star (1 / 4 : ℂ) = 1 / 4 := by norm_num [Complex.ext_iff, Complex.star_def]
      by_cases h : G.Adj a b
      · simp only [h, G.symm h, if_true]
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
          (fermionSiteNumber_isHermitian N a).eq, (fermionSiteNumber_isHermitian N b).eq,
          fermionSpinDot_conjTranspose, h4]
      · have h' : ¬ G.Adj b a := fun hba => h hba.symm
        simp only [h, h', if_false, Matrix.conjTranspose_zero]
    calc (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
            (if G.Adj x y then (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
              fermionSpinDot N x y else 0))ᴴ
        = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
            (if G.Adj x y then (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
              fermionSpinDot N x y else 0)ᴴ := by
          simp only [Matrix.conjTranspose_sum]
      _ = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
            (if G.Adj y x then (1 / 4 : ℂ) • (fermionSiteNumber N y * fermionSiteNumber N x) -
              fermionSpinDot N y x else 0) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          exact key x y
      _ = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
            (if G.Adj x y then (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) -
              fermionSpinDot N x y else 0) := Finset.sum_comm

/-! ### Total-`Ŝ⁻` invariance -/

/-- **Total-`Ŝ⁻` invariance of the ferromagnetic t-J model:** `[Ĥ_tJ, Ŝ⁻_tot] = 0`. -/
theorem fermionTotalSpinMinus_commute_tJHamiltonian (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    Commute (fermionTotalSpinMinus N) (tJHamiltonian N G τ J) := by
  have hplus := (fermionTotalSpinPlus_commute_tJHamiltonian N G τ J).eq
  have hH := (tJHamiltonian_isHermitian N G τ J).eq
  have hadj := congrArg Matrix.conjTranspose hplus
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose N, hH] at hadj
  exact hadj.symm

end LatticeSystem.Fermion
