import LatticeSystem.Math.MatrixAnalysis.CommutingEigenspaceInvariance
import LatticeSystem.Math.InvariantSubmoduleEigenvector
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Delocalised eigenmodes of a transitively permutation-invariant matrix

A matrix `t` invariant under a permutation `σ` of its index type commutes with the permutation
matrix of `σ`, so every eigenspace of `t` is invariant under that permutation matrix and therefore
contains an eigenvector `w` of it.  The corresponding eigenvalue is a phase, because `σ` merely
permutes the summands of `∑ x, ‖w x‖`; if the powers of `σ` act transitively, the phase relation
turns into constancy of `x ↦ ‖w x‖`, and rescaling produces a unit vector with
`‖v x‖ ^ 2 = 1 / |index type|` at every index.

The module also records the bridge from a re-enumeration of the spectrum of a Hermitian matrix to
non-triviality of the corresponding eigenspaces, which is what supplies the hypothesis of the
capstone in applications where the eigenvalue is given by a monotone level list rather than by
mathlib's `Matrix.IsHermitian.eigenvalues`.

The two non-trivial ingredients are reused from
`LatticeSystem.Math.MatrixAnalysis.CommutingEigenspaceInvariance` (a commuting matrix preserves
every eigenspace) and `LatticeSystem.Math.InvariantSubmoduleEigenvector` (a non-zero invariant
submodule over an algebraically closed field contains an eigenvector).
-/

namespace LatticeSystem.Math

open Matrix

/-- **A permutation symmetry of the hopping matrix commutes with its permutation matrix**: if
`t (σ i) (σ j) = t i j` then `P_σ · t = t · P_σ`, where `P_σ = σ.toPEquiv.toMatrix`. -/
theorem commute_toPEquiv_toMatrix_of_perm_invariant {n : Type*} [Fintype n] [DecidableEq n]
    {t : Matrix n n ℂ} {σ : Equiv.Perm n} (htrans : ∀ i j, t (σ i) (σ j) = t i j) :
    Commute (σ.toPEquiv.toMatrix : Matrix n n ℂ) t := by
  change (σ.toPEquiv.toMatrix : Matrix n n ℂ) * t = t * σ.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [Matrix.submatrix_apply, id]
  rw [← htrans i (σ.symm j), Equiv.apply_symm_apply]

/-- **Constant modulus along a transitive orbit**: if `w ∘ σ = μ • w` for a nonzero `w` and the
powers of `σ` act transitively, then `x ↦ ‖w x‖` is constant.  The phase `μ` has modulus one
because `σ` only permutes the summands of `∑ x, ‖w x‖`, so the relation is modulus preserving and
propagates along the orbit of any point. -/
theorem norm_apply_eq_norm_apply_of_comp_perm_smul {n : Type*} [Finite n]
    {σ : Equiv.Perm n} {w : n → ℂ} {μ : ℂ}
    (hw : w ∘ σ = μ • w) (hne : w ≠ 0)
    (htransitive : ∀ i j : n, ∃ k : ℕ, (σ ^ k) i = j) (x y : n) :
    ‖w x‖ = ‖w y‖ := by
  have _inst : Fintype n := Fintype.ofFinite n
  have hpt : ∀ z, w (σ z) = μ * w z := fun z => congrFun hw z
  have hsum : ∑ z, ‖w (σ z)‖ = ∑ z, ‖w z‖ := Equiv.sum_comp σ fun z => ‖w z‖
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hne
  have hx₀' : w x₀ ≠ 0 := by simpa using hx₀
  have hpos : 0 < ∑ z, ‖w z‖ :=
    Finset.sum_pos' (fun z _ => norm_nonneg (w z))
      ⟨x₀, Finset.mem_univ x₀, norm_pos_iff.mpr hx₀'⟩
  have hμ : ‖μ‖ = 1 := by
    have hscaled : ∑ z, ‖w (σ z)‖ = ‖μ‖ * ∑ z, ‖w z‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by rw [hpt z, norm_mul]
    have : ‖μ‖ * ∑ z, ‖w z‖ = 1 * ∑ z, ‖w z‖ := by rw [one_mul, ← hscaled, hsum]
    exact mul_right_cancel₀ hpos.ne' this
  have hstep : ∀ z, ‖w (σ z)‖ = ‖w z‖ := fun z => by rw [hpt z, norm_mul, hμ, one_mul]
  have hpow : ∀ (k : ℕ) (z : n), ‖w ((σ ^ k) z)‖ = ‖w z‖ := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
        intro z
        have hz : (σ ^ (k + 1)) z = (σ ^ k) (σ z) := by
          rw [pow_succ]; rfl
        rw [hz, ih (σ z), hstep z]
  obtain ⟨k, hk⟩ := htransitive x y
  rw [← hk, hpow k x]

/-- **The monotone re-enumeration lists genuine eigenvalues**: if the multiset of values of
`ε : n → ℝ` equals the multiset of eigenvalues of a Hermitian `t`, then the eigenspace of `t` at
`ε i` is non-trivial for every `i`. -/
theorem eigenspace_mulVecLin_ne_bot_of_map_eq {n : Type*} [Fintype n] [DecidableEq n]
    {t : Matrix n n ℂ} (hT : t.IsHermitian) {ε : n → ℝ}
    (hspec : Finset.univ.val.map ε = Finset.univ.val.map hT.eigenvalues) (i : n) :
    Module.End.eigenspace t.mulVecLin ((ε i : ℝ) : ℂ) ≠ ⊥ := by
  have hmem : ε i ∈ Finset.univ.val.map hT.eigenvalues := by
    rw [← hspec]
    exact Multiset.mem_map_of_mem ε (Finset.mem_val.mpr (Finset.mem_univ i))
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  rw [Submodule.ne_bot_iff]
  refine ⟨⇑(hT.eigenvectorBasis j), ?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, hT.mulVec_eigenvectorBasis, hj]
    funext x
    simp [Complex.real_smul]
  · exact (WithLp.ofLp_eq_zero 2).ne.2 (hT.eigenvectorBasis.orthonormal.ne_zero j)

/-- **Delocalised eigenmode of a transitively symmetric matrix**: if the hopping matrix `t` is
invariant under a permutation `σ` whose powers act transitively, then every non-trivial eigenspace
of `t` contains a normalised vector of constant modulus, `‖v x‖ ^ 2 = 1 / |Λ|` for every site `x`.
The permutation matrix preserves the eigenspace, which therefore contains an eigenvector of the
permutation; transitivity turns its phase relation into constancy of the modulus. -/
theorem exists_uniformModulus_eigenvector_of_transitive_perm_invariance {n : Type*} [Fintype n]
    {t : Matrix n n ℂ} {lam : ℂ} {σ : Equiv.Perm n}
    (htrans : ∀ i j, t (σ i) (σ j) = t i j)
    (htransitive : ∀ i j : n, ∃ k : ℕ, (σ ^ k) i = j)
    (hlam : Module.End.eigenspace t.mulVecLin lam ≠ ⊥) :
    ∃ v : n → ℂ, t.mulVec v = lam • v ∧ ∀ x, ‖v x‖ ^ 2 = 1 / (Fintype.card n : ℝ) := by
  classical
  have hcomm := commute_toPEquiv_toMatrix_of_perm_invariant (t := t) htrans
  have hinv : Module.End.eigenspace t.mulVecLin lam
      ≤ (Module.End.eigenspace t.mulVecLin lam).comap
          (σ.toPEquiv.toMatrix : Matrix n n ℂ).mulVecLin := by
    intro z hz
    simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using
      mulVec_mem_eigenspace_of_commute (A := (σ.toPEquiv.toMatrix : Matrix n n ℂ)) hcomm hz
  obtain ⟨μ, w, hw_mem, hw_ne, hw_eq⟩ :=
    exists_eigenvector_in_invariant_submodule
      (σ.toPEquiv.toMatrix : Matrix n n ℂ).mulVecLin
      (Module.End.eigenspace t.mulVecLin lam) hinv hlam
  have hw_comp : w ∘ σ = μ • w := by
    rwa [Matrix.mulVecLin_apply, PEquiv.toMatrix_toPEquiv_mulVec] at hw_eq
  have hw_eig : t.mulVec w = lam • w := by
    have hmem := Module.End.mem_eigenspace_iff.mp hw_mem
    rwa [Matrix.mulVecLin_apply] at hmem
  have hconst := norm_apply_eq_norm_apply_of_comp_perm_smul hw_comp hw_ne htransitive
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hw_ne
  have hx₀' : w x₀ ≠ 0 := by simpa using hx₀
  have hCpos : 0 < ‖w x₀‖ := norm_pos_iff.mpr hx₀'
  have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨x₀⟩
  set s : ℝ := Real.sqrt (Fintype.card n) * ‖w x₀‖ with hs_def
  have hspos : 0 < s := mul_pos (Real.sqrt_pos.mpr hcard) hCpos
  refine ⟨((s : ℂ))⁻¹ • w, ?_, fun x => ?_⟩
  · rw [Matrix.mulVec_smul, hw_eig, smul_comm]
  · have hnorm : ‖(((s : ℂ))⁻¹ • w) x‖ = ‖w x₀‖ / s := by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hspos, hconst x x₀, inv_mul_eq_div]
    rw [hnorm, div_pow, hs_def, mul_pow, Real.sq_sqrt hcard.le]
    field_simp

end LatticeSystem.Math
