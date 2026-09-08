import LatticeSystem.Quantum.SpinS.SaturatedBondBound
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Math.FrustrationFree

/-!
# Tasaki §2.4, p. 32: the saturated-ferromagnet energy is the ground-state energy

For a real, ferromagnetic (`(J x y).re ≤ 0`), loopless (`J x x = 0`) spin-`S` Heisenberg coupling
with `1 ≤ N`, the Hamiltonian is bounded below by the saturated-ferromagnet eigenvalue
`saturatedFerromagnetEigenvalueS J N`, the energy of the all-up state `|Φ↑⟩` of eq. (2.4.4).
Tasaki's argument (p. 32) is exactly Lemma A.9 (p. 469): each bond term `−Ŝ_x·Ŝ_y` is bounded
below by `−S²` and `|Φ↑⟩` saturates every one of those bounds simultaneously (eq. (2.4.5)), so
`E_GS = −|B| S²`.  Here the bond bounds are `spinSDot_maxSpin_sub_posSemidef`, the simultaneous
eigenvector is `allAlignedStateS V N 0`, and the frustration-free assembly is
`frustration_free_isGroundState` over the ordered index set `V × V` (each bond appears twice on
both sides of the accounting, so the double counting cancels identically).

Two remarks on faithfulness.  The book fixes the uniform coupling `Ĥ = −∑_{{x,y}∈B} Ŝ_x·Ŝ_y`
(eq. (2.4.1)); what is proved here is the weighted generalization with `(J x y).re ≤ 0`, whose
`J = couplingOf G (−1/2)` instance is the printed statement.  And the bound carries **no**
connectedness hypothesis, matching the book, which establishes `E_GS` on p. 32 before stating
Theorem 2.1 on p. 34.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4, eqs. (2.4.1), (2.4.4), (2.4.5) and the text below (2.4.5), p. 32; Lemma A.9, p. 469.
-/

open Matrix
open scoped ComplexOrder

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The bond terms indexed by ordered pairs sum to the Heisenberg Hamiltonian.  Kept as its own
lemma so that the `V × V` index conversion is discharged in a goal of its own, away from the
frustration-free assembly (`maxRecDepth` is per goal). -/
private theorem sum_prod_smul_spinSDot (J : V → V → ℂ) (N : ℕ) :
    ∑ p : V × V, J p.1 p.2 • spinSDot p.1 p.2 N = heisenbergHamiltonianS (Λ := V) J N := by
  rw [heisenbergHamiltonianS_def, Fintype.sum_prod_type]

/-- For a real coupling vanishing on the diagonal, the saturated-ferromagnet eigenvalue is the
real number `∑_{x,y} (J x y).re · S²` — Tasaki's `E_GS = −|B| S²` (p. 32) in the weighted,
ordered-pair accounting.  The diagonal `N(N+2)/4` branch of
`saturatedFerromagnetEigenvalueS_explicit` is killed by `J x x = 0`. -/
private theorem saturatedFerromagnetEigenvalueS_eq_ofReal_sum {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0) (hJ_diag : ∀ x, J x x = 0) :
    saturatedFerromagnetEigenvalueS (V := V) J N
      = ((∑ p : V × V, (J p.1 p.2).re * ((N : ℝ) / 2 * ((N : ℝ) / 2)) : ℝ) : ℂ) := by
  rw [saturatedFerromagnetEigenvalueS_explicit, Complex.ofReal_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, hJ_diag x]
    simp
  · have hc : ((N : ℂ) / 2 * ((N : ℂ) / 2)) = (((N : ℝ) / 2 * ((N : ℝ) / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [if_neg hxy, hc]
    refine Complex.ext ?_ ?_
    · simp [Complex.mul_re, hJ_real x y]
    · simp [Complex.mul_im, hJ_real x y]

/-- **The saturated-ferromagnet energy is a lower bound for the Hamiltonian** (Tasaki §2.4,
p. 32, via eq. (2.4.5) and Lemma A.9, p. 469): for a real, ferromagnetic, loopless coupling with
`1 ≤ N`, the shifted Hamiltonian `Ĥ − E_GS` is positive semidefinite.  Each ordered-pair term
`J x y • Ŝ_x·Ŝ_y − (J x y).re S²` is `(−(J x y).re) • (S² · 1 − Ŝ_x·Ŝ_y) ≥ 0` by
`spinSDot_maxSpin_sub_posSemidef`, the diagonal terms vanish, and the all-up state saturates
every bond bound (`spinSDot_mulVec_allAlignedStateS_zero_of_ne`), so
`frustration_free_isGroundState` applies with `ε (x,y) = (J x y).re S²`.  No connectedness is
assumed. -/
theorem heisenbergHamiltonianS_sub_saturatedFerromagnetEigenvalueS_posSemidef {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0) (hJ_nonpos : ∀ x y, (J x y).re ≤ 0)
    (hJ_diag : ∀ x, J x x = 0) (hN : 1 ≤ N) :
    (heisenbergHamiltonianS (Λ := V) J N
      - ((saturatedFerromagnetEigenvalueS (V := V) J N).re : ℂ) • 1).PosSemidef := by
  have hreal : ∀ x y : V, ∃ a : ℝ, J x y = (a : ℂ) := fun x y =>
    ⟨(J x y).re, Complex.ext rfl (by rw [hJ_real x y]; simp)⟩
  have hlb : ∀ p ∈ (Finset.univ : Finset (V × V)),
      ((J p.1 p.2 • spinSDot p.1 p.2 N : ManyBodyOpS V N)
        - (((J p.1 p.2).re * ((N : ℝ) / 2 * ((N : ℝ) / 2)) : ℝ) : ℂ) • 1).PosSemidef := by
    rintro ⟨x, y⟩ -
    by_cases hxy : x = y
    · subst hxy
      simpa [hJ_diag x] using (Matrix.PosSemidef.zero (n := V → Fin (N + 1)) (R := ℂ))
    · obtain ⟨a, ha⟩ := hreal x y
      have hle : a ≤ 0 := by
        have := hJ_nonpos x y
        rwa [ha, Complex.ofReal_re] at this
      rw [ha]
      simp only [Complex.ofReal_re]
      have hrw : ((a : ℂ) • spinSDot x y N
            - (((a * ((N : ℝ) / 2 * ((N : ℝ) / 2))) : ℝ) : ℂ) • (1 : ManyBodyOpS V N))
          = ((-a : ℝ) : ℂ) •
            ((((N : ℂ) / 2) * ((N : ℂ) / 2)) • (1 : ManyBodyOpS V N) - spinSDot x y N) := by
        push_cast
        match_scalars <;> ring
      rw [hrw]
      refine (spinSDot_maxSpin_sub_posSemidef hN hxy).smul ?_
      rw [← Complex.ofReal_zero, Complex.real_le_real]
      linarith
  have heig : ∀ p ∈ (Finset.univ : Finset (V × V)),
      (J p.1 p.2 • spinSDot p.1 p.2 N : ManyBodyOpS V N).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1)))
        = (((J p.1 p.2).re * ((N : ℝ) / 2 * ((N : ℝ) / 2)) : ℝ) : ℂ)
          • allAlignedStateS V N (0 : Fin (N + 1)) := by
    rintro ⟨x, y⟩ -
    by_cases hxy : x = y
    · subst hxy
      simp [hJ_diag x]
    · obtain ⟨a, ha⟩ := hreal x y
      rw [ha, Matrix.smul_mulVec, spinSDot_mulVec_allAlignedStateS_zero_of_ne hxy, smul_smul]
      simp only [Complex.ofReal_re]
      congr 1
      push_cast
      ring
  rw [saturatedFerromagnetEigenvalueS_eq_ofReal_sum hJ_real hJ_diag, Complex.ofReal_re,
    ← sum_prod_smul_spinSDot J N]
  exact (LatticeSystem.Math.frustration_free_isGroundState (Finset.univ : Finset (V × V))
    (fun p => J p.1 p.2 • spinSDot p.1 p.2 N)
    (fun p => (J p.1 p.2).re * ((N : ℝ) / 2 * ((N : ℝ) / 2)))
    (allAlignedStateS V N (0 : Fin (N + 1))) hlb heig).1

end LatticeSystem.Quantum
