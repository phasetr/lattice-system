import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationGroundEnergy
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueContinuous

/-!
# Minimum energy of a Hamiltonian restricted to a subspace (Tasaki Theorem 10.4)

This file formalizes the **minimum energy on a subspace** ingredient of Tasaki Theorem 10.4
(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.2, p. 350; proof pp. 351–353): for a Hamiltonian `H` and a candidate low-energy subspace
`W`, the quantity

  `minEnergyOn W H = inf { re ⟪v, H v⟫ | v ∈ W, ‖v‖ = 1 }`

is the lowest value the energy functional attains on the unit sphere of `W`.

Theorem 10.4 is a statement about the **repulsive** Hubbard model at half filling `N = |Λ|`:
every ground state has total spin `Stot = ||A| − |B||/2`, and the ground states are exactly
`2 Stot + 1 = ||A| − |B|| + 1` fold degenerate. Tasaki's proof works inside the balanced spin-`z`
sector `H_{N/2,N/2}` (for odd `N`, `H_{(N+1)/2,(N−1)/2}`) and carries that sector by the **Shiba
transformation** to the **attractive** model (eqs. (10.2.10)/(10.2.11)), where Theorem 10.2
supplies a unique ground state; the total-spin value is then pinned by continuously deforming the
couplings (`U_x → U`, `t_{x,y} → ±λ`) and letting `λ → 0` (p. 353). `minEnergyOn` is the
sector-restricted energy functional such a deformation argument varies, which is why reachability
and parameter continuity are proved for it here.

Provenance: the contents are generic matrix analysis, not a formalization of a numbered Tasaki
statement; the citation records which argument they are built for.

This is a **thin wrapper** around existing infrastructure:

* reachability identifies `minEnergyOn` with the ground eigenvalue supplied by
  `exists_isGroundEigenvalueOn`, its variational sharpness coming from
  `IsGroundEigenvalueOn.mul_norm_sq_le` (`DegeneratePerturbationGroundEnergy.lean`);
* the entry-norm Lipschitz bound and the parameter-continuity corollary mirror
  `abs_hermitianMinEigenvalue_sub_le_sum_entryNorms` and `Continuous.hermitianMinEigenvalue_comp`
  (`HermitianMinEigenvalueLipschitz.lean` / `HermitianMinEigenvalueContinuous.lean`), specialized
  from the whole space to unit vectors of a fixed nonzero subspace `W`.

Unlike `hermitianMinEigenvalue`, `minEnergyOn` does not require `H` to be Hermitian to be
*defined*: only the real part of the (possibly non-Hermitian) Rayleigh quotient is taken. The
Hermitian hypothesis is only needed for the reachability statement, where it guarantees an
eigenvector witness.
-/

namespace LatticeSystem.Math

open Matrix LatticeSystem.Quantum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **minimum energy** of `H` on the subspace `W`: the infimum, over unit vectors `v ∈ W`, of
the real part of the Rayleigh quotient `⟪v, H v⟫` — the sector-restricted energy functional varied
in the proof of Tasaki Theorem 10.4 (§10.2.2, pp. 351–353).  (For `W = ⊥` there is
no unit vector and the infimum degenerates to the junk value `minEnergyOn ⊥ H = sInf ∅ = 0`, which
is why the lower bounds below assume `W ≠ ⊥`.) -/
noncomputable def minEnergyOn (W : Submodule ℂ (EuclideanSpace ℂ n)) (H : Matrix n n ℂ) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ W, ‖v‖ = 1 ∧ r = RCLike.re (inner ℂ v (Matrix.toEuclideanLin H v))}

/-- The energy at a unit vector is bounded by the sum of entrywise norms.  This is the
`EuclideanSpace`-side form of `abs_rayleighOnVec_le_sum_entryNorms_of_unit`, obtained by
transporting the inner product to the matrix-side dot product. -/
private theorem abs_re_inner_toEuclideanLin_le_sum_entryNorms (A : Matrix n n ℂ)
    {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1) :
    |RCLike.re (inner ℂ v (Matrix.toEuclideanLin A v))| ≤ ∑ i, ∑ j, ‖A i j‖ := by
  have hunit : star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  have hbridge : RCLike.re (inner ℂ v (Matrix.toEuclideanLin A v))
      = rayleighOnVec A (WithLp.ofLp v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, rayleighOnVec]
    change (A *ᵥ WithLp.ofLp v ⬝ᵥ star (WithLp.ofLp v)).re = _
    rw [dotProduct_comm]
  rw [hbridge]
  exact abs_rayleighOnVec_le_sum_entryNorms_of_unit A hunit

/-- The energies of `H` at unit vectors of a nonzero subspace form a nonempty set: any nonzero
vector of `W` normalises to a unit vector of `W`. -/
private theorem energySet_nonempty {W : Submodule ℂ (EuclideanSpace ℂ n)} (hW : W ≠ ⊥)
    (H : Matrix n n ℂ) :
    {r : ℝ | ∃ v ∈ W, ‖v‖ = 1
      ∧ r = RCLike.re (inner ℂ v (Matrix.toEuclideanLin H v))}.Nonempty := by
  obtain ⟨w, hwW, hwne⟩ := (Submodule.ne_bot_iff W).mp hW
  exact ⟨_, (‖w‖⁻¹ : ℂ) • w, W.smul_mem _ hwW, norm_smul_inv_norm hwne, rfl⟩

/-- The energies of `H` at unit vectors are bounded below by `-∑ ‖H i j‖`, so the infimum defining
`minEnergyOn` is a genuine greatest lower bound. -/
private theorem energySet_bddBelow (W : Submodule ℂ (EuclideanSpace ℂ n)) (H : Matrix n n ℂ) :
    BddBelow {r : ℝ | ∃ v ∈ W, ‖v‖ = 1
      ∧ r = RCLike.re (inner ℂ v (Matrix.toEuclideanLin H v))} := by
  refine ⟨-∑ i, ∑ j, ‖H i j‖, ?_⟩
  rintro r ⟨v, -, hv, rfl⟩
  exact neg_le_of_abs_le (abs_re_inner_toEuclideanLin_le_sum_entryNorms H hv)

/-- Variational upper bound: every unit vector of `W` is a trial state for `minEnergyOn W H`.
Kept `private` because the public `minEnergyOn_isGroundEigenvalueOn` recovers it for Hermitian `H`
preserving `W`; a consumer needing the bound for a non-Hermitian `H` or a non-invariant `W` cannot
derive it from the public API and should promote this lemma instead of restating it. -/
private theorem minEnergyOn_le {W : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ}
    {v : EuclideanSpace ℂ n} (hvW : v ∈ W) (hv : ‖v‖ = 1) :
    minEnergyOn W H ≤ RCLike.re (inner ℂ v (Matrix.toEuclideanLin H v)) :=
  csInf_le (energySet_bddBelow W H) ⟨v, hvW, hv, rfl⟩

/-- Variational lower bound: a constant dominated by the energy of every unit vector of a nonzero
`W` is dominated by `minEnergyOn W H`.  `private` for the same reason as `minEnergyOn_le`: it is
recoverable from `minEnergyOn_isGroundEigenvalueOn` only in the Hermitian invariant case. -/
private theorem le_minEnergyOn {W : Submodule ℂ (EuclideanSpace ℂ n)} (hW : W ≠ ⊥)
    {H : Matrix n n ℂ} {c : ℝ}
    (h : ∀ v ∈ W, ‖v‖ = 1 → c ≤ RCLike.re (inner ℂ v (Matrix.toEuclideanLin H v))) :
    c ≤ minEnergyOn W H := by
  refine le_csInf (energySet_nonempty hW H) ?_
  rintro r ⟨v, hvW, hv, rfl⟩
  exact h v hvW hv

/-- **Reachability**: if `H` is Hermitian and preserves the nonzero subspace `W`, then
`minEnergyOn W H` is the ground eigenvalue of `H` on `W`, attained by a unit eigenvector of `H`
lying in `W`. The ground eigenvalue `E` itself comes from `exists_isGroundEigenvalueOn`; the two
inequalities identifying it with `minEnergyOn W H` are the variational bounds, the `≥` direction
being the sharpness statement `IsGroundEigenvalueOn.mul_norm_sq_le` and the `≤` direction the
trial state obtained by normalising a ground eigenvector. -/
theorem minEnergyOn_isGroundEigenvalueOn {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {W : Submodule ℂ (EuclideanSpace ℂ n)}
    (hInv : ∀ v ∈ W, Matrix.toEuclideanLin H v ∈ W) (hW : W ≠ ⊥) :
    IsGroundEigenvalueOn W H (minEnergyOn W H) := by
  obtain ⟨E, hE⟩ := exists_isGroundEigenvalueOn hH hInv hW
  obtain ⟨φ, hφW, hφne, hφeig⟩ := hE.1
  have heq : minEnergyOn W H = E := by
    refine le_antisymm ?_ (le_minEnergyOn hW ?_)
    · have hvnorm : ‖(‖φ‖⁻¹ : ℂ) • φ‖ = 1 := norm_smul_inv_norm hφne
      have hvenergy : RCLike.re (inner ℂ ((‖φ‖⁻¹ : ℂ) • φ)
          (Matrix.toEuclideanLin H ((‖φ‖⁻¹ : ℂ) • φ))) = E := by
        rw [map_smul, hφeig, smul_comm, inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm]
        simp
      rw [← hvenergy]
      exact minEnergyOn_le (W.smul_mem _ hφW) hvnorm
    · intro v hvW hv
      have hb := IsGroundEigenvalueOn.mul_norm_sq_le hH hInv hE v hvW
      rwa [hv, one_pow, mul_one] at hb
  rw [heq]
  exact hE

/-- **Entry-norm Lipschitz continuity** of `minEnergyOn W` in the matrix argument: bounded by the
sum of entrywise norm differences, uniformly over the choice of nonzero subspace `W`. Mirrors
`abs_hermitianMinEigenvalue_sub_le_sum_entryNorms`, restricted to unit vectors of `W` rather than
the whole space. -/
theorem abs_minEnergyOn_sub_le_sum_entryNorms {W : Submodule ℂ (EuclideanSpace ℂ n)}
    (hW : W ≠ ⊥) (H₁ H₂ : Matrix n n ℂ) :
    |minEnergyOn W H₁ - minEnergyOn W H₂| ≤ ∑ i, ∑ j, ‖(H₁ - H₂) i j‖ := by
  have key : ∀ A B : Matrix n n ℂ, minEnergyOn W A ≤ minEnergyOn W B + ∑ i, ∑ j, ‖(A - B) i j‖ := by
    intro A B
    refine sub_le_iff_le_add.mp (le_minEnergyOn hW ?_)
    intro v hvW hv
    have h1 : minEnergyOn W A ≤ RCLike.re (inner ℂ v (Matrix.toEuclideanLin A v)) :=
      minEnergyOn_le hvW hv
    have hdiff : RCLike.re (inner ℂ v (Matrix.toEuclideanLin (A - B) v))
        = RCLike.re (inner ℂ v (Matrix.toEuclideanLin A v))
          - RCLike.re (inner ℂ v (Matrix.toEuclideanLin B v)) := by
      rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub]
    have h2 : RCLike.re (inner ℂ v (Matrix.toEuclideanLin (A - B) v)) ≤ ∑ i, ∑ j, ‖(A - B) i j‖ :=
      le_of_abs_le (abs_re_inner_toEuclideanLin_le_sum_entryNorms (A - B) hv)
    linarith
  have hsym : (∑ i, ∑ j, ‖(H₂ - H₁) i j‖) = ∑ i, ∑ j, ‖(H₁ - H₂) i j‖ := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show (H₂ - H₁) i j = -((H₁ - H₂) i j) from by rw [Matrix.sub_apply, Matrix.sub_apply]; ring,
      norm_neg]
  have h12 := key H₁ H₂
  have h21 := key H₂ H₁
  rw [hsym] at h21
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- **Continuity of `minEnergyOn W` under a continuous matrix-valued parameter**: if
`F : X → Matrix n n ℂ` is continuous, so is `x ↦ minEnergyOn W (F x)`. Mirrors
`Continuous.hermitianMinEigenvalue_comp`, via the Lipschitz bound
`abs_minEnergyOn_sub_le_sum_entryNorms` in place of the Hermitian-specific one. -/
theorem Continuous.minEnergyOn_comp {W : Submodule ℂ (EuclideanSpace ℂ n)} (hW : W ≠ ⊥)
    {X : Type*} [PseudoMetricSpace X] {F : X → Matrix n n ℂ} (hF : Continuous F) :
    Continuous (fun x => minEnergyOn W (F x)) := by
  refine Metric.continuous_iff.mpr (fun x₀ ε hε => ?_)
  have hcont : ContinuousAt (fun x => ∑ i, ∑ j, ‖(F x - F x₀) i j‖) x₀ :=
    continuous_sum_entryNorms.continuousAt.comp
      (hF.sub (continuous_const : Continuous (fun _ : X => F x₀))).continuousAt
  have hzero : (∑ i, ∑ j, ‖(F x₀ - F x₀) i j‖) = 0 := by simp
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont ε hε
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hsumlt : ∑ i, ∑ j, ‖(F x - F x₀) i j‖ < ε := by
    have h := hδ hx
    rw [hzero, Real.dist_eq, sub_zero] at h
    have hnn : (0 : ℝ) ≤ ∑ i, ∑ j, ‖(F x - F x₀) i j‖ :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
    rwa [abs_of_nonneg hnn] at h
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_minEnergyOn_sub_le_sum_entryNorms hW (F x) (F x₀)) hsumlt

/-- **Constant-shift lemma**: shifting a Hamiltonian by a real multiple of the identity shifts
`minEnergyOn` by the same constant, `minEnergyOn W (H + c • 1) = minEnergyOn W H + c`, for any
nonzero subspace `W`. Every unit vector picks up the same additive `c` in its energy, since
`⟪v, (H + c • 1) v⟫ = ⟪v, H v⟫ + c ⟪v, v⟫ = ⟪v, H v⟫ + c` at `‖v‖ = 1`. Added in the Theorem 10.4
arc (issue #5320, PR-5) for later PRs of that arc, which normalise the energy origin of a
degenerate unperturbed Hamiltonian `Ĥ₀` before comparing it with the second-order effective
Hamiltonian of Tasaki Lemma 10.1 (`DegeneratePerturbation.lean`); it has no consumer yet, and is
to be deleted if the arc's assembly does not take it up. -/
theorem minEnergyOn_add_const_smul_one {W : Submodule ℂ (EuclideanSpace ℂ n)} (hW : W ≠ ⊥)
    (H : Matrix n n ℂ) (c : ℝ) :
    minEnergyOn W (H + (c : ℂ) • (1 : Matrix n n ℂ)) = minEnergyOn W H + c := by
  have hshift : ∀ (A : Matrix n n ℂ) (d : ℝ) (v : EuclideanSpace ℂ n), ‖v‖ = 1 →
      RCLike.re (inner ℂ v (Matrix.toEuclideanLin (A + (d : ℂ) • (1 : Matrix n n ℂ)) v))
        = RCLike.re (inner ℂ v (Matrix.toEuclideanLin A v)) + d := by
    intro A d v hv
    have hone : Matrix.toEuclideanLin (1 : Matrix n n ℂ) v = v := by
      apply WithLp.ofLp_injective 2
      simp
    have happ : Matrix.toEuclideanLin (A + (d : ℂ) • (1 : Matrix n n ℂ)) v
        = Matrix.toEuclideanLin A v + (d : ℂ) • v := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hone]
    rw [happ, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    simp
  have key : ∀ (A : Matrix n n ℂ) (d : ℝ),
      minEnergyOn W A + d ≤ minEnergyOn W (A + (d : ℂ) • (1 : Matrix n n ℂ)) := by
    intro A d
    refine le_minEnergyOn hW fun v hvW hv => ?_
    rw [hshift A d v hv]
    have hle : minEnergyOn W A ≤ RCLike.re (inner ℂ v (Matrix.toEuclideanLin A v)) :=
      minEnergyOn_le hvW hv
    linarith
  refine le_antisymm ?_ (key H c)
  have hback := key (H + (c : ℂ) • (1 : Matrix n n ℂ)) (-c)
  have hcancel : H + (c : ℂ) • (1 : Matrix n n ℂ) + ((-c : ℝ) : ℂ) • (1 : Matrix n n ℂ) = H := by
    push_cast
    module
  rw [hcancel] at hback
  linarith

end LatticeSystem.Math
