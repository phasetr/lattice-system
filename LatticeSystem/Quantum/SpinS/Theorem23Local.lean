import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLeTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLadderInvariant
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.MarshallSign
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder
import LatticeSystem.Quantum.SpinS.Theorem23Casimir
import LatticeSystem.Quantum.SpinS.Theorem23Sectors

/-!
# Tasaki §2.5 Theorem 2.3 local ladder and adjacent-sector API

This module contains the local ladder, signed site-contribution, and
adjacent-sector energy comparison API used by the Tasaki §2.5 Theorem 2.3
interval-chain module. It is split out from `Theorem23.lean` so the main
interval-chain module does not accumulate the local calculation layer.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Ladder eigenvalue preservation -/

/-- **Tasaki §2.5 Theorem 2.3 sector shift, lowering direction**:
if a vector is embedded from the `magSumS = M` sector, then applying
`Ŝ^-_tot` gives a full vector supported on the adjacent sector
`magSumS = M + 1`.

This is the support half of the neighboring-sector comparison: combined
with eigenvalue preservation, `Ŝ^-_tot Ψ_M` is an eigenvector in the
next sector at the same Heisenberg eigenvalue. -/
theorem totalSpinSOpMinus_mulVec_magSectorEmbedding_supported_succ {M : ℕ}
    (Φ : magConfigS V N M → ℂ) :
    ∀ σ : V → Fin (N + 1), magSumS σ ≠ M + 1 →
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) σ = 0 := by
  intro σ hσ
  have hshift :
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
    totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
      (magSectorEmbedding_mem_magSubspaceS Φ)
  have hshift' :
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) := by
    convert hshift using 1
    norm_num
    ring_nf
  exact magSubspaceS_apply_eq_zero_of_magSumS_ne hshift' hσ

/-- **Tasaki §2.5 Theorem 2.3 sector shift, raising direction**:
if a vector is embedded from the `magSumS = M + 1` sector, then
applying `Ŝ^+_tot` gives a full vector supported on the adjacent sector
`magSumS = M`.

This is the raising-direction support half of the neighboring-sector
comparison, complementing
`totalSpinSOpMinus_mulVec_magSectorEmbedding_supported_succ`. -/
theorem totalSpinSOpPlus_mulVec_magSectorEmbedding_supported_pred {M : ℕ}
    (Φ : magConfigS V N (M + 1) → ℂ) :
    ∀ σ : V → Fin (N + 1), magSumS σ ≠ M →
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) σ = 0 := by
  intro σ hσ
  have hshift :
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1) :=
    totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem
      (magSectorEmbedding_mem_magSubspaceS Φ)
  have hshift' :
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    convert hshift using 1
    norm_num
    ring_nf
  exact magSubspaceS_apply_eq_zero_of_magSumS_ne hshift' hσ

/-- **Tasaki §2.5 Theorem 2.3 ladder step, lowering direction**:
if `Ψ` is a Heisenberg eigenvector at real eigenvalue `μ`, then
`Ŝ^-_tot Ψ` is a Heisenberg eigenvector at the same eigenvalue.

This is the operator identity used to compare adjacent magnetization
sectors in the proof of Tasaki §2.5 Theorem 2.3, p. 42: the
Hamiltonian commutes with `Ŝ^-_tot`, so applying the lowering ladder
does not change the Heisenberg eigenvalue. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_of_eigenvec
    (J : V → V → ℂ) (N : ℕ) {μ : ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ) :
    (heisenbergHamiltonianS J N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (μ : ℂ) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  have hcomm : heisenbergHamiltonianS J N * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * heisenbergHamiltonianS J N :=
    heisenbergHamiltonianS_commute_totalSpinSOpMinus J
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 ladder step, raising direction**:
if `Ψ` is a Heisenberg eigenvector at real eigenvalue `μ`, then
`Ŝ^+_tot Ψ` is a Heisenberg eigenvector at the same eigenvalue.

Together with the lowering-direction statement, this is the SU(2)
ladder mechanism for proving that the sector ground-state eigenvalues
in the Theorem 2.3 multiplet coincide. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_of_eigenvec
    (J : V → V → ℂ) (N : ℕ) {μ : ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ) :
    (heisenbergHamiltonianS J N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (μ : ℂ) • ((totalSpinSOpPlus V N).mulVec Ψ) := by
  have hcomm : heisenbergHamiltonianS J N * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * heisenbergHamiltonianS J N :=
    heisenbergHamiltonianS_commute_totalSpinSOpPlus J
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ, Matrix.mulVec_smul]

/-! ## Adjacent-sector energy comparison -/

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector non-vanishing**:
strict Marshall positivity of the lowered vector in the adjacent sector
implies that `Ŝ^-_tot Ψ_M` is not the zero full-space vector.

This is the non-vanishing bookkeeping needed before the lowered vector
can serve as the sector-linking eigenvector in the adjacent-sector
comparison. -/
theorem tasaki23_lowered_ne_zero_of_marshall_pos
    (A : V → Bool) {M : ℕ} [Nonempty (magConfigS V N (M + 1))]
    (Φ : magConfigS V N M → ℂ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 := by
  classical
  intro hzero
  let τ : magConfigS V N (M + 1) := Classical.choice inferInstance
  have hτ := hlowered_marshall_pos τ
  have hcomponent := congrFun hzero τ.1
  rw [hcomponent] at hτ
  simp at hτ

/-- **Tasaki §2.5 Theorem 2.3 raised-vector non-vanishing**:
strict Marshall positivity of the raised vector in the adjacent
predecessor sector implies that `Ŝ^+_tot Ψ_{M+1}` is not the zero
full-space vector.

This is the raising-direction companion to
`tasaki23_lowered_ne_zero_of_marshall_pos`. -/
theorem tasaki23_raised_ne_zero_of_marshall_pos
    (A : V → Bool) {M : ℕ} [Nonempty (magConfigS V N M)]
    (Φ : magConfigS V N (M + 1) → ℂ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 := by
  classical
  intro hzero
  let τ : magConfigS V N M := Classical.choice inferInstance
  have hτ := hraised_marshall_pos τ
  have hcomponent := congrFun hzero τ.1
  rw [hcomponent] at hτ
  simp at hτ

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector site-sum expansion**:
the `Ŝ^-_tot`-lowered embedded sector vector is the sum of its
single-site lowering contributions at each target configuration.

This rewrites the remaining Marshall-positivity input for the
adjacent-sector comparison into the local form needed to analyze the
predecessor configurations site by site. -/
theorem totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum {M : ℕ}
    (Φ : magConfigS V N M → ℂ) (τ : V → Fin (N + 1)) :
    ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ =
      ∑ x : V,
        ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  rw [totalSpinSOpMinus_def, Matrix.sum_mulVec]
  simp [Finset.sum_apply]

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered sublattice expansion**:
the `Ŝ_A^-` component of an embedded sector vector is the sum of
single-site lowering contributions over sites in `A`.

This is the sublattice analogue of
`totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum`, used
to connect the coefficient split to the actual sublattice ladder
operators in the remaining lowered-vector Marshall-positivity proof. -/
theorem sublatticeSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : V → Fin (N + 1)) :
    ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) τ =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  classical
  rw [sublatticeSpinSOpMinus, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec (if A c = true then onSiteS c (spinSOpMinus N) else 0)
        (magSectorEmbedding Φ) τ) =
        ∑ c : V, if A c = true then
          Matrix.mulVec (onSiteS c (spinSOpMinus N)) (magSectorEmbedding Φ) τ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hA : A x = true
          · simp [hA]
          · cases hx : A x <;> simp [hx] at hA ⊢
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
          rw [Finset.sum_filter]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered sublattice expansion**:
the `Ŝ_¬A^-` component of an embedded sector vector is the sum of
single-site lowering contributions over sites outside `A`.

This packages the complement sublattice with the same `A x = false`
filter used by the lowered coefficient split. -/
theorem sublatticeSpinSOpMinus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : V → Fin (N + 1)) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (magSectorEmbedding Φ)) τ =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  classical
  rw [sublatticeSpinSOpMinus, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec
        (if (!A c) = true then onSiteS c (spinSOpMinus N) else 0)
        (magSectorEmbedding Φ) τ) =
        ∑ c : V, if A c = false then
          Matrix.mulVec (onSiteS c (spinSOpMinus N)) (magSectorEmbedding Φ) τ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          cases A x <;> simp
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
          rw [Finset.sum_filter]

/-- **Tasaki §2.5 Theorem 2.3 lowered Marshall-signed vector realness**:
lowering a real Marshall-signed sector representative gives a real-valued
full vector.

This is the imaginary-part half needed to upgrade the sector-uniqueness
relation, which is stated on real parts, to an equality of full complex
vectors. -/
theorem totalSpinSOpMinus_mulVec_marshallSignedEmbedding_im_zero
    (A : V → Bool) {M : ℕ} (v : magConfigS V N M → ℝ)
    (σ : V → Fin (N + 1)) :
    (((totalSpinSOpMinus V N).mulVec
      (magSectorEmbedding
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) σ).im = 0 := by
  rw [totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum]
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [Matrix.mulVec, dotProduct, Complex.im_sum]
  refine Finset.sum_eq_zero (fun τ _ => ?_)
  have hτ_im :
      (magSectorEmbedding
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ).im = 0 := by
    by_cases hτM : magSumS τ = M
    · rw [magSectorEmbedding_apply_of_mem
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) hτM]
      simp
    · rw [magSectorEmbedding_apply_of_not_mem
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) hτM]
      simp
  rw [Complex.mul_im]
  rw [onSiteS_spinSOpMinus_apply_im_zero, hτ_im]
  ring

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector scalar identification**:
if the real parts of the lowered Marshall-signed source vector agree with
a positive real scalar multiple of the successor representative in the
target sector, then the full lowered vector is that scalar multiple of
the zero-extended successor representative.

The proof uses sector support for the lowered vector and the realness of
both sides. -/
theorem totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
    (A : V → Bool) {M : ℕ} {v : magConfigS V N M → ℝ}
    {v_succ : magConfigS V N (M + 1) → ℝ} {r : ℝ}
    (hrel :
      ∀ τ : magConfigS V N (M + 1),
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
          r * ((marshallSignS A τ.1).re * v_succ τ)) :
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (r : ℂ) •
        magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) := by
  funext σ
  by_cases hσ : magSumS σ = M + 1
  · let τ : magConfigS V N (M + 1) := ⟨σ, hσ⟩
    have hleft_im :
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) σ).im = 0 :=
      totalSpinSOpMinus_mulVec_marshallSignedEmbedding_im_zero A v σ
    have hleft_re :
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) σ).re =
          r * ((marshallSignS A σ).re * v_succ τ) := by
      simpa [τ] using hrel τ
    change (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) σ =
      (r : ℂ) *
        magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) σ
    rw [magSectorEmbedding_apply_of_mem
      (fun τ : magConfigS V N (M + 1) =>
        (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) hσ]
    apply Complex.ext
    · simpa using hleft_re
    · simpa using hleft_im
  · rw [totalSpinSOpMinus_mulVec_magSectorEmbedding_supported_succ
      (fun τ : magConfigS V N M =>
        (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ hσ]
    change (0 : ℂ) =
      (r : ℂ) *
        magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) σ
    rw [magSectorEmbedding_apply_of_not_mem
      (fun τ : magConfigS V N (M + 1) =>
        (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) hσ]
    simp

/-- **Tasaki §2.5 Theorem 2.3 raised-vector site-sum expansion**:
the `Ŝ^+_tot`-raised embedded sector vector is the sum of its
single-site raising contributions at each target configuration.

This is the raising-direction companion to
`totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum`. -/
theorem totalSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_site_sum {M : ℕ}
    (Φ : magConfigS V N (M + 1) → ℂ) (τ : V → Fin (N + 1)) :
    ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ =
      ∑ x : V,
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  rw [totalSpinSOpPlus_def, Matrix.sum_mulVec]
  simp [Finset.sum_apply]

/-- **Tasaki §2.5 Theorem 2.3 on-`A` raised sublattice expansion**:
the `Ŝ_A^+` component of an embedded successor-sector vector is the sum
of single-site raising contributions over sites in `A`.

This is the raising-direction companion to
`sublatticeSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum`
and is used after re-embedding lowered components in the cross-ladder
identity. -/
theorem sublatticeSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : V → Fin (N + 1)) :
    ((sublatticeSpinSOpPlus N A).mulVec (magSectorEmbedding Φ)) τ =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  classical
  rw [sublatticeSpinSOpPlus, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec (if A c = true then onSiteS c (spinSOpPlus N) else 0)
        (magSectorEmbedding Φ) τ) =
        ∑ c : V, if A c = true then
          Matrix.mulVec (onSiteS c (spinSOpPlus N)) (magSectorEmbedding Φ) τ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hA : A x = true
          · simp [hA]
          · cases hx : A x <;> simp [hx] at hA ⊢
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
          rw [Finset.sum_filter]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` raised sublattice expansion**:
the `Ŝ_¬A^+` component of an embedded successor-sector vector is the sum
of single-site raising contributions over sites outside `A`.

This packages the complement sublattice with the same `A x = false`
filter used by the local coefficient comparison. -/
theorem sublatticeSpinSOpPlus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : V → Fin (N + 1)) :
    ((sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
        (magSectorEmbedding Φ)) τ =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
  classical
  rw [sublatticeSpinSOpPlus, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec
        (if (!A c) = true then onSiteS c (spinSOpPlus N) else 0)
        (magSectorEmbedding Φ) τ) =
        ∑ c : V, if A c = false then
          Matrix.mulVec (onSiteS c (spinSOpPlus N)) (magSectorEmbedding Φ) τ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          cases A x <;> simp
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ := by
          rw [Finset.sum_filter]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This is the magnetization bookkeeping behind the local component
formula for a single summand in `Ŝ^-_tot`. -/
private theorem magSumS_single_site_lowering_predecessor {M : ℕ}
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val - 1, by omega⟩) = M := by
  classical
  have hsum_succ :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val - 1, by omega⟩) + 1 = magSumS τ.1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val - 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    have hpred_val :
        (⟨(τ.1 x).val - 1, by
          omega⟩ : Fin (N + 1)).val + 1 = (τ.1 x).val := by
      simp
      omega
    omega
  have hτ : magSumS τ.1 = M + 1 := τ.2
  omega

/-- **Tasaki §2.5 Theorem 2.3 single-site raising successor**:
if a target configuration `τ` in sector `M` has local value below `N`
at `x`, raising that local value by one gives a configuration in
sector `M + 1`.

This is the magnetization bookkeeping behind the raising-direction
local component formula for a single summand in `Ŝ^+_tot`. -/
private theorem magSumS_single_site_raising_successor {M : ℕ}
    (τ : magConfigS V N M) (x : V) (hx : (τ.1 x).val < N) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val + 1, by omega⟩) = M + 1 := by
  classical
  have hsum :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val + 1, by omega⟩) =
        magSumS τ.1 + 1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val + 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    omega
  have hτ : magSumS τ.1 = M := τ.2
  omega

/-- **Tasaki §2.5 Theorem 2.3 zero local lowering component**:
if the target configuration already has local value `0` at `x`, the
single-site lowering summand at `x` contributes zero to that target
component.

This is the boundary case for the local predecessor analysis of the
`Ŝ^-_tot` site-sum expansion. -/
theorem onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
    {M : ℕ} (Φ : magConfigS V N M → ℂ) (τ : magConfigS V N (M + 1))
    (x : V) (hx : (τ.1 x).val = 0) :
    (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) = 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro σ _hσ
  by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
  · rw [onSiteS_apply_of_off_site_agree x _ hoff]
    have hnot_lower : (σ x).val + 1 ≠ (τ.1 x).val := by omega
    rw [spinSOpMinus_apply_other N hnot_lower, zero_mul]
  · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering component**:
if a target sector configuration `τ` has positive local value at `x`,
then the `x`-summand of `Ŝ^-_tot` at `τ` is exactly the lowering matrix
coefficient times the source-sector coefficient at the unique
predecessor configuration obtained by decreasing `τ x` by one.

This is the local component formula needed before applying the
single-site Marshall predecessor sign lemmas in the adjacent-sector
positivity argument. -/
theorem onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred
    {M : ℕ} (Φ : magConfigS V N M → ℂ) (τ : magConfigS V N (M + 1))
    (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) =
        spinSOpMinus N (τ.1 x) predVal *
          Φ ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩ := by
  classical
  dsimp only
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single
    (Function.update τ.1 x
      ⟨(τ.1 x).val - 1, by omega⟩)]
  · rw [onSiteS_apply_of_off_site_agree]
    · rw [magSectorEmbedding_apply_of_mem Φ
        (magSumS_single_site_lowering_predecessor τ x hx)]
      simp
    · intro y hy
      rw [Function.update_of_ne hy]
  · intro σ _hσ hσ_ne
    by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
    · rw [onSiteS_apply_of_off_site_agree x _ hoff]
      have hnot_lower : (σ x).val + 1 ≠ (τ.1 x).val := by
        intro h_lower
        apply hσ_ne
        funext y
        by_cases hy : y = x
        · subst y
          apply Fin.ext
          simp
          omega
        · rw [Function.update_of_ne hy]
          exact (hoff y hy).symm
      rw [spinSOpMinus_apply_other N hnot_lower, zero_mul]
    · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]
  · intro hnot_mem
    exact False.elim (hnot_mem (Finset.mem_univ _))

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering real part**:
at a target configuration with positive local value, the real part of
the single-site lowering summand is the product of the positive
lowering matrix coefficient and the real part of the predecessor
coefficient.

This is the real-valued form of
`onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred`,
using that every `Ŝ^-` matrix entry is real. -/
theorem onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
    {M : ℕ} (Φ : magConfigS V N M → ℂ) (τ : magConfigS V N (M + 1))
    (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re) =
        (spinSOpMinus N (τ.1 x) predVal).re *
          (Φ ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩).re := by
  classical
  dsimp only
  rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred
    Φ τ x hx]
  rw [Complex.mul_re, spinSOpMinus_apply_im_zero]
  ring

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered coefficient identity**:
if the lowered site lies outside `A`, then the signed real single-site
lowering contribution is the positive lowering coefficient times the
Marshall-signed predecessor coefficient.

This is the coefficient-level form behind
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`; it is
the exact identity needed before summing the off-`A` contributions in
the lowered-vector Marshall-positivity argument. -/
theorem tasaki23_signed_single_site_lowering_component_eq_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = false) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) =
      (spinSOpMinus N (τ.1 x) predVal).re *
        ((marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re) := by
  classical
  dsimp only
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsign_eq : (marshallSignS A τ.1).re = (marshallSignS A pred).re := by
    calc
      (marshallSignS A τ.1).re =
          (marshallSignS A τ.1).re * 1 := by ring
      _ =
          (marshallSignS A τ.1).re *
            ((marshallSignS A pred).re * (marshallSignS A pred).re) := by
          rw [hsq]
      _ =
          ((marshallSignS A τ.1).re * (marshallSignS A pred).re) *
            (marshallSignS A pred).re := by ring
      _ = 1 * (marshallSignS A pred).re := by rw [hsign]
      _ = (marshallSignS A pred).re := by ring
  rw [hcomponent]
  rw [hsign_eq]
  ring

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered coefficient identity**:
if the lowered site lies inside `A`, then the signed real single-site
lowering contribution is the negative of the positive lowering
coefficient times the Marshall-signed predecessor coefficient.

This is the exact sign-reversal identity behind
`tasaki23_signed_single_site_lowering_component_neg_of_A_true`, and it
isolates the coefficient relation that the later dominance proof must
control after summing over sites in `A`. -/
theorem tasaki23_signed_single_site_lowering_component_eq_neg_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = true) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) =
      -((spinSOpMinus N (τ.1 x) predVal).re *
        ((marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re)) := by
  classical
  dsimp only
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = -1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsign_eq : (marshallSignS A τ.1).re = - (marshallSignS A pred).re := by
    calc
      (marshallSignS A τ.1).re =
          (marshallSignS A τ.1).re * 1 := by ring
      _ =
          (marshallSignS A τ.1).re *
            ((marshallSignS A pred).re * (marshallSignS A pred).re) := by
          rw [hsq]
      _ =
          ((marshallSignS A τ.1).re * (marshallSignS A pred).re) *
            (marshallSignS A pred).re := by ring
      _ = (-1) * (marshallSignS A pred).re := by rw [hsign]
      _ = - (marshallSignS A pred).re := by ring
  rw [hcomponent]
  rw [hsign_eq]
  ring

/-- **Tasaki §2.5 Theorem 2.3 off-`A` single-site positivity**:
if the lowered site lies outside `A`, then the signed real part of its
single-site lowering contribution is strictly positive whenever the
source-sector vector is Marshall-positive.

This combines the predecessor component formula with the off-`A`
Marshall sign preservation under a one-step lowering. -/
theorem tasaki23_signed_single_site_lowering_component_pos_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 < (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hcoef_lower : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpMinus N (τ.1 x) predVal).re :=
    spinSOpMinus_apply_re_pos_of_lower N hcoef_lower
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsrc :
      0 < (marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re :=
    hΦ_pos ⟨pred, hpredM⟩
  have htarget_src :
      0 < (marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re := by
    nlinarith [hsign, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re) =
        (spinSOpMinus N (τ.1 x) predVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_pos hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 on-`A` single-site negativity**:
if the lowered site lies in `A`, then the signed real part of its
single-site lowering contribution is strictly negative whenever the
source-sector vector is Marshall-positive.

The sign reversal is the complementary local case to
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_lowering_component_neg_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) < 0 := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hcoef_lower : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpMinus N (τ.1 x) predVal).re :=
    spinSOpMinus_apply_re_pos_of_lower N hcoef_lower
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = -1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsrc :
      0 < (marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re :=
    hΦ_pos ⟨pred, hpredM⟩
  have htarget_src :
      (marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re < 0 := by
    nlinarith [hsign, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re) =
        (spinSOpMinus N (τ.1 x) predVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_neg_of_pos_of_neg hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 off-`A` local lowering non-negativity**:
including the boundary case where the target local value is zero, the
signed single-site lowering contribution is non-negative at every site
outside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  by_cases hx : 0 < (τ.1 x).val
  · exact le_of_lt
      (tasaki23_signed_single_site_lowering_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos)
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp

/-- **Tasaki §2.5 Theorem 2.3 on-`A` local lowering non-positivity**:
including the boundary case where the target local value is zero, the
signed single-site lowering contribution is non-positive at every site
inside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_lowering_component_neg_of_A_true`. -/
theorem tasaki23_signed_single_site_lowering_component_nonpos_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) ≤ 0 := by
  by_cases hx : 0 < (τ.1 x).val
  · exact le_of_lt
      (tasaki23_signed_single_site_lowering_component_neg_of_A_true
        A Φ τ x hx hAx hΦ_pos)
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered sign-sum bound**:
the filtered sum of signed single-site lowering contributions over
sites outside `A` is non-negative.

This is the finite-sum form of
`tasaki23_signed_single_site_lowering_component_nonneg_of_A_false`. -/
theorem tasaki23_signed_lowering_offA_sum_nonneg
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  apply Finset.sum_nonneg
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered sign-sum bound**:
the filtered sum of signed single-site lowering contributions over
sites inside `A` is non-positive.

This is the finite-sum form of
`tasaki23_signed_single_site_lowering_component_nonpos_of_A_true`. -/
theorem tasaki23_signed_lowering_onA_sum_nonpos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro x hx
  have hAx : A x = true := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_lowering_component_nonpos_of_A_true
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 signed local lowering contribution**:
the real signed contribution of the `x`-summand in the lowered
site-sum at a target-sector configuration.

This packages the repeated real expression used to split the lowered
site-sum into its off-`A` and on-`A` filtered pieces. -/
noncomputable def tasaki23SignedLoweringSiteContribution
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  (marshallSignS A τ.1).re *
    ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re)

/-- **Tasaki §2.5 Theorem 2.3 lowered predecessor signed coefficient**:
the boundary-inclusive coefficient obtained from the predecessor
configuration of `τ` at `x`.

If the target value `(τ.1 x).val` is positive, this is the positive
`Ŝ^-` matrix coefficient times the Marshall-signed predecessor
coefficient. If the target value is zero, the single-site lowering
summand is zero and this coefficient is defined to be zero as well. -/
noncomputable def tasaki23LoweringPredecessorSignedCoefficient
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  if hx : 0 < (τ.1 x).val then
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (spinSOpMinus N (τ.1 x) predVal).re *
      ((marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re)
  else
    0

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 positive predecessor coefficient value**:
for a Marshall-signed real sector vector, the boundary-inclusive lowered
predecessor coefficient at a lowerable site is just the positive
single-site lowering matrix coefficient times the positive real source
coefficient at the predecessor.

The two Marshall signs cancel by `marshallSignS_re_sq`; this is the
local positivity normalization used before comparing the on-`A` and
off-`A` predecessor coefficient sums. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x =
      (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩ := by
  classical
  dsimp only
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  let hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  rw [tasaki23LoweringPredecessorSignedCoefficient]
  simp only [hx, ↓reduceDIte, Complex.ofReal_re]
  change
    (spinSOpMinus N (τ.1 x) predVal).re *
        ((marshallSignS A pred).re *
          ((marshallSignS A pred).re * v ⟨pred, hpredM⟩)) =
      (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩
  have hcancel :
      (marshallSignS A pred).re *
          ((marshallSignS A pred).re * v ⟨pred, hpredM⟩) =
        v ⟨pred, hpredM⟩ := by
    calc
      (marshallSignS A pred).re *
          ((marshallSignS A pred).re * v ⟨pred, hpredM⟩) =
          ((marshallSignS A pred).re * (marshallSignS A pred).re) *
            v ⟨pred, hpredM⟩ := by ring
      _ = 1 * v ⟨pred, hpredM⟩ := by rw [hsq]
      _ = v ⟨pred, hpredM⟩ := by ring
  rw [hcancel]

/-- **Tasaki §2.5 Theorem 2.3 positive predecessor coefficient at a
lowerable site**: if the real source coefficients are strictly positive,
then every lowerable predecessor coefficient is strictly positive. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_pos_of_lowerable
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 <
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcoef_lower : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpMinus N (τ.1 x) predVal).re :=
    spinSOpMinus_apply_re_pos_of_lower N hcoef_lower
  rw [tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
    A v τ x hx]
  exact mul_pos hcoef_pos (hv_pos ⟨pred, hpredM⟩)

/-- **Tasaki §2.5 Theorem 2.3 non-negative predecessor coefficient**:
for a strictly positive real source vector, the boundary-inclusive
predecessor coefficient is non-negative at every site, with the
non-lowerable boundary case contributing zero. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_nonneg
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 ≤
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · exact le_of_lt
      (tasaki23_lowering_predecessor_signed_coefficient_pos_of_lowerable
        A v τ x hx hv_pos)
  · simp [tasaki23LoweringPredecessorSignedCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 positive-source predecessor coefficient**:
the boundary-inclusive lowered predecessor coefficient after the
Marshall signs have been cancelled.

At a lowerable site this is the positive single-site lowering matrix
coefficient times the real positive source coefficient at the predecessor;
at the lower boundary it is zero. -/
noncomputable def tasaki23LoweringPredecessorPositiveSourceCoefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  if hx : 0 < (τ.1 x).val then
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩
  else
    0

/-- **Tasaki §2.5 Theorem 2.3 lowerable positive-source predecessor
coefficient**: the explicit lowered predecessor coefficient at a site
where the successor configuration can actually be lowered.

This is the non-boundary branch of
`tasaki23LoweringPredecessorPositiveSourceCoefficient`. -/
noncomputable def tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) : ℝ :=
  let predVal : Fin (N + 1) :=
    ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  let hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  (spinSOpMinus N (τ.1 x) predVal).re * v ⟨pred, hpredM⟩

set_option linter.style.longLine false in
omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predecessor ladder coefficient mirror**:
the raising coefficient from the lowering predecessor back to the
successor configuration equals the lowering coefficient used in the
explicit lowerable positive-source predecessor coefficient.

Both sides are the real ladder coefficient
`sqrt (τ_x * (N - τ_x + 1))`. -/
theorem tasaki23_spinSOpPlus_lowering_predecessor_re_eq_spinSOpMinus
    {M : ℕ} (N : ℕ) (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    (spinSOpPlus N predVal (τ.1 x)).re =
      (spinSOpMinus N (τ.1 x) predVal).re := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  change (spinSOpPlus N predVal (τ.1 x)).re =
    (spinSOpMinus N (τ.1 x) predVal).re
  have hpredVal : predVal.val = (τ.1 x).val - 1 := rfl
  have hstep : predVal.val + 1 = (τ.1 x).val := by omega
  rw [spinSOpPlus_apply_raise N hstep, spinSOpMinus_apply_lower N hstep]
  simp only [Complex.ofReal_re]
  congr 1
  have hxle : 1 ≤ (τ.1 x).val := Nat.succ_le_of_lt hx
  rw [hpredVal, Nat.cast_sub hxle]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient as predecessor
raising coefficient**: the explicit lowerable positive-source coefficient
can be read with the matching raising matrix coefficient at the lowering
predecessor.

This is the coefficient bridge needed to compare the real predecessor
source-weight raising sums with the attached lowerable positive-source
coefficient sums. -/
theorem tasaki23_lowerable_positive_source_coefficient_eq_raising_predecessor_source
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient v τ x hx =
      (spinSOpPlus N predVal (τ.1 x)).re *
        v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩ := by
  classical
  dsimp only [tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient]
  rw [tasaki23_spinSOpPlus_lowering_predecessor_re_eq_spinSOpMinus
    (V := V) N τ x hx]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient sums as predecessor
raising-source sums**: an attached sum of explicit lowerable
positive-source coefficients can be read as the attached sum of the
matching predecessor raising coefficients times the positive predecessor
source values.

This is the finite-sum form of
`tasaki23_lowerable_positive_source_coefficient_eq_raising_predecessor_source`.
-/
theorem tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
      (fun x =>
        tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
          v τ x.1 ((Finset.mem_filter.mp x.2).2))) =
      ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  classical
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_lowerable_positive_source_coefficient_eq_raising_predecessor_source
      (V := V) (N := N) v τ x.1 ((Finset.mem_filter.mp x.2).2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowerable coefficient dominance from
predecessor raising-source dominance**: strict dominance of the attached
predecessor raising-source sums implies strict dominance of the attached
explicit lowerable positive-source coefficient sums.

This removes the coefficient notation from the remaining local estimate
and exposes the same real raising coefficients that occur in the
predecessor source-weight identity. -/
theorem tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    (((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
            v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
      (((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
            v τ x.1 ((Finset.mem_filter.mp x.2).2))) := by
  rw [
    tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  exact hdominates

/-- **Tasaki §2.5 Theorem 2.3 boundary-inclusive predecessor
raising-source coefficient**: the predecessor raising-source summand at
a successor site, with the non-lowerable boundary case contributing
zero.

This is the `S^+`-coefficient version of the lowerable attached summand
used by the final raising-source dominance callback. -/
noncomputable def tasaki23RaisingPredecessorSourceCoefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) : ℝ :=
  if hx : 0 < (τ.1 x).val then
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (spinSOpPlus N predVal (τ.1 x)).re *
      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩
  else
    0

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 attached raising-source sum as a boundary
sum**: the attached sum over lowerable sites agrees with the
boundary-inclusive predecessor raising-source coefficient sum over the
ambient finite set.

This removes the proof-carrying lowerable filter before applying Boolean
partitions of the vertex set. -/
theorem tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) =
      ∑ x ∈ s, tasaki23RaisingPredecessorSourceCoefficient v τ x := by
  classical
  let f : V → ℝ := fun x => tasaki23RaisingPredecessorSourceCoefficient v τ x
  calc
    ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) =
        (s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x => f x.1) := by
      apply Finset.sum_congr rfl
      intro x _hxmem
      have hx : 0 < (τ.1 x.1).val := (Finset.mem_filter.mp x.2).2
      dsimp [f, tasaki23RaisingPredecessorSourceCoefficient]
      rw [dif_pos hx]
    _ = ∑ x ∈ s.filter (fun x : V => 0 < (τ.1 x).val), f x := by
      simpa using
        (Finset.sum_attach (s.filter (fun x : V => 0 < (τ.1 x).val)) f)
    _ = ∑ x ∈ s, f x := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := s) (p := fun x : V => 0 < (τ.1 x).val) (f := f)]
      have hzero :
          (∑ x ∈ s.filter (fun x : V => ¬ 0 < (τ.1 x).val), f x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hxmem
        have hxnot : ¬ 0 < (τ.1 x).val := (Finset.mem_filter.mp hxmem).2
        dsimp [f, tasaki23RaisingPredecessorSourceCoefficient]
        rw [dif_neg hxnot]
      rw [hzero, add_zero]
    _ = ∑ x ∈ s, tasaki23RaisingPredecessorSourceCoefficient v τ x := by
      rfl

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 positive predecessor raising-source
summand**: at a lowerable successor site, the real raising coefficient
from the lowering predecessor back to the successor is strictly positive,
so multiplying by the strictly positive source coefficient gives a
strictly positive raising-source summand.

This is the sign-side input for extracting dominance from the real
predecessor source-weight equation. -/
theorem tasaki23_raising_predecessor_source_summand_pos
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 <
      (let predVal : Fin (N + 1) :=
        ⟨(τ.1 x).val - 1, by omega⟩
      let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
      (spinSOpPlus N predVal (τ.1 x)).re *
        v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩) := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hstep : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpPlus N predVal (τ.1 x)).re :=
    spinSOpPlus_apply_re_pos_of_raise N hstep
  change 0 <
    (spinSOpPlus N predVal (τ.1 x)).re *
      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩
  exact mul_pos hcoef_pos
    (hv_pos ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 non-negative predecessor raising-source
sum**: every attached predecessor raising-source sum over lowerable
successor sites is non-negative for a strictly positive real source
vector.

This packages summand positivity in the exact finite-sum shape used by
the final raising-source dominance callback. -/
theorem tasaki23_raising_predecessor_source_attach_sum_nonneg
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V)
    (hv_pos : ∀ σ : magConfigS V N M, 0 < v σ) :
    0 ≤
      ((s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  classical
  apply Finset.sum_nonneg
  intro x _hx
  exact le_of_lt
    (tasaki23_raising_predecessor_source_summand_pos
      (V := V) (N := N) v τ x.1 ((Finset.mem_filter.mp x.2).2) hv_pos)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 total predecessor raising-source sum
partition**: the attached predecessor raising-source sum over all
lowerable successor sites splits into the on-`A` and off-`A` attached
sums used by the final dominance callback.

This is the finite-set partition needed before applying the real
predecessor source-weight equation to the two sublattice sums. -/
theorem tasaki23_raising_predecessor_source_univ_attach_sum_eq_onA_add_offA
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) :
    ((Finset.univ.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) =
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) +
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  classical
  rw [tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    (V := V) (N := N) v τ Finset.univ]
  rw [tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true))]
  rw [tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
    (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = true)]
  simp [Bool.not_eq_true]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source dominance from
positive difference**: positivity of the off-`A` predecessor
raising-source sum minus the on-`A` sum is the strict dominance
condition required by the final raising-source callback.

This states the local comparison in the difference form naturally
produced by the real predecessor source-weight identity. -/
theorem tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdiff :
      0 <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
          (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                v ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    (((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
      (((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x.1).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
          (spinSOpPlus N predVal (τ.1 x.1)).re *
            v ⟨pred,
              magSumS_single_site_lowering_predecessor
                τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  linarith

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source dominance
callback from positive differences**: a pointwise callback proving
positivity of the off-`A` minus on-`A` predecessor raising-source sums
supplies the strict dominance callback used by the final theorem
boundary.

This is the quantified callback form of
`tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos`. -/
theorem tasaki23_raising_predecessor_source_sum_lt_callback_of_offA_sub_onA_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hdiff :
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                v ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∀ τ : magConfigS V N (M + 1),
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x.1).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
            (spinSOpPlus N predVal (τ.1 x.1)).re *
              v ⟨pred,
                magSumS_single_site_lowering_predecessor
                  τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) := by
  intro τ
  exact
    tasaki23_raising_predecessor_source_sum_lt_of_offA_sub_onA_pos
      (V := V) (N := N) A v τ (hdiff τ)

/-- **Tasaki §2.5 Theorem 2.3 boundary coefficient as lowerable
coefficient**: at a lowerable site, the boundary-inclusive positive-source
coefficient is the explicit lowerable coefficient. -/
theorem tasaki23_positive_source_coefficient_eq_lowerable_coefficient
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x =
      tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient v τ x hx := by
  simp [tasaki23LoweringPredecessorPositiveSourceCoefficient,
    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 positive-source coefficient sum over
lowerable sites**: the boundary-inclusive positive-source coefficient sum
over a finite set is unchanged after restricting the finite set to sites
where the successor configuration can actually be lowered. -/
theorem tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s, tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) =
      ∑ x ∈ s.filter (fun x : V => 0 < (τ.1 x).val),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := s) (p := fun x : V => 0 < (τ.1 x).val)
    (f := fun x : V => tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x)]
  have hzero :
      (∑ x ∈ s.filter (fun x : V => ¬ 0 < (τ.1 x).val),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxnot : ¬ 0 < (τ.1 x).val := (Finset.mem_filter.mp hx).2
    simp [tasaki23LoweringPredecessorPositiveSourceCoefficient, hxnot]
  rw [hzero, add_zero]

/-- **Tasaki §2.5 Theorem 2.3 explicit lowerable coefficient sum**:
after filtering to sites where the successor configuration can be lowered,
the boundary-inclusive positive-source coefficient sum is the attached
finite sum of the explicit lowerable predecessor coefficients. -/
theorem tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
    {M : ℕ} (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s.filter (fun x : V => 0 < (τ.1 x).val),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) =
      (s.filter (fun x : V => 0 < (τ.1 x).val)).attach.sum
        (fun x =>
          tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
            v τ x.1 ((Finset.mem_filter.mp x.2).2)) := by
  classical
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_positive_source_coefficient_eq_lowerable_coefficient
      v τ x.1 ((Finset.mem_filter.mp x.2).2)

/-- **Tasaki §2.5 Theorem 2.3 explicit lowerable coefficient dominance**:
dominance of the attached sums of explicit lowerable predecessor
coefficients implies the filtered boundary-inclusive positive-source
coefficient dominance used by the previous callback boundary. -/
theorem tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
              v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
        (((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)).attach.sum
          (fun x =>
            tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
              v τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
        (fun x : V => 0 < (τ.1 x).val)),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
      ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
        (fun x : V => 0 < (τ.1 x).val)),
        tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  rw [
    tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
      v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
      v τ (Finset.univ.filter (fun x : V => A x = false))]
  exact hdominates

/-- **Tasaki §2.5 Theorem 2.3 signed coefficient as positive-source
coefficient**: for a Marshall-signed real source vector, the
boundary-inclusive signed predecessor coefficient is exactly the
sign-normalized positive-source coefficient. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source_coefficient
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) :
    tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x =
      tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · rw [tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
      A v τ x hx]
    simp [tasaki23LoweringPredecessorPositiveSourceCoefficient, hx]
  · simp [tasaki23LoweringPredecessorSignedCoefficient,
      tasaki23LoweringPredecessorPositiveSourceCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 signed coefficient sum as positive-source
coefficient sum**: over any finite site set, the Marshall-signed
predecessor coefficient sum for a Marshall-signed real source vector is
the corresponding sign-normalized positive-source coefficient sum. -/
theorem tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s,
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x) =
      ∑ x ∈ s, tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source_coefficient
      A v τ x

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered contribution split**:
outside `A`, the signed single-site lowering contribution is exactly
the boundary-inclusive signed predecessor coefficient.

This packages the off-`A` coefficient identity in a form that can be
summed without carrying a separate lowerability proof for every site. -/
theorem tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = false) :
    tasaki23SignedLoweringSiteContribution A Φ τ x =
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · simpa [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient, hx]
      using
        tasaki23_signed_single_site_lowering_component_eq_of_A_false
          A Φ τ x hx hAx
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient]
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp [hx]

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered contribution split**:
inside `A`, the signed single-site lowering contribution is the
negative of the boundary-inclusive signed predecessor coefficient.

This is the on-`A` companion to
`tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false`
and isolates the exact term whose total size must be dominated by the
off-`A` contribution in the final lowered Marshall-positivity proof. -/
theorem tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = true) :
    tasaki23SignedLoweringSiteContribution A Φ τ x =
      -tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · simpa [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient, hx]
      using
        tasaki23_signed_single_site_lowering_component_eq_neg_of_A_true
          A Φ τ x hx hAx
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient]
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp [hx]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` coefficient-sum split**:
the off-`A` filtered signed lowering sum is exactly the corresponding
sum of boundary-inclusive predecessor coefficients.

This is the finite-sum form of
`tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false`
and is the off-`A` side of the coefficient-level dominance comparison. -/
theorem tasaki23_signed_lowering_offA_sum_eq_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
    ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  apply Finset.sum_congr rfl
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false
    A Φ τ x hAx

/-- **Tasaki §2.5 Theorem 2.3 on-`A` coefficient-sum split**:
the on-`A` filtered signed lowering sum is the negative of the
corresponding boundary-inclusive predecessor coefficient sum.

This is the finite-sum form of
`tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true`
and isolates the negative sublattice contribution that must be
controlled in the final lowered Marshall-positivity proof. -/
theorem tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
    -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  calc
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          -tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hAx : A x = true := by
            simpa using (Finset.mem_filter.mp hx).2
          exact
            tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true
              A Φ τ x hAx
    _ = -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
          rw [Finset.sum_neg_distrib]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered sublattice coefficient
component**: the Marshall-signed real component of `Ŝ_¬A^- Φ` at a
target configuration is the off-`A` predecessor-coefficient sum.

This turns the off-sublattice half of the coefficient split into a
statement about the actual complement-sublattice lowering operator. -/
theorem tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
          (magSectorEmbedding Φ)) τ.1).re =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  rw [sublatticeSpinSOpMinus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum
    A Φ τ.1]
  rw [Complex.re_sum, Finset.mul_sum]
  change
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x
  exact tasaki23_signed_lowering_offA_sum_eq_coefficient_sum A Φ τ

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered sublattice coefficient
component**: the Marshall-signed real component of `Ŝ_A^- Φ` at a
target configuration is the negative of the on-`A`
predecessor-coefficient sum.

This is the operator-level form of the on-sublattice half of the
coefficient split. -/
theorem tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (((sublatticeSpinSOpMinus N A).mulVec
          (magSectorEmbedding Φ)) τ.1).re =
      -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  rw [sublatticeSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum
    A Φ τ.1]
  rw [Complex.re_sum, Finset.mul_sum]
  change
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
      -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x
  exact tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum A Φ τ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source difference as a
lowered component**: for a Marshall-signed positive source vector, the
off-`A` minus on-`A` predecessor raising-source difference is exactly the
Marshall-signed real component of the full lowered vector
`Ŝ^-_tot Ψ`.

This identifies the difference-form callback with the operator-level
lowered-vector positivity statement used in the adjacent-sector
comparison. -/
theorem tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
        tasaki23RaisingPredecessorSourceCoefficient v τ x) -
      (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
        tasaki23RaisingPredecessorSourceCoefficient v τ x) =
      (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  classical
  let Φ : magConfigS V N M → ℂ :=
    fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)
  have hoff :
      (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ)) τ.1).re =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23RaisingPredecessorSourceCoefficient v τ x := by
    rw [tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
      A Φ τ]
    rw [show
        (∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23LoweringPredecessorSignedCoefficient A
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x from by
        rfl]
    rw [
      tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
        A v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
        v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
        v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  have hon :
      (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N A).mulVec
            (magSectorEmbedding Φ)) τ.1).re =
        -∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23RaisingPredecessorSourceCoefficient v τ x := by
    rw [tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
      A Φ τ]
    rw [show
        (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23LoweringPredecessorSignedCoefficient A
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x from by
        rfl]
    rw [
      tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
        A v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
        v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
        v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true))]
  rw [show
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) =
        ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) +
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ)) from by
      rw [totalSpinSOpMinus_eq_sublattice_sum (N := N) A]
      rw [Matrix.add_mulVec]]
  rw [Pi.add_apply, Complex.add_re, mul_add, hon, hoff]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered Marshall positivity from
predecessor raising-source differences**: positivity of the off-`A`
minus on-`A` predecessor raising-source difference proves the
Marshall-positive lowered-vector component.

The proof first rewrites the lowerable attached sums as boundary sums
and then applies
`tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component`.
This connects the real source-weight difference callback to the
lowered-sector Marshall-positivity hypothesis used by the adjacent-sector
energy comparison. -/
theorem tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hdiff :
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                v ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  intro τ
  have hτ := hdiff τ
  rw [
    tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false)),
    tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component
      A v τ] at hτ
  exact hτ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered Marshall positivity from the
unpacked real predecessor difference callback**: the fully threaded local
callback used by the final theorem boundary can be read as a
lowered-sector Marshall-positivity proof.

This is the callback-shaped version of
`tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos`:
after the predicted-GS, real source-weight, sublattice-Casimir, and
successor-support data have produced the off-`A` minus on-`A`
predecessor raising-source positive difference, the result is converted
directly into the lowered-vector Marshall-positive component. -/
theorem
    tasaki23_lowered_marshall_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hsource_difference_pos :
      ∀ Ψ : (V → Fin (N + 1)) → ℂ,
        Ψ =
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
        (∀ τ : magConfigS V N (M + 1), ∀ x : V,
          ∀ hx : 0 < (τ.1 x).val,
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (magSectorRestriction (M := M + 1)
                      ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
              ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (magSectorRestriction (M := M + 1)
                      ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
              ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                  2 *
                    ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                        ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                      (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                        ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
                ((marshallSignS A pred).re *
                  v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 <
            (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) :=
                  Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                  (fun x : V => 0 < (τ.1 x).val)).attach.sum
                (fun x =>
                  let predVal : Fin (N + 1) :=
                    ⟨(τ.1 x.1).val - 1, by omega⟩
                  let pred : V → Fin (N + 1) :=
                    Function.update τ.1 x.1 predVal
                  (spinSOpPlus N predVal (τ.1 x.1)).re *
                    v ⟨pred,
                      magSumS_single_site_lowering_predecessor
                        τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)))
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΨ_pred : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hpred :
      ∀ τ : magConfigS V N (M + 1), ∀ x : V,
        ∀ hx : 0 < (τ.1 x).val,
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (magSectorRestriction (M := M + 1)
                    ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
            ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (magSectorRestriction (M := M + 1)
                    ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
            ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                2 *
                  ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                      ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                    (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                      ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
              ((marshallSignS A pred).re *
                v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩))
    (hA_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  exact
    tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
      (V := V) (N := N) A v
      (hsource_difference_pos Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag hB_A hB_B hB_mag)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 strict site-sum positivity from the
unpacked real predecessor difference callback**: the same fully threaded
local callback also supplies the single-site lowered sum positivity used
directly by the adjacent-sector chain.

This is the site-sum analogue of
`tasaki23_lowered_marshall_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`.
It applies the predecessor raising-source difference to site-sum bridge
after the predicted-GS, real source-weight, sublattice-Casimir, and
successor-support data have produced the positive off-`A` minus on-`A`
difference. -/
theorem
    tasaki23_lowered_site_sum_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hsource_difference_pos :
      ∀ Ψ : (V → Fin (N + 1)) → ℂ,
        Ψ =
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
        (∀ τ : magConfigS V N (M + 1), ∀ x : V,
          ∀ hx : 0 < (τ.1 x).val,
            let predVal : Fin (N + 1) :=
              ⟨(τ.1 x).val - 1, by omega⟩
            let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (magSectorRestriction (M := M + 1)
                      ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
              ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (magSectorRestriction (M := M + 1)
                      ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
              ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                  2 *
                    ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                        ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                      (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                        ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
                ((marshallSignS A pred).re *
                  v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        (sublatticeSpinSquaredS N A).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)) •
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
          magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 <
            (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) :=
                  Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                  (fun x : V => 0 < (τ.1 x).val)).attach.sum
                (fun x =>
                  let predVal : Fin (N + 1) :=
                    ⟨(τ.1 x.1).val - 1, by omega⟩
                  let pred : V → Fin (N + 1) :=
                    Function.update τ.1 x.1 predVal
                  (spinSOpPlus N predVal (τ.1 x.1)).re *
                    v ⟨pred,
                      magSumS_single_site_lowering_predecessor
                        τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)))
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΨ_pred : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hpred :
      ∀ τ : magConfigS V N (M + 1), ∀ x : V,
        ∀ hx : 0 < (τ.1 x).val,
          let predVal : Fin (N + 1) :=
            ⟨(τ.1 x).val - 1, by omega⟩
          let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (magSectorRestriction (M := M + 1)
                    ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
            ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (magSectorRestriction (M := M + 1)
                    ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
            ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                2 *
                  ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                      ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                    (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                      ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
              ((marshallSignS A pred).re *
                v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩))
    (hA_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N A).mulVec Ψ))
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_A :
      (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_B :
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
        ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) + 1)) •
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  intro τ
  have hτ :=
    tasaki23_lowered_marshall_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      (V := V) (N := N) A v hsource_difference_pos hΨ_eq hΨ_pred hpred
      hA_A hA_B hA_mag hB_A hB_B hB_mag τ
  rw [
    totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ.1] at hτ
  simpa [map_sum] using hτ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 callback adapter from unpacked real
predecessor differences to lowered site sums**: the fully threaded
predecessor-difference callback can be consumed directly as the strict
single-site lowered sum positivity callback used by the site-sum
successor chain.

This names the callback-level API of
`tasaki23_lowered_site_sum_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`
so later final wrappers can route the predecessor-difference boundary to
the lowered site-sum chain without first passing through the
raising-source dominance final wrapper. -/
abbrev
    tasaki23_lowered_site_sum_pos_callback_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ) :=
  tasaki23_lowered_site_sum_pos_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    (V := V) (N := N) A v

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` lowered sign-sum witness**:
if at least one site outside `A` can be lowered in the target
configuration, then the off-`A` filtered signed lowering sum is strictly
positive.

This is the strict companion to
`tasaki23_signed_lowering_offA_sum_nonneg`: all off-`A` terms are
non-negative, and the witness site contributes strictly positively. -/
theorem tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hwitness : ∃ x : V, A x = false ∧ 0 < (τ.1 x).val) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x := by
  classical
  obtain ⟨x, hAx, hx⟩ := hwitness
  apply Finset.sum_pos'
  · intro y hy
    unfold tasaki23SignedLoweringSiteContribution
    have hAy : A y = false := by
      simpa using (Finset.mem_filter.mp hy).2
    exact tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
      A Φ τ y hAy hΦ_pos
  · refine ⟨x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAx⟩
    · unfold tasaki23SignedLoweringSiteContribution
      exact tasaki23_signed_single_site_lowering_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowerable witness from occupation**:
if the total local occupation on the complement sublattice is positive,
then some site outside `A` has positive local occupation and can
contribute a strict lowered summand. -/
theorem tasaki23_exists_lowerable_offA_of_offA_occupation_pos
    (A : V → Bool) {M : ℕ} (τ : magConfigS V N (M + 1))
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) :
    ∃ x : V, A x = false ∧ 0 < (τ.1 x).val := by
  classical
  by_contra hnone
  have hzero :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hAx : A x = false := by
      simpa using (Finset.mem_filter.mp hx).2
    have hxzero : ¬ 0 < (τ.1 x).val := by
      intro hxpos
      exact hnone ⟨x, hAx, hxpos⟩
    omega
  omega

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` lowered sign-sum from
positive off-`A` occupation**: a positive complement-sublattice
occupation sum supplies the lowerable witness needed for strict
off-`A` lowered signed-sum positivity. -/
theorem tasaki23_signed_lowering_offA_sum_pos_of_offA_occupation_pos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x :=
  tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA
    A Φ τ hΦ_pos
    (tasaki23_exists_lowerable_offA_of_offA_occupation_pos A τ hoffA_pos)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum decomposition**:
the full signed lowered site-sum is the sum of its off-`A` and on-`A`
filtered signed pieces.

This is the exact Boolean partition needed before comparing the
non-negative off-`A` part with the non-positive on-`A` part. -/
theorem tasaki23_signed_lowering_site_sum_eq_offA_add_onA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23SignedLoweringSiteContribution A Φ τ x) +
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23SignedLoweringSiteContribution A Φ τ x) := by
  classical
  unfold tasaki23SignedLoweringSiteContribution
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = false)
    (f := fun x : V =>
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re))]
  congr 1
  apply Finset.sum_congr
  · ext x
    by_cases hAx : A x = false
    · simp [hAx]
    · cases hA : A x <;> simp [hA] at hAx ⊢
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
sublattice dominance**: if the negative of the on-`A` signed sum is
strictly smaller than the off-`A` signed sum, then the full signed
lowered site-sum is strictly positive.

This packages the remaining dominance obligation in the site-sum proof. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23SignedLoweringSiteContribution A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23SignedLoweringSiteContribution A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  rw [tasaki23_signed_lowering_site_sum_eq_offA_add_onA A Φ τ]
  linarith

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
coefficient dominance**: if the on-`A` predecessor-coefficient sum is
strictly smaller than the off-`A` predecessor-coefficient sum, then
the full signed lowered site-sum is strictly positive.

This rewrites the earlier signed-contribution dominance callback using
the coefficient-sum split, leaving the remaining proof obligation in
the direct coefficient form. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
      A Φ τ (by
        rw [tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum A Φ τ,
          tasaki23_signed_lowering_offA_sum_eq_coefficient_sum A Φ τ]
        simpa using hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
positive-source coefficient dominance**: after cancelling the Marshall
signs in the local predecessor coefficients, it is enough to compare the
positive-source coefficient sums over the two sublattices. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
      A
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ
      (by
        rw [
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from lowerable
positive-source coefficient dominance**: after discarding the boundary
sites where the successor configuration cannot be lowered, dominance of
the remaining positive-source predecessor coefficient sums still implies
strict lowered site-sum positivity. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_positive_source_lowerable_coefficient_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
        ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
      A v τ (by
        rw [
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from sublattice
component dominance**: if the negative Marshall-signed `Ŝ_A^-` component
is strictly smaller than the Marshall-signed `Ŝ_¬A^-` component, then the
full signed lowered site-sum is strictly positive.

This is the operator-component form of
`tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA`. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_sublattice_component_lt
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      -((marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N A).mulVec
            (magSectorEmbedding Φ)) τ.1).re) <
        (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
      A Φ τ (by
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A Φ τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A Φ τ
        rw [← hoffA]
        rw [← show
          -((marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N A).mulVec
              (magSectorEmbedding Φ)) τ.1).re) =
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A Φ τ x from by
                rw [honA]
                simp]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 zero local raising component**:
if the target configuration already has local value `N` at `x`, the
single-site raising summand at `x` contributes zero to that target
component.

This is the boundary case for the raising-direction local successor
analysis of the `Ŝ^+_tot` site-sum expansion. -/
theorem onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_top
    {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ) (τ : magConfigS V N M)
    (x : V) (hx : (τ.1 x).val = N) :
    (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) = 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro σ _hσ
  by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
  · rw [onSiteS_apply_of_off_site_agree x _ hoff]
    have hnot_raise : (τ.1 x).val + 1 ≠ (σ x).val := by
      have hσx : (σ x).val ≤ N := by have := (σ x).isLt; omega
      omega
    rw [spinSOpPlus_apply_other N hnot_raise, zero_mul]
  · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]

/-- **Tasaki §2.5 Theorem 2.3 single-site raising component**:
if a target sector configuration `τ` has local value below `N` at
`x`, then the `x`-summand of `Ŝ^+_tot` at `τ` is exactly the raising
matrix coefficient times the source-sector coefficient at the unique
successor configuration obtained by increasing `τ x` by one.

This is the raising-direction companion to
`onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred`. -/
theorem onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ
    {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ) (τ : magConfigS V N M)
    (x : V) (hx : (τ.1 x).val < N) :
    let succVal : Fin (N + 1) :=
      ⟨(τ.1 x).val + 1, by omega⟩
    let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
    (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) =
        spinSOpPlus N (τ.1 x) succVal *
          Φ ⟨succ, magSumS_single_site_raising_successor τ x hx⟩ := by
  classical
  dsimp only
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single
    (Function.update τ.1 x
      ⟨(τ.1 x).val + 1, by omega⟩)]
  · rw [onSiteS_apply_of_off_site_agree]
    · rw [magSectorEmbedding_apply_of_mem Φ
        (magSumS_single_site_raising_successor τ x hx)]
      simp
    · intro y hy
      rw [Function.update_of_ne hy]
  · intro σ _hσ hσ_ne
    by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
    · rw [onSiteS_apply_of_off_site_agree x _ hoff]
      have hnot_raise : (τ.1 x).val + 1 ≠ (σ x).val := by
        intro h_raise
        apply hσ_ne
        funext y
        by_cases hy : y = x
        · subst y
          apply Fin.ext
          simp
          omega
        · rw [Function.update_of_ne hy]
          exact (hoff y hy).symm
      rw [spinSOpPlus_apply_other N hnot_raise, zero_mul]
    · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]
  · intro hnot_mem
    exact False.elim (hnot_mem (Finset.mem_univ _))

/-- **Tasaki §2.5 Theorem 2.3 single-site raising real part**:
at a target configuration whose local value is below `N`, the real
part of the single-site raising summand is the product of the positive
raising matrix coefficient and the real part of the successor
coefficient.

This is the real-valued raising-direction companion to
`onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re`. -/
theorem onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ_re
    {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ) (τ : magConfigS V N M)
    (x : V) (hx : (τ.1 x).val < N) :
    let succVal : Fin (N + 1) :=
      ⟨(τ.1 x).val + 1, by omega⟩
    let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
    ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re) =
        (spinSOpPlus N (τ.1 x) succVal).re *
          (Φ ⟨succ, magSumS_single_site_raising_successor τ x hx⟩).re := by
  classical
  dsimp only
  rw [onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ
    Φ τ x hx]
  rw [Complex.mul_re, spinSOpPlus_apply_im_zero]
  ring

/-- **Tasaki §2.5 Theorem 2.3 off-`A` single-site raising positivity**:
if the raised site lies outside `A`, then the signed real part of its
single-site raising contribution is strictly positive whenever the
source-sector vector is Marshall-positive.

This is the raising-direction counterpart of
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_raising_component_pos_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hx : (τ.1 x).val < N) (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 < (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  classical
  let succVal : Fin (N + 1) := ⟨(τ.1 x).val + 1, by omega⟩
  let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
  have hsuccM : magSumS succ = M + 1 :=
    magSumS_single_site_raising_successor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re := by
    simpa [succVal, succ, hsuccM]
      using
        onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ_re
          Φ τ x hx
  have hcoef_raise : (τ.1 x).val + 1 = succVal.val := by
    dsimp [succVal]
  have hcoef_pos : 0 < (spinSOpPlus N (τ.1 x) succVal).re :=
    spinSOpPlus_apply_re_pos_of_raise N hcoef_raise
  have hoff : ∀ k, k ≠ x → succ k = τ.1 k := by
    intro k hk
    dsimp [succ]
    rw [Function.update_of_ne hk]
  have hsign_raise : (τ.1 x).val + 1 = (succ x).val := by
    dsimp [succ, succVal]
    simp
  have hsign :
      (marshallSignS A succ).re * (marshallSignS A τ.1).re = 1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
      A hAx hoff hsign_raise
  have hsign_target :
      (marshallSignS A τ.1).re * (marshallSignS A succ).re = 1 := by
    rw [mul_comm]
    exact hsign
  have hsq : (marshallSignS A succ).re * (marshallSignS A succ).re = 1 :=
    marshallSignS_re_sq A succ
  have hsrc :
      0 < (marshallSignS A succ).re * (Φ ⟨succ, hsuccM⟩).re :=
    hΦ_pos ⟨succ, hsuccM⟩
  have htarget_src :
      0 < (marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re := by
    nlinarith [hsign_target, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re) =
        (spinSOpPlus N (τ.1 x) succVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_pos hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 on-`A` single-site raising negativity**:
if the raised site lies in `A`, then the signed real part of its
single-site raising contribution is strictly negative whenever the
source-sector vector is Marshall-positive.

This is the raising-direction counterpart of
`tasaki23_signed_single_site_lowering_component_neg_of_A_true`. -/
theorem tasaki23_signed_single_site_raising_component_neg_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hx : (τ.1 x).val < N) (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) < 0 := by
  classical
  let succVal : Fin (N + 1) := ⟨(τ.1 x).val + 1, by omega⟩
  let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
  have hsuccM : magSumS succ = M + 1 :=
    magSumS_single_site_raising_successor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re := by
    simpa [succVal, succ, hsuccM]
      using
        onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ_re
          Φ τ x hx
  have hcoef_raise : (τ.1 x).val + 1 = succVal.val := by
    dsimp [succVal]
  have hcoef_pos : 0 < (spinSOpPlus N (τ.1 x) succVal).re :=
    spinSOpPlus_apply_re_pos_of_raise N hcoef_raise
  have hoff : ∀ k, k ≠ x → succ k = τ.1 k := by
    intro k hk
    dsimp [succ]
    rw [Function.update_of_ne hk]
  have hsign_raise : (τ.1 x).val + 1 = (succ x).val := by
    dsimp [succ, succVal]
    simp
  have hsign :
      (marshallSignS A succ).re * (marshallSignS A τ.1).re = -1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
      A hAx hoff hsign_raise
  have hsign_target :
      (marshallSignS A τ.1).re * (marshallSignS A succ).re = -1 := by
    rw [mul_comm]
    exact hsign
  have hsq : (marshallSignS A succ).re * (marshallSignS A succ).re = 1 :=
    marshallSignS_re_sq A succ
  have hsrc :
      0 < (marshallSignS A succ).re * (Φ ⟨succ, hsuccM⟩).re :=
    hΦ_pos ⟨succ, hsuccM⟩
  have htarget_src :
      (marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re < 0 := by
    nlinarith [hsign_target, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re) =
        (spinSOpPlus N (τ.1 x) succVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_neg_of_pos_of_neg hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 off-`A` local raising non-negativity**:
including the boundary case where the target local value is already
`N`, the signed single-site raising contribution is non-negative at
every site outside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_raising_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_raising_component_nonneg_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  by_cases hx : (τ.1 x).val < N
  · exact le_of_lt
      (tasaki23_signed_single_site_raising_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos)
  · have htop : (τ.1 x).val = N := by
      have hle : (τ.1 x).val ≤ N := by
        have := (τ.1 x).isLt
        omega
      omega
    rw [onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_top
      Φ τ x htop]
    simp

/-- **Tasaki §2.5 Theorem 2.3 on-`A` local raising non-positivity**:
including the boundary case where the target local value is already
`N`, the signed single-site raising contribution is non-positive at
every site inside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_raising_component_neg_of_A_true`. -/
theorem tasaki23_signed_single_site_raising_component_nonpos_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) ≤ 0 := by
  by_cases hx : (τ.1 x).val < N
  · exact le_of_lt
      (tasaki23_signed_single_site_raising_component_neg_of_A_true
        A Φ τ x hx hAx hΦ_pos)
  · have htop : (τ.1 x).val = N := by
      have hle : (τ.1 x).val ≤ N := by
        have := (τ.1 x).isLt
        omega
      omega
    rw [onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_top
      Φ τ x htop]
    simp

/-- **Tasaki §2.5 Theorem 2.3 off-`A` raised sign-sum bound**:
the filtered sum of signed single-site raising contributions over
sites outside `A` is non-negative.

This is the finite-sum form of
`tasaki23_signed_single_site_raising_component_nonneg_of_A_false`. -/
theorem tasaki23_signed_raising_offA_sum_nonneg
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  apply Finset.sum_nonneg
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_raising_component_nonneg_of_A_false
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 on-`A` raised sign-sum bound**:
the filtered sum of signed single-site raising contributions over
sites inside `A` is non-positive.

This is the finite-sum form of
`tasaki23_signed_single_site_raising_component_nonpos_of_A_true`. -/
theorem tasaki23_signed_raising_onA_sum_nonpos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro x hx
  have hAx : A x = true := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_raising_component_nonpos_of_A_true
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 signed local raising contribution**:
the real signed contribution of the `x`-summand in the raised
site-sum at a target predecessor-sector configuration.

This packages the repeated real expression used to split the raised
site-sum into its off-`A` and on-`A` filtered pieces. -/
noncomputable def tasaki23SignedRaisingSiteContribution
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V) : ℝ :=
  (marshallSignS A τ.1).re *
    ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re)

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` raised sign-sum witness**:
if at least one site outside `A` can be raised in the target predecessor
configuration, then the off-`A` filtered signed raising sum is strictly
positive.

This is the raising-direction companion to
`tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA`. -/
theorem tasaki23_signed_raising_offA_sum_pos_of_exists_raiseable_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hwitness : ∃ x : V, A x = false ∧ (τ.1 x).val < N) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedRaisingSiteContribution A Φ τ x := by
  classical
  obtain ⟨x, hAx, hx⟩ := hwitness
  apply Finset.sum_pos'
  · intro y hy
    unfold tasaki23SignedRaisingSiteContribution
    have hAy : A y = false := by
      simpa using (Finset.mem_filter.mp hy).2
    exact tasaki23_signed_single_site_raising_component_nonneg_of_A_false
      A Φ τ y hAy hΦ_pos
  · refine ⟨x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAx⟩
    · unfold tasaki23SignedRaisingSiteContribution
      exact tasaki23_signed_single_site_raising_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 off-`A` raiseable witness from vacancy**:
if the total local vacancy on the complement sublattice is positive,
then some site outside `A` is below the top local occupation `N` and
can contribute a strict raised summand. -/
theorem tasaki23_exists_raiseable_offA_of_offA_vacancy_pos
    (A : V → Bool) {M : ℕ} (τ : magConfigS V N M)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (N - (τ.1 x).val)) :
    ∃ x : V, A x = false ∧ (τ.1 x).val < N := by
  classical
  by_contra hnone
  have hzero :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        (N - (τ.1 x).val)) = 0 := by
    simpa using
      (Finset.sum_eq_zero
        (s := Finset.univ.filter (fun x : V => A x = false))
        (f := fun x : V => N - (τ.1 x).val)
        (by
          intro x hx
          have hAx : A x = false := by
            simpa using (Finset.mem_filter.mp hx).2
          have hxnot : ¬ (τ.1 x).val < N := by
            intro hxlt
            exact hnone ⟨x, hAx, hxlt⟩
          have hxge : N ≤ (τ.1 x).val := by omega
          exact Nat.sub_eq_zero_of_le hxge))
  omega

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` raised sign-sum from
positive off-`A` vacancy**: a positive complement-sublattice vacancy
sum supplies the raiseable witness needed for strict off-`A` raised
signed-sum positivity. -/
theorem tasaki23_signed_raising_offA_sum_pos_of_offA_vacancy_pos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (N - (τ.1 x).val)) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedRaisingSiteContribution A Φ τ x :=
  tasaki23_signed_raising_offA_sum_pos_of_exists_raiseable_offA
    A Φ τ hΦ_pos
    (tasaki23_exists_raiseable_offA_of_offA_vacancy_pos A τ hoffA_pos)

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum decomposition**:
the full signed raised site-sum is the sum of its off-`A` and on-`A`
filtered signed pieces.

This is the exact Boolean partition needed before comparing the
non-negative off-`A` part with the non-positive on-`A` part. -/
theorem tasaki23_signed_raising_site_sum_eq_offA_add_onA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) :
    (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23SignedRaisingSiteContribution A Φ τ x) +
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23SignedRaisingSiteContribution A Φ τ x) := by
  classical
  unfold tasaki23SignedRaisingSiteContribution
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = false)
    (f := fun x : V =>
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re))]
  congr 1
  apply Finset.sum_congr
  · ext x
    by_cases hAx : A x = false
    · simp [hAx]
    · cases hA : A x <;> simp [hA] at hAx ⊢
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum positivity from
sublattice dominance**: if the negative of the on-`A` signed sum is
strictly smaller than the off-`A` signed sum, then the full signed
raised site-sum is strictly positive.

This is the raising-direction companion to
`tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA`. -/
theorem tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hdominates :
      -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23SignedRaisingSiteContribution A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23SignedRaisingSiteContribution A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  rw [tasaki23_signed_raising_site_sum_eq_offA_add_onA A Φ τ]
  linarith

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
site-sum positivity**: to prove the Marshall positivity required by the
adjacent-sector comparison, it suffices to prove the corresponding
strict positivity after expanding `Ŝ^-_tot` as the real part of the sum
of single-site lowering contributions.

This is the bridge from the global lowered-vector hypothesis to the
sitewise predecessor analysis used in Tasaki's ladder comparison. -/
theorem tasaki23_lowered_marshall_pos_of_site_sum_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  intro τ
  rw [totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1]
  simpa [map_sum] using hlowered_site_sum_pos τ

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
vector Marshall positivity**: the vector-level Marshall positivity of
`S^-_{\mathrm{tot}} Φ` implies the corresponding strict site-sum
positivity after expanding the total lowering operator into its
single-site summands.

Together with `tasaki23_lowered_marshall_pos_of_site_sum_pos`, this
identifies the direct site-sum callback used by the interval chain with
the natural Marshall-positivity statement for the lowered ladder image. -/
theorem tasaki23_lowered_site_sum_pos_of_marshall_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) := by
  intro τ
  have hτ := hlowered_marshall_pos τ
  rw [totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1] at hτ
  simpa [map_sum] using hτ

/-- **Tasaki §2.5 Theorem 2.3 source-form lowered site-sum positivity from
lowered Marshall positivity**: for a Marshall-signed positive real source
representative, vector-level Marshall positivity of the total lowered
image supplies the explicit single-site lowering sum positivity consumed
by the adjacent-sector chain.

This is the source-representative specialization of
`tasaki23_lowered_site_sum_pos_of_marshall_pos`, matching the output shape
of the predecessor raising-source difference bridge. -/
theorem tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_lowered_site_sum_pos_of_marshall_pos (V := V) (N := N) A
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
      hlowered_marshall_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from predecessor
raising-source positive differences**: for a Marshall-signed positive
source representative, positivity of the off-`A` minus on-`A` predecessor
raising-source difference supplies the strict single-site lowered sum
positivity consumed by the adjacent-sector chain.

This composes
`tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos`
with the source-form site-sum bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos`. -/
theorem tasaki23_lowered_site_sum_pos_of_raising_predecessor_source_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hdiff :
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                v ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
      (tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
        (V := V) (N := N) A v hdiff)

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
sublattice dominance**: a pointwise dominance of the off-`A` signed
lowered sum over the negative on-`A` signed sum implies the
Marshall-positive lowered-vector hypothesis.

This feeds the dominance bridge into
`tasaki23_lowered_marshall_pos_of_site_sum_pos`. -/
theorem tasaki23_lowered_marshall_pos_of_onA_neg_lt_offA
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A Φ τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A Φ τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
coefficient dominance**: a pointwise coefficient dominance of the
off-`A` lowered predecessor sum over the on-`A` lowered predecessor sum
implies the Marshall-positive lowered-vector hypothesis.

This is the coefficient-level version of
`tasaki23_lowered_marshall_pos_of_onA_neg_lt_offA`, using the
coefficient-sum split to remove the signed-contribution notation from
the remaining callback. -/
theorem tasaki23_lowered_marshall_pos_of_onA_coefficient_lt_offA
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
positive-source coefficient dominance**: a pointwise dominance of the
sign-normalized positive-source predecessor coefficient sum over `A` by
the corresponding sum over `¬A` implies Marshall positivity of the
lowered vector. -/
theorem tasaki23_lowered_marshall_pos_of_positive_source_coefficient_lt
    (A : V → Bool) {M : ℕ} (v : magConfigS V N M → ℝ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A
    (fun σ : magConfigS V N M =>
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
        A v τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
lowerable positive-source coefficient dominance**: it is enough to prove
the positive-source coefficient dominance after restricting both
sublattice sums to sites where the successor configuration can be
lowered. -/
theorem tasaki23_lowered_marshall_pos_of_positive_source_lowerable_coefficient_lt
    (A : V → Bool) {M : ℕ} (v : magConfigS V N M → ℝ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A
    (fun σ : magConfigS V N M =>
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_positive_source_lowerable_coefficient_lt
        A v τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
sublattice component dominance**: a pointwise operator-level dominance
of the Marshall-signed `Ŝ_¬A^-` component over the negative
Marshall-signed `Ŝ_A^-` component implies the Marshall-positive
lowered-vector hypothesis.

This is the sublattice-operator version of
`tasaki23_lowered_marshall_pos_of_onA_coefficient_lt_offA`. -/
theorem tasaki23_lowered_marshall_pos_of_sublattice_component_lt
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -((marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N A).mulVec
              (magSectorEmbedding Φ)) τ.1).re) <
          (marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec
              (magSectorEmbedding Φ)) τ.1).re) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_sublattice_component_lt
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 raised-vector Marshall positivity from
site-sum positivity**: to prove the Marshall positivity required by the
raising-direction adjacent-sector comparison, it suffices to prove the
corresponding strict positivity after expanding `Ŝ^+_tot` as the real
part of the sum of single-site raising contributions.

This is the raising-direction companion to
`tasaki23_lowered_marshall_pos_of_site_sum_pos`. -/
theorem tasaki23_raised_marshall_pos_of_site_sum_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ)
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    ∀ τ : magConfigS V N M,
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  intro τ
  rw [totalSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1]
  simpa [map_sum] using hraised_site_sum_pos τ

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum positivity from
vector Marshall positivity**: the vector-level Marshall positivity of
`S^+_{\mathrm{tot}} Φ` implies the corresponding strict site-sum
positivity after expanding the total raising operator into its
single-site summands.

This is the raising-direction companion to
`tasaki23_lowered_site_sum_pos_of_marshall_pos`. -/
theorem tasaki23_raised_site_sum_pos_of_marshall_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    ∀ τ : magConfigS V N M,
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) := by
  intro τ
  have hτ := hraised_marshall_pos τ
  rw [totalSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1] at hτ
  simpa [map_sum] using hτ

/-- **Tasaki §2.5 Theorem 2.3 raised-vector Marshall positivity from
sublattice dominance**: a pointwise dominance of the off-`A` signed
raised sum over the negative on-`A` signed sum implies the
Marshall-positive raised-vector hypothesis.

This feeds the raising-direction dominance bridge into
`tasaki23_raised_marshall_pos_of_site_sum_pos`. -/
theorem tasaki23_raised_marshall_pos_of_onA_neg_lt_offA
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A Φ τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A Φ τ x) :
    ∀ τ : magConfigS V N M,
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_raised_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector energy step, lowering
direction**: if a source-sector eigenvector is embedded from
`magSumS = M`, and its lowered vector `Ŝ^-_tot Ψ` is Marshall-positive
in the adjacent sector `M + 1`, then the target sector's Theorem 2.2
ground-state eigenvalue is the same eigenvalue.

This isolates the exact remaining positivity input in the proof of
Tasaki §2.5 Theorem 2.3: after ladder eigenvalue preservation and the
sector-support shift, the target-sector uniqueness clause identifies
the neighboring sector energy. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N M → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  obtain ⟨μ_succ, v_succ, hμ_succ_lt, hv_succ_pos, hmul_succ,
      _hsupp_succ, huniq_succ⟩ :=
    marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
      (M := M + 1) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hlowered_eigen :
      (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_of_eigenvec J N hΦ
  have hlowered_supp :
      ∀ σ : V → Fin (N + 1), magSumS σ ≠ M + 1 →
        ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) σ = 0 :=
    totalSpinSOpMinus_mulVec_magSectorEmbedding_supported_succ Φ
  obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
    huniq_succ hlowered_eigen hlowered_supp hlowered_marshall_pos
  exact ⟨μ_succ, v_succ, hμ_succ_lt, hv_succ_pos, hmul_succ, hμ_eq,
    r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector energy step, raising
direction**: if a source-sector eigenvector is embedded from
`magSumS = M + 1`, and its raised vector `Ŝ^+_tot Ψ` is
Marshall-positive in the adjacent sector `M`, then the target sector's
Theorem 2.2 ground-state eigenvalue is the same eigenvalue.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy`, using the
sector-support shift for `Ŝ^+_tot`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N (M + 1) → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  obtain ⟨μ_pred, v_pred, hμ_pred_lt, hv_pred_pos, hmul_pred,
      _hsupp_pred, huniq_pred⟩ :=
    marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hraised_eigen :
      (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_of_eigenvec J N hΦ
  have hraised_supp :
      ∀ σ : V → Fin (N + 1), magSumS σ ≠ M →
        ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) σ = 0 :=
    totalSpinSOpPlus_mulVec_magSectorEmbedding_supported_pred Φ
  obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
    huniq_pred hraised_eigen hraised_supp hraised_marshall_pos
  exact ⟨μ_pred, v_pred, hμ_pred_lt, hv_pred_pos, hmul_pred, hμ_eq,
    r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with
non-vanishing**: the strict Marshall-positive lowered vector is
non-zero, and the adjacent target sector has the same Theorem 2.2
ground-state eigenvalue as the source sector.

This is the same conditional comparison as
`tasaki23_lowering_identifies_adjacent_sector_energy`, with the
non-zero lowered-vector conclusion made explicit for the sector-linking
proof of Theorem 2.3. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N M → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact ⟨tasaki23_lowered_ne_zero_of_marshall_pos A Φ hlowered_marshall_pos,
    tasaki23_lowering_identifies_adjacent_sector_energy A N c hJ_real hJ_real'
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hΦ
      hlowered_marshall_pos⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with
non-vanishing, raising direction**: the strict Marshall-positive raised
vector is non-zero, and the adjacent predecessor sector has the same
Theorem 2.2 ground-state eigenvalue as the source sector.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy_with_nonzero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N (M + 1) → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact ⟨tasaki23_raised_ne_zero_of_marshall_pos A Φ hraised_marshall_pos,
    tasaki23_raising_identifies_adjacent_sector_energy A N c hJ_real hJ_real'
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hΦ
      hraised_marshall_pos⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with Casimir
non-vanishing, lowering direction**: for a Marshall-positive source
sector vector, a non-endpoint total-Casimir eigenvalue gives the
non-zero lowered-vector conclusion, while the existing
Marshall-positive lowered-vector hypothesis identifies the adjacent
sector energy.

This connects the Casimir obstruction package to the adjacent-sector
energy comparison used in the Theorem 2.3 chain. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy_with_casimir_nonzero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)))
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    ⟨tasaki23_totalSpinSOpMinus_mulVec_marshallPositive_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
        A hΦ_cas hγ_ne hv_pos,
      tasaki23_lowering_identifies_adjacent_sector_energy A N c hJ_real
        hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        h_intermediate hΦ hlowered_marshall_pos⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with Casimir
non-vanishing, raising direction**: for a Marshall-positive source
sector vector, a non-endpoint total-Casimir eigenvalue gives the
non-zero raised-vector conclusion, while the existing
Marshall-positive raised-vector hypothesis identifies the adjacent
predecessor-sector energy.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy_with_casimir_nonzero`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy_with_casimir_nonzero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N (M + 1) → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1)))
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    ⟨tasaki23_totalSpinSOpPlus_mulVec_marshallPositive_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
        A hΦ_cas hγ_ne hv_pos,
      tasaki23_raising_identifies_adjacent_sector_energy A N c hJ_real
        hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        h_intermediate hΦ hraised_marshall_pos⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package from site-sum
positivity**: a site-sum Marshall-positivity proof for the lowered
vector is enough to obtain both non-vanishing and the adjacent-sector
ground-state energy identification.

This is the same sector-linking package as
`tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero`, but
with the remaining positivity obligation stated in the local single-site
sum form. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N M → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero A N c
      hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hΦ
      (tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ hlowered_site_sum_pos)

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package from site-sum
positivity, raising direction**: a site-sum Marshall-positivity proof
for the raised vector is enough to obtain both non-vanishing and the
adjacent predecessor-sector ground-state energy identification.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N (M + 1) → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_raising_identifies_adjacent_sector_energy_with_nonzero A N c
      hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hΦ
      (tasaki23_raised_marshall_pos_of_site_sum_pos A Φ hraised_site_sum_pos)

end LatticeSystem.Quantum
