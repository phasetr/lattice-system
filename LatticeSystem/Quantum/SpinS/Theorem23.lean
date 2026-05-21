import Mathlib.Data.Nat.Lattice
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLeTotalSpinSSquaredEigenspace
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLadderInvariant
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.MarshallSign
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder
import LatticeSystem.Quantum.SpinS.Theorem23Casimir

/-!
# Tasaki §2.5 Theorem 2.3 — Marshall–Lieb–Mattis, general spin-S, `|A| ≠ |¬A|`

This file states the final form of Tasaki §2.5 Theorem 2.3 (p. 42):

> Let `(Λ, B)` be a connected bipartite lattice with `|A| ≥ 1` and
> `|B| ≥ 1`. Then the ground states have total spin
>   `S_tot = ||A| − |B|| · S`,
> and are `2 S_tot + 1` fold degenerate. The ground states are
> expanded as in (2.5.4) with the restriction `σ = 0` replaced by
> `σ = M`, where `M = −S_tot, …, S_tot − 1, S_tot`.

The statement is encoded as a `Prop`-valued definition
`tasaki_2_5_theorem_2_3` whose hypothesis bundle and conclusion
match the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(file `MagSectorEmbedding.lean`, PR #869), iterated across the range
of admissible magnetization sectors
`M ∈ tasaki23GroundStateSectors A N` (= the closed integer interval
`[min(|A|, |¬A|)·N, max(|A|, |¬A|)·N]` in `magSumS` units; centered
units `m = M − |V|·N/2 ∈ {−S_tot, …, S_tot}`).

Per Tasaki ("essentially a straightforward modification of that of
Theorem 2.2"), the proof reuses the Marshall sign + Perron–Frobenius
+ toy-Hamiltonian argument with `H_M` replacing `H_0` to obtain
`2 S_tot + 1` sector-unique ground states sharing energy `μ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
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

/-- **Tasaki §2.5 Theorem 2.3 predicted total-spin magnitude**
`S_tot = ||A| − |¬A|| · (N/2)` (the real-valued half-integer
prediction). Equivalent to `‖bipartiteImbalanceWeight A N‖`. -/
noncomputable def tasaki23PredictedTotalSpin (A : V → Bool) (N : ℕ) : ℝ :=
  |((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ)| *
    ((N : ℝ) / 2)

/-- **Tasaki §2.5 Theorem 2.3 predicted total-Casimir value**:
`S_tot * (S_tot + 1)` for the predicted total spin. -/
noncomputable def tasaki23PredictedCasimirValue (A : V → Bool) (N : ℕ) : ℝ :=
  tasaki23PredictedTotalSpin (V := V) A N *
    (tasaki23PredictedTotalSpin (V := V) A N + 1)

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 sublattice-cardinality partition**:
the `A` and `¬A` Boolean fibers partition the finite vertex set. -/
theorem tasaki23_card_filter_A_add_card_notA (A : V → Bool) :
    (Finset.univ.filter (fun x : V => A x = true)).card +
      (Finset.univ.filter (fun x : V => (! A x) = true)).card =
        Fintype.card V := by
  classical
  have hfilter_eq :
      Finset.univ.filter (fun x : V => (! A x) = true) =
        Finset.univ.filter (fun x : V => ¬ A x = true) := by
    congr 1
    funext x
    by_cases hA : A x = true
    · simp [hA]
    · simp [hA]
  rw [hfilter_eq, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not (fun x : V => A x = true)

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predicted spin as half-width**:
the predicted total spin is half the width of the admissible
`magSumS` interval. -/
theorem tasaki23PredictedTotalSpin_eq_sector_half_width (A : V → Bool) (N : ℕ) :
    tasaki23PredictedTotalSpin (V := V) A N =
      (((max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) -
        (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
        ℕ) : ℝ) / 2 := by
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  change |(cA : ℝ) - (cB : ℝ)| * ((N : ℝ) / 2) =
    (((max cA cB * N - min cA cB * N : ℕ) : ℝ) / 2)
  rcases le_total cA cB with h | h
  · have hmin : min cA cB = cA := min_eq_left h
    have hmax : max cA cB = cB := max_eq_right h
    have hle_real : (cA : ℝ) ≤ (cB : ℝ) := by exact_mod_cast h
    have hnonpos : (cA : ℝ) - (cB : ℝ) ≤ 0 := by nlinarith
    rw [hmin, hmax, ← Nat.sub_mul]
    rw [abs_of_nonpos hnonpos]
    have hsub_cast : ((cB - cA : ℕ) : ℝ) = (cB : ℝ) - (cA : ℝ) := by
      have hsub_add : ((cB - cA : ℕ) : ℝ) + (cA : ℝ) = (cB : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel h
      nlinarith
    rw [Nat.cast_mul, hsub_cast]
    ring
  · have hmin : min cA cB = cB := min_eq_right h
    have hmax : max cA cB = cA := max_eq_left h
    have hle_real : (cB : ℝ) ≤ (cA : ℝ) := by exact_mod_cast h
    have hnonneg : 0 ≤ (cA : ℝ) - (cB : ℝ) := by nlinarith
    rw [hmin, hmax, ← Nat.sub_mul]
    rw [abs_of_nonneg hnonneg]
    have hsub_cast : ((cA - cB : ℕ) : ℝ) = (cA : ℝ) - (cB : ℝ) := by
      have hsub_add : ((cA - cB : ℕ) : ℝ) + (cB : ℝ) = (cA : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel h
      nlinarith
    rw [Nat.cast_mul, hsub_cast]
    ring

/-- **Tasaki §2.5 Theorem 2.3 predicted spectral degeneracy**
`2 S_tot + 1 = ||A| − |¬A|| · N + 1` (integer-valued). -/
def tasaki23PredictedDegeneracy (A : V → Bool) (N : ℕ) : ℕ :=
  (Int.natAbs (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℤ))) * N + 1

/-- **Tasaki §2.5 Theorem 2.3 admissible magnetization sectors**:
the set of `magSumS` values `M` whose centered magnetization
`m = M − |V|·N/2` satisfies `m ∈ {−S_tot, …, S_tot}`. In `magSumS`
(non-negative integer) units this is the closed integer interval
`[min(|A|, |¬A|) · N, max(|A|, |¬A|) · N]`, of cardinality
`2 S_tot + 1 = ||A| − |¬A|| · N + 1` (= `tasaki23PredictedDegeneracy`). -/
def tasaki23GroundStateSectors (A : V → Bool) (N : ℕ) : Finset ℕ :=
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  Finset.Icc (min cA cB * N) (max cA cB * N)

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 admissible-sector membership**:
membership in `tasaki23GroundStateSectors A N` is exactly the closed
integer interval between `min(|A|, |¬A|)·N` and `max(|A|, |¬A|)·N`. -/
theorem tasaki23GroundStateSectors_mem_iff (A : V → Bool) (N M : ℕ) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ↔
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N ≤ M ∧
        M ≤ max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N := by
  simp [tasaki23GroundStateSectors]

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 left endpoint sector**:
the lower endpoint `min(|A|, |¬A|)·N` belongs to the admissible
sector interval. -/
theorem tasaki23GroundStateSectors_left_mem (A : V → Bool) (N : ℕ) :
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N ∈
      tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff]
  exact ⟨le_rfl, Nat.mul_le_mul_right N min_le_max⟩

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 right endpoint sector**:
the upper endpoint `max(|A|, |¬A|)·N` belongs to the admissible
sector interval. -/
theorem tasaki23GroundStateSectors_right_mem (A : V → Bool) (N : ℕ) :
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N ∈
      tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff]
  exact ⟨Nat.mul_le_mul_right N min_le_max, le_rfl⟩

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 successor sector closure**:
inside the admissible interval, any non-right-endpoint sector has its
successor in the same interval. This is the combinatorial form needed
to apply the lowering-direction adjacent-sector ladder step. -/
theorem tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right (A : V → Bool) (N : ℕ)
    {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff] at hM ⊢
  omega

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predecessor sector closure**:
inside the admissible interval, any non-left-endpoint sector has its
predecessor in the same interval. This is the combinatorial form needed
to apply the raising-direction adjacent-sector ladder step. -/
theorem tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem (A : V → Bool) (N : ℕ)
    {M : ℕ}
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N < M)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N) :
    M - 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
  rw [tasaki23GroundStateSectors_mem_iff] at hM ⊢
  omega

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 admissible-sector cardinality**:
the interval of ground-state magnetization sectors has the predicted
degeneracy `||A| - |¬A||·N + 1 = 2 S_tot + 1`. -/
theorem tasaki23GroundStateSectors_card (A : V → Bool) (N : ℕ) :
    (tasaki23GroundStateSectors (V := V) A N).card =
      tasaki23PredictedDegeneracy (V := V) A N := by
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  change (Finset.Icc (min cA cB * N) (max cA cB * N)).card =
    Int.natAbs ((cA : ℤ) - (cB : ℤ)) * N + 1
  rcases le_total cA cB with h | h
  · have hmin : min cA cB = cA := min_eq_left h
    have hmax : max cA cB = cB := max_eq_right h
    have habs : Int.natAbs ((cA : ℤ) - (cB : ℤ)) = cB - cA := by
      omega
    rw [hmin, hmax, Nat.card_Icc, habs]
    have hmul : cA * N ≤ cB * N := Nat.mul_le_mul_right N h
    have hcard : cB * N + 1 - cA * N = (cB * N - cA * N) + 1 := by
      omega
    rw [hcard, ← Nat.sub_mul]
  · have hmin : min cA cB = cB := min_eq_right h
    have hmax : max cA cB = cA := max_eq_left h
    have habs : Int.natAbs ((cA : ℤ) - (cB : ℤ)) = cA - cB := by
      omega
    rw [hmin, hmax, Nat.card_Icc, habs]
    have hmul : cB * N ≤ cA * N := Nat.mul_le_mul_right N h
    have hcard : cA * N + 1 - cB * N = (cA * N - cB * N) + 1 := by
      omega
    rw [hcard, ← Nat.sub_mul]

/-- **Tasaki §2.5 Theorem 2.3 real lowering endpoint inequality**:
inside the spin interval and strictly above the lowest weight, the
lowering-kernel value is strictly below `S(S+1)`. -/
private theorem tasaki23_lowering_kernel_lt_predicted_of_m_interval {S m : ℝ}
    (hleft : -S < m) (hright : m ≤ S) :
    m * (m - 1) < S * (S + 1) := by
  have hpos_left : 0 < S + m := by nlinarith
  have hpos_right : 0 < S - m + 1 := by nlinarith
  have hprod : 0 < (S + m) * (S - m + 1) :=
    mul_pos hpos_left hpos_right
  have hdiff : S * (S + 1) - m * (m - 1) =
      (S + m) * (S - m + 1) := by
    ring
  nlinarith

/-- **Tasaki §2.5 Theorem 2.3 real raising endpoint inequality**:
inside the spin interval and strictly below the highest weight, the
raising-kernel value is strictly below `S(S+1)`. -/
private theorem tasaki23_raising_kernel_lt_predicted_of_m_interval {S m : ℝ}
    (hleft : -S ≤ m) (hright : m < S) :
    m * (m + 1) < S * (S + 1) := by
  have hpos_left : 0 < S - m := by nlinarith
  have hpos_right : 0 < S + m + 1 := by nlinarith
  have hprod : 0 < (S - m) * (S + m + 1) :=
    mul_pos hpos_left hpos_right
  have hdiff : S * (S + 1) - m * (m + 1) =
      (S - m) * (S + m + 1) := by
    ring
  nlinarith

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 lowering endpoint mismatch, real form**:
for every admissible sector strictly before the right endpoint, the
lowering-kernel Casimir value is strictly smaller than the predicted
Casimir `S_tot(S_tot+1)`. -/
theorem tasaki23_lowering_kernel_value_lt_predictedCasimirValue_of_mem_of_lt_right
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
    (((Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)) *
        (((Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)) - 1)) <
      tasaki23PredictedCasimirValue (V := V) A N := by
  classical
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  let left := min cA cB * N
  let right := max cA cB * N
  let S := tasaki23PredictedTotalSpin (V := V) A N
  let m := ((Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ))
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  have hleft_le_M : left ≤ M := by simpa [left, cA, cB] using hbounds.1
  have hleft_le_right : left ≤ right := by
    exact Nat.mul_le_mul_right N min_le_max
  have hS_eq_nat : S = (((right - left : ℕ) : ℝ) / 2) := by
    simpa [S, left, right, cA, cB] using
      tasaki23PredictedTotalSpin_eq_sector_half_width (V := V) A N
  have hS_eq : S = ((right : ℝ) - (left : ℝ)) / 2 := by
    have hsub_cast : ((right - left : ℕ) : ℝ) = (right : ℝ) - (left : ℝ) := by
      have hsub_add : ((right - left : ℕ) : ℝ) + (left : ℝ) = (right : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hleft_le_right
      nlinarith
    rw [hS_eq_nat, hsub_cast]
  have hcard_sum : cA + cB = Fintype.card V := by
    simpa [cA, cB] using tasaki23_card_filter_A_add_card_notA (V := V) A
  have hminmax : min cA cB + max cA cB = cA + cB := min_add_max cA cB
  have hcard_mul : Fintype.card V * N = left + right := by
    calc
      Fintype.card V * N = (cA + cB) * N := by rw [hcard_sum]
      _ = (min cA cB + max cA cB) * N := by rw [hminmax]
      _ = left + right := by rw [Nat.add_mul]
  have hcenter : (Fintype.card V : ℝ) * (N : ℝ) / 2 =
      ((left : ℝ) + (right : ℝ)) / 2 := by
    have hcast : ((Fintype.card V * N : ℕ) : ℝ) = ((left + right : ℕ) : ℝ) := by
      exact_mod_cast hcard_mul
    rw [← Nat.cast_mul, hcast, Nat.cast_add]
  have hleft_le_M_real : (left : ℝ) ≤ (M : ℝ) := by exact_mod_cast hleft_le_M
  have hM_lt_right_real : (M : ℝ) < (right : ℝ) := by
    simpa [right, cA, cB] using (show (M : ℝ) <
      (max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N : ℝ) from
        (by exact_mod_cast hMlt))
  have hm_le_S : m ≤ S := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hnegS_lt_m : -S < m := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hlt := tasaki23_lowering_kernel_lt_predicted_of_m_interval
    (S := S) (m := m) hnegS_lt_m hm_le_S
  simpa [tasaki23PredictedCasimirValue, S, m] using hlt

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 raising endpoint mismatch, real form**:
for every admissible source sector strictly above the left endpoint, the
raising-kernel Casimir value is strictly smaller than the predicted
Casimir `S_tot(S_tot+1)`. -/
theorem tasaki23_raising_kernel_value_lt_predictedCasimirValue_of_mem_of_left_lt
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1) :
    (((Fintype.card V : ℝ) * (N : ℝ) / 2 - ((M + 1 : ℕ) : ℝ)) *
        (((Fintype.card V : ℝ) * (N : ℝ) / 2 - ((M + 1 : ℕ) : ℝ)) + 1)) <
      tasaki23PredictedCasimirValue (V := V) A N := by
  classical
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  let left := min cA cB * N
  let right := max cA cB * N
  let S := tasaki23PredictedTotalSpin (V := V) A N
  let m := ((Fintype.card V : ℝ) * (N : ℝ) / 2 - ((M + 1 : ℕ) : ℝ))
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N (M + 1)).mp hM
  have hM_le_right : M + 1 ≤ right := by simpa [right, cA, cB] using hbounds.2
  have hleft_le_right : left ≤ right := by
    exact Nat.mul_le_mul_right N min_le_max
  have hS_eq_nat : S = (((right - left : ℕ) : ℝ) / 2) := by
    simpa [S, left, right, cA, cB] using
      tasaki23PredictedTotalSpin_eq_sector_half_width (V := V) A N
  have hS_eq : S = ((right : ℝ) - (left : ℝ)) / 2 := by
    have hsub_cast : ((right - left : ℕ) : ℝ) = (right : ℝ) - (left : ℝ) := by
      have hsub_add : ((right - left : ℕ) : ℝ) + (left : ℝ) = (right : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hleft_le_right
      nlinarith
    rw [hS_eq_nat, hsub_cast]
  have hcard_sum : cA + cB = Fintype.card V := by
    simpa [cA, cB] using tasaki23_card_filter_A_add_card_notA (V := V) A
  have hminmax : min cA cB + max cA cB = cA + cB := min_add_max cA cB
  have hcard_mul : Fintype.card V * N = left + right := by
    calc
      Fintype.card V * N = (cA + cB) * N := by rw [hcard_sum]
      _ = (min cA cB + max cA cB) * N := by rw [hminmax]
      _ = left + right := by rw [Nat.add_mul]
  have hcenter : (Fintype.card V : ℝ) * (N : ℝ) / 2 =
      ((left : ℝ) + (right : ℝ)) / 2 := by
    have hcast : ((Fintype.card V * N : ℕ) : ℝ) = ((left + right : ℕ) : ℝ) := by
      exact_mod_cast hcard_mul
    rw [← Nat.cast_mul, hcast, Nat.cast_add]
  have hM_le_right_real : ((M + 1 : ℕ) : ℝ) ≤ (right : ℝ) := by
    exact_mod_cast hM_le_right
  have hleft_lt_M_real : (left : ℝ) < ((M + 1 : ℕ) : ℝ) := by
    simpa [left, cA, cB] using (show
      (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N : ℝ) <
          ((M + 1 : ℕ) : ℝ) from
        (by exact_mod_cast hMlt))
  have hnegS_le_m : -S ≤ m := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hm_lt_S : m < S := by
    dsimp [m]
    rw [hcenter, hS_eq]
    nlinarith
  have hlt := tasaki23_raising_kernel_lt_predicted_of_m_interval
    (S := S) (m := m) hnegS_le_m hm_lt_S
  simpa [tasaki23PredictedCasimirValue, S, m] using hlt

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 lowering endpoint mismatch, complex form**:
the predicted Casimir value is not the lowering-kernel value in any
admissible sector strictly before the right endpoint. This is the
`hγ_ne` form used by the Casimir non-vanishing successor wrapper. -/
theorem tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N) :
    (tasaki23PredictedCasimirValue (V := V) A N : ℂ) ≠
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hlt :=
    tasaki23_lowering_kernel_value_lt_predictedCasimirValue_of_mem_of_lt_right
      (V := V) A N hM hMlt
  nlinarith

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 raising endpoint mismatch, complex form**:
the predicted Casimir value is not the raising-kernel value in any
admissible source sector strictly above the left endpoint. This is the
`hγ_ne` form used by the Casimir non-vanishing predecessor wrapper. -/
theorem tasaki23_predictedCasimirValue_ne_raising_kernel_value_of_mem_of_left_lt
    (A : V → Bool) (N : ℕ) {M : ℕ}
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1) :
    (tasaki23PredictedCasimirValue (V := V) A N : ℂ) ≠
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) *
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1)) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hlt :=
    tasaki23_raising_kernel_value_lt_predictedCasimirValue_of_mem_of_left_lt
      (V := V) A N hM hMlt
  have hM1 : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by norm_num
  rw [hM1] at hlt
  nlinarith

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 predicted Casimir value, canonical
orientation**: if the complement sublattice is no larger than `A`, then
the absolute value in `tasaki23PredictedTotalSpin` drops to
`|A| - |¬A|`, and `tasaki23PredictedCasimirValue` is the canonical
joint-Casimir target used in `bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23PredictedCasimirValue_eq_canonical_of_card_notA_le_cardA
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card) :
    tasaki23PredictedCasimirValue (V := V) A N =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) *
              ((N : ℝ) / 2) -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
              ((N : ℝ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) *
              ((N : ℝ) / 2) -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
              ((N : ℝ) / 2)) + 1)) := by
  have hnonneg :
      0 ≤ ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hBA)
  unfold tasaki23PredictedCasimirValue tasaki23PredictedTotalSpin
  rw [abs_of_nonneg hnonneg]
  ring

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS total-Casimir bridge**:
in the canonical orientation `|¬A| ≤ |A|`, membership in the predicted
toy ground-state subspace gives exactly the
`tasaki23PredictedCasimirValue` total-Casimir eigenvector hypothesis.

This packages the definitional total-Casimir component of
`bipartiteToyGroundStateSubspacePredicted` in the form used by the
adjacent-sector Theorem 2.3 chain. -/
theorem tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec Ψ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_totalSpinSSquaredEigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  rw [tasaki23PredictedCasimirValue_eq_canonical_of_card_notA_le_cardA
    (V := V) A N hBA]
  simpa using hmem

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-sublattice Casimir
bridge**: membership in the predicted toy ground-state subspace gives
the maximum `A`-sublattice Casimir eigenvector identity.

This packages the definitional `(Ŝ_A)^2` component of
`bipartiteToyGroundStateSubspacePredicted` for the later sublattice
ladder comparison. -/
theorem tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec Ψ =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_sublatticeSpinSquaredSEigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  simpa using hmem

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-sublattice Casimir
bridge**: membership in the predicted toy ground-state subspace gives
the maximum `¬A`-sublattice Casimir eigenvector identity.

This is the complement companion to
`tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec Ψ =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_sublatticeSpinSquaredS_complementEigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  simpa using hmem

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS toy-Hamiltonian bridge**:
membership in the predicted toy ground-state subspace gives the
predicted toy-Hamiltonian eigenvector identity.

This packages the Casimir-decomposition eigenspace inclusion in pointwise
`mulVec` form, so the later sublattice comparison can use the cross
spin-dot part of the toy Hamiltonian without reopening the joint
eigenspace definition. -/
theorem tasaki23_heisenbergToyHamiltonianS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (heisenbergToyHamiltonianS (Λ := V) A N).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
  have hmem :=
    bipartiteToyGroundStateSubspacePredicted_le_heisenbergToyHamiltonianS_eigenspace
      (Λ := V) A N hΨ
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hmem
  simpa using hmem

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS cross-dot bridge**:
membership in the predicted toy ground-state subspace gives the pointwise
eigenvector identity for `2 • Ŝ_A · Ŝ_¬A`.

Together with the ladder expansion of `Ŝ_A · Ŝ_¬A`, this is the operator
identity that connects the predicted-GS Casimir structure to the
remaining comparison between the `A` and `¬A` lowering components. -/
theorem tasaki23_two_sublatticeSpinSDot_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((2 : ℂ) • sublatticeSpinSDot N A (fun x => ! A x)).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
  rw [← heisenbergToyHamiltonianS_eq_two_sublatticeSpinSDot (Λ := V) (N := N) A]
  exact
    tasaki23_heisenbergToyHamiltonianS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hΨ

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS cross-ladder bridge**:
membership in the predicted toy ground-state subspace gives the pointwise
eigenvector identity for twice the ladder-expanded cross spin-dot
operator.

This is the exact operator form used to separate the `Ŝ_A^+ Ŝ_¬A^-` and
`Ŝ_A^- Ŝ_¬A^+` terms in the remaining sublattice lowering comparison. -/
theorem tasaki23_two_cross_ladder_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((2 : ℂ) •
      (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x) +
        (1 / 2 : ℂ) •
          (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N (fun x => ! A x) +
            sublatticeSpinSOpMinus N A *
              sublatticeSpinSOpPlus N (fun x => ! A x)))).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
  rw [← sublatticeSpinSDot_eq_op3_add_ladder (Λ := V) (N := N) A (fun x => ! A x)]
  exact
    tasaki23_two_sublatticeSpinSDot_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hΨ

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS cross-ladder isolation**:
membership in the predicted toy ground-state subspace isolates the sum
of the two cross-ladder products as the predicted toy energy term minus
twice the `S^3_A S^3_¬A` contribution.

This is the algebraic form used after the cross-dot bridge: the remaining
component comparison can now refer directly to
`Ŝ_A^+ Ŝ_¬A^- + Ŝ_A^- Ŝ_¬A^+` instead of the full dot product. -/
theorem
    tasaki23_cross_ladder_sum_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N (fun x => ! A x) +
        sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec Ψ =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ := by
  let Z : ManyBodyOpS V N :=
    sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)
  let L : ManyBodyOpS V N :=
    sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N (fun x => ! A x) +
      sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N (fun x => ! A x)
  change L.mulVec Ψ =
    bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ - ((2 : ℂ) • Z).mulVec Ψ
  have hbridge :
      ((2 : ℂ) • (Z + (1 / 2 : ℂ) • L)).mulVec Ψ =
        bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ := by
    dsimp [Z, L]
    exact
      tasaki23_two_cross_ladder_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  rw [← hbridge]
  have hop : (2 : ℂ) • (Z + (1 / 2 : ℂ) • L) = (2 : ℂ) • Z + L := by
    ext σ τ
    simp [Z, L]
    ring
  rw [hop]
  ext σ
  rw [Matrix.add_mulVec]
  rw [Matrix.add_mulVec]
  rw [Matrix.add_mulVec]
  simp [Matrix.smul_mulVec]

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS sequential cross-ladder
identity**: the isolated cross-ladder sum can be read as the sum of the
two sequential actions `Ŝ_A^+ (Ŝ_¬A^- Ψ)` and
`Ŝ_A^- (Ŝ_¬A^+ Ψ)`.

This is the component-comparison form of the predicted-GS cross-ladder
constraint: it exposes the two lowered pieces that the remaining
Marshall-positivity argument compares. -/
theorem
    tasaki23_cross_ladder_sequential_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSOpPlus N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
      (sublatticeSpinSOpMinus N A).mulVec
        ((sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec Ψ) =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ := by
  rw [← tasaki23_cross_ladder_sum_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ]
  ext σ
  rw [Matrix.add_mulVec]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec]

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raised-lowered component
identity**: the sequential cross-ladder identity can be read as applying
the opposite sublattice raising operators to the two lowered components
`Ŝ_¬A^- Ψ` and `Ŝ_A^- Ψ`.

This is the component-comparison form used before the remaining
Marshall-positivity step: both summands now act directly on one of the
two lowered sublattice components whose pointwise sizes must be compared.
-/
theorem
    tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSOpPlus N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
      (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ := by
  rw [← tasaki23_cross_ladder_sequential_mulVec_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ]
  have hterm :
      (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
          ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
        (sublatticeSpinSOpMinus N A).mulVec
          ((sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec Ψ) := by
    have hcomm :
        sublatticeSpinSOpMinus N A * sublatticeSpinSOpPlus N (fun x => ! A x) =
          sublatticeSpinSOpPlus N (fun x => ! A x) * sublatticeSpinSOpMinus N A :=
      (sublatticeSpinSOpMinus_cross_commute_plus N A).eq
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [← hcomm]
  rw [hterm]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 re-embedded source-sector cross-ladder
site sums**: after the two lowered components are known to lie in the
successor magnetization eigenspace, re-embed their sector restrictions
and evaluate the raised-lowered cross-ladder identity at a source-sector
configuration.

The left-hand side is now expressed as the on-`A` and off-`A`
single-site raising sums applied to the sector restrictions of
`Ŝ_¬A^- Ψ` and `Ŝ_A^- Ψ`.  This is the component form needed before the
remaining local Marshall-signed coefficient comparison. -/
theorem
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
    (A : V → Bool) (N : ℕ) {M : ℕ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (σ : magConfigS V N M) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
        ((2 : ℂ) •
          (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ)
        σ.1 := by
  have hcross :=
    tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
      (V := V) A N hΨ
  have hA_embed :
      magSectorEmbedding
          (magSectorRestriction (M := M + 1)
            ((sublatticeSpinSOpMinus N A).mulVec Ψ)) =
        (sublatticeSpinSOpMinus N A).mulVec Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
      (V := V) (N := N) (M := M + 1) hA_mag
  have hB_embed :
      magSectorEmbedding
          (magSectorRestriction (M := M + 1)
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)) =
        (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
      (V := V) (N := N) (M := M + 1) hB_mag
  have hcomponent := congrFun hcross σ.1
  rw [← hB_embed, ← hA_embed] at hcomponent
  rw [Pi.add_apply] at hcomponent
  rw [sublatticeSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum,
    sublatticeSpinSOpPlus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum]
    at hcomponent
  simpa [Pi.add_apply] using hcomponent

/-- **Tasaki §2.5 Theorem 2.3 single-site `S^3` source weight**:
the diagonal on-site `Ŝ_x^3` action multiplies an arbitrary vector by the
local source weight `N / 2 - σ x` at configuration `σ`.

This is the local diagonal-action bridge needed to evaluate the
`Ŝ_A^3 Ŝ_¬A^3` term in the re-embedded cross-ladder identity. -/
theorem onSiteS_spinSOp3_mulVec_apply
    (x : V) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ) (σ : V → Fin (N + 1)) :
    ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N).mulVec Φ) σ =
      ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ := by
  classical
  change ∑ τ, (onSiteS x (spinSOp3 N) : ManyBodyOpS V N) σ τ * Φ τ =
    ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ
  rw [Finset.sum_eq_single σ]
  · rw [onSiteS_apply_diag, spinSOp3_apply_diag]
  · intro τ _hτ hτσ
    rw [onSiteS_apply]
    by_cases hoff : ∀ k, k ≠ x → σ k = τ k
    · rw [if_pos hoff]
      have hx : σ x ≠ τ x := by
        intro hxeq
        apply hτσ
        funext k
        by_cases hk : k = x
        · subst k
          exact hxeq.symm
        · exact (hoff k hk).symm
      simp [spinSOp3_apply_offdiag N hx]
    · rw [if_neg hoff, zero_mul]
  · intro hσ
    simp at hσ

/-- **Tasaki §2.5 Theorem 2.3 sublattice `S^3` source weight**:
the on-`A` sublattice `Ŝ_A^3` action multiplies an arbitrary vector by the
sum of the local `S^3` weights over sites in `A`.

This is the sublattice diagonal-action bridge used to evaluate the
right-hand side of the re-embedded cross-ladder identity at source-sector
configurations. -/
theorem sublatticeSpinSOp3_mulVec_apply_eq_onA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A).mulVec Φ) σ =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
  classical
  rw [sublatticeSpinSOp3, Matrix.sum_mulVec, Finset.sum_apply]
  calc
    (∑ c : V,
      Matrix.mulVec (if A c = true then onSiteS c (spinSOp3 N) else 0) Φ σ) =
        ∑ c : V, if A c = true then
          ((N : ℂ) / 2 - ((σ c).val : ℂ)) * Φ σ
        else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases hA : A x = true
          · simp [hA, onSiteS_spinSOp3_mulVec_apply]
          · cases hx : A x <;> simp [hx] at hA ⊢
    _ = ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) * Φ σ := by
          rw [Finset.sum_filter]
    _ = (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
          rw [Finset.sum_mul]

/-- **Tasaki §2.5 Theorem 2.3 complement sublattice `S^3` source weight**:
the `Ŝ_¬A^3` action multiplies an arbitrary vector by the sum of the local
`S^3` weights over sites outside `A`.

This packages the complement sublattice with the `A x = false` filter used
by the local coefficient comparison. -/
theorem sublatticeSpinSOp3_complement_mulVec_apply_eq_offA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N (fun x => ! A x)).mulVec Φ) σ =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((N : ℂ) / 2 - ((σ x).val : ℂ))) * Φ σ := by
  classical
  rw [sublatticeSpinSOp3_mulVec_apply_eq_onA_weight]
  congr 1
  apply Finset.sum_congr
  · ext x
    cases A x <;> simp
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 cross-sublattice `S^3` source weight**:
the diagonal product `Ŝ_A^3 Ŝ_¬A^3` multiplies an arbitrary vector by the
product of the on-`A` and off-`A` local `S^3` weight sums.

This is the right-hand-side evaluation bridge for the re-embedded
cross-ladder source-sector identity. -/
theorem
    sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight
    (A : V → Bool) (N : ℕ) (Φ : (V → Fin (N + 1)) → ℂ)
    (σ : V → Fin (N + 1)) :
    ((sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)).mulVec Φ) σ =
      ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          ((N : ℂ) / 2 - ((σ x).val : ℂ))) *
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          ((N : ℂ) / 2 - ((σ x).val : ℂ)))) * Φ σ := by
  rw [← Matrix.mulVec_mulVec]
  rw [sublatticeSpinSOp3_mulVec_apply_eq_onA_weight]
  rw [sublatticeSpinSOp3_complement_mulVec_apply_eq_offA_weight]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 re-embedded cross-ladder source-weight RHS**:
the re-embedded source-sector cross-ladder site-sum identity can be
rewritten with the explicit `Ŝ_A^3 Ŝ_¬A^3` source-weight product on the
right-hand side.

This substitutes the diagonal `S^3` source-weight evaluation into the
non-ladder term, leaving a scalar multiple of the source coefficient
`Ψ σ`. -/
theorem
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_sublattice_weight_product_of_predictedGS
    (A : V → Bool) (N : ℕ) {M : ℕ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (σ : magConfigS V N M) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
            (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
  rw [tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
    (V := V) A N hΨ hA_mag hB_mag σ]
  rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
  rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
  simp [smul_eq_mul]
  ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 source-weight identity at a lowering
predecessor**: the re-embedded scalar cross-ladder identity can be
specialized to the source-sector predecessor obtained from a successor
configuration `τ` by lowering a site `x`.

This aligns the source-weight equation with the exact predecessor
configuration used in `tasaki23LoweringPredecessorSignedCoefficient`. -/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS
    (A : V → Bool) (N : ℕ) {M : ℕ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hA_mag :
      ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (hB_mag :
      ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
      ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
        ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (magSectorRestriction (M := M + 1)
              ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
      (bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
            (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred := by
  classical
  dsimp only
  exact
    tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_sublattice_weight_product_of_predictedGS
      (V := V) A N hΨ hA_mag hB_mag
      ⟨Function.update τ.1 x ⟨(τ.1 x).val - 1, by omega⟩,
        magSumS_single_site_lowering_predecessor τ x hx⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real source-weight RHS at a lowering
predecessor**: for a Marshall-positive sector embedding, the real part
of the predecessor source-weight right-hand side is the real predicted
toy energy minus twice the real on-`A`/off-`A` source-weight product,
times the signed positive sector coefficient at the predecessor.

This is the real-valued form of the scalar RHS exposed by
`tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS`.
-/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun ρ : magConfigS V N M =>
            (((marshallSignS A ρ.1).re * v ρ : ℝ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (((bipartiteToyMinEnergyPredicted (Λ := V) A N -
        (2 : ℂ) *
          ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
            (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
              ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred).re =
      ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
          2 *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
        ((marshallSignS A pred).re *
          v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) := by
  classical
  dsimp only
  subst Ψ
  rw [magSectorEmbedding_apply_of_mem _
    (magSumS_single_site_lowering_predecessor τ x hx)]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp only [mul_zero, sub_zero]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.re_sum, Complex.im_sum, Complex.natCast_re, Complex.natCast_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.div_re, Complex.div_im,
    zero_mul, mul_zero, sub_zero]
  norm_num [Complex.normSq]
  ring_nf
  exact Or.inl trivial

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real predecessor source-weight identity**:
the complex predecessor source-weight equality can be read on the real
axis for a Marshall-positive sector embedding.

This combines `Complex.re` of the predecessor-specialized cross-ladder
equation with
`tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq`,
so the remaining local comparison may use the real scalar coefficient
directly. -/
theorem
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq :
      Ψ =
        magSectorEmbedding
          (fun ρ : magConfigS V N M =>
            (((marshallSignS A ρ.1).re * v ρ : ℝ) : ℂ)))
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val)
    (hpred :
      let predVal : Fin (N + 1) :=
        ⟨(τ.1 x).val - 1, by omega⟩
      let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
      (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
          ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (magSectorRestriction (M := M + 1)
                ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
        ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
          ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (magSectorRestriction (M := M + 1)
                ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
        (bipartiteToyMinEnergyPredicted (Λ := V) A N -
          (2 : ℂ) *
            ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
              (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) :
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
          v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩) := by
  classical
  dsimp only at hpred ⊢
  have hre := congrArg Complex.re hpred
  rw [
    tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_rhs_re_eq
      (V := V) A N hΨ_eq τ x hx] at hre
  exact hre

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS lowering closure**:
if a full spin-`S` vector lies in the predicted toy ground-state
subspace, then its total-lowering image also lies in that subspace.

This packages the existing predicted-GS ladder invariance in the
pointwise form used by the adjacent-sector Theorem 2.3 chain, without
adding a new membership hypothesis for the lowered vector. -/
theorem tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSOpMinus V N).mulVec Ψ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    bipartiteToyGroundStateSubspacePredicted_totalSpinSOpMinus_invariant
      (Λ := V) A N ⟨Ψ, hΨ, by simp⟩

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raising closure**:
if a full spin-`S` vector lies in the predicted toy ground-state
subspace, then its total-raising image also lies in that subspace.

This is the raising-direction companion to
`tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23_totalSpinSOpPlus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSOpPlus V N).mulVec Ψ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    bipartiteToyGroundStateSubspacePredicted_totalSpinSOpPlus_invariant
      (Λ := V) A N ⟨Ψ, hΨ, by simp⟩

/-- **Tasaki §2.5 Theorem 2.3 lowered predicted-GS `A`-sublattice
Casimir bridge**: the total-lowering image of a predicted toy ground
state still has the maximum `A`-sublattice Casimir eigenvalue.

This combines predicted-GS lowering closure with the `A`-sublattice
Casimir bridge. -/
theorem tasaki23_lowered_sublatticeSpinSquaredS_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered predicted-GS complement-sublattice
Casimir bridge**: the total-lowering image of a predicted toy ground
state still has the maximum `¬A`-sublattice Casimir eigenvalue.

This is the complement companion to
`tasaki23_lowered_sublatticeSpinSquaredS_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem tasaki23_lowered_sublatticeSpinSquaredS_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((totalSpinSOpMinus V N).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered
sublattice-Casimir bridge**: the `A`-sublattice lowering component of
a predicted toy ground state remains in the maximum `A`-sublattice
Casimir eigenspace.

This is the component-level version needed for comparing
`Ŝ_A^- Ψ` with `Ŝ_¬A^- Ψ` in the remaining lowered-Marshall positivity
argument. -/
theorem
    tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((sublatticeSpinSOpMinus N A).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus N A)
      (tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered
sublattice-Casimir bridge**: the `¬A`-sublattice lowering component of
a predicted toy ground state remains in the maximum complement
sublattice-Casimir eigenspace.

This is the complement companion to
`tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem
    tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) •
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus N (fun x => !A x))
      (tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered complement
sublattice-Casimir bridge**: the `A`-sublattice lowering component of
a predicted toy ground state also remains in the maximum complement
sublattice-Casimir eigenspace.

Together with
`tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted`,
this places `Ŝ_A^- Ψ` in the joint maximum sublattice-Casimir
eigenspace needed for the remaining component comparison. -/
theorem
    tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((sublatticeSpinSOpMinus N A).mulVec Ψ) := by
  have hcomm :
      Commute (sublatticeSpinSquaredS N (fun x => ! A x))
        (sublatticeSpinSOpMinus N A) := by
    simpa using
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement
        N (fun x : V => ! A x))
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N hcomm
      (tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered `A`
sublattice-Casimir bridge**: the `¬A`-sublattice lowering component of
a predicted toy ground state also remains in the maximum `A`-sublattice
Casimir eigenspace.

Together with
`tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted`,
this places `Ŝ_¬A^- Ψ` in the joint maximum sublattice-Casimir
eigenspace needed for the remaining component comparison. -/
theorem
    tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) •
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement N A)
      (tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 joint sublattice-Casimir eigenspace**:
the intersection of the maximum `A`- and `¬A`-sublattice Casimir
eigenspaces.

This names the structural target used by the component-lowering chain,
where both `Ŝ_A^- Ψ` and `Ŝ_¬A^- Ψ` are compared after being shown to
remain in the joint maximum sublattice-Casimir eigenspace. -/
noncomputable def tasaki23JointSublatticeCasimirEigenspace
    (A : V → Bool) (N : ℕ) : Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
        ((N : ℂ) / 2)) *
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
        ((N : ℂ) / 2)) + 1))
    ⊓ Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered joint
sublattice-Casimir eigenspace bridge**: the `A`-sublattice lowering
component of a predicted toy ground state lies in the joint maximum
sublattice-Casimir eigenspace.

This packages the same-side and cross-side Casimir identities for
`Ŝ_A^- Ψ` in the exact intersection form needed by the remaining
component comparison. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
      tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23JointSublatticeCasimirEigenspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered joint
sublattice-Casimir eigenspace bridge**: the complement-sublattice
lowering component of a predicted toy ground state lies in the joint
maximum sublattice-Casimir eigenspace.

This packages the same-side and cross-side Casimir identities for
`Ŝ_¬A^- Ψ` in the exact intersection form needed by the remaining
component comparison. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
      tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23JointSublatticeCasimirEigenspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered component joint-magnetization
subspace**: the structural target for a lowered component of a
sector-`M` source vector.

It combines the joint maximum sublattice-Casimir eigenspace with the
successor magnetization subspace `magSumS = M + 1`, in centered
magnetization units.  The remaining comparison can then use one
submodule membership carrying both the Casimir and sector-support
facts for the lowered components. -/
noncomputable def tasaki23LoweredJointMagSubspace
    (A : V → Bool) (N M : ℕ) : Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  tasaki23JointSublatticeCasimirEigenspace (V := V) A N ⊓
    magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 `A`-lowered joint-magnetization bridge**:
if a sector-`M` representative is in the predicted toy ground-state
subspace, then its `A`-sublattice lowering component lies in the
combined joint-Casimir and successor-sector subspace.

This packages the PR #3408 joint-Casimir membership together with the
standard sublattice-lowering magnetization shift. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {M : ℕ} {Φ : magConfigS V N M → ℂ}
    (hΦ : magSectorEmbedding Φ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) ∈
      tasaki23LoweredJointMagSubspace (V := V) A N M := by
  unfold tasaki23LoweredJointMagSubspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΦ
  · have hshift :
        (sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ) ∈
          magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
      sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        N A (magSectorEmbedding_mem_magSubspaceS Φ)
    convert hshift using 1
    norm_num
    ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 complement-lowered joint-magnetization
bridge**: if a sector-`M` representative is in the predicted toy
ground-state subspace, then its complement-sublattice lowering component
lies in the combined joint-Casimir and successor-sector subspace.

This is the complement component version of
`tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_sublatticeSpinSOpMinus_complement_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {M : ℕ} {Φ : magConfigS V N M → ℂ}
    (hΦ : magSectorEmbedding Φ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (magSectorEmbedding Φ)) ∈
      tasaki23LoweredJointMagSubspace (V := V) A N M := by
  unfold tasaki23LoweredJointMagSubspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΦ
  · have hshift :
        (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ) ∈
          magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
      sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        N (fun x => ! A x) (magSectorEmbedding_mem_magSubspaceS Φ)
    convert hshift using 1
    norm_num
    ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization Casimir
projection**: membership in `tasaki23LoweredJointMagSubspace` exposes
the joint maximum sublattice-Casimir component.

This is an unpacking lemma for the cross-ladder comparison callback. -/
theorem tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    w ∈ tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23LoweredJointMagSubspace at hw
  exact (Submodule.mem_inf.mp hw).1

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization sector
projection**: membership in `tasaki23LoweredJointMagSubspace` exposes
the successor magnetization support.

This is the sector-support companion to
`tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace`. -/
theorem tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    w ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) := by
  unfold tasaki23LoweredJointMagSubspace at hw
  exact (Submodule.mem_inf.mp hw).2

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization `A`-Casimir
equation**: a vector in `tasaki23LoweredJointMagSubspace` satisfies the
maximum `A`-sublattice Casimir eigenvector identity.

This turns the packed subspace membership used by the interval chain
into the explicit equation needed by the remaining representation-
theoretic comparison. -/
theorem tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    (sublatticeSpinSquaredS N A).mulVec w =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • w := by
  have hjoint :=
    tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
      (V := V) A N M hw
  unfold tasaki23JointSublatticeCasimirEigenspace at hjoint
  have hA := (Submodule.mem_inf.mp hjoint).1
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hA
  exact hA

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization complement
Casimir equation**: a vector in `tasaki23LoweredJointMagSubspace`
satisfies the maximum `¬A`-sublattice Casimir eigenvector identity.

This is the complement-sublattice companion to
`tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace`. -/
theorem tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • w := by
  have hjoint :=
    tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
      (V := V) A N M hw
  unfold tasaki23JointSublatticeCasimirEigenspace at hjoint
  have hB := (Submodule.mem_inf.mp hjoint).2
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hB
  exact hB

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS transfer across a non-zero
real scalar**: if a vector in the predicted toy ground-state subspace is
a non-zero real scalar multiple of another vector, then the second vector
also lies in the predicted toy ground-state subspace.

This is the membership analogue of
`tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq`, used
after the lowered ladder image is identified with the successor-sector
representative up to a positive real scalar. -/
theorem tasaki23_mem_bipartiteToyGroundStateSubspacePredicted_of_real_smul_eq
    (A : V → Bool) (N : ℕ) {r : ℝ}
    {Ψ Φ : (V → Fin (N + 1)) → ℂ}
    (hr : r ≠ 0)
    (hrel : Ψ = (r : ℂ) • Φ)
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    Φ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hsmul :
      (r : ℂ) • Φ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    simpa [← hrel] using hΨ
  have hinv :
      ((r : ℂ)⁻¹) • ((r : ℂ) • Φ) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    Submodule.smul_mem _ _ hsmul
  have hscale : ((r : ℂ)⁻¹) • ((r : ℂ) • Φ) = Φ := by
    rw [smul_smul, inv_mul_cancel₀ hrC, one_smul]
  rwa [hscale] at hinv

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS lowered Casimir bridge**:
in the canonical orientation, a vector in the predicted toy ground-state
subspace has a total-lowering image with the Theorem 2.3 predicted
total-Casimir eigenvalue.

This combines predicted-GS lowering closure with the predicted-GS
total-Casimir bridge, so no separate Casimir hypothesis is needed for
the lowered ladder image. -/
theorem tasaki23_lowered_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hBA
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raised Casimir bridge**:
in the canonical orientation, a vector in the predicted toy ground-state
subspace has a total-raising image with the Theorem 2.3 predicted
total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_lowered_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23_raised_predictedCasimirValue_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpPlus V N).mulVec Ψ) := by
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N hBA
      (tasaki23_totalSpinSOpPlus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir preservation under
lowering**: if a full spin-`S` vector has the Theorem 2.3 predicted
total-Casimir eigenvalue, then its image under `Ŝ^-_tot` has the same
total-Casimir eigenvalue.

This is the one-step Casimir stability needed when the admissible-sector
chain propagates Theorem 2.3 ground states by the total lowering
operator. -/
theorem tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        (totalSpinSOpMinus V N).mulVec Ψ := by
  have hcomm : totalSpinSSquared V N * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSSquared V N :=
    (totalSpinSSquared_commute_totalSpinSOpMinus (V := V) (N := N)).eq
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ_cas, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir preservation under
raising**: if a full spin-`S` vector has the Theorem 2.3 predicted
total-Casimir eigenvalue, then its image under `Ŝ^+_tot` has the same
total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue`, used when
the admissible-sector chain is traversed toward smaller `magSumS`
sectors. -/
theorem tasaki23_totalSpinSOpPlus_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        (totalSpinSOpPlus V N).mulVec Ψ := by
  have hcomm : totalSpinSSquared V N * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSSquared V N :=
    (totalSpinSSquared_commute_totalSpinSOpPlus (V := V) (N := N)).eq
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hΨ_cas, Matrix.mulVec_smul]

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded predicted-Casimir
preservation under lowering**: if a Marshall-signed sector vector has the
Theorem 2.3 predicted total-Casimir eigenvalue after zero-extension to the
full spin-`S` Hilbert space, then its image under `Ŝ^-_tot` has the same
total-Casimir eigenvalue.

This is the sector-vector form used in the adjacent-sector chain, before the
lowered vector is compared with the target sector's Theorem 2.2
Marshall-positive representative. -/
theorem
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_totalSpinSOpMinus_preserves_predictedCasimirValue
      (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 sector-embedded predicted-Casimir
preservation under raising**: if a Marshall-signed sector vector has the
Theorem 2.3 predicted total-Casimir eigenvalue after zero-extension to the
full spin-`S` Hilbert space, then its image under `Ŝ^+_tot` has the same
total-Casimir eigenvalue.

This is the raising-direction companion to
the corresponding lowering theorem above. -/
theorem
    tasaki23_totalSpinSOpPlus_marshallSignedEmbedding_preserves_predictedCasimirValue
    (A : V → Bool) (N : ℕ) {M : ℕ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        ((totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
        ((totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_totalSpinSOpPlus_preserves_predictedCasimirValue
      (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir transfer across a
non-zero real scalar**: if a vector with the predicted total-Casimir
eigenvalue is a non-zero real scalar multiple of another vector, then
the second vector has the same predicted total-Casimir eigenvalue.

This is the cancellation step used after identifying a lowered ladder
image with the adjacent-sector Marshall-positive representative up to a
positive real scalar. -/
theorem tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
    (A : V → Bool) (N : ℕ) {r : ℝ}
    {Ψ Φ : (V → Fin (N + 1)) → ℂ}
    (hr : r ≠ 0)
    (hrel : Ψ = (r : ℂ) • Φ)
    (hΨ_cas :
      (totalSpinSSquared V N).mulVec Ψ =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Ψ) :
    (totalSpinSSquared V N).mulVec Φ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) • Φ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [hrel, Matrix.mulVec_smul] at hΨ_cas
  funext σ
  have hσ := congrFun hΨ_cas σ
  change (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) *
        ((r : ℂ) * Φ σ) at hσ
  change ((totalSpinSSquared V N).mulVec Φ) σ =
      (tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ
  have hσ' :
      (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
        (r : ℂ) * ((tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ) := by
    calc
      (r : ℂ) * ((totalSpinSSquared V N).mulVec Φ) σ =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) *
            ((r : ℂ) * Φ σ) := hσ
      _ = (r : ℂ) * ((tasaki23PredictedCasimirValue (V := V) A N : ℂ) * Φ σ) := by
        ring
  exact mul_left_cancel₀ hrC hσ'

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step**:
inside the admissible sector interval, a source-sector
Marshall-positive eigenvector in sector `M`, together with the lowered
site-sum positivity input, produces a Marshall-positive eigenvector in
the successor sector `M + 1` at the same eigenvalue.

This is the one-step chain link for the final Theorem 2.3 proof.  The
interval hypotheses prove that `M + 1` is still an admissible sector,
and the previously established lowered site-sum package identifies the
successor-sector Theorem 2.2 eigenvalue with the source eigenvalue. -/
theorem tasaki23_successor_sector_common_energy_of_site_sum_pos
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hsucc_mem :
      M + 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right A N hM hMlt
  obtain ⟨hlowered_ne, μ_succ, v_succ, hμ_succ_lt, hv_succ_pos,
      hmul_succ, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ hlowered_site_sum_pos
  subst μ_succ
  exact ⟨hsucc_mem, hμ_lt, hv_pos, hΦ, hlowered_ne, v_succ,
    hμ_succ_lt, hv_succ_pos, hmul_succ, r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
Casimir non-vanishing**: inside the admissible sector interval, a
Marshall-positive source-sector Casimir eigenvector whose Casimir value
is not the lowering endpoint value has a non-zero lowered image, and a
site-sum positivity proof identifies the successor-sector ground-state
energy with the source energy.

This connects the Casimir endpoint obstruction to the one-step
successor link used in the final Theorem 2.3 chain. -/
theorem tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
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
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hsucc_mem :
      M + 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_succ_mem_of_mem_of_lt_right A N hM hMlt
  obtain ⟨hlowered_ne, μ_succ, v_succ, hμ_succ_lt, hv_succ_pos,
      hmul_succ, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_lowering_identifies_adjacent_sector_energy_with_casimir_nonzero
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ_cas hγ_ne hv_pos hΦ
      (tasaki23_lowered_marshall_pos_of_site_sum_pos A
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        hlowered_site_sum_pos)
  subst μ_succ
  exact ⟨hsucc_mem, hμ_lt, hv_pos, hΦ, hlowered_ne, v_succ,
    hμ_succ_lt, hv_succ_pos, hmul_succ, r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step**:
inside the admissible sector interval, a source-sector
Marshall-positive eigenvector in sector `M + 1`, together with the
raised site-sum positivity input, produces a Marshall-positive
eigenvector in the predecessor sector `M` at the same eigenvalue.

This is the raising-direction interval wrapper corresponding to
`tasaki23_successor_sector_common_energy_of_site_sum_pos`. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  have hpred_mem_raw :
      (M + 1) - 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem A N hMlt hM
  have hpred_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa using hpred_mem_raw
  obtain ⟨hraised_ne, μ_pred, v_pred, hμ_pred_lt, hv_pred_pos,
      hmul_pred, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_raising_identifies_adjacent_sector_energy_of_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ hraised_site_sum_pos
  subst μ_pred
  exact ⟨hpred_mem, hμ_lt, hv_pos, hΦ, hraised_ne, v_pred,
    hμ_pred_lt, hv_pred_pos, hmul_pred, r, hr_pos, hrel⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step
from Casimir non-vanishing**: inside the admissible sector interval, a
Marshall-positive source-sector Casimir eigenvector whose Casimir value
is not the raising endpoint value has a non-zero raised image, and a
site-sum positivity proof identifies the predecessor-sector ground-state
energy with the source energy.

This is the raising-direction interval wrapper corresponding to
`tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
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
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  have hpred_mem_raw :
      (M + 1) - 1 ∈ tasaki23GroundStateSectors (V := V) A N :=
    tasaki23GroundStateSectors_pred_mem_of_left_lt_of_mem A N hMlt hM
  have hpred_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa using hpred_mem_raw
  obtain ⟨hraised_ne, μ_pred, v_pred, hμ_pred_lt, hv_pred_pos,
      hmul_pred, hμ_eq, r, hr_pos, hrel⟩ :=
    tasaki23_raising_identifies_adjacent_sector_energy_with_casimir_nonzero
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hΦ_cas hγ_ne hv_pos hΦ
      (tasaki23_raised_marshall_pos_of_site_sum_pos A
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        hraised_site_sum_pos)
  subst μ_pred
  exact ⟨hpred_mem, hμ_lt, hv_pos, hΦ, hraised_ne, v_pred,
    hμ_pred_lt, hv_pred_pos, hmul_pred, r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
the predicted Casimir value**: inside the admissible sector interval, a
Marshall-positive source vector whose total-Casimir eigenvalue is the
Theorem 2.3 predicted value has a non-zero lowered image away from the
right endpoint, and the site-sum positivity input identifies the
successor-sector ground-state energy with the source energy.

This specializes
`tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`
by discharging its endpoint-mismatch hypothesis with the
predicted-Casimir mismatch lemma. -/
theorem tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right
        (V := V) A N hM hMlt)
      hlowered_site_sum_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step from
the predicted Casimir value**: inside the admissible sector interval, a
Marshall-positive source vector in sector `M + 1` whose total-Casimir
eigenvalue is the Theorem 2.3 predicted value has a non-zero raised
image away from the left endpoint, and the site-sum positivity input
identifies the predecessor-sector ground-state energy with the source
energy.

This specializes
`tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value`
by discharging its endpoint-mismatch hypothesis with the
predicted-Casimir mismatch lemma. -/
theorem tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_casimir_ne_kernel_value
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (tasaki23_predictedCasimirValue_ne_raising_kernel_value_of_mem_of_left_lt
        (V := V) A N hM hMlt)
      hraised_site_sum_pos

/-- **Tasaki §2.5 Theorem 2.3 successor step with lowered predicted
Casimir image**: the predicted-Casimir successor common-energy wrapper also
returns that the actual lowered full-space ladder image has the predicted
total-Casimir eigenvalue.

This packages the adjacent-sector energy comparison with
`tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue`.
-/
theorem tasaki23_successor_common_energy_with_lowered_predictedCasimir
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
      μ < c ∧ (∀ τ, 0 < v τ) ∧
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
      ∃ v_succ : magConfigS V N (M + 1) → ℝ,
        μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
        ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N (M + 1),
            (((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
              r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  constructor
  · exact
      tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
        A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
        hlowered_site_sum_pos
  · exact
      tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
        (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 predecessor step with raised predicted
Casimir image**: the predicted-Casimir predecessor common-energy wrapper
also returns that the actual raised full-space ladder image has the
predicted total-Casimir eigenvalue.

This is the raising-direction companion to
`tasaki23_successor_common_energy_with_lowered_predictedCasimir`. -/
theorem tasaki23_predecessor_common_energy_with_raised_predictedCasimir
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
      μ < c ∧ (∀ τ, 0 < v τ) ∧
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (totalSpinSOpPlus V N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
      ∃ v_pred : magConfigS V N M → ℝ,
        μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
        ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
              r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  constructor
  · exact
      tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
        A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
        hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
        hraised_site_sum_pos
  · exact
      tasaki23_totalSpinSOpPlus_marshallSignedEmbedding_preserves_predictedCasimirValue
        (V := V) A N hΦ_cas

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy successor step from
lowered dominance**: inside the admissible sector interval, the pointwise
dominance of the off-`A` lowered signed sum over the negative on-`A`
signed sum supplies the strict site-sum positivity input and hence
produces the successor-sector common-energy conclusion.

This is the dominance-form wrapper around
`tasaki23_successor_sector_common_energy_of_site_sum_pos`.  The
substantive remaining proof obligation is the dominance hypothesis
itself. -/
theorem tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact tasaki23_successor_sector_common_energy_of_site_sum_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
        A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent common-energy predecessor step from
raised dominance**: inside the admissible sector interval, the pointwise
dominance of the off-`A` raised signed sum over the negative on-`A`
signed sum supplies the strict site-sum positivity input and hence
produces the predecessor-sector common-energy conclusion.

This is the raising-direction dominance-form wrapper around
`tasaki23_predecessor_sector_common_energy_of_site_sum_pos`. The
substantive remaining proof obligation is the dominance hypothesis
itself. -/
theorem tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact tasaki23_predecessor_sector_common_energy_of_site_sum_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
    (fun τ =>
      tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
        A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
from lowered dominance**: the lowered dominance hypothesis supplies the
strict site-sum positivity input for the predicted-Casimir successor
common-energy wrapper.

This is the predicted-Casimir analogue of
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA`; the
substantive dominance estimate remains an explicit hypothesis. -/
theorem
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (fun τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
with successor Casimir**: the lowered dominance common-energy wrapper also
transfers the predicted total-Casimir identity to the successor-sector
Marshall-positive representative.

This is the source-vector form of the interval-threading step: once the
source sector carries the predicted Casimir, the adjacent successor returned
by Theorem 2.2 uniqueness carries it as well, so later interval induction does
not need a fresh source-Casimir callback at the successor sector. -/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas hdominates
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hcas_lowered :
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) :=
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
      A N hΦ_cas
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
      ⟨r, hr_pos, hrel⟩⟩⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir successor step
with successor Casimir from lowered site-sum positivity**: the direct
lowered site-sum positivity common-energy wrapper also transfers the
predicted total-Casimir identity to the successor-sector Marshall-positive
representative.

This is the site-sum form of
`tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA`.
-/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_site_sum_pos
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      hlowered_site_sum_pos
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hcas_lowered :
      (totalSpinSSquared V N).mulVec
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          ((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) :=
    tasaki23_totalSpinSOpMinus_marshallSignedEmbedding_preserves_predictedCasimirValue
      A N hΦ_cas
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hne,
    ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
      ⟨r, hr_pos, hrel⟩⟩⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-Casimir predecessor step
from raised dominance**: the raised dominance hypothesis supplies the
strict site-sum positivity input for the predicted-Casimir predecessor
common-energy wrapper.

This is the raising-direction companion to
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue`.
-/
theorem
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ hΦ_cas
      (fun τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hdominates τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS successor step from
lowered dominance**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the source-sector vector in the predicted toy
ground-state subspace supplies the predicted-Casimir hypothesis needed
by the lowered dominance common-energy wrapper.

The dominance estimate remains explicit; this theorem only replaces the
source total-Casimir input by predicted-GS membership. -/
theorem
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
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
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hdominates

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS successor step from
lowered site-sum positivity**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the source-sector vector in the predicted toy ground-state
subspace supplies the predicted-Casimir hypothesis, while the direct
lowered site-sum positivity hypothesis supplies Marshall positivity of
the lowered vector.

This is the site-sum analogue of
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
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
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hlowered_site_sum_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent successor step with successor
predicted-GS membership from lowered site-sum positivity**: if the source
representative lies in the predicted toy ground-state subspace, then the
successor representative produced by the lowered adjacent-sector step
lies in the same predicted subspace.

The proof uses predicted-GS invariance under `Ŝ^-_tot` and then cancels
the positive real scalar relating the lowered image to the successor
Marshall-positive representative. -/
theorem
    tasaki23_successor_sector_common_energy_with_successor_predictedGS_of_site_sum_pos
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
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_succ : magConfigS V N (M + 1) → ℝ,
      μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  have hstep :=
    tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hM hMlt hμ_lt hv_pos hΦ hΦ_pred
      hlowered_site_sum_pos
  rcases hstep with ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hlowered_ne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, r, hr_pos, hrel⟩
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hlowered_pred :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
      A N hΦ_pred
  have hsucc_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N :=
    tasaki23_mem_bipartiteToyGroundStateSubspacePredicted_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hlowered_pred
  exact ⟨hsucc_mem, hμ_lt', hv_pos', hΦ', hlowered_ne,
    v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred,
    r, hr_pos, hrel⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent predicted-GS predecessor step from
raised dominance**: in the canonical orientation `|¬A| ≤ |A|`,
membership of the sector-`M+1` source vector in the predicted toy
ground-state subspace supplies the predicted-Casimir hypothesis needed
by the raised dominance common-energy wrapper.

This is the raising-direction companion to
`tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
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
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ}
    (hμ_lt : μ < c)
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hΦ_pred :
      magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ∧
    μ < c ∧ (∀ τ, 0 < v τ) ∧
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ v_pred : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_predecessor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        A N hBA hΦ_pred)
      hdominates

/-- **Tasaki §2.5 Theorem 2.3 (Marshall–Lieb–Mattis general spin-S), final
statement** as a `Prop`.

The hypothesis bundle matches the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(PR #869) exactly. Given:
- real symmetric coupling `J` (`(J x y).im = 0`, `star (J x y) = J x y`,
  `J x y = J y x`, `0 ≤ (J x y).re`);
- bipartite support (`A x = A y → J x y = 0`);
- positive on the bipartite complete graph (`Adj → 0 < (J x y).re`);
- non-empty sublattices (`|A| ≥ 1`, `|¬A| ≥ 1`);
- a uniform spectral shift `c` strictly above the dressed diagonal;
- the intermediate-existence hypothesis from Theorem 2.2 (#869);
- each admissible sector `M` is non-empty;

the conclusion asserts existence of a common ground-state energy `μ`
realised on every admissible sector by a Marshall-positive
eigenvector (Tasaki (2.5.4) with `σ = M`), with within-sector
uniqueness up to positive scalar, plus global minimality of `μ`.

The proof iterates #869 sector-by-sector across
`tasaki23GroundStateSectors A N`. -/
def tasaki_2_5_theorem_2_3
    (A : V → Bool) (N : ℕ) (J : V → V → ℂ) (c : ℝ) : Prop :=
  -- Coupling hypotheses (matching #869's bundle).
  (∀ x y, (J x y).im = 0) →
  (∀ x y, star (J x y) = J x y) →
  (∀ x y, J x y = J y x) →
  (∀ x y, 0 ≤ (J x y).re) →
  (∀ x y, A x = A y → J x y = 0) →
  (∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re) →
  -- Spectral shift strictly above the dressed diagonal (matching #869).
  (∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c) →
  -- Intermediate-existence hypothesis (matching #869).
  (∀ τ : V → Fin (N + 1), ∀ x : V, ∃ z, A z ≠ A x ∧ (τ z).val < N) →
  -- Non-empty sublattices (Tasaki Theorem 2.3 hypothesis `|A| ≥ 1`, `|¬A| ≥ 1`).
  (1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card) →
  (1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) →
  -- Conclusion.
  ∃ μ : ℝ,
    -- (Existence + Marshall expansion + sector uniqueness) per admissible sector.
    (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      [Nonempty (magConfigS V N M)] →
      ∃ v : magConfigS V N M → ℝ,
        μ < c ∧ (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
          (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
          μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ))) ∧
    -- Global minimality of μ across all eigenvalues.
    (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ')

/-- **Per-sector existence step (toward Tasaki §2.5 Theorem 2.3 proof)**.

For each admissible magnetization sector `M ∈ tasaki23GroundStateSectors A N`
with `Nonempty (magConfigS V N M)`, the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full` (#869)
gives a Marshall-positive ground state of the spin-`S` antiferromagnetic
Heisenberg Hamiltonian (Tasaki (2.5.4) with `σ = M`) at some sector
eigenvalue `μ_M < c`, plus within-sector uniqueness up to positive scalar.

This is the first step of the Tasaki §2.5 Theorem 2.3 proof
("essentially a straightforward modification of that of Theorem 2.2"):
the proof of `tasaki_2_5_theorem_2_3` then iterates this per-sector
existence across the admissible range and shows the sector eigenvalues
`μ_M` coincide (constancy via the SU(2) ladder
`heisenbergHamiltonianS_commute_totalSpinSOpMinus`) and that the common
value is the global minimum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42. -/
theorem tasaki_2_5_theorem_2_3_sector_existence
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
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) :=
  marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir**: choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir successor package.

The remaining hypotheses are exactly the two mathematical inputs still
needed for the chosen Theorem 2.2 sector vector: predicted total-Casimir
eigenvalue and lowered site-sum positivity. -/
theorem tasaki23_successor_sector_existence_with_lowered_predictedCasimir
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_successor_common_energy_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

/-- **Tasaki §2.5 Theorem 2.3 successor predicted-Casimir
propagation**: in the lowering-direction sector-existence step, the
successor representative returned by the adjacent-sector comparison also
has the Theorem 2.3 predicted total-Casimir eigenvalue.

The existing package already proves that the lowered source vector has
the predicted Casimir eigenvalue and that its real parts are a positive
real scalar multiple of the successor representative in Marshall
coordinates.  Since both vectors are real and supported in the successor
sector, this is a full scalar equality, so the Casimir eigenvector
equation cancels the scalar. -/
theorem
    tasaki23_successor_sector_existence_with_successor_predictedCasimir
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hpack⟩ :=
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas hsource_site_sum
  have hM_succ := hpack.1.1
  have hμ_lt := hpack.1.2.1
  have hv_pos := hpack.1.2.2.1
  have hΦ := hpack.1.2.2.2.1
  have hlowered_ne := hpack.1.2.2.2.2.1
  have hsucc := hpack.1.2.2.2.2.2
  have hcas_lowered := hpack.2
  obtain ⟨v_succ, hsucc_pack⟩ := hsucc
  have hμ_succ_lt := hsucc_pack.1
  have hv_succ_pos := hsucc_pack.2.1
  have hΦ_succ := hsucc_pack.2.2.1
  obtain ⟨r, hr_pos, hrel⟩ := hsucc_pack.2.2.2
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨μ, v,
    ⟨hM_succ, hμ_lt, hv_pos, hΦ, hlowered_ne,
      ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
        ⟨r, hr_pos, hrel⟩⟩⟩,
    hcas_lowered⟩

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir**: choose the sector-`M+1` Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir predecessor package.

This is the raising-direction companion to
`tasaki23_successor_sector_existence_with_lowered_predictedCasimir`. -/
theorem tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M + 1) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_predecessor_common_energy_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir from lowered dominance**: choose the source-sector
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the lowered off-`A` dominance hypothesis into strict
lowered site-sum positivity, then apply the predicted-Casimir successor
package.

The dominance estimate remains an explicit hypothesis; this theorem only
connects that estimate to the sector-existence adjacent-chain wrapper. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir from raised dominance**: choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the raised off-`A` dominance hypothesis into strict
raised site-sum positivity, then apply the predicted-Casimir predecessor
package.

This is the raising-direction companion to the lowered dominance wrapper
above. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted-GS membership from lowered dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, use
predicted-GS membership to supply the predicted-Casimir input, and
convert the lowered off-`A` dominance hypothesis into the strict
site-sum positivity input.

The membership and dominance estimates remain explicit callbacks for the
chosen source-sector vector. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedGS_of_onA_neg_lt_offA
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
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N (M + 1),
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedLoweringSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted-GS membership from raised dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, use predicted-GS membership to supply the predicted-Casimir
input, and convert the raised off-`A` dominance hypothesis into the
strict site-sum positivity input.

This is the raising-direction companion to the lowered predicted-GS
sector-existence wrapper. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedGS_of_onA_neg_lt_offA
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
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain**:
in the canonical orientation `|¬A| ≤ |A|`, choose the left endpoint
sector by the per-sector Theorem 2.2 wrapper and propagate its energy
through the whole admissible interval by the predicted-GS lowered
dominance common-energy step.

The theorem deliberately keeps the two remaining mathematical inputs as
callbacks for each currently chosen source vector: membership in
`bipartiteToyGroundStateSubspacePredicted A N` and the lowered off-`A`
dominance estimate. It isolates the discrete interval induction needed
for the final Theorem 2.3 proof. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_pred hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain from
lowered site-sum positivity**: in the canonical orientation `|¬A| ≤ |A|`,
choose the left endpoint sector by the per-sector Theorem 2.2 wrapper and
propagate its energy through the whole admissible interval using the
direct lowered site-sum positivity successor step.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA`,
this version keeps the actual Marshall-positivity input for
`S^-_{\mathrm{tot}}` as a strict site-sum positivity callback, without
packaging it first as an off-`A`/on-`A` dominance inequality. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_pred hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_site_sum_pos hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain from
lowered vector Marshall positivity**: in the canonical orientation
`|¬A| ≤ |A|`, choose the left endpoint sector by the per-sector
Theorem 2.2 wrapper and propagate its energy through the admissible
interval using the actual Marshall positivity of the lowered ladder
image.

This is the vector-positivity version of
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos`.
The source-form bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos` converts
the Marshall-signed positive real representative input into the site-sum
callback consumed by the existing successor step. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  exact
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
          (hsource_lowered_marshall_pos hM hMlt hμ_lt hv_pos hΦ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain threading predicted-GS
membership from lowered site-sum positivity**: in the canonical
orientation `|¬A| ≤ |A|`, left-endpoint predicted-GS membership
propagates to every representative produced by the lowered site-sum
interval chain.

The successor step uses `Ŝ^-_tot`-invariance of
`bipartiteToyGroundStateSubspacePredicted` and scalar cancellation, so
the all-source predicted-GS membership callback is no longer needed. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hpred_left :
      magSectorEmbedding
          (fun τ : magConfigS V N left =>
            (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    simpa [left] using hleft_predictedGS hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hpred_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hpred⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedGS_of_site_sum_pos
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hpred
            (hsource_site_sum_pos hM_mem (by simpa [right] using hMlt)
              hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from unpacked real
predecessor-difference data through lowered site sums**: this is the
direct site-sum version of the fully threaded predecessor-difference
route.

At each successor step, predicted-GS membership supplies the re-embedded
source-weight cross-ladder identity and the lowered sublattice Casimir
data. The predecessor-difference callback is then converted by
`tasaki23_lowered_site_sum_pos_callback_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`
to the strict lowered site-sum input consumed by the site-sum successor
chain. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
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
                            τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hpred_left :
      magSectorEmbedding
          (fun τ : magConfigS V N left =>
            (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    simpa [left] using hleft_predictedGS hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hpred_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hΨ_pred⟩ := ih hM_le_right
        let Ψ : (V → Fin (N + 1)) → ℂ :=
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        have hΨ_eq :
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := rfl
        have hA_lowered :
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M :=
          tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
            (V := V) A N (Φ := fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
            (by simpa [Ψ] using hΨ_pred)
        have hB_lowered :
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M :=
          tasaki23_sublatticeSpinSOpMinus_complement_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
            (V := V) A N (Φ := fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
            (by simpa [Ψ] using hΨ_pred)
        have hA_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hB_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hpred :
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
                      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩) := by
          intro τ x hx
          exact
            tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq
              (V := V) A N hΨ_eq τ x hx
              (tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS
                (V := V) A N hΨ_pred hA_mag hB_mag τ x hx)
        have hsite :
            ∀ τ : magConfigS V N (M + 1),
              0 < (marshallSignS A τ.1).re *
                (∑ x : V,
                  (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))))
                        τ.1).re) :=
          tasaki23_lowered_site_sum_pos_callback_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
            (V := V) (N := N) A v
            (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
              hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag hB_A hB_B hB_mag
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedGS_of_site_sum_pos
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hΨ_pred hsite
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain threading predicted-GS
membership from lowered vector Marshall positivity**: this is the
vector-positivity form of
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos`.
The source-form bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos` converts
the lowered ladder-vector positivity hypothesis for the Marshall-signed
positive real representative into the site-sum callback. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
          (hsource_lowered_marshall_pos hM hMlt hμ_lt hv_pos hΦ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from predicted-GS
sublattice-component comparison**: in the threaded predicted-GS
interval induction, the local sublattice comparison callback may use
the already-propagated membership in
`bipartiteToyGroundStateSubspacePredicted A N`.

This is the critical-path bridge toward proving the remaining
operator-level inequality from the predicted-GS / sublattice-Casimir
structure, instead of assuming it for arbitrary positive sector
eigenvectors. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_sublattice_component_lt_of_predictedGS
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_sublattice_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
          ∀ τ : magConfigS V N (M + 1),
            -((marshallSignS A τ.1).re *
                (((sublatticeSpinSOpMinus N A).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))))
                    τ.1).re) <
              (marshallSignS A τ.1).re *
                (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))))
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hpred_left :
      magSectorEmbedding
          (fun τ : magConfigS V N left =>
            (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    simpa [left] using hleft_predictedGS hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hpred_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hpred⟩ := ih hM_le_right
        have hsite_sum_pos :
            ∀ τ : magConfigS V N (M + 1),
              0 < (marshallSignS A τ.1).re *
                (∑ x : V,
                  (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))))
                      τ.1).re) := by
          intro τ
          exact
            tasaki23_signed_lowering_site_sum_pos_of_sublattice_component_lt A
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
              τ
              ((hsource_sublattice_component_lt hM_mem (by simpa [right] using hMlt)
                hμ_lt hv_pos hΦ hpred) τ)
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedGS_of_site_sum_pos
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hpred hsite_sum_pos
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_pred⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from joint component
structure**: in the threaded predicted-GS interval induction, the local
sublattice comparison callback receives the propagated predicted-GS
membership and the two lowered-component joint sublattice-Casimir
memberships.

This is the direct consumer-facing form of the PR #3408 joint-eigenspace
bridges: the remaining strict comparison can now assume exactly the
structural facts already proved for `Ŝ_A^- Φ` and `Ŝ_¬A^- Φ`. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_joint_sublattice_component_lt_of_predictedGS
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_joint_sublattice_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_sublattice_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ hpred τ => by
        let Ψ : (V → Fin (N + 1)) → ℂ :=
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        have hΨ_def :
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := rfl
        have hpredΨ :
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
          simpa [Ψ] using hpred
        have hA_joint :
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        have hB_joint :
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        simpa [Ψ] using
          (hsource_joint_sublattice_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_def hpredΨ hA_joint hB_joint τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from lowered joint
magnetization structure**: in the threaded predicted-GS interval
induction, the local sublattice comparison callback receives the two
lowered components as members of the combined joint-Casimir and
successor-sector subspace.

This is the direct consumer-facing form of
`tasaki23LoweredJointMagSubspace`: the remaining strict comparison can
assume each lowered component carries both the joint maximum
sublattice-Casimir structure and the `M + 1` magnetization support. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_joint_magSubspace_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_sublattice_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ hpred τ => by
        let Ψ : (V → Fin (N + 1)) → ℂ :=
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        have hΨ_def :
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := rfl
        have hpredΨ :
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
          simpa [Ψ] using hpred
        have hA_lowered :
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        have hB_lowered :
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_complement_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        simpa [Ψ] using
          (hsource_lowered_joint_magSubspace_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_def hpredΨ hA_lowered hB_lowered τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from lowered joint
magnetization and cross-ladder structure**: in the threaded predicted-GS
interval induction, the local sublattice comparison callback also
receives the raised-lowered cross-ladder identity satisfied by the
source predicted toy ground state.

This sharpens
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS`:
the remaining local comparison can now use the lowered joint
magnetization memberships and the predicted-GS cross-ladder equation in
one callback. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_predictedGS
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_joint_cross_ladder_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hA_lowered hB_lowered τ => by
        have hcross :
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ :=
          tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
            (V := V) A N hΨ_pred
        exact
          hsource_lowered_joint_cross_ladder_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS interval chain with
unpacked lowered joint cross-ladder data**: refine the cross-ladder-aware
callback so it receives the lowered components' explicit sublattice
Casimir equations and successor-sector support, rather than the packed
`tasaki23LoweredJointMagSubspace` memberships.

This is the form needed for the remaining representation-theoretic
comparison: the callback has the cross-ladder equation, the two maximum
Casimir equations for each lowered component, and the common successor
magnetization support. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_predictedGS
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_lowered_joint_cross_ladder_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ => by
        have hA_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hB_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        exact
          hsource_unpacked_lowered_joint_cross_ladder_component_lt hM hMlt hμ_lt
            hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir energy interval chain**:
in the canonical orientation `|¬A| ≤ |A|`, choose the left endpoint sector
by the per-sector Theorem 2.2 wrapper and propagate its energy through the
whole admissible interval using the lowered dominance successor step.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA`,
this version asks directly for the source vector's predicted total-Casimir
identity instead of membership in the predicted toy ground-state subspace. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_casimir :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_casimir hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-Casimir interval chain**:
choose the left endpoint sector by the per-sector Theorem 2.2 wrapper and
propagate both the common energy and the predicted total-Casimir identity
through the whole admissible interval.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA`,
this version only asks for the predicted-Casimir identity at the left endpoint.
The induction invariant carries the successor Casimir returned by the adjacent
common-energy step. -/
theorem
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hcas_left :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) := by
    simpa [left] using hleft_casimir hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hcas_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hcas⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hcas
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-Casimir interval chain
from lowered site-sum positivity**: choose the left endpoint sector by the
per-sector Theorem 2.2 wrapper and propagate both the common energy and the
predicted total-Casimir identity through the whole admissible interval.

Compared with
`tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA`,
this version uses the direct lowered site-sum positivity callback instead of
the off-`A`/on-`A` dominance formulation. -/
theorem
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hcas_left :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) := by
    simpa [left] using hleft_casimir hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hcas_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hcas⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_site_sum_pos
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hcas
            (hsource_site_sum_pos hM_mem (by simpa [right] using hMlt)
              hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-Casimir interval chain
from lowered vector Marshall positivity**: this is the vector-positivity
version of
`tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_site_sum_pos`.
The source-form bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos` converts
the lowered ladder-vector positivity hypothesis for the Marshall-signed
positive real representative into the site-sum callback. -/
theorem
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  exact
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hsector_nonempty hleft_casimir
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
          (hsource_lowered_marshall_pos hM hMlt hμ_lt hv_pos hΦ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 global-minimality bridge from sectors**:
to prove the full-Hilbert-space global minimality clause, it is enough to
prove the same lower bound in every magnetization sector.

Given a nonzero full-space eigenvector, choose a configuration where it is
nonzero, restrict to that configuration's `magSumS` sector, and use the
sector-restriction eigenvector bridge. This reduces the remaining global
minimality input for Theorem 2.3 to a sectorwise statement. -/
theorem tasaki23_global_minimality_of_sector_minimality
    {J : V → V → ℂ} (N : ℕ) {μ : ℝ}
    (hsector_min :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
          Φ ≠ 0 →
          (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
            (μ' : ℂ) • Φ →
          μ ≤ μ') :
    ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ' := by
  intro μ' Ψ' hΨ'_ne hΨ'_eigen
  classical
  have hnonzero_point : ∃ σ : V → Fin (N + 1), Ψ' σ ≠ 0 := by
    by_contra h
    apply hΨ'_ne
    funext σ
    by_contra hσ
    exact h ⟨σ, hσ⟩
  obtain ⟨σ, hσ_ne⟩ := hnonzero_point
  let M : ℕ := magSumS σ
  letI : Nonempty (magConfigS V N M) := ⟨⟨σ, rfl⟩⟩
  have hrestr_ne :
      magSectorRestriction (M := M) Ψ' ≠ 0 := by
    intro hzero
    have hval := congrFun hzero ⟨σ, rfl⟩
    exact hσ_ne hval
  have hrestr_eigen :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) Ψ') =
        (μ' : ℂ) • magSectorRestriction (M := M) Ψ' :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      J hΨ'_eigen
  exact hsector_min M hrestr_ne hrestr_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-minimality bridge from real sectors**:
for real coupling, it is enough to prove the sector lower bound for
nonzero real-form sector eigenvectors.

An arbitrary nonzero complex sector eigenvector has either nonzero real
part or nonzero imaginary part.  Since the complex sector matrix has real
entries under `hJ_real`, that nonzero component is an eigenvector of the
real-form sector matrix at the same real eigenvalue. -/
theorem tasaki23_sector_minimality_of_real_sector_minimality
    {J : V → V → ℂ} (N : ℕ) {μ : ℝ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hreal_sector_min :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
          φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
          μ ≤ μ') :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
        Φ ≠ 0 →
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
          (μ' : ℂ) • Φ →
        μ ≤ μ' := by
  intro M _ μ' Φ hΦ_ne hΦ_eigen
  classical
  by_cases hRe_ne : (fun σ : magConfigS V N M => (Φ σ).re) ≠ 0
  · exact hreal_sector_min M hRe_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦ_eigen)
  · have hRe_zero : (fun σ : magConfigS V N M => (Φ σ).re) = 0 := by
      by_contra h
      exact hRe_ne h
    have hIm_ne : (fun σ : magConfigS V N M => (Φ σ).im) ≠ 0 := by
      intro hIm_zero
      apply hΦ_ne
      funext σ
      apply Complex.ext
      · have h := congrFun hRe_zero σ
        simpa using h
      · have h := congrFun hIm_zero σ
        simpa using h
    exact hreal_sector_min M hIm_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
        N hJ_real hΦ_eigen)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real-sector lower bound on admissible
sectors**: once the common-energy chain has produced a Marshall-positive
sector representative at energy `μ` in an admissible sector, the
Perron-Frobenius shifted-matrix comparison makes `μ` a lower bound for
every real-form eigenvalue in that same sector.

This proves the real-sector spectral-minimality callback on the
`tasaki23GroundStateSectors` interval; sectors outside the interval remain
the separate global spectral input for the final Theorem 2.3 wrapper. -/
theorem tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ}
    (hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) :
    ∀ M : ℕ, M ∈ tasaki23GroundStateSectors (V := V) A N →
      [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
          φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
          μ ≤ μ' := by
  intro M hM _ μ' φ hφ_ne hφ_eigen
  obtain ⟨v, _hμ_lt, hv_pos, hfull⟩ := hcommon M hM
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μ : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hfull
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hsector_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μ • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hsector_complex
    simpa [Φ] using hre
  exact
    heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hsector_real
      (fun τ => by
        have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
          marshallSignS_re_sq A τ.1
        nlinarith [hv_pos τ])
      hφ_ne hφ_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector real lower bound from
outside-sector ground energies**: for sectors outside the admissible
Theorem 2.3 interval, it is enough to prove the lower bound against the
Marshall-positive sector ground-state representative supplied by the
per-sector Theorem 2.2 wrapper.

The Perron-Frobenius comparison for the shifted dressed real sector matrix
then places that sector ground energy below every real-form sector
eigenvalue, giving the full outside-real-sector callback needed by the
final global-minimality step. -/
theorem tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (houtside_ground_energy_lower :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        M ∉ tasaki23GroundStateSectors (V := V) A N →
        ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
          μM < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μM : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          μ ≤ μM) :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      M ∉ tasaki23GroundStateSectors (V := V) A N →
      ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
        φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
        μ ≤ μ' := by
  intro M _ hM_out μ' φ hφ_ne hφ_eigen
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hΦM, _hsupportM, _huniqM⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μM : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦM
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hsector_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * vM τ) =
        μM • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * vM τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hsector_complex
    simpa [Φ] using hre
  have hμ_le_μM : μ ≤ μM :=
    houtside_ground_energy_lower M hM_out hμM_lt hvM_pos hΦM
  have hμM_le_μ' : μM ≤ μ' :=
    heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hsector_real
      (fun τ => by
        have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
          marshallSignS_re_sq A τ.1
        have hv := hvM_pos τ
        nlinarith [hv])
      hφ_ne hφ_eigen
  exact hμ_le_μM.trans hμM_le_μ'

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector minimality from common interval energy
and outside-sector ground energies**: combine the admissible-sector
minimality supplied by the common-energy chain with the outside-sector
ground-energy bridge, then pass from real-form sector eigenvectors to
complex sector eigenvectors.

This is the sectorwise spectral-minimality package needed to turn the
outside-sector ground-energy lower-bound callback into the final global
minimality callback for Theorem 2.3. -/
theorem
    tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (houtside_ground_energy_lower :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        M ∉ tasaki23GroundStateSectors (V := V) A N →
        ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
          μM < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μM : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          μ ≤ μM) :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
        Φ ≠ 0 →
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
          (μ' : ℂ) • Φ →
        μ ≤ μ' := by
  exact
    tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
      (fun M => by
        by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
        · exact
            tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
              A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
              hcommon M hM
        · exact
            tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
              A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
              hc_strict h_intermediate houtside_ground_energy_lower M hM)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from a common interval energy**:
if one real energy `μ` is already realised by Marshall-positive sector
eigenvectors in every admissible sector, then the per-sector Theorem 2.2
uniqueness wrapper upgrades those representatives to the final
existence-and-uniqueness format.

This helper isolates the final packaging step from the particular mechanism
used to construct the common sector energy. -/
theorem tasaki_2_5_theorem_2_3_of_common_energy_chain
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    {μ : ℝ}
    (hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hglobal_min :
      ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  refine ⟨μ, ?_, hglobal_min⟩
  intro M hM _hM_nonempty
  obtain ⟨v_chain, hμ_chain_lt, hv_chain_pos, hΦ_chain⟩ := hcommon M hM
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hΦM, _hsupportM, huniqM⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hsupport_chain :
      ∀ σ, magSumS σ ≠ M →
        magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v_chain τ : ℝ) : ℂ)) σ = 0 := by
    intro σ hσ
    exact magSectorEmbedding_apply_of_not_mem _ hσ
  have hpos_chain_full :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v_chain τ : ℝ) : ℂ)) τ.1).re := by
    intro τ
    rw [magSectorEmbedding_apply_subtype, Complex.ofReal_re]
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv := hv_chain_pos τ
    nlinarith
  obtain ⟨hμ_eq_μM, _hr⟩ := huniqM hΦ_chain hsupport_chain hpos_chain_full
  refine ⟨vM, ?_, hvM_pos, ?_, ?_⟩
  · exact hμ_chain_lt
  · rwa [hμ_eq_μM]
  · intro μ' Ψ' hΨ'_eigen hΨ'_support hΨ'_positive
    obtain ⟨hμ'_eq_μM, hr⟩ := huniqM hΨ'_eigen hΨ'_support hΨ'_positive
    exact ⟨by rw [hμ'_eq_μM, ← hμ_eq_μM], hr⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from common interval energy and
outside-sector ground energies**: once the adjacent-sector chain has
produced a common Marshall-positive energy on the admissible interval, it
is enough to prove lower bounds only for the Marshall-positive
ground-state representatives in outside sectors.

The sector-minimality bridge packages the admissible and outside sectors,
and the global-minimality bridge then supplies the final full-space
minimality callback required by the textbook statement. -/
theorem
    tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (houtside_ground_energy_lower :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        M ∉ tasaki23GroundStateSectors (V := V) A N →
        ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
          μM < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μM : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          μ ≤ μM) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro _hJ_real _hJ_real' _hJ_sym _hJ_nn _hJ_bipartite _hJ_pos
    _hc_strict _h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N
        (tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate hcommon houtside_ground_energy_lower))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 conditional final wrapper**:
under the canonical orientation `|¬A| ≤ |A|`, the predicted-GS
left-endpoint interval chain supplies one common energy `μ` on every
admissible sector.  Combining that chain with the per-sector Theorem 2.2
wrapper upgrades the sector witnesses to the final Theorem 2.3
existence-and-uniqueness format.

The remaining mathematical inputs are kept explicit as callbacks:
membership in the predicted toy-Hamiltonian ground-state subspace,
lowered off-`A` dominance for the adjacent-sector step, and global
minimality of the common value.  Thus this theorem packages the final
Theorem 2.3 `Prop` once those three inputs are available.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42. -/
theorem tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hglobal_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          Ψ' ≠ 0 →
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred hsource_dominance
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon (hglobal_min hcommon)
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate _hA_nonempty _hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 conditional final wrapper from sector
minimality**: this is the same canonical-orientation final wrapper as
`tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_of_onA_neg_lt_offA`,
but replaces the full-space global-minimality callback by the sharper
sectorwise minimality callback.

The bridge `tasaki23_global_minimality_of_sector_minimality` then supplies
the full global-minimality clause by restricting any nonzero full-space
eigenvector to a nonzero magnetization-sector component. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_of_onA_neg_lt_offA_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_of_onA_neg_lt_offA
      A N c hBA hsector_nonempty hsource_pred hsource_dominance ?_
  intro μ hcommon
  exact tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 conditional final wrapper from real-sector
minimality**: this refines the sector-minimality wrapper by replacing the
complex sectorwise minimality callback with a real-form sectorwise
minimality callback.

The bridge `tasaki23_sector_minimality_of_real_sector_minimality` extracts
a nonzero real or imaginary component of any complex sector eigenvector,
then `tasaki23_global_minimality_of_sector_minimality` upgrades the result
to the full-Hilbert-space global-minimality clause. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_of_onA_neg_lt_offA_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedGS_of_onA_neg_lt_offA_of_sector_minimality
      A N c hBA hsector_nonempty hsource_pred hsource_dominance
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 conditional final wrapper from predicted
Casimir**: this is the common-energy final wrapper with the interval chain
constructed from predicted total-Casimir identities and lowered off-`A`
dominance, rather than from predicted-GS membership.

The remaining mathematical inputs are now the source vector's predicted
total-Casimir identity, the lowered off-`A` dominance estimate, and global
minimality of the common value. -/
theorem tasaki_2_5_theorem_2_3_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_casimir :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hglobal_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          Ψ' ≠ 0 →
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_energy_interval_chain_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hsector_nonempty hsource_casimir hsource_dominance
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon (hglobal_min hcommon)
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir final wrapper from sector
minimality**: this replaces the full-space global-minimality callback in
`tasaki_2_5_theorem_2_3_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA`
by the sectorwise minimality callback. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_casimir :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
      A N c hsector_nonempty hsource_casimir hsource_dominance ?_
  intro μ hcommon
  exact tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir final wrapper from real-sector
minimality**: this combines the predicted-Casimir interval chain with the
real-form sector minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_casimir :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA_of_sector_minimality
      A N c hsector_nonempty hsource_casimir hsource_dominance
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from left-endpoint predicted
Casimir**: this refines the predicted-Casimir final wrapper by using the
threaded interval chain, so the predicted total-Casimir input is needed only
for the left endpoint sector selected by Theorem 2.2.

The threaded interval chain carries both the common energy and the predicted
Casimir through the whole admissible interval.  This wrapper strips the
propagated Casimir component and passes the common-energy chain to the
existing final Theorem 2.3 packaging theorem. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hglobal_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          Ψ' ≠ 0 →
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_cas⟩ :=
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hsector_nonempty hleft_casimir hsource_dominance
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hcas⟩ := hcommon_cas M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon (hglobal_min hcommon)
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-Casimir final wrapper
from sector minimality**: this replaces the full-space global-minimality
callback in the left-endpoint predicted-Casimir final wrapper by the
sectorwise minimality callback. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedCasimir_of_onA_neg_lt_offA_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedCasimir_of_onA_neg_lt_offA
      A N c hsector_nonempty hleft_casimir hsource_dominance ?_
  intro μ hcommon
  exact tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-Casimir final wrapper
from real-sector minimality**: this combines the threaded predicted-Casimir
interval chain with the real-form sector minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedCasimir_of_onA_neg_lt_offA_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedCasimir_of_onA_neg_lt_offA_of_sector_minimality
      A N c hsector_nonempty hleft_casimir hsource_dominance
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from left-endpoint predicted
toy ground-state membership**: this refines the threaded predicted-Casimir
final wrapper by replacing the direct left-endpoint total-Casimir callback
with membership in `bipartiteToyGroundStateSubspacePredicted A N`.

In the canonical orientation `|¬A| ≤ |A|`, predicted-GS membership supplies
the required total-Casimir identity at the left endpoint.  The threaded
interval chain then propagates that Casimir identity through every
admissible sector. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hglobal_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          Ψ' ≠ 0 →
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedCasimir_of_onA_neg_lt_offA
      A N c hsector_nonempty ?_ hsource_dominance hglobal_min
  intro μ v hμ_lt hv_pos hΦ
  exact
    tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      A N hBA (hleft_predictedGS hμ_lt hv_pos hΦ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS final wrapper
from sector minimality**: this replaces the full-space global-minimality
callback in the left-endpoint predicted-GS final wrapper by the sectorwise
minimality callback. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_onA_neg_lt_offA_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_onA_neg_lt_offA
      A N c hBA hsector_nonempty hleft_predictedGS hsource_dominance ?_
  intro μ hcommon
  exact tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS final wrapper
from real-sector minimality**: this combines the threaded predicted-Casimir
interval chain, the predicted-GS total-Casimir bridge, and the real-form
sector minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_onA_neg_lt_offA_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_onA_neg_lt_offA_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS hsource_dominance
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from left-endpoint predicted
toy ground-state membership and lowered vector Marshall positivity**: this
combines the left-endpoint predicted-GS Casimir bridge with the threaded
lowered-Marshall interval chain.

Compared with
`tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos`, the
predicted-GS membership hypothesis is needed only for the left endpoint
sector; the interval induction propagates the predicted total-Casimir
identity through the remaining admissible sectors. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hglobal_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          Ψ' ≠ 0 →
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_cas⟩ :=
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_marshall_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hsector_nonempty
      (fun hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hleft_predictedGS hμ_lt hv_pos hΦ))
      hsource_lowered_marshall_pos
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hcas⟩ := hcommon_cas M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon (hglobal_min hcommon)
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS lowered-Marshall
final wrapper from sector minimality**: this replaces the full-space
global-minimality callback by sectorwise minimality. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos
      A N c hBA hsector_nonempty hleft_predictedGS hsource_lowered_marshall_pos ?_
  intro μ hcommon
  exact tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS lowered-Marshall
final wrapper from real-sector minimality**: this combines the threaded
lowered-Marshall interval chain with the real-form sector minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS hsource_lowered_marshall_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS lowered-Marshall
final wrapper from outside-interval real-sector minimality**: the
admissible-sector part of the real-sector spectral lower bound is proved
from the common Marshall-positive energy chain, so the remaining
real-sector callback only has to handle sectors outside
`tasaki23GroundStateSectors`.

This is the lowered-Marshall final wrapper with the interval spectral
minimality discharged by
`tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos_of_outside_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (houtside_real_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          M ∉ tasaki23GroundStateSectors (V := V) A N →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos_of_real_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS hsource_lowered_marshall_pos
      (fun hcommon M => by
        by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
        · exact
            tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
              A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
              hcommon M hM
        · exact houtside_real_sector_min hcommon M hM)
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from sublattice lowering
component dominance**: this is the strongest current final wrapper with
the local lowered-Marshall callback replaced by the operator-level
comparison between the Marshall-signed real parts of `Ŝ_A^- Φ` and
`Ŝ_¬A^- Φ`.

The proof uses
`tasaki23_lowered_marshall_pos_of_sublattice_component_lt` to feed the
existing left-endpoint predicted-GS lowered-Marshall final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_sublattice_component_lt_of_outside_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_sublattice_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            -((marshallSignS A τ.1).re *
                (((sublatticeSpinSOpMinus N A).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))))
                    τ.1).re) <
              (marshallSignS A τ.1).re *
                (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))))
                    τ.1).re)
    (houtside_real_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          M ∉ tasaki23GroundStateSectors (V := V) A N →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_marshall_pos_of_outside_real_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_marshall_pos_of_sublattice_component_lt A
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          (hsource_sublattice_component_lt hM hMlt hμ_lt hv_pos hΦ))
      houtside_real_sector_min
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from joint component
structure**: the final theorem may consume the local strict comparison
callback in the form where the source predicted-GS membership and both
lowered-component joint sublattice-Casimir memberships are explicit
hypotheses.

This is the final-wrapper companion to
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_joint_sublattice_component_lt_of_predictedGS`.
It keeps the remaining local task focused on proving the strict
Marshall-signed comparison under the exact predicted-GS and joint-Casimir
facts already available. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_joint_sublattice_component_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_joint_sublattice_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_joint_sublattice_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_joint_sublattice_component_lt
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpred⟩ := hcommon_pred M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from joint coefficient
dominance**: the remaining local callback may be stated directly as a
strict dominance of the on-`A` predecessor coefficient sum by the
off-`A` predecessor coefficient sum.

The callback receives the same predicted-GS and lowered-component joint
sublattice-Casimir facts as the joint-component wrapper.  The proof then
uses the existing sublattice component coefficient formulas to recover
the strict operator-component comparison required by that wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_joint_sublattice_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_joint_sublattice_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_joint_sublattice_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hA_joint hB_joint τ
        have hcoeff :=
          hsource_joint_sublattice_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hA_joint hB_joint τ
        subst Ψ
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        rw [honA, hoffA]
        simpa using hcoeff)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowered joint
magnetization structure**: the final theorem may consume the local
strict comparison callback in the form where both lowered components
are provided as members of `tasaki23LoweredJointMagSubspace`.

This is the final-wrapper companion to
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS`.
It keeps the remaining local task focused on proving the strict
Marshall-signed comparison after the predicted-GS, joint-Casimir, and
successor-sector support facts have already been threaded. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_magSubspace_component_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_joint_magSubspace_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_lowered_joint_magSubspace_component_lt
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpred⟩ := hcommon_pred M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N (hsector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowered joint
magnetization coefficient dominance**: the final theorem boundary can
consume the remaining local comparison as a strict dominance of the
on-`A` predecessor coefficient sum by the off-`A` predecessor
coefficient sum, while exposing the stronger lowered joint-magnetization
subspace memberships to the callback.

The proof rewrites coefficient dominance into the strict
Marshall-signed sublattice-component comparison and then applies the
lowered joint-magnetization component wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_magSubspace_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_joint_magSubspace_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_magSubspace_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hA_lowered hB_lowered τ
        have hcoeff :=
          hsource_lowered_joint_magSubspace_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hA_lowered hB_lowered τ
        subst Ψ
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        rw [honA, hoffA]
        simpa using hcoeff)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowered joint
magnetization and cross-ladder structure**: the final theorem may
consume the local strict comparison callback after exposing the
predicted-GS raised-lowered cross-ladder identity together with the
lowered joint-magnetization memberships.

This keeps the remaining local task focused on deriving the strict
Marshall-signed component comparison from exactly the structural
equation and subspace memberships already proved for predicted toy
ground-state representatives. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_joint_cross_ladder_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_magSubspace_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hA_lowered hB_lowered τ
        have hcross :
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ :=
          tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
            (V := V) A N hΨ_pred
        exact
          hsource_lowered_joint_cross_ladder_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowered joint
cross-ladder coefficient dominance**: the final theorem boundary can
consume the remaining local comparison as predecessor coefficient
dominance after the callback receives the predicted-GS cross-ladder
identity and the lowered joint-magnetization memberships.

The proof rewrites the coefficient dominance into the strict
Marshall-signed component comparison and applies the preceding
cross-ladder-aware final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_joint_cross_ladder_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ
        have hcoeff :=
          hsource_lowered_joint_cross_ladder_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ
        subst Ψ
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        rw [honA, hoffA]
        simpa using hcoeff)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from unpacked lowered joint
cross-ladder data**: the final theorem may consume the local strict
comparison callback after the lowered joint-magnetization memberships
have been unpacked into explicit sublattice-Casimir equations and
successor-sector support.

This is the final-theorem counterpart of
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_predictedGS`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_lowered_joint_cross_ladder_component_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ
        have hA_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hB_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        exact
          hsource_unpacked_lowered_joint_cross_ladder_component_lt hM hMlt hμ_lt
            hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from unpacked lowered joint
cross-ladder coefficient dominance**: the final theorem boundary can
consume the remaining local comparison as predecessor coefficient
dominance after the unpacked cross-ladder callback receives the explicit
Casimir equations and successor-sector support for both lowered
components.

The proof rewrites coefficient dominance into the strict
Marshall-signed component comparison and applies the unpacked component
wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_lowered_joint_cross_ladder_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hcoeff :=
          hsource_unpacked_lowered_joint_cross_ladder_coefficient_lt hM hMlt
            hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ
        subst Ψ
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        rw [honA, hoffA]
        simpa using hcoeff)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from re-embedded cross-ladder
source-sector site sums**: the final theorem boundary may consume the
remaining local comparison after the predicted-GS cross-ladder identity
has already been evaluated at source-sector configurations and rewritten
through the successor-sector restrictions of the two lowered components.

This is the direct consumer of
`tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS`.
The callback receives the pointwise filtered `A`/`¬A` raising sums, plus
the explicit sublattice-Casimir equations for both lowered components. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_reembedded_cross_ladder_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_reembedded_cross_ladder_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                  ((2 : ℂ) •
                    (sublatticeSpinSOp3 N A *
                      sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ) σ.1) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred _hcross hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hsite :
            ∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                  ((2 : ℂ) •
                    (sublatticeSpinSOp3 N A *
                      sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ) σ.1 := by
          intro σ
          exact
            tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
              (V := V) A N hΨ_pred hA_mag hB_mag σ
        exact
          hsource_reembedded_cross_ladder_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hsite hA_A hA_B hB_A hB_B τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from re-embedded
source-weight cross-ladder sums**: this strengthens the remaining local
callback boundary by giving it the scalar source-weight form of the
re-embedded cross-ladder equation.

The callback no longer receives the raw `Ŝ_A^3 Ŝ_¬A^3` operator term on
the right-hand side. Instead, the filtered raising sums are equated to
`(E_toy - 2 W_A(σ) W_¬A(σ)) * Ψ σ`, where the two weights are the
source-configuration `S^3` sums over `A` and `¬A`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_reembedded_source_weight_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_reembedded_source_weight_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_reembedded_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hraw hA_A hA_B
          hB_A hB_B τ
        have hsite :
            ∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
          intro σ
          rw [hraw σ]
          rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
          rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
          simp [smul_eq_mul]
          ring_nf
        exact
          hsource_reembedded_source_weight_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hsite hA_A hA_B hB_A hB_B τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from unpacked re-embedded
source-weight cross-ladder sums**: this keeps the successor-sector support
from the unpacked lowered-joint callback while replacing the raw
cross-ladder operator equation by the scalar source-weight form.

The callback receives the pointwise identity
`(E_toy - 2 W_A(σ) W_¬A(σ)) * Ψ σ`, the four explicit sublattice-Casimir
equations, and the two `magSubspaceS` memberships for the lowered
components. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_source_weight_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred _hraw hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hsite :
            ∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
          intro σ
          rw [
            tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
              (V := V) A N hΨ_pred hA_mag hB_mag σ]
          rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
          rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
          simp [smul_eq_mul]
          ring_nf
        exact
          hsource_unpacked_reembedded_source_weight_coefficient_lt hM hMlt hμ_lt
            hv_pos hΦ Ψ hΨ_eq hΨ_pred hsite hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor-specialized
source-weight sums**: this threads the scalar re-embedded source-weight
identity after specializing it to the lowering predecessor configuration
attached to each successor site.

The callback receives exactly the local source-weight identity at the
predecessor used by `tasaki23LoweringPredecessorSignedCoefficient`,
together with the four explicit sublattice-Casimir equations and the two
successor-sector `magSubspaceS` support facts for the lowered components. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_source_weight_predecessor_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred _hraw hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hpred :
            ∀ τ : magConfigS V N (M + 1), ∀ x : V,
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred := by
          intro τ x hx
          exact
            tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS
              (V := V) A N hΨ_pred hA_mag hB_mag τ x hx
        exact
          hsource_unpacked_reembedded_source_weight_predecessor_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive-source
coefficient sums**: this threads the predecessor-specialized source-weight
identity while stating the remaining local dominance callback in the
sign-normalized positive-source coefficient form.

The wrapper rewrites the positive-source coefficient sums back to the
Marshall-signed predecessor coefficient sums consumed by the previous
predecessor-specialized final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hpos :=
          hsource_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ
        rw [
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hpos)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowerable predecessor
positive-source coefficient sums**: this threads the
predecessor-specialized source-weight identity while allowing the final
local callback to compare only lowerable sites of the successor
configuration.

The wrapper rewrites the unfiltered positive-source coefficient sums of
the previous final wrapper by
`tasaki23_positive_source_coefficient_sum_eq_lowerable_sum`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
                  (fun x : V => 0 < (τ.1 x).val)),
                  tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
                ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
                  (fun x : V => 0 < (τ.1 x).val)),
                  tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hlowerable :=
          hsource_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ
        rw [
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hlowerable)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from explicit lowerable
positive-source coefficient sums**: this threads the predecessor-specialized
source-weight identity while asking the final local callback only for
attached sums of the explicit lowerable predecessor coefficients.

The wrapper converts those attached sums back to the lowerable-filtered
boundary-inclusive sums by
`tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
                (((Finset.univ.filter (fun x : V => A x = false)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
            A v τ
            (hsource_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag τ))
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from real predecessor
source-weight data**: this threads the real part of the predecessor
source-weight equality into the explicit lowerable positive-source
coefficient callback.

The wrapper derives the real predecessor equality from the older complex
predecessor-specialized source-weight identity using
`tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq`,
then reuses the explicit lowerable positive-source callback boundary. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
                (((Finset.univ.filter (fun x : V => A x = false)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          hsource_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred
            (by
              intro τ x hx
              exact
                tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq
                  (V := V) A N hΨ_eq τ x hx (hpred τ x hx))
            hA_A hA_B hA_mag hB_A hB_B hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor
raising-source sums**: this threads the real predecessor source-weight
data into a callback stated directly as strict dominance of the
predecessor raising-source sums.

The wrapper uses
`tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt`
to recover the explicit lowerable positive-source coefficient comparison
expected by the preceding real predecessor callback. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
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
                          τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
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
                          τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt
            (V := V) (N := N) A v τ
            (hsource_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag τ))
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor
raising-source positive differences**: this threads the real predecessor
source-weight data into a callback stated as positivity of the off-`A`
minus on-`A` predecessor raising-source difference.

The wrapper converts the difference-form callback to the strict
raising-source dominance callback by
`tasaki23_raising_predecessor_source_sum_lt_callback_of_offA_sub_onA_pos`
and then reuses the preceding final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
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
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag
        exact
          tasaki23_raising_predecessor_source_sum_lt_callback_of_offA_sub_onA_pos
            (V := V) (N := N) A v
            (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag))
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive
differences through lowered site sums**: this routes the fully threaded
predecessor-difference callback through the lowered site-sum successor
chain, rather than converting it first to the raising-source dominance
final wrapper.

The wrapper uses
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`
to propagate the common energy and predicted-GS membership, then applies
the usual common-energy and sector-minimality final packaging. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
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
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpred⟩ := hcommon_pred M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N
        (hsector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive
differences and outside-interval real-sector minimality**: this refines the
direct lowered-site-sum wrapper by discharging the real-sector spectral
minimality callback on the admissible Theorem 2.3 interval from the common
Marshall-positive energy chain itself.

The remaining real-sector lower-bound hypothesis only has to handle
sectors outside `tasaki23GroundStateSectors`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
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
    (houtside_real_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          M ∉ tasaki23GroundStateSectors (V := V) A N →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (fun M => by
            by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
            · exact
                tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
                  A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
                  hcommon M hM
            · exact houtside_real_sector_min hcommon M hM))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive
differences and outside-sector ground energies**: this replaces the
outside-real-sector minimality callback in the predecessor-difference
lowered-site-sum boundary by lower bounds only for the Theorem 2.2
Marshall-positive ground-state representatives in sectors outside
`tasaki23GroundStateSectors`.

The admissible interval is still supplied by the predecessor-difference
energy chain.  Outside the interval, the Perron--Frobenius sector bridge
turns the ground-representative lower bound into the full real-sector
minimality callback consumed by the preceding final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
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
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
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
    (houtside_ground_energy_lower :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          M ∉ tasaki23GroundStateSectors (V := V) A N →
          ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
            μM < c →
            (∀ τ, 0 < v τ) →
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μM : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            μ ≤ μM) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_real_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      (fun hcommon =>
        tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate
          (houtside_ground_energy_lower hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final predecessor-difference boundary from
outside-sector ground energies**: this names the final API obtained from
the lowered-site-sum route.  The remaining inputs are exactly the
left-endpoint predicted-GS callback, the local predecessor-difference
callback, and outside-sector lower bounds for the Marshall-positive
Theorem 2.2 ground-state representatives.

The proof content is supplied by
`tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_sector_ground_energy_lower_bound`;
this alias keeps the public boundary independent of the technical
site-sum route used internally. -/
abbrev
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_via_lowered_site_sum_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-GS outside-ground
boundary**: this replaces the left-endpoint-only predicted-GS callback
in the public outside-ground predecessor-difference boundary by a uniform
callback over every admissible source sector.  The wrapper feeds the
left endpoint into that uniform callback and leaves the local
predecessor-difference comparison and the outside-sector ground-energy
lower bounds as the remaining inputs.

This is still a boundary for the same Tasaki §2.5 Theorem 2.3 final
statement; it only exposes the predicted-GS input in the canonical
threaded form used by the adjacent-sector chain. -/
abbrev
    tasaki_2_5_theorem_2_3_of_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_predictedGS :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :=
  tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_of_outside_sector_ground_energy_lower_bound
    (V := V) A (J := J) N c hBA hsector_nonempty
    (fun {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ} hμ_lt hv_pos hΦ =>
      hsource_predictedGS
        (M :=
          min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N)
        (by
          simpa using tasaki23GroundStateSectors_left_mem (V := V) A N)
        hμ_lt hv_pos hΦ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS final wrapper from
lowered site-sum positivity**: this replaces the lowered off-`A` dominance
callback by the direct strict site-sum positivity callback needed to prove
Marshall positivity of the lowered vector.

The predicted-GS callback supplies the predicted-Casimir identity at each
source sector, and global minimality remains explicit. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hglobal_min :
      ∀ {μ μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      hsource_site_sum_pos
  exact tasaki_2_5_theorem_2_3_of_common_energy_chain
    A N c hcommon (hglobal_min hcommon)
    hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-site-sum final wrapper from sector
minimality**: this refines
`tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos`
by replacing the full-space global-minimality callback with sectorwise
minimality. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos
      A N c hBA hsector_nonempty hsource_pred hsource_site_sum_pos ?_
  intro μ μ' Ψ' hcommon hΨ'_ne hΨ'_eigen
  exact tasaki23_global_minimality_of_sector_minimality N
    (hsector_min hcommon) hΨ'_ne hΨ'_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-site-sum final wrapper from real-sector
minimality**: this combines the direct lowered site-sum interval chain with
the real-form sector minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
      A N c hBA hsector_nonempty hsource_pred hsource_site_sum_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS site-sum final
wrapper from sector minimality**: this packages the direct lowered
site-sum interval chain into the final theorem while requiring predicted
toy ground-state membership only at the left endpoint.

This is the final-wrapper counterpart of
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos`.
It is the direct site-sum analogue of the lowered-Marshall final wrapper
used later in the chain. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_site_sum_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N
                (min
                  (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
                  (Finset.card
                    (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                    N) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_site_sum_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  obtain ⟨μ, hcommon_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_site_sum_pos
  have hcommon :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hM
    obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpred⟩ := hcommon_pred M hM
    exact ⟨v, hμ_lt, hv_pos, hΦ⟩
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N
        (hsector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowered vector Marshall
positivity**: this replaces the direct site-sum positivity callback by
the natural vector-level Marshall positivity of the lowered ladder image
`S^-_{\mathrm{tot}} Ψ`.

The bridge `tasaki23_lowered_site_sum_pos_of_marshall_pos` expands the
lowered ladder vector into the single-site site-sum callback used by the
successor interval chain. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hglobal_min :
      ∀ {μ μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_marshall_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      hsource_lowered_marshall_pos
  exact tasaki_2_5_theorem_2_3_of_common_energy_chain
    A N c hcommon (hglobal_min hcommon)
    hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-vector-Marshall final wrapper from
sector minimality**: this refines
`tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos`
by replacing the full-space global-minimality callback with sectorwise
minimality. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  refine
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos
      A N c hBA hsector_nonempty hsource_pred hsource_lowered_marshall_pos ?_
  intro μ μ' Ψ' hcommon hΨ'_ne hΨ'_eigen
  exact tasaki23_global_minimality_of_sector_minimality N
    (hsector_min hcommon) hΨ'_ne hΨ'_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-vector-Marshall final wrapper from
real-sector minimality**: this combines the vector-level lowered
Marshall-positivity interval chain with the real-form sector minimality
bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos_of_real_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_pred :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_lowered_marshall_pos :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)
    (hreal_sector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
            φ ≠ 0 →
            (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ =
              μ' • φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_predictedGS_of_lowered_marshall_pos_of_sector_minimality
      A N c hBA hsector_nonempty hsource_pred hsource_lowered_marshall_pos
      (fun hcommon =>
        tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
          (hreal_sector_min hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

end LatticeSystem.Quantum
