import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

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

/-- Pointwise diagonal action of `Ŝ_tot^(3)` on an arbitrary full
spin-`S` configuration vector.

This is the full-vector form of the computational-basis identity
`Ŝ_tot^(3) |σ⟩ = magEigenvalueS σ • |σ⟩`, used here to pass between
`magSumS`-sector support and `magSubspaceS` eigenvector membership. -/
theorem totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul
    (Ψ : (V → Fin (N + 1)) → ℂ) (σ : V → Fin (N + 1)) :
    (totalSpinSOp3 V N).mulVec Ψ σ = magEigenvalueS σ * Ψ σ := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single σ]
  · rw [totalSpinSOp3_apply_diag]
  · intro τ _ hτσ
    rw [totalSpinSOp3_apply_off_diag (Ne.symm hτσ), zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- A zero-extended `magSumS = M` sector vector lies in the corresponding
`Ŝ_tot^(3)` eigenspace, whose eigenvalue is
`|V| * N / 2 - M`.

This is the sector-support bridge needed for the Tasaki §2.5 Theorem 2.3
ladder argument. -/
theorem magSectorEmbedding_mem_magSubspaceS {M : ℕ}
    (Φ : magConfigS V N M → ℂ) :
    magSectorEmbedding Φ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
  rw [mem_magSubspaceS_iff]
  funext σ
  rw [totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul]
  by_cases h : magSumS σ = M
  · have hmag :
        magEigenvalueS σ =
          ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) := by
      unfold magEigenvalueS
      rw [h]
    rw [hmag]
    simp [Pi.smul_apply, smul_eq_mul]
  · have hz : magSectorEmbedding Φ σ = 0 :=
      magSectorEmbedding_apply_of_not_mem Φ h
    simp [Pi.smul_apply, smul_eq_mul, hz]

/-- A vector in the `Ŝ_tot^(3)` eigenspace labelled by `magSumS = M`
vanishes on configurations outside that `magSumS` sector.

This is the converse support bridge used after applying a ladder
operator and obtaining the shifted `magSubspaceS` membership. -/
theorem magSubspaceS_apply_eq_zero_of_magSumS_ne {M : ℕ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)))
    {σ : V → Fin (N + 1)} (hσ : magSumS σ ≠ M) :
    Ψ σ = 0 := by
  rw [mem_magSubspaceS_iff] at hΨ
  have hτ_lhs :
      (totalSpinSOp3 V N).mulVec Ψ σ = magEigenvalueS σ * Ψ σ :=
    totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul Ψ σ
  have hτ_rhs :
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) • Ψ) σ =
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) * Ψ σ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq :
      magEigenvalueS σ * Ψ σ =
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) * Ψ σ := by
    rw [← hτ_lhs, hΨ, hτ_rhs]
  have hsub :
      (magEigenvalueS σ -
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))) * Ψ σ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  have hne :
      magEigenvalueS σ -
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hmag
    apply hσ
    have hcast : (magSumS σ : ℂ) = (M : ℂ) := by
      unfold magEigenvalueS at hmag
      linear_combination -hmag
    exact_mod_cast hcast
  exact (mul_eq_zero.mp hsub).resolve_left hne

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

/-- **Tasaki §2.5 Theorem 2.3 predicted total-spin magnitude**
`S_tot = ||A| − |¬A|| · (N/2)` (the real-valued half-integer
prediction). Equivalent to `‖bipartiteImbalanceWeight A N‖`. -/
noncomputable def tasaki23PredictedTotalSpin (A : V → Bool) (N : ℕ) : ℝ :=
  |((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ)| *
    ((N : ℝ) / 2)

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

end LatticeSystem.Quantum
