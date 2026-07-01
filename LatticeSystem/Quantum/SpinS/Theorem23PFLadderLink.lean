import LatticeSystem.Quantum.SpinS.Theorem23Casimir
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.Theorem23Predicted
import LatticeSystem.Quantum.SpinS.Theorem23PredictedEndpoint

/-!
# Tasaki §2.5 Theorem 2.3 — Perron–Frobenius adjacent-sector ladder link

Sound replacement for the deleted saturated-ladder-iterate route (Issue
#3542; see `.self-local/docs/tasaki-2-5-pf-route-design.md`).  The
per-sector Marshall-positive Perron–Frobenius ground state
(`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`) is
chained across adjacent
magnetization sectors by the SU(2) total-lowering operator, using only
`[Ĥ, Ŝ⁻_tot] = 0` and the total-Casimir non-vanishing criterion.

This is the mechanism behind the constancy of the sector ground energies
in Tasaki §2.5 Theorem 2.3 (and the first half of Theorem 2.2): applying
`Ŝ⁻_tot` to a Heisenberg eigenvector preserves its energy (commutation)
and moves it to the next magnetization sector, where it is non-zero as
long as the total-Casimir eigenvalue is away from the lowering-kernel
value.  It does **not** require Marshall positivity of the lowered vector
— exactly the (false) hypothesis on which the deleted ferromagnetic-ladder
route foundered.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 Perron–Frobenius adjacent-sector ladder
link (lowering direction)**: if a magnetization-`M` sector vector
`Ψ = magSectorEmbedding Φ` is a Heisenberg eigenvector at energy `μ` and
a total-Casimir eigenvector at a value `γ` away from the sector's
lowering-kernel value, then its total-lowering image `Ŝ⁻_tot · Ψ` is

* a Heisenberg eigenvector at the **same** energy `μ`
  (by `[Ĥ, Ŝ⁻_tot] = 0`);
* non-zero (by the total-Casimir non-vanishing criterion); and
* supported in the next magnetization sector
  (`Ŝ⁻_tot` lowers the `Ŝ_tot^(3)` eigenvalue by one).

This packages the sound energy-preserving step that chains the per-sector
Perron–Frobenius ground states of
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
across the admissible range.  No Marshall positivity of the lowered vector
is used. -/
theorem tasaki23_pf_ladder_link_succ
    {N M : ℕ} {J : V → V → ℂ} {μ : ℝ} {γ : ℂ}
    {Φ : magConfigS V N M → ℂ}
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hCas :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        γ • magSectorEmbedding Φ)
    (hγ :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)))
    (hΦ : magSectorEmbedding Φ ≠ 0) :
    (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∧
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact mulVec_preserves_eigenvalue_of_commuteS
      (heisenbergHamiltonianS_commute_totalSpinSOpMinus J) hH
  · exact tasaki23_totalSpinSOpMinus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
      hCas hγ hΦ
  · exact totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
      (magSectorEmbedding_mem_magSubspaceS (V := V) (N := N) (M := M) Φ)

/-- **Tasaki §2.5 Theorem 2.3 Perron–Frobenius adjacent-sector ladder
link from predicted-GS membership**: the Casimir hypotheses of
`tasaki23_pf_ladder_link_succ` are discharged for any sector vector that
lies in the predicted toy ground-state subspace.

In the canonical orientation `|¬A| ≤ |A|`, membership in
`bipartiteToyGroundStateSubspacePredicted A N` pins the total-Casimir
eigenvalue to `tasaki23PredictedCasimirValue A N`
(`tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted`),
and that predicted value differs from the lowering-kernel value of any
admissible sector below the right endpoint
(`tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right`).

Hence, for a predicted-GS Heisenberg eigenvector at energy `μ` in an
admissible sector `M` below the right endpoint, `Ŝ⁻_tot · Ψ` is a non-zero
Heisenberg eigenvector at the **same** `μ` in sector `M + 1`.  This is the
energy-preserving chaining step specialised to the physical (predicted)
ground-state line, with no remaining abstract Casimir input. -/
theorem tasaki23_pf_ladder_link_succ_of_mem_predictedGS
    (A : V → Bool) {N M : ℕ} {J : V → V → ℂ} {μ : ℝ}
    {Φ : magConfigS V N M → ℂ}
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      M <
        max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hΨ_pred :
      magSectorEmbedding Φ ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hΦ : magSectorEmbedding Φ ≠ 0) :
    (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∧
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
  tasaki23_pf_ladder_link_succ hH
    (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      A N hBA hΨ_pred)
    (tasaki23_predictedCasimirValue_ne_lowering_kernel_value_of_mem_of_lt_right
      A N hM hMlt)
    hΦ

/-- **Tasaki §2.5 Theorem 2.3 Perron–Frobenius adjacent-sector ladder
link (raising direction)**: the raising companion of
`tasaki23_pf_ladder_link_succ`.  If a magnetization-`K` sector vector
`magSectorEmbedding Φ` is a Heisenberg eigenvector at `μ` and a
total-Casimir eigenvector at `γ` away from the sector's raising-kernel
value, then `Ŝ⁺_tot · magSectorEmbedding Φ` is a Heisenberg eigenvector at
the **same** `μ`, non-zero, and supported in the previous magnetization
sector. -/
theorem tasaki23_pf_ladder_link_pred
    {N K : ℕ} {J : V → V → ℂ} {μ : ℝ} {γ : ℂ}
    {Φ : magConfigS V N K → ℂ}
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hCas :
      (totalSpinSSquared V N).mulVec (magSectorEmbedding Φ) =
        γ • magSectorEmbedding Φ)
    (hγ :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ)) + 1)))
    (hΦ : magSectorEmbedding Φ ≠ 0) :
    (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∧
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ)) + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact mulVec_preserves_eigenvalue_of_commuteS
      (heisenbergHamiltonianS_commute_totalSpinSOpPlus J) hH
  · exact tasaki23_totalSpinSOpPlus_mulVec_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
      hCas hγ hΦ
  · exact totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem
      (magSectorEmbedding_mem_magSubspaceS (V := V) (N := N) (M := K) Φ)

/-- **Tasaki §2.5 Theorem 2.3 raising ladder link from predicted-GS
membership**: discharges the Casimir hypotheses of
`tasaki23_pf_ladder_link_pred` for a predicted toy ground-state sector
vector in sector `M + 1` strictly above the left endpoint.  The total
Casimir eigenvalue is pinned to `tasaki23PredictedCasimirValue A N`, which
differs from the raising-kernel value of that sector. -/
theorem tasaki23_pf_ladder_link_pred_of_mem_predictedGS
    (A : V → Bool) {N M : ℕ} {J : V → V → ℂ} {μ : ℝ}
    {Φ : magConfigS V N (M + 1) → ℂ}
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
        M + 1)
    (hΨ_pred :
      magSectorEmbedding Φ ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hΦ : magSectorEmbedding Φ ≠ 0) :
    (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∧
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1) :=
  tasaki23_pf_ladder_link_pred hH
    (tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      A N hBA hΨ_pred)
    (tasaki23_predictedCasimirValue_ne_raising_kernel_value_of_mem_of_left_lt
      A N hM hMlt)
    hΦ

end LatticeSystem.Quantum
