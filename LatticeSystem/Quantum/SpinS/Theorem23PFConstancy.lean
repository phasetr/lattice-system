import LatticeSystem.Quantum.SpinS.Theorem23PFLadderLink
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique

/-!
# Tasaki §2.5 Theorem 2.3 — Perron–Frobenius adjacent-sector energy bound

Sound Perron–Frobenius route (Issue #3542; see
`.self-local/docs/tasaki-2-5-pf-route-design.md`).  Combining the
adjacent-sector ladder link (`Theorem23PFLadderLink.lean`) with the
per-sector spectral lower bound for Marshall-positive ground states
(`heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive`),
the ground energy is non-increasing along the lowering ladder across the
admissible range.  Together with the raising companion this yields the
constancy of the sector ground energies (the common-energy chain) in the
sound route, with no Marshall positivity of the lowered vector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector ground-energy bound
(lowering)**: in the canonical orientation `|¬A| ≤ |A|`, if a predicted
toy ground-state Heisenberg eigenvector `magSectorEmbedding Φ` sits at
energy `μ` in an admissible sector `M` below the right endpoint, and
sector `M + 1` carries a Marshall-positive real eigenvector `w` at energy
`μ'`, then `μ' ≤ μ`.

Proof: the ladder link makes `Ŝ⁻_tot · magSectorEmbedding Φ` a non-zero
Heisenberg eigenvector at the same `μ` supported in sector `M + 1`; its
sector restriction is a non-zero complex sector eigenvector at `μ`, so one
of its real/imaginary parts is a non-zero real-form sector eigenvector at
`μ`.  The Marshall-positive ground state `w` at `μ'` then bounds every
real sector eigenvalue from below, giving `μ' ≤ μ`.  No Marshall
positivity of the lowered vector is used. -/
theorem tasaki23_pf_sector_energy_succ_le
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      M <
        max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    {μ μ' : ℝ} {Φ : magConfigS V N M → ℂ} {w : magConfigS V N (M + 1) → ℝ}
    (hΨ_pred :
      magSectorEmbedding Φ ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hΦ_ne : magSectorEmbedding Φ ≠ 0)
    (hw_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w σ)
    (hw :
      (heisenbergHamiltonianSReMatrixOnMagSector J N (M + 1)).mulVec w =
        μ' • w) :
    μ' ≤ μ := by
  obtain ⟨hH_succ, hne_succ, hmem⟩ :=
    tasaki23_pf_ladder_link_succ_of_mem_predictedGS A hBA hM hMlt hΨ_pred hH hΦ_ne
  have hmem' :
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) := by
    convert hmem using 2
    push_cast
    ring
  set Ψ := (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) with hΨdef
  set W : magConfigS V N (M + 1) → ℂ := magSectorRestriction (M := M + 1) Ψ with hWdef
  have hembedW : magSectorEmbedding W = Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS hmem'
  have hW_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N (M + 1)).mulVec W = (μ : ℂ) • W := by
    apply heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH_succ
    intro σ hσ
    exact magSubspaceS_apply_eq_zero_of_magSumS_ne hmem' hσ
  have hW_ne : W ≠ 0 := by
    intro h0
    apply hne_succ
    rw [← hembedW, h0, magSectorEmbedding_zero]
  obtain ⟨σ0, hσ0⟩ := Function.ne_iff.mp hW_ne
  have hRe :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW_eig
  have hIm :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hW_eig
  by_cases hre : (fun σ => (W σ).re) = (0 : magConfigS V N (M + 1) → ℝ)
  · have him_ne : (fun σ => (W σ).im) ≠ 0 := by
      intro h0
      apply hσ0
      apply Complex.ext
      · exact congrFun hre σ0
      · exact congrFun h0 σ0
    exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      him_ne hIm
  · exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      hre hRe

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector ground-energy bound
(raising)**: the raising companion of `tasaki23_pf_sector_energy_succ_le`.
If a predicted toy ground-state Heisenberg eigenvector sits at energy `μ`
in an admissible sector `M + 1` strictly above the left endpoint, and
sector `M` carries a Marshall-positive real eigenvector `w` at `μ'`, then
`μ' ≤ μ`.  Proof mirrors the lowering case with `Ŝ⁺_tot`. -/
theorem tasaki23_pf_sector_energy_pred_le
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
        M + 1)
    {μ μ' : ℝ} {Φ : magConfigS V N (M + 1) → ℂ} {w : magConfigS V N M → ℝ}
    (hΨ_pred :
      magSectorEmbedding Φ ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hH :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
        (μ : ℂ) • magSectorEmbedding Φ)
    (hΦ_ne : magSectorEmbedding Φ ≠ 0)
    (hw_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w σ)
    (hw :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ' • w) :
    μ' ≤ μ := by
  obtain ⟨hH_pred, hne_pred, hmem⟩ :=
    tasaki23_pf_ladder_link_pred_of_mem_predictedGS A hBA hM hMlt hΨ_pred hH hΦ_ne
  have hmem' :
      (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    convert hmem using 2
    push_cast
    ring
  set Ψ := (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) with hΨdef
  set W : magConfigS V N M → ℂ := magSectorRestriction (M := M) Ψ with hWdef
  have hembedW : magSectorEmbedding W = Ψ :=
    magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS hmem'
  have hW_eig :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W = (μ : ℂ) • W := by
    apply heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction J hH_pred
    intro σ hσ
    exact magSubspaceS_apply_eq_zero_of_magSumS_ne hmem' hσ
  have hW_ne : W ≠ 0 := by
    intro h0
    apply hne_pred
    rw [← hembedW, h0, magSectorEmbedding_zero]
  obtain ⟨σ0, hσ0⟩ := Function.ne_iff.mp hW_ne
  have hRe :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW_eig
  have hIm :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hW_eig
  by_cases hre : (fun σ => (W σ).re) = (0 : magConfigS V N M → ℝ)
  · have him_ne : (fun σ => (W σ).im) ≠ 0 := by
      intro h0
      apply hσ0
      apply Complex.ext
      · exact congrFun hre σ0
      · exact congrFun h0 σ0
    exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      him_ne hIm
  · exact heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hw hw_marshall_pos
      hre hRe

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector ground-energy constancy**:
the two predicted-GS adjacent-sector bounds combine to equate the
Marshall-positive Perron–Frobenius ground energies of two adjacent
admissible sectors `M` and `M + 1` (interior to the admissible range).

For each sector the Marshall-positive ground state `marshallSignS · v`
(with `v > 0`) is supplied both as a full-space Heisenberg eigenvector
(`magSectorEmbedding` form) and as a real-form sector-matrix eigenvector,
together with predicted toy ground-state membership.  The lowering bound
gives `μ_{M+1} ≤ μ_M` and the raising bound gives `μ_M ≤ μ_{M+1}`, hence
`μ_M = μ_{M+1}`.  This is the inductive constancy step of the
common-energy chain (sound route), still modulo the predicted-GS
membership of the per-sector ground states. -/
theorem tasaki23_pf_sector_energy_eq
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hM1_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt_right :
      M <
        max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hMlt_left :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
        M + 1)
    {μM μM1 : ℝ} {vM : magConfigS V N M → ℝ} {vM1 : magConfigS V N (M + 1) → ℝ}
    (hvM_pos : ∀ σ, 0 < vM σ) (hvM1_pos : ∀ σ, 0 < vM1 σ)
    (hH_M :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)))
    (hH_M1 :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ))) =
        (μM1 : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ)))
    (hRe_M :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun σ => (marshallSignS A σ.1).re * vM σ) =
        μM • (fun σ => (marshallSignS A σ.1).re * vM σ))
    (hRe_M1 :
      (heisenbergHamiltonianSReMatrixOnMagSector J N (M + 1)).mulVec
          (fun σ => (marshallSignS A σ.1).re * vM1 σ) =
        μM1 • (fun σ => (marshallSignS A σ.1).re * vM1 σ))
    (hpred_M :
      magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hpred_M1 :
      magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * vM1 τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    μM = μM1 := by
  have hmarshall_pos_M : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hvM_pos σ
  have hmarshall_pos_M1 : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM1 σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hvM1_pos σ
  have hΦM_ne := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvM_pos
  have hΦM1_ne := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvM1_pos
  have hle1 : μM1 ≤ μM :=
    tasaki23_pf_sector_energy_succ_le A N c hJ_real hJ_real' hJ_nn hJ_sym
      hJ_bipartite hc_strict hBA hM_mem hMlt_right hpred_M hH_M hΦM_ne
      hmarshall_pos_M1 hRe_M1
  have hle2 : μM ≤ μM1 :=
    tasaki23_pf_sector_energy_pred_le A N c hJ_real hJ_real' hJ_nn hJ_sym
      hJ_bipartite hc_strict hBA hM1_mem hMlt_left hpred_M1 hH_M1 hΦM1_ne
      hmarshall_pos_M hRe_M
  exact le_antisymm hle2 hle1

end LatticeSystem.Quantum
