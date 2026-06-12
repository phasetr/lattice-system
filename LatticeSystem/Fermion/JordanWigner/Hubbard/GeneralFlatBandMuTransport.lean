import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandFilling

/-!
# Transport of the flat-band Fock span to the special basis (Tasaki §11.3.4, toward 11.3.47)

The flat-band spanning of eq. (11.3.46) was proved over the spectral eigenbasis of `T`.  To reach the
spin-system representation (eq. 11.3.47), which is stated over the *special basis* `{μ_z}` (Lemma
11.16), we transport the span: since both the flat eigenvectors and `{μ_z}` are bases of the same
flat band `ker T`, the Fock span of one is contained in the Fock span of the other.

This module records the single-particle identity `ker T = span{μ_z}` (at the coordinate level) — the
linear-algebra input for the operator-level transport.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eqs. (11.3.46)–(11.3.47).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {M : ℕ}

/-- The coordinate kernel `ker(T·) ⊆ (Fin (M+1) → ℂ)` has the flat-band dimension `D₀`: it
corresponds, under the `WithLp` identification, to `generalFlatBandKernel` on `EuclideanSpace`. -/
theorem finrank_ker_mulVecLin_eq_generalFlatBandDim
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) :
    Module.finrank ℂ (LinearMap.ker T.mulVecLin) = generalFlatBandDim T := by
  classical
  set e : EuclideanSpace ℂ (Fin (M + 1)) ≃ₗ[ℂ] (Fin (M + 1) → ℂ) :=
    WithLp.linearEquiv 2 ℂ (Fin (M + 1) → ℂ) with he
  have hmap : (generalFlatBandKernel T).map (e : _ →ₗ[ℂ] _) = LinearMap.ker T.mulVecLin := by
    ext w
    simp only [Submodule.mem_map, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [generalFlatBand_mem_kernel_iff] at hv
      exact hv
    · intro hw
      exact ⟨e.symm w, by
        rw [generalFlatBand_mem_kernel_iff]; simpa using hw, by simp⟩
  rw [generalFlatBandDim, ← hmap, ((e.submoduleMap (generalFlatBandKernel T)).finrank_eq).symm]

/-- **`ker T = span{μ_z}` (coordinate level)**: the special basis `{μ_z}_{z∈I}` of Lemma 11.16
spans the entire coordinate flat band `ker(T·)`.  (Each `μ_z` lies in `ker T`; they are linearly
independent and number `D₀ = dim ker T`, so they span it.) -/
theorem ker_mulVecLin_eq_span_specialBasis
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ) :
    LinearMap.ker T.mulVecLin
      = Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ))) := by
  obtain ⟨hcard, hker, hli, _, _⟩ := hbasis
  have hspan_le : Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)))
      ≤ LinearMap.ker T.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hker z.1 z.2
  have hfr_span : Module.finrank ℂ
      (Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ)))) = I.card := by
    rw [finrank_span_eq_card hli, Fintype.card_coe]
  have hfr_ker : Module.finrank ℂ (LinearMap.ker T.mulVecLin) = I.card := by
    rw [finrank_ker_mulVecLin_eq_generalFlatBandDim, hcard]
  exact (Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hfr_span, hfr_ker])).symm

/-- The `μ`-Slater Fock submodule is invariant under each special-basis mode creation
`â†_{μ_z,σ}` (prepending the mode to a Slater list). -/
theorem generalFlatBandCreation_mulVec_mem_fockSubmodule (μ : Fin (M + 1) → Fin (M + 1) → ℂ)
    (z : Fin (M + 1)) (σ : Fin 2) {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : v ∈ generalFlatBandFockSubmodule μ) :
    (generalFlatBandCreation μ z σ).mulVec v ∈ generalFlatBandFockSubmodule μ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨qs, rfl⟩
    rw [generalFlatBandCreation_mulVec_slaterState]
    exact generalFlatBandSlaterState_mem_fockSubmodule μ _
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx

/-- **The `μ`-Slater Fock submodule is invariant under `Ĉ†_σ(w)` for every `w ∈ span{μ_z}` (= ker T)**:
since `w` is a combination of the `μ_z`, the smeared creator is a combination of the mode creators,
each of which keeps the submodule invariant. -/
theorem spinfulCreationFromVector_span_mulVec_mem_fockSubmodule
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (σ : Fin 2) {w : Fin (M + 1) → ℂ}
    (hw : w ∈ Submodule.span ℂ (Set.range (fun z : I => (μ z.1 : Fin (M + 1) → ℂ))))
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ} (hv : v ∈ generalFlatBandFockSubmodule μ) :
    (spinfulCreationFromVector M w σ).mulVec v ∈ generalFlatBandFockSubmodule μ := by
  induction hw using Submodule.span_induction with
  | mem w' hw' =>
    obtain ⟨z, rfl⟩ := hw'
    exact generalFlatBandCreation_mulVec_mem_fockSubmodule μ z.1 σ hv
  | zero =>
    rw [spinfulCreationFromVector_zero, Matrix.zero_mulVec]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [spinfulCreationFromVector_add, Matrix.add_mulVec]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [spinfulCreationFromVector_smul, Matrix.smul_mulVec]; exact Submodule.smul_mem _ a hx

end LatticeSystem.Fermion
