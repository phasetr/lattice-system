import LatticeSystem.Quantum.SpinS.Theorem23JointPredictedLowering
import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import LatticeSystem.Quantum.SpinS.JointDiagonalPredictedEigenvector

/-!
# A joint predicted-Casimir eigenvector in every admissible sector

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3).

Combining the extremal-sector minimal-total-spin joint eigenvector (#3709) with the
Casimir-preserving lowering step (#3714,
`tasaki23_jointPredicted_lowering_succ`) gives, in **every** admissible sector
`M ∈ tasaki23GroundStateSectors A N = [min(|A|,|¬A|)·N, max(|A|,|¬A|)·N]`, a non-zero
simultaneous eigenvector of `(Ŝ_tot)²` (at the predicted value), `(Ŝ_A)²` and `(Ŝ_¬A)²`.
This is the Casimir-controlled spread of the predicted total spin across the whole
admissible range — the per-sector predicted-Casimir input the constancy chain (#3713)
and the overlap pin (#3712) consume, obtained WITHOUT any lowered Marshall-positivity
("site-sum") hypothesis.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Abbreviation: the maximal sublattice-`A` Casimir eigenvalue `s_A(s_A+1)`. -/
noncomputable def maxCasA (A : Λ → Bool) (N : ℕ) : ℂ :=
  ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
    (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)

/-- Abbreviation: the maximal sublattice-`¬A` Casimir eigenvalue `s_B(s_B+1)`. -/
noncomputable def maxCasB (A : Λ → Bool) (N : ℕ) : ℂ :=
  ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) *
    (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) + 1)

/-- **Joint predicted-Casimir eigenvector at the extremal base sector**
`M = min(|A|,|¬A|)·N`, in embedded sector form: re-derivation of #3709 retaining the
magnetization-sector membership so the vector is `magSectorEmbedding Φ`. -/
theorem exists_jointPredictedCasimir_embed_base (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ∃ Φ : magConfigS Λ N
        (min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N) → ℂ,
      magSectorEmbedding Φ ≠ 0 ∧
      (totalSpinSSquared Λ N).mulVec (magSectorEmbedding Φ) =
        ((tasaki23PredictedCasimirValue (V := Λ) A N : ℝ) : ℂ) • magSectorEmbedding Φ ∧
      (sublatticeSpinSquaredS N A).mulVec (magSectorEmbedding Φ) =
        maxCasA A N • magSectorEmbedding Φ ∧
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (magSectorEmbedding Φ) =
        maxCasB A N • magSectorEmbedding Φ := by
  obtain ⟨w, hw_ne, hw_span, hw_ker⟩ := exists_jointDiagonal_totalSpinSOpPlus_kernel A horient
  have hw_W : w ∈ jointSublatticeCasimirEigenspace (Λ := Λ) A N :=
    (Submodule.span_le.mpr
      (Set.range_subset_iff.mpr (jointDiagonalIterate_mem_jointSublatticeCasimirEigenspace A)))
      hw_span
  obtain ⟨hw_A, hw_B⟩ := hw_W
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hw_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hw_B
  have hw_mag : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) :=
    (Submodule.span_le.mpr
      (Set.range_subset_iff.mpr (jointDiagonalIterate_mem_magSubspaceS A))) hw_span
  have hmin : min (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := min_eq_right horient
  have hw_mag' : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      ((min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) := by
    rw [hmin]; exact hw_mag
  have hw_tot := tasaki23_extremal_highestWeight_totalCasimir_eq_predicted (V := Λ) (N := N) A
    hw_mag' hw_ker
  -- Re-embed: w = magSectorEmbedding (magSectorRestriction w) at sector min(·)·N.
  set M₀ := min (Finset.univ.filter (fun x : Λ => A x = true)).card
    (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N with hM₀
  have hembed := magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS (M := M₀) hw_mag'
  refine ⟨magSectorRestriction (M := M₀) w, ?_, ?_, ?_, ?_⟩
  · rw [hembed]; exact hw_ne
  · rw [hembed]; exact hw_tot
  · rw [hembed]; exact hw_A
  · rw [hembed]; exact hw_B

/-- **Joint predicted-Casimir eigenvector in every admissible sector** (for
`|¬A| ≤ |A|`): in each `M ∈ tasaki23GroundStateSectors A N` there is a non-zero
`magSectorEmbedding Φ` that is a simultaneous eigenvector of `(Ŝ_tot)²` (at the
predicted value), `(Ŝ_A)²` (at `s_A(s_A+1)`) and `(Ŝ_¬A)²` (at `s_B(s_B+1)`).  Proved by
lowering the extremal base eigenvector (#3714) along the admissible range. -/
theorem exists_jointPredictedCasimir_embed_sector (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := Λ) A N) :
    ∃ Φ : magConfigS Λ N M → ℂ,
      magSectorEmbedding Φ ≠ 0 ∧
      (totalSpinSSquared Λ N).mulVec (magSectorEmbedding Φ) =
        ((tasaki23PredictedCasimirValue (V := Λ) A N : ℝ) : ℂ) • magSectorEmbedding Φ ∧
      (sublatticeSpinSquaredS N A).mulVec (magSectorEmbedding Φ) =
        maxCasA A N • magSectorEmbedding Φ ∧
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (magSectorEmbedding Φ) =
        maxCasB A N • magSectorEmbedding Φ := by
  set cmin := min (Finset.univ.filter (fun x : Λ => A x = true)).card
    (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N with hcmin
  set cmax := max (Finset.univ.filter (fun x : Λ => A x = true)).card
    (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N with hcmax
  -- The per-sector statement, abstracted for induction on the distance from the base.
  suffices hgen : ∀ d : ℕ, cmin + d ≤ cmax →
      ∃ Φ : magConfigS Λ N (cmin + d) → ℂ,
        magSectorEmbedding Φ ≠ 0 ∧
        (totalSpinSSquared Λ N).mulVec (magSectorEmbedding Φ) =
          ((tasaki23PredictedCasimirValue (V := Λ) A N : ℝ) : ℂ) • magSectorEmbedding Φ ∧
        (sublatticeSpinSquaredS N A).mulVec (magSectorEmbedding Φ) =
          maxCasA A N • magSectorEmbedding Φ ∧
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (magSectorEmbedding Φ) =
          maxCasB A N • magSectorEmbedding Φ by
    obtain ⟨hlow, hhigh⟩ := (tasaki23GroundStateSectors_mem_iff (V := Λ) A N M).mp hM
    have hMeq : cmin + (M - cmin) = M := by omega
    have := hgen (M - cmin) (by omega)
    rw [hMeq] at this
    exact this
  intro d
  induction d with
  | zero =>
    intro _
    simpa using exists_jointPredictedCasimir_embed_base (N := N) A horient
  | succ d ih =>
    intro hle
    obtain ⟨Φ, hΦ_ne, hΦ_tot, hΦ_A, hΦ_B⟩ := ih (by omega)
    -- The source sector `cmin + d` is admissible and strictly below the right endpoint.
    have hKmem : cmin + d ∈ tasaki23GroundStateSectors (V := Λ) A N := by
      rw [tasaki23GroundStateSectors_mem_iff]; omega
    have hKlt : cmin + d < cmax := by omega
    -- Lower the joint eigenvector (Casimir-preserving, non-vanishing).
    obtain ⟨hne, htot, hA, hB⟩ :=
      tasaki23_jointPredicted_lowering_succ (N := N) A hKmem hKlt hΦ_ne hΦ_tot hΦ_A hΦ_B
    -- The lowered vector sits in the successor sector; re-embed it.
    have hmem_succ :
        (totalSpinSOpMinus Λ N).mulVec (magSectorEmbedding Φ) ∈
          magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - ((cmin + d + 1 : ℕ) : ℂ)) := by
      have h := totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        (magSectorEmbedding_mem_magSubspaceS (V := Λ) (N := N) (M := cmin + d) Φ)
      convert h using 2
      push_cast
      ring
    have hembed :=
      magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS (M := cmin + d + 1) hmem_succ
    refine ⟨magSectorRestriction (M := cmin + d + 1)
      ((totalSpinSOpMinus Λ N).mulVec (magSectorEmbedding Φ)), ?_, ?_, ?_, ?_⟩
    · rw [hembed]; exact hne
    · rw [hembed]; exact htot
    · rw [hembed]; exact hA
    · rw [hembed]; exact hB

end LatticeSystem.Quantum
