import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Quantum.SpinS.Theorem23StructuralSectorLiftCasimir
import LatticeSystem.Quantum.SpinS.EigenspaceFinrankLeOneTransfer
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector
import LatticeSystem.Quantum.SpinS.Theorem24SectorPFFromTheorem23
import LatticeSystem.Math.ComplexVectorKernel
/-!
# SU(2)-point global uniqueness from the MLM endpoint — core lemmas

Core (foundational) lemmas behind Tasaki §2.5 Theorem 2.4 obligation (2):
balanced-sector setup, zero-Casimir transfer bridges, the singlet-image
obstruction, the strict outside-sector ordering, the Hermitian-minimum
identification, and full-eigenspace simplicity helpers.  The packaged
MLM-to-SU(2) uniqueness endpoints are assembled in
`Theorem24SU2GlobalUniquenessFromMLM`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3 and 2.4, pp. 42-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- **Symmetric sublattice sector singleton, membership form**: if the two
Boolean sublattices have equal cardinality, then Tasaki Theorem 2.3's predicted
ground-state sector interval contains exactly `|A| * N`. -/
theorem tasaki23GroundStateSectors_mem_iff_eq_of_card_eq
    (A : V → Bool) (N M : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    M ∈ tasaki23GroundStateSectors (V := V) A N ↔
      M = (Finset.univ.filter (fun x : V => A x = true)).card * N := by
  rw [tasaki23GroundStateSectors_mem_iff]
  rw [← h_card_eq, min_self, max_self]
  omega

omit [DecidableEq V] in
/-- **Symmetric sublattice sector singleton, finset form**: if the two Boolean
sublattices have equal cardinality, then Theorem 2.3's predicted ground-state
sector set is the singleton `{|A| * N}`. -/
theorem tasaki23GroundStateSectors_eq_singleton_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    tasaki23GroundStateSectors (V := V) A N =
      {((Finset.univ.filter (fun x : V => A x = true)).card * N)} := by
  ext M
  rw [tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N M h_card_eq,
    Finset.mem_singleton]

omit [DecidableEq V] in
/-- **Symmetric sublattice predicted total spin is zero**: in the balanced
cardinality case, Tasaki Theorem 2.3's predicted total-spin magnitude
`||A| - |not A|| * N / 2` vanishes. -/
theorem tasaki23PredictedTotalSpin_eq_zero_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    tasaki23PredictedTotalSpin (V := V) A N = 0 := by
  unfold tasaki23PredictedTotalSpin
  rw [h_card_eq, sub_self, abs_zero, zero_mul]

omit [DecidableEq V] in
/-- **Symmetric sublattice predicted Casimir is zero**: in the balanced
cardinality case, the predicted total spin is `0`, so the predicted
total-Casimir value `S(S+1)` is also `0`. -/
theorem tasaki23PredictedCasimirValue_eq_zero_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    tasaki23PredictedCasimirValue (V := V) A N = 0 := by
  rw [tasaki23PredictedCasimirValue,
    tasaki23PredictedTotalSpin_eq_zero_of_card_eq A N h_card_eq]
  ring

/-- **Symmetric-sector lift with zero total Casimir**: the structural
Theorem 2.3 PF/Casimir lift specializes in the balanced-cardinality case to a
full Heisenberg eigenvector whose total-Casimir eigenvalue is `0`.  This is
the equality-case input needed for the strict outside-sector MLM endpoint. -/
theorem tasaki23_sector_lift_and_casimir_zero_of_card_eq
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
      (N : ℝ) / 2)
    {M : ℕ} (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hReEig : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v σ)) :
    ((heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ∧
    ((totalSpinSSquared V N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      (0 : ℂ) •
        magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) := by
  classical
  have horient :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card := by
    rw [← h_card_eq]
  obtain ⟨hH, hCas⟩ :=
    tasaki23_sector_lift_and_casimir (N := N) A c c_toy horient hsB hM
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
      hA_ne hB_ne hN hv_pos hReEig
  refine ⟨hH, ?_⟩
  have hpred0 := tasaki23PredictedCasimirValue_eq_zero_of_card_eq (V := V) A N h_card_eq
  simpa [hpred0] using hCas

/-- **Zero-Casimir transfer along a one-dimensional sector ground line**: suppose the
full Heisenberg `μ`-eigenspace, restricted to sector `M`, has dimension at most
one, and it contains a non-zero sector-supported vector `Φ0` with total-Casimir
eigenvalue `0`.  Then every other sector-supported full eigenvector `Ψ` at the
same eigenvalue also has total-Casimir image `0`.

This is the equality-case bridge for the MLM endpoint: once the outside-sector
ladder lands in the balanced sector at the common energy, sector PF simplicity
pins the landed vector to the zero-Casimir PF line. -/
theorem heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_zero_of_sector_pf_zero_casimir
    (J : V → V → ℂ) (M : ℕ) (μ : ℂ)
    {Φ0 Ψ : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = μ • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = 0)
    (hΨ_eig : (heisenbergHamiltonianS J N).mulVec Ψ = μ • Ψ)
    (hΨ_mem : Ψ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M)) μ) ≤ 1) :
    (totalSpinSSquared V N).mulVec Ψ = 0 := by
  classical
  set E := End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
    with hEdef
  set A :=
    magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ))
    with hAdef
  have hline :
      finrank ℂ ↥(E ⊓ A) ≤ 1 := by
    subst E
    subst A
    exact heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
      (Λ := V) (N := N) J M μ h_sector_pf
  have hΦ0_in : Φ0 ∈ E ⊓ A := by
    refine ⟨?_, ?_⟩
    · change Φ0 ∈ End.eigenspace
        (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hΦ0_eig
    · rw [hAdef]
      exact hΦ0_mem
  have hΨ_in : Ψ ∈ E ⊓ A := by
    refine ⟨?_, ?_⟩
    · change Ψ ∈ End.eigenspace
        (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hΨ_eig
    · rw [hAdef]
      exact hΨ_mem
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hline
  obtain ⟨a, ha⟩ := hv ⟨Φ0, hΦ0_in⟩
  obtain ⟨b, hb⟩ := hv ⟨Ψ, hΨ_in⟩
  have ha' : a • (v : (V → Fin (N + 1)) → ℂ) = Φ0 := by
    have h := congrArg ((↑) : ↥(E ⊓ A) → (V → Fin (N + 1)) → ℂ) ha
    simpa using h
  have hb' : b • (v : (V → Fin (N + 1)) → ℂ) = Ψ := by
    have h := congrArg ((↑) : ↥(E ⊓ A) → (V → Fin (N + 1)) → ℂ) hb
    simpa using h
  have ha_ne : a ≠ 0 := by
    intro h0
    apply hΦ0_ne
    rw [← ha', h0, zero_smul]
  have hΨ_eq : Ψ = (b * a⁻¹) • Φ0 := by
    rw [← hb', ← ha', smul_smul]
    have hscalar : (b * a⁻¹) * a = b := by
      rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
    rw [hscalar]
  rw [hΨ_eq, Matrix.mulVec_smul, hΦ0_cas, smul_zero]

/-- **Lowering-landed zero-Casimir bridge**: suppose a non-zero full
Heisenberg eigenvector `Φ` starts in sector `M`, and `k` valid total-lowering
steps land it in sector `M + k` without changing the energy.  If sector PF
simplicity pins the landed sector to a known non-zero zero-Casimir vector
`Φ0`, then the landed vector is still non-zero and has total-Casimir image
`0`.

This packages the equality-case endpoint of the inward ladder used in the
MLM/Casimir strict outside-sector argument. -/
theorem heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_eq_zero_of_sector_pf
    (J : V → V → ℂ) (M k : ℕ) (μ : ℝ)
    {Φ0 Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = 0)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_mem : Φ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hpos : ∀ j : ℕ, j < k →
      0 < ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) - (j : ℂ)).re)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N (M + k))) (μ : ℂ)) ≤ 1) :
    ((totalSpinSOpMinus V N ^ k).mulVec Φ ≠ 0) ∧
      (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N ^ k).mulVec Φ) = 0 := by
  classical
  obtain ⟨hland_ne, hland_mem, hland_eig⟩ :=
    lower_iterate_ne_zero (V := V) (N := N) (J := J) (lam := μ) k
      hΦ_ne hΦ_mem hΦ_eig hpos
  have hland_mem' :
      (totalSpinSOpMinus V N ^ k).mulVec Φ ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)) := by
    convert hland_mem using 1
    push_cast
    ring_nf
  refine ⟨hland_ne, ?_⟩
  exact heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_zero_of_sector_pf_zero_casimir
    (V := V) (N := N) J (M + k) (μ : ℂ)
    hΦ0_ne hΦ0_eig hΦ0_mem hΦ0_cas hland_eig hland_mem' h_sector_pf

/-- **Raising-landed zero-Casimir bridge**: suppose a non-zero full
Heisenberg eigenvector `Φ` starts in sector `M + k`, and `k` valid
total-raising steps land it in sector `M` without changing the energy.  If
sector PF simplicity pins the landed sector to a known non-zero zero-Casimir
vector `Φ0`, then the landed vector is still non-zero and has total-Casimir
image `0`.

This is the raising-side companion to
`heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_eq_zero_of_sector_pf`. -/
theorem heisenbergHamiltonianS_totalSpinSSquared_mulVec_raise_landed_eq_zero_of_sector_pf
    (J : V → V → ℂ) (M k : ℕ) (μ : ℝ)
    {Φ0 Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = 0)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_mem : Φ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)))
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hneg : ∀ j : ℕ, j < k →
      ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)) + (j : ℂ)).re < 0)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M)) (μ : ℂ)) ≤ 1) :
    ((totalSpinSOpPlus V N ^ k).mulVec Φ ≠ 0) ∧
      (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N ^ k).mulVec Φ) = 0 := by
  classical
  obtain ⟨hland_ne, hland_mem, hland_eig⟩ :=
    raise_iterate_ne_zero (V := V) (N := N) (J := J) (lam := μ) k
      hΦ_ne hΦ_mem hΦ_eig hneg
  have hland_mem' :
      (totalSpinSOpPlus V N ^ k).mulVec Φ ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) := by
    convert hland_mem using 1
    push_cast
    ring_nf
  refine ⟨hland_ne, ?_⟩
  exact heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_zero_of_sector_pf_zero_casimir
    (V := V) (N := N) J M (μ : ℂ)
    hΦ0_ne hΦ0_eig hΦ0_mem hΦ0_cas hland_eig hland_mem' h_sector_pf

/-! ## Zero-Casimir singlet image obstruction -/

omit [DecidableEq V] in
/-- If a vector is in the range of `M` and is killed by `Mᴴ`, then the vector is
zero.  This is the finite-dimensional Hilbert-space fact `range M ⟂ ker Mᴴ`. -/
private theorem eq_zero_of_eq_mulVec_and_conjTranspose_mulVec_eq_zero
    {n : Type*} [Fintype n] (M : Matrix n n ℂ) {u w : n → ℂ}
    (hw_eq : w = M.mulVec u)
    (hstar : M.conjTranspose.mulVec w = 0) :
    w = 0 := by
  have hnorm :
      ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) = 0 := by
    calc
      ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) =
          star u ⬝ᵥ (M.conjTranspose * M).mulVec u := by
            rw [star_dotProduct_conjTranspose_mul_mulVec_eq]
            simp [hw_eq]
      _ = star u ⬝ᵥ M.conjTranspose.mulVec w := by
            rw [hw_eq, ← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hstar, dotProduct_zero]
  have hsum : ∑ i, Complex.normSq (w i) = 0 := Complex.ofReal_eq_zero.mp hnorm
  have hnorm_all :
      ∀ i ∈ (Finset.univ : Finset n), Complex.normSq (w i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (fun j _ => Complex.normSq_nonneg (w j))).mp (by simpa using hsum)
  funext i
  exact Complex.normSq_eq_zero.mp (hnorm_all i (Finset.mem_univ i))

/-- A zero-total-Casimir vector in the zero magnetization sector is killed by
`Ŝ⁺_tot`.  This is the singlet highest-weight half of the equality-case
obstruction. -/
theorem totalSpinSOpPlus_mulVec_eq_zero_of_totalSpinSSquared_mulVec_eq_zero_of_mem_zero_magSubspaceS
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_mem : Ψ ∈ magSubspaceS V N 0)
    (hΨ_cas : (totalSpinSSquared V N).mulVec Ψ = 0) :
    (totalSpinSOpPlus V N).mulVec Ψ = 0 := by
  have hz : (totalSpinSOp3 V N).mulVec Ψ = 0 := by
    have hz' := (mem_magSubspaceS_iff (Λ := V) (N := N) 0 Ψ).mp hΨ_mem
    simpa using hz'
  have hZsq : ((totalSpinSOp3 V N * totalSpinSOp3 V N : ManyBodyOpS V N).mulVec Ψ) = 0 := by
    rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have hMP :
      ((totalSpinSOpMinus V N : ManyBodyOpS V N) * totalSpinSOpPlus V N).mulVec Ψ = 0 := by
    rw [totalSpinSOpMinus_mul_totalSpinSOpPlus_eq_casimir_minus_z_sq_sub_z,
      Matrix.sub_mulVec, Matrix.sub_mulVec, hΨ_cas, hZsq, hz]
    simp
  exact eq_zero_of_eq_mulVec_and_conjTranspose_mulVec_eq_zero
    (totalSpinSOpPlus V N)
    (u := Ψ) (w := (totalSpinSOpPlus V N).mulVec Ψ) rfl
    (by
      rw [totalSpinSOpPlus_conjTranspose (Λ := V) (N := N)]
      rw [Matrix.mulVec_mulVec]
      exact hMP)

/-- A zero-total-Casimir vector in the zero magnetization sector is killed by
`Ŝ⁻_tot`.  This is the singlet lowest-weight half of the equality-case
obstruction. -/
theorem totSpinSOpMinus_mulVecZero_of_totSpinS2_mulVecZero_of_mem_zero_magSubS
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_mem : Ψ ∈ magSubspaceS V N 0)
    (hΨ_cas : (totalSpinSSquared V N).mulVec Ψ = 0) :
    (totalSpinSOpMinus V N).mulVec Ψ = 0 := by
  have hz : (totalSpinSOp3 V N).mulVec Ψ = 0 := by
    have hz' := (mem_magSubspaceS_iff (Λ := V) (N := N) 0 Ψ).mp hΨ_mem
    simpa using hz'
  have hZsq : ((totalSpinSOp3 V N * totalSpinSOp3 V N : ManyBodyOpS V N).mulVec Ψ) = 0 := by
    rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have hPM :
      ((totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N).mulVec Ψ = 0 := by
    rw [totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z,
      Matrix.add_mulVec, Matrix.sub_mulVec, hΨ_cas, hZsq, hz]
    simp
  exact eq_zero_of_eq_mulVec_and_conjTranspose_mulVec_eq_zero
    (totalSpinSOpMinus V N)
    (u := Ψ) (w := (totalSpinSOpMinus V N).mulVec Ψ) rfl
    (by
      rw [totalSpinSOpMinus_conjTranspose (Λ := V) (N := N)]
      rw [Matrix.mulVec_mulVec]
      exact hPM)

/-- A non-zero vector in the zero-Casimir, zero-magnetization line cannot be a
total-lowering image. -/
theorem not_exists_totalSpinSOpMinus_image_of_zero_casimir_zero_magSubspaceS
    {Υ Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq : Ψ = (totalSpinSOpMinus V N).mulVec Υ)
    (hΨ_ne : Ψ ≠ 0)
    (hΨ_mem : Ψ ∈ magSubspaceS V N 0)
    (hΨ_cas : (totalSpinSSquared V N).mulVec Ψ = 0) :
    False := by
  have hplus :
      (totalSpinSOpPlus V N).mulVec Ψ = 0 :=
    totalSpinSOpPlus_mulVec_eq_zero_of_totalSpinSSquared_mulVec_eq_zero_of_mem_zero_magSubspaceS
      hΨ_mem hΨ_cas
  exact hΨ_ne (eq_zero_of_eq_mulVec_and_conjTranspose_mulVec_eq_zero
    (totalSpinSOpMinus V N) (u := Υ) (w := Ψ) hΨ_eq
    (by
      rw [totalSpinSOpMinus_conjTranspose (Λ := V) (N := N)]
      exact hplus))

/-- A non-zero vector in the zero-Casimir, zero-magnetization line cannot be a
total-raising image. -/
theorem not_exists_totalSpinSOpPlus_image_of_zero_casimir_zero_magSubspaceS
    {Υ Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_eq : Ψ = (totalSpinSOpPlus V N).mulVec Υ)
    (hΨ_ne : Ψ ≠ 0)
    (hΨ_mem : Ψ ∈ magSubspaceS V N 0)
    (hΨ_cas : (totalSpinSSquared V N).mulVec Ψ = 0) :
    False := by
  have hminus :
      (totalSpinSOpMinus V N).mulVec Ψ = 0 :=
    totSpinSOpMinus_mulVecZero_of_totSpinS2_mulVecZero_of_mem_zero_magSubS
      hΨ_mem hΨ_cas
  exact hΨ_ne (eq_zero_of_eq_mulVec_and_conjTranspose_mulVec_eq_zero
    (totalSpinSOpPlus V N) (u := Υ) (w := Ψ) hΨ_eq
    (by
      rw [totalSpinSOpPlus_conjTranspose (Λ := V) (N := N)]
      exact hminus))

/-- A positive number of total-lowering steps cannot produce a non-zero
zero-Casimir vector in the zero magnetization sector. -/
theorem not_totalSpinSOpMinus_pow_mulVec_ne_zero_of_zero_casimir_zero_magSubspaceS
    (k : ℕ) (hk : 0 < k) {Φ : (V → Fin (N + 1)) → ℂ}
    (hland_ne : (totalSpinSOpMinus V N ^ k).mulVec Φ ≠ 0)
    (hland_mem : (totalSpinSOpMinus V N ^ k).mulVec Φ ∈ magSubspaceS V N 0)
    (hland_cas : (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N ^ k).mulVec Φ) = 0) :
    False := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  set Υ := (totalSpinSOpMinus V N ^ r).mulVec Φ
  have hstep :
      (totalSpinSOpMinus V N ^ (r + 1)).mulVec Φ =
        (totalSpinSOpMinus V N).mulVec Υ := by
    rw [pow_succ', Matrix.mulVec_mulVec]
  exact not_exists_totalSpinSOpMinus_image_of_zero_casimir_zero_magSubspaceS
    (V := V) (N := N) (Υ := Υ)
    (Ψ := (totalSpinSOpMinus V N ^ (r + 1)).mulVec Φ)
    hstep hland_ne hland_mem hland_cas

/-- A positive number of total-raising steps cannot produce a non-zero
zero-Casimir vector in the zero magnetization sector. -/
theorem not_totalSpinSOpPlus_pow_mulVec_ne_zero_of_zero_casimir_zero_magSubspaceS
    (k : ℕ) (hk : 0 < k) {Φ : (V → Fin (N + 1)) → ℂ}
    (hland_ne : (totalSpinSOpPlus V N ^ k).mulVec Φ ≠ 0)
    (hland_mem : (totalSpinSOpPlus V N ^ k).mulVec Φ ∈ magSubspaceS V N 0)
    (hland_cas : (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N ^ k).mulVec Φ) = 0) :
    False := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  set Υ := (totalSpinSOpPlus V N ^ r).mulVec Φ
  have hstep :
      (totalSpinSOpPlus V N ^ (r + 1)).mulVec Φ =
        (totalSpinSOpPlus V N).mulVec Υ := by
    rw [pow_succ', Matrix.mulVec_mulVec]
  exact not_exists_totalSpinSOpPlus_image_of_zero_casimir_zero_magSubspaceS
    (V := V) (N := N) (Υ := Υ)
    (Ψ := (totalSpinSOpPlus V N ^ (r + 1)).mulVec Φ)
    hstep hland_ne hland_mem hland_cas

omit [DecidableEq V] in
/-- In the balanced-cardinality case, the centered magnetization of the
balanced sector `|A| * N` is zero. -/
private theorem centered_weight_cardA_mul_eq_zero_of_card_eq
    (A : V → Bool) (N : ℕ)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
      (((Finset.univ.filter (fun x : V => A x = true)).card * N : ℕ) : ℂ) = 0 := by
  have hsum := tasaki23_card_filter_A_add_card_notA A
  have hcard :
      Fintype.card V =
        2 * (Finset.univ.filter (fun x : V => A x = true)).card := by
    rw [← hsum, h_card_eq]
    omega
  rw [hcard]
  push_cast
  ring

/-- **Strict outside-sector ordering from the zero-Casimir ladder obstruction**:
in the balanced-cardinality case, the non-strict `hOutside` bound from Theorem
2.3 is strict once the balanced sector is pinned by PF simplicity to a non-zero
zero-Casimir vector.

If an outside-sector eigenvalue equalled the common energy `μ`, the corresponding
sector eigenvector could be lifted to the full Hilbert space and moved by a
positive number of total ladder steps into the balanced sector.  PR #4022 pins
that landed vector to total Casimir zero, while the zero-Casimir image
obstruction above forbids such a non-zero positive-step ladder image. -/
theorem tasaki23_strict_hOutside_of_card_eq_zero_casimir_ladder_obstruction
    (A : V → Bool) (N : ℕ) (c : ℝ)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    {μ : ℝ}
    (hcommon : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ))
    {Φ0 : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
        (((Finset.univ.filter (fun x : V => A x = true)).card * N : ℕ) : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = 0)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
        ((Finset.univ.filter (fun x : V => A x = true)).card * N))) (μ : ℂ)) ≤ 1)
    {M : ℕ}
    (hM_ne : M ≠ (Finset.univ.filter (fun x : V => A x = true)).card * N)
    [Nonempty (magConfigS V N M)]
    {μM : ℝ} {φ : magConfigS V N M → ℝ}
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ) :
    μ < μM := by
  classical
  set M0 := (Finset.univ.filter (fun x : V => A x = true)).card * N with hM0def
  have hM_non : M ∉ tasaki23GroundStateSectors (V := V) A N := by
    rw [tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N M h_card_eq]
    exact hM_ne
  have hle : μ ≤ μM :=
    tasaki23_general_hOutside A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hcommon hM_non hφ_ne hφ
  have hne : μ ≠ μM := by
    intro hμ_eq
    have hComplex :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal (J := J) N hJ_real hφ
    have hHμM := heisenbergHamiltonianS_mulVec_magSectorEmbedding J
      (fun σ => ((φ σ : ℝ) : ℂ)) hComplex
    set Φ : (V → Fin (N + 1)) → ℂ :=
      magSectorEmbedding (fun σ => ((φ σ : ℝ) : ℂ)) with hΦdef
    have hΦ_ne : Φ ≠ 0 := by
      obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hφ_ne
      intro h0
      apply hτ
      have happ : Φ τ.1 = ((φ τ : ℝ) : ℂ) := by
        rw [hΦdef]
        exact magSectorEmbedding_apply_subtype _ τ
      rw [h0] at happ
      simp only [Pi.zero_apply] at happ
      have := congrArg Complex.re happ
      simpa using this.symm
    have hΦ_mem :
        Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
      rw [hΦdef]
      exact magSectorEmbedding_mem_magSubspaceS (fun σ => ((φ σ : ℝ) : ℂ))
    have hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ := by
      rw [hΦdef]
      simpa [hμ_eq] using hHμM
    have hzero :
        ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ) = 0 := by
      rw [hM0def]
      exact centered_weight_cardA_mul_eq_zero_of_card_eq (V := V) A N h_card_eq
    rcases lt_or_gt_of_ne hM_ne with hlt | hgt
    · set k := M0 - M with hk
      have hk_pos : 0 < k := by rw [hk]; omega
      have hkval : M0 = M + k := by rw [hk]; omega
      have hpos : ∀ j : ℕ, j < k →
          0 < ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) - (j : ℂ)).re := by
        intro j hj
        have hjlt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
        have hrewrite :
            (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ) - (j : ℂ)).re =
              (k : ℝ) - (j : ℝ) := by
          have hweight :
              ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ) =
                (k : ℂ) := by
            calc
              ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)
                  = (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) +
                    (k : ℂ) := by
                      rw [hkval]
                      push_cast
                      ring
              _ = (k : ℂ) := by rw [hzero, zero_add]
          rw [hweight]
          simp
        rw [hrewrite]
        linarith
      obtain ⟨_hland_ne', hland_mem, _hland_eig⟩ :=
        lower_iterate_ne_zero (V := V) (N := N) (J := J) (lam := μ) k
          hΦ_ne hΦ_mem hΦ_eig hpos
      have hsector_pf' : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N (M + k))) (μ : ℂ)) ≤ 1 := by
        rw [← hkval, hM0def]
        exact h_sector_pf
      have hΦ0_mem' : Φ0 ∈
          magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
            ((M + k : ℕ) : ℂ)) := by
        rw [← hkval, hM0def]
        exact hΦ0_mem
      obtain ⟨hland_ne, hland_cas⟩ :=
        heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_eq_zero_of_sector_pf
          (V := V) (N := N) J M k μ
          hΦ0_ne hΦ0_eig hΦ0_mem' hΦ0_cas hΦ_ne hΦ_mem hΦ_eig hpos hsector_pf'
      have hland_mem_zero :
          (totalSpinSOpMinus V N ^ k).mulVec Φ ∈ magSubspaceS V N 0 := by
        have hweight0 :
            (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) - (k : ℂ) = 0 := by
          calc
            (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) - (k : ℂ)
                = ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ) := by
                  rw [hkval]
                  push_cast
                  ring
            _ = 0 := hzero
        rwa [← hweight0]
      exact not_totalSpinSOpMinus_pow_mulVec_ne_zero_of_zero_casimir_zero_magSubspaceS
        (V := V) (N := N) k hk_pos hland_ne hland_mem_zero hland_cas
    · set k := M - M0 with hk
      have hk_pos : 0 < k := by rw [hk]; omega
      have hkval : M = M0 + k := by rw [hk]; omega
      have hneg : ∀ j : ℕ, j < k →
          ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M0 + k : ℕ) : ℂ)) +
              (j : ℂ)).re < 0 := by
        intro j hj
        have hjlt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
        have hrewrite :
            ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M0 + k : ℕ) : ℂ)) +
                (j : ℂ)).re =
              (j : ℝ) - (k : ℝ) := by
          have hweight :
              ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M0 + k : ℕ) : ℂ) =
                -(k : ℂ) := by
            calc
              ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M0 + k : ℕ) : ℂ)
                  = (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) -
                    (k : ℂ) := by
                      push_cast
                      ring
              _ = -(k : ℂ) := by rw [hzero, zero_sub]
          rw [hweight]
          simp
          ring
        rw [hrewrite]
        linarith
      have hΦ_mem' :
          Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
            ((M0 + k : ℕ) : ℂ)) := by
        rw [← hkval]
        exact hΦ_mem
      obtain ⟨_hland_ne', hland_mem, _hland_eig⟩ :=
        raise_iterate_ne_zero (V := V) (N := N) (J := J) (lam := μ) k
          hΦ_ne hΦ_mem' hΦ_eig hneg
      have hsector_pf' : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M0)) (μ : ℂ)) ≤ 1 := by
        rw [hM0def]
        exact h_sector_pf
      have hΦ0_mem' : Φ0 ∈
          magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) := by
        rw [hM0def]
        exact hΦ0_mem
      obtain ⟨hland_ne, hland_cas⟩ :=
        heisenbergHamiltonianS_totalSpinSSquared_mulVec_raise_landed_eq_zero_of_sector_pf
          (V := V) (N := N) J M0 k μ
          hΦ0_ne hΦ0_eig hΦ0_mem' hΦ0_cas hΦ_ne hΦ_mem' hΦ_eig hneg hsector_pf'
      have hland_mem_zero :
          (totalSpinSOpPlus V N ^ k).mulVec Φ ∈ magSubspaceS V N 0 := by
        have hweight0 :
            ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M0 + k : ℕ) : ℂ) + (k : ℂ) =
              0 := by
          calc
            ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M0 + k : ℕ) : ℂ) + (k : ℂ)
                = ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ) := by
                  push_cast
                  ring
            _ = 0 := hzero
        rwa [← hweight0]
      exact not_totalSpinSOpPlus_pow_mulVec_ne_zero_of_zero_casimir_zero_magSubspaceS
        (V := V) (N := N) k hk_pos hland_ne hland_mem_zero hland_cas
  exact lt_of_le_of_ne hle hne

end LatticeSystem.Quantum
