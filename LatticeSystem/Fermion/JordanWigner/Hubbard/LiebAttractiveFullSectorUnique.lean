import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveFullSectorSU2Algebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedUniqueness
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSingletGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionTotalSpinCasimirCharges
import LatticeSystem.Math.InvariantSubmoduleEigenvector
import LatticeSystem.Math.AngularMomentum.SpinHalfSector
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# The full `Ne`-electron ground eigenspace is the balanced singlet (Tasaki §10.2.1, Theorem 10.2)

Final structural piece of the Lieb-attractive-Hubbard singlet theorem (Tasaki Theorem 10.2).  The
balanced (`Ŝ³ = 0`) results already deliver, on the balanced ground eigenspace, both `finrank ≤ 1`
(`balanced_ground_eigenspace_finrank_le_one`) and the singlet property
(`balancedGround_totalSpinSquared_eigenvalue_zero`).  Here we lift these to the **whole**
`Ne`-electron sector: the full-sector ground eigenspace

`G_full := (Ĥ = E_full) ⊓ (N̂ = Ne)`   (`attractiveHubbardFullSectorGround`)

is contained in the balanced ground eigenspace, hence is `≤ 1`-dimensional and a spin singlet.

## The argument (single-operator `Ŝ³` spectral route)

`Ŝ³` (`fermionTotalSpinZ`) commutes with `Ĥ` and `N̂`, so it preserves `G_full`; and its eigenspaces
span the whole space (it is diagonal on the computational basis).  Hence `G_full` decomposes into
its `Ŝ³` weight blocks, `G_full = ⨆ μ, G_full ⊓ eigenspace Ŝ³ μ`
(`Submodule.eq_iSup_inf_genEigenspace`, the mirror of the t-J weight decomposition
`tJ_groundSubmodule_eq_iSup_inf_eigenspace`).  Every nonzero-weight block is trivial:

* Diagonalising the Casimir `Ŝ²` (`fermionTotalSpinSquared`) inside a weight-`μ` block
  (`exists_eigenvector_in_invariant_submodule`) yields a joint
  `(Ĥ = E_full, N̂ = Ne, Ŝ³ = m, Ŝ² = λ)` eigenstate `χ ≠ 0` at weight `m ≠ 0`, with
  `λ = Jr(Jr+1)`, `Jr ≥ |m| > 0`.
* For even `Ne` the weight `m` is an integer (`N̂_↑ = Ne/2 + m ∈ ℕ`), so the SU(2) multiplet of `χ`
  (`ham_su2_multiplet_companion`, Theorem A.16) reaches a nonzero **weight-0** companion `Ψ` at the
  same energy `E_full` and — tracking `N̂` through the ladder — the same electron number `Ne`.
* `Ψ` is thus a nonzero balanced state at `E_full = E_bal`
  (`attractiveHubbard_balanced_energy_eq_number_sector`), so it lies in `balancedGroundEigenspace`
  and by `balancedGround_totalSpinSquared_eigenvalue_zero` is a singlet, `Ŝ² Ψ = 0`.  But
  `Ŝ² Ψ = λ Ψ` with `λ = Jr(Jr+1) > 0` and `Ψ ≠ 0` — a contradiction.  Hence the weight-`μ` block
  is `⊥`.

Therefore `G_full ⊆ (Ŝ³ = 0)`; combined with `N̂ = Ne = 2k` (`attractiveHubbard_up_down_...`), that
is `N̂_↑ = N̂_↓ = k`, i.e. `G_full ⊆ balancedGroundEigenspace`, giving `finrank G_full ≤ 1` and the
singlet property.

## Main results

* `attractiveHubbardFullSectorGround` — the full-`Ne`-sector ground eigenspace
  `(Ĥ = E_full) ⊓ (N̂ = Ne)`.
* `attractiveHubbardFullSectorGround_le_balanced` — `G_full ≤ balancedGroundEigenspace`
  (for `Ne = 2k`).
* `attractiveHubbardFullSectorGround_unique_singlet` — **the milestone package:** `G_full` contains
  a nonzero vector, has `finrank ℂ ≤ 1`, and every nonzero member is a spin singlet `Ŝ² = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2), §10.2.4; Appendix A.3.2 Theorems A.16/A.17; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## The Cartesian total-spin Casimir identity and positive semidefiniteness -/

/-- **The Casimir as a Cartesian square sum:** `(Ŝ_tot)² = (Ŝ⁽¹⁾)² + (Ŝ⁽²⁾)² + (Ŝ³)²`.  With
`Ŝ⁽¹⁾ = ½(Ŝ⁺+Ŝ⁻)`, `Ŝ⁽²⁾ = −(i/2)(Ŝ⁺−Ŝ⁻)` one has `(Ŝ⁽¹⁾)² + (Ŝ⁽²⁾)² = ½(Ŝ⁺Ŝ⁻+Ŝ⁻Ŝ⁺)`, and the
ladder commutator `Ŝ⁺Ŝ⁻ − Ŝ⁻Ŝ⁺ = 2Ŝ³` reconciles this with the Casimir definition
`Ŝ⁻Ŝ⁺ + Ŝ³(Ŝ³+1)`.  This is the bridge between the generic angular-momentum engine's Casimir
`J1²+J2²+J3²` and the physical total-spin operator `fermionTotalSpinSquared`. -/
theorem fermionTotalSpinSquared_eq_cartesianSqSum (N : ℕ) :
    fermionTotalSpinSquared N = tJTotalSpinOne N * tJTotalSpinOne N
      + tJTotalSpinTwo N * tJTotalSpinTwo N + fermionTotalSpinZ N * fermionTotalSpinZ N := by
  have e1 : tJTotalSpinOne N * tJTotalSpinOne N = ((1 / 4 : ℂ))
      • ((fermionTotalSpinPlus N + fermionTotalSpinMinus N)
        * (fermionTotalSpinPlus N + fermionTotalSpinMinus N)) := by
    rw [tJTotalSpinOne, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    norm_num
  have e2 : tJTotalSpinTwo N * tJTotalSpinTwo N = (-(1 / 4 : ℂ))
      • ((fermionTotalSpinPlus N - fermionTotalSpinMinus N)
        * (fermionTotalSpinPlus N - fermionTotalSpinMinus N)) := by
    rw [tJTotalSpinTwo, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [neg_mul_neg, div_mul_div_comm, Complex.I_mul_I]
    norm_num
  have hsum : tJTotalSpinOne N * tJTotalSpinOne N + tJTotalSpinTwo N * tJTotalSpinTwo N
      = (1 / 2 : ℂ) • (fermionTotalSpinPlus N * fermionTotalSpinMinus N
        + fermionTotalSpinMinus N * fermionTotalSpinPlus N) := by
    rw [e1, e2]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
    module
  have hPMeq : fermionTotalSpinPlus N * fermionTotalSpinMinus N
      = fermionTotalSpinMinus N * fermionTotalSpinPlus N + (2 : ℂ) • fermionTotalSpinZ N := by
    have h := fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N
    rw [sub_eq_iff_eq_add] at h
    rw [h]; module
  rw [fermionTotalSpinSquared, hsum, hPMeq, mul_add, mul_one]
  module

/-- **The total-spin Casimir is positive semidefinite.**  Writing `(Ŝ_tot)² = J1²+J2²+J3²` with each
Cartesian component `Jα` self-adjoint (`Jα² = JαᴴJα`), the Casimir is a sum `∑ JαᴴJα` of positive
semidefinite matrices. -/
theorem fermionTotalSpinSquared_posSemidef (N : ℕ) :
    (fermionTotalSpinSquared N).PosSemidef := by
  rw [fermionTotalSpinSquared_eq_cartesianSqSum]
  have h1 := (tJTotalSpinOne_isHermitian N).eq
  have h2 := (tJTotalSpinTwo_isHermitian N).eq
  have h3 := (fermionTotalSpinZ_isHermitian N).eq
  rw [show tJTotalSpinOne N * tJTotalSpinOne N + tJTotalSpinTwo N * tJTotalSpinTwo N
      + fermionTotalSpinZ N * fermionTotalSpinZ N
      = (tJTotalSpinOne N)ᴴ * tJTotalSpinOne N
        + ((tJTotalSpinTwo N)ᴴ * tJTotalSpinTwo N
          + (fermionTotalSpinZ N)ᴴ * fermionTotalSpinZ N) by rw [h1, h2, h3]; abel]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).add
    ((Matrix.posSemidef_conjTranspose_mul_self _).add
      (Matrix.posSemidef_conjTranspose_mul_self _))

/-! ## The total electron number commutes with the Cartesian generators -/

/-- `N̂` commutes with `Ŝ⁽¹⁾_tot = ½(Ŝ⁺+Ŝ⁻)` (both `Ŝ⁺` and `Ŝ⁻` conserve the electron number). -/
theorem fermionTotalNumber_mul_tJTotalSpinOne (N : ℕ) :
    fermionTotalNumber (2 * N + 1) * tJTotalSpinOne N
      = tJTotalSpinOne N * fermionTotalNumber (2 * N + 1) := by
  have hP := (fermionTotalSpinPlus_commute_fermionTotalNumber N).symm.eq
  have hM := (fermionTotalSpinMinus_commute_fermionTotalNumber N).symm.eq
  rw [tJTotalSpinOne, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hP, hM]

/-- `N̂` commutes with `Ŝ⁽²⁾_tot = −(i/2)(Ŝ⁺−Ŝ⁻)`. -/
theorem fermionTotalNumber_mul_tJTotalSpinTwo (N : ℕ) :
    fermionTotalNumber (2 * N + 1) * tJTotalSpinTwo N
      = tJTotalSpinTwo N * fermionTotalNumber (2 * N + 1) := by
  have hP := (fermionTotalSpinPlus_commute_fermionTotalNumber N).symm.eq
  have hM := (fermionTotalSpinMinus_commute_fermionTotalNumber N).symm.eq
  rw [tJTotalSpinTwo, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hP, hM]

/-! ## A commuting operator preserves an eigenspace -/

/-- If `A` commutes with `B` then `A` maps each `B`-eigenspace into itself: from `B x = e x` and
`A B = B A` one gets `B (A x) = e (A x)`. -/
private theorem mulVec_mem_eigenspace_of_commute {n : Type*} [Fintype n]
    {A B : Matrix n n ℂ} (hAB : Commute A B) {e : ℂ} {x : n → ℂ}
    (hx : x ∈ Module.End.eigenspace B.mulVecLin e) :
    A.mulVec x ∈ Module.End.eigenspace B.mulVecLin e := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hx ⊢
  rw [Matrix.mulVec_mulVec, ← hAB.eq, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

/-! ## The full `Ne`-sector ground eigenspace -/

/-- **The full `Ne`-electron ground eigenspace** of the attractive Hubbard Hamiltonian: the
`ℂ`-subspace of configuration vectors that are simultaneously `Ĥ`-eigenvectors at the
number-sector-compression minimum energy `E_full` and `N̂`-eigenvectors at eigenvalue `Ne`. -/
noncomputable def attractiveHubbardFullSectorGround (N Ne : ℕ)
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (attractiveHubbardHamiltonian N T U).mulVecLin
      ((hermitianMinEigenvalue (configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
        (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) : ℝ) : ℂ)
    ⊓ Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ)

/-- Membership in the full-sector ground eigenspace unfolds to the two eigenvector relations
`Ĥ v = E_full v` and `N̂ v = Ne v`. -/
theorem mem_attractiveHubbardFullSectorGround_iff (Ne : ℕ)
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    v ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm ↔
      (attractiveHubbardHamiltonian N T U).mulVec v
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardNumberSectorPred N Ne)
              (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) : ℝ) : ℂ) • v
        ∧ (fermionTotalNumber (2 * N + 1)).mulVec v = (Ne : ℂ) • v := by
  rw [attractiveHubbardFullSectorGround, Submodule.mem_inf, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]

/-- **`Ŝ³` preserves the full-sector ground eigenspace** (it commutes with `Ĥ` and `N̂`), so
`G_full` is an invariant submodule of `Ŝ³` — the input to the weight decomposition. -/
theorem fermionTotalSpinZ_mulVec_mem_attractiveHubbardFullSectorGround (Ne : ℕ)
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm) :
    (fermionTotalSpinZ N).mulVec v ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm := by
  rw [attractiveHubbardFullSectorGround, Submodule.mem_inf] at hv ⊢
  obtain ⟨hH, hN⟩ := hv
  exact ⟨mulVec_mem_eigenspace_of_commute
      (fermionTotalSpinZ_commute_attractiveHubbardHamiltonian N T U) hH,
    mulVec_mem_eigenspace_of_commute (fermionTotalSpinZ_commute_fermionTotalNumber N) hN⟩

/-- **The full-sector ground eigenspace decomposes into `Ŝ³` weight blocks.**  `Ŝ³` preserves
`G_full` and its eigenspaces span `⊤`, so `G_full = ⨆ μ, G_full ⊓ eigenspace Ŝ³ μ`
(`Submodule.eq_iSup_inf_genEigenspace`). -/
theorem attractiveHubbardFullSectorGround_eq_iSup_inf_eigenspace (Ne : ℕ)
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    attractiveHubbardFullSectorGround N Ne T U hT_symm =
      ⨆ μ : ℂ, attractiveHubbardFullSectorGround N Ne T U hT_symm ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ := by
  have hinv : ∀ x ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm,
      (fermionTotalSpinZ N).mulVecLin x ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm := by
    intro x hx
    rw [Matrix.mulVecLin_apply]
    exact fermionTotalSpinZ_mulVec_mem_attractiveHubbardFullSectorGround Ne T U hT_symm hx
  have htop : ⨆ μ : ℂ,
      Module.End.genEigenspace (fermionTotalSpinZ N).mulVecLin μ 1 = ⊤ := by
    simpa only [Module.End.genEigenspace_one] using fermionTotalSpinZ_iSup_eigenspace_eq_top N
  simpa only [Module.End.genEigenspace_one] using
    Submodule.eq_iSup_inf_genEigenspace
      (p := attractiveHubbardFullSectorGround N Ne T U hT_symm)
      (f := (fermionTotalSpinZ N).mulVecLin) 1 hinv htop

/-! ## Every nonzero-weight block is trivial -/

/-- **The nonzero-weight `Ŝ³` blocks of `G_full` are trivial.**  For even `Ne = 2k` and `μ ≠ 0`, no
nonzero full-sector ground state has `Ŝ³ = μ`: the SU(2) multiplet of such a state (Theorem A.16)
would contain a nonzero **balanced** companion at the same energy with total spin `Jr ≥ |m| > 0`,
contradicting the balanced singlet theorem `balancedGround_totalSpinSquared_eigenvalue_zero`. -/
theorem attractiveHubbardFullSectorGround_inf_spinZ_eigenspace_eq_bot (k Ne : ℕ)
    (hNe : Ne = 2 * k) (hNe_even : Even Ne)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected) (μ : ℂ) (hμ : μ ≠ 0) :
    attractiveHubbardFullSectorGround N Ne T U hT_symm ⊓
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊥ := by
  classical
  set Efull : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardNumberSectorPred N Ne)
    (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) with hEfull
  set B := attractiveHubbardFullSectorGround N Ne T U hT_symm ⊓
    Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ with hBdef
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  -- `B` is a nonzero submodule invariant under the Casimir `Ŝ²`.
  have hBne : B ≠ ⊥ := (Submodule.ne_bot_iff B).mpr ⟨v, hv, hv0⟩
  have hBinv : B ≤ B.comap (fermionTotalSpinSquared N).mulVecLin := by
    intro x hx
    rw [hBdef, Submodule.mem_inf, attractiveHubbardFullSectorGround, Submodule.mem_inf] at hx
    obtain ⟨⟨hxH, hxN⟩, hxS3⟩ := hx
    rw [Submodule.mem_comap, hBdef, Submodule.mem_inf, attractiveHubbardFullSectorGround,
      Submodule.mem_inf]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rw [Matrix.mulVecLin_apply]
    · exact mulVec_mem_eigenspace_of_commute
        (fermionTotalSpinSquared_commute_attractiveHubbardHamiltonian N T U hT_symm) hxH
    · exact mulVec_mem_eigenspace_of_commute
        (fermionTotalSpinSquared_commute_fermionTotalNumber N) hxN
    · exact mulVec_mem_eigenspace_of_commute
        (fermionTotalSpinSquared_commute_fermionTotalSpinZ N) hxS3
  -- Diagonalise `Ŝ²` inside `B`: a joint `(Ĥ, N̂, Ŝ³, Ŝ²)` eigenstate `χ`.
  obtain ⟨lam, χ, hχB, hχ0, hχlam⟩ :=
    exists_eigenvector_in_invariant_submodule (fermionTotalSpinSquared N).mulVecLin B hBinv hBne
  rw [Matrix.mulVecLin_apply] at hχlam
  rw [hBdef, Submodule.mem_inf, attractiveHubbardFullSectorGround, Submodule.mem_inf] at hχB
  obtain ⟨⟨hχH, hχN⟩, hχS3⟩ := hχB
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hχH hχN hχS3
  -- The weight `μ` is real (`Ŝ³` Hermitian): `μ = m`, `m ≠ 0`.
  obtain ⟨m, hm⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (fermionTotalSpinZ_isHermitian N) hχ0 hχS3
  have hm0 : m ≠ 0 := fun h => hμ (by rw [← hm, h, Complex.ofReal_zero])
  have hχ3 : (fermionTotalSpinZ N).mulVec χ = (m : ℂ) • χ := by rw [hχS3, hm]
  -- The Casimir eigenvalue `lam` is real and nonnegative: `lam = Jr(Jr+1)`, `Jr ≥ 0`.
  obtain ⟨lr, hlr⟩ := isHermitian_mulVec_eigenvalue_eq_ofReal
    (fermionTotalSpinSquared_isHermitian N) hχ0 hχlam
  have hχlr : (fermionTotalSpinSquared N).mulVec χ = (lr : ℂ) • χ := by rw [hχlam, hlr]
  have hlr_nonneg : 0 ≤ lr :=
    Matrix.posSemidef_mulVec_eigenvalue_nonneg (fermionTotalSpinSquared_posSemidef N) hχ0 hχlr
  set Jr : ℝ := (Real.sqrt (1 + 4 * lr) - 1) / 2 with hJr_def
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (1 + 4 * lr) := by
    have h1 : Real.sqrt 1 ≤ Real.sqrt (1 + 4 * lr) := Real.sqrt_le_sqrt (by linarith)
    simpa using h1
  have hJr_nonneg : 0 ≤ Jr := by rw [hJr_def]; linarith [hsqrt1]
  have hJr_eq : Jr * (Jr + 1) = lr := by
    have hs : Real.sqrt (1 + 4 * lr) ^ 2 = 1 + 4 * lr := Real.sq_sqrt (by linarith)
    rw [hJr_def]; nlinarith [hs]
  -- SU(2) engine inputs for the plain Cartesian generators.
  have hsq_engine : (tJTotalSpinOne N * tJTotalSpinOne N + tJTotalSpinTwo N * tJTotalSpinTwo N
      + fermionTotalSpinZ N * fermionTotalSpinZ N).mulVec χ = ((Jr * (Jr + 1) : ℝ) : ℂ) • χ := by
    rw [← fermionTotalSpinSquared_eq_cartesianSqSum, hχlr,
      show ((Jr * (Jr + 1) : ℝ) : ℂ) = (lr : ℂ) by rw [hJr_eq]]
  -- The seed weight `m` is a nonzero integer (even-`Ne` sector): `Jr` is a nonneg integer too.
  obtain ⟨hmlb, hmub⟩ := angMom_abs_le_J (tJTotalSpinOne N) (tJTotalSpinTwo N)
    (fermionTotalSpinZ N) (tJTotalSpinOne_isHermitian N) (tJTotalSpinTwo_isHermitian N)
    (tJTotalSpin_su2_12 N) hχ0 hJr_nonneg hsq_engine hχ3
  have hJr_pos : 0 < Jr := by rcases lt_or_gt_of_ne hm0 with h | h <;> linarith
  obtain ⟨hχup, _⟩ := attractiveHubbard_up_down_mulVec_of_number_spinZ Ne (m : ℂ) hχN hχ3
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hχ0
  rw [Pi.zero_apply] at hw
  have hupcount : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ))
      = (Ne : ℂ) / 2 + (m : ℂ) := by
    by_contra hne
    exact hw (mulVec_apply_eq_zero_of_upNumber_ne χ ((Ne : ℂ) / 2 + (m : ℂ)) hχup w hne)
  set upc : ℕ := ∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val with hupc
  have hupcast : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) = (upc : ℂ) := by
    rw [hupc]; push_cast; rfl
  set mz : ℤ := (upc : ℤ) - (k : ℤ) with hmz
  have hm_int : (mz : ℝ) = m := by
    have hkNe : (Ne : ℂ) / 2 = (k : ℂ) := by rw [hNe]; push_cast; ring
    rw [hupcast, hkNe] at hupcount
    have hc : ((mz : ℤ) : ℂ) = (m : ℂ) := by rw [hmz]; push_cast; linear_combination hupcount
    exact_mod_cast hc
  obtain ⟨t, ht⟩ := angMom_sub_mem_nat (tJTotalSpinOne N) (tJTotalSpinTwo N)
    (fermionTotalSpinZ N) (tJTotalSpinOne_isHermitian N) (tJTotalSpinTwo_isHermitian N)
    (tJTotalSpin_su2_12 N) (tJTotalSpin_su2_23 N) (tJTotalSpin_su2_31 N) hχ0 hJr_nonneg
    hsq_engine hχ3
  -- `Jr = mz + t` is a nonnegative integer; take the weight-lowering count `kmult = Jr`.
  set kmz : ℤ := mz + (t : ℤ) with hkmz
  have hJr_kmz : Jr = (kmz : ℝ) := by rw [hkmz]; push_cast; rw [hm_int]; linarith [ht]
  have hkmz_nonneg : 0 ≤ kmz := by
    have : (0 : ℝ) ≤ (kmz : ℝ) := by rw [← hJr_kmz]; exact hJr_nonneg
    exact_mod_cast this
  set kmult : ℕ := kmz.toNat with hkmult
  have hkmult_cast : (kmult : ℝ) = Jr := by
    rw [hJr_kmz, hkmult]; exact_mod_cast Int.toNat_of_nonneg hkmz_nonneg
  -- The weight-0 companion `Ψ` from the SU(2) multiplet, tracking `Ĥ` and `N̂`.
  obtain ⟨Ψ, hΨ0, hΨsq, hΨ3, hclause⟩ :=
    ham_su2_multiplet_companion (tJTotalSpinOne N) (tJTotalSpinTwo N) (fermionTotalSpinZ N)
      (tJTotalSpinOne_isHermitian N) (tJTotalSpinTwo_isHermitian N) (tJTotalSpin_su2_12 N)
      (tJTotalSpin_su2_23 N) (tJTotalSpin_su2_31 N) hχ0 hJr_nonneg hsq_engine hχ3 kmult
      (by rw [hkmult_cast]; linarith)
  have hΨ3zero : (fermionTotalSpinZ N).mulVec Ψ = (0 : ℂ) • Ψ := by
    rw [hΨ3, show ((Jr - (kmult : ℝ) : ℝ) : ℂ) = 0 by rw [hkmult_cast]; push_cast; ring]
  have hΨH : (attractiveHubbardHamiltonian N T U).mulVec Ψ = (Efull : ℂ) • Ψ :=
    hclause (attractiveHubbardHamiltonian N T U) (Efull : ℂ)
      (attractiveHubbardHamiltonian_mul_tJTotalSpinOne T U hT_symm)
      (attractiveHubbardHamiltonian_mul_tJTotalSpinTwo T U hT_symm) hχH
  have hΨN : (fermionTotalNumber (2 * N + 1)).mulVec Ψ = (Ne : ℂ) • Ψ :=
    hclause (fermionTotalNumber (2 * N + 1)) (Ne : ℂ)
      (fermionTotalNumber_mul_tJTotalSpinOne N) (fermionTotalNumber_mul_tJTotalSpinTwo N) hχN
  -- `Ψ` is balanced: `N̂_↑ = N̂_↓ = k`.
  obtain ⟨hΨup, hΨdn⟩ := attractiveHubbard_up_down_mulVec_of_number_spinZ Ne (0 : ℂ) hΨN hΨ3zero
  have hk : (Ne : ℂ) / 2 + 0 = (k : ℂ) := by rw [hNe]; push_cast; ring
  have hk' : (Ne : ℂ) / 2 - 0 = (k : ℂ) := by rw [hNe]; push_cast; ring
  rw [hk] at hΨup
  rw [hk'] at hΨdn
  -- `Ψ` is a balanced ground at `E_bal = E_full`, hence a singlet.
  have hEbal : hermitianMinEigenvalue (configSectorCompress_isHermitian
      (hubbardBalancedSectorPred N k) (attractiveHubbardHamiltonian_isHermitian T U hT_symm))
      = Efull :=
    attractiveHubbard_balanced_energy_eq_number_sector k Ne hNe hNe_even T U hT_symm
  have hΨmem : Ψ ∈ balancedGroundEigenspace k T U hT_symm :=
    (mem_balancedGroundEigenspace_iff k T U hT_symm Ψ).mpr
      ⟨by rw [hEbal]; exact hΨH, hΨup, hΨdn⟩
  have hΨsinglet := balancedGround_totalSpinSquared_eigenvalue_zero k T U hT_symm hU_pos hT_conn
    hΨmem hΨ0
  -- But `Ŝ² Ψ = lr Ψ` with `lr = Jr(Jr+1) > 0`, contradicting the singlet.
  have hΨcas : (fermionTotalSpinSquared N).mulVec Ψ = (lr : ℂ) • Ψ := by
    rw [fermionTotalSpinSquared_eq_cartesianSqSum, hΨsq,
      show ((Jr * (Jr + 1) : ℝ) : ℂ) = (lr : ℂ) by rw [hJr_eq]]
  rw [hΨsinglet] at hΨcas
  have hlr_pos : 0 < lr := by rw [← hJr_eq]; positivity
  rcases smul_eq_zero.mp hΨcas.symm with hlr0 | hΨ0'
  · exact absurd (Complex.ofReal_eq_zero.mp hlr0) (ne_of_gt hlr_pos)
  · exact hΨ0 hΨ0'

/-! ## The full-sector ground eigenspace is the balanced singlet -/

/-- **`G_full` has zero total `Ŝ³`.**  Every full-sector ground state has `Ŝ³ = 0`: the `Ŝ³` weight
decomposition of `G_full` has all nonzero-weight blocks trivial
(`attractiveHubbardFullSectorGround_inf_spinZ_eigenspace_eq_bot`). -/
theorem attractiveHubbardFullSectorGround_spinZ_eq_zero (k Ne : ℕ)
    (hNe : Ne = 2 * k) (hNe_even : Even Ne)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm) :
    (fermionTotalSpinZ N).mulVec v = 0 := by
  have hle : attractiveHubbardFullSectorGround N Ne T U hT_symm ≤
      Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (0 : ℂ) := by
    conv_lhs => rw [attractiveHubbardFullSectorGround_eq_iSup_inf_eigenspace Ne T U hT_symm]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · subst hμ; exact inf_le_right
    · rw [attractiveHubbardFullSectorGround_inf_spinZ_eigenspace_eq_bot k Ne hNe hNe_even T U
        hT_symm hU_pos hT_conn μ hμ]
      exact bot_le
  have hmem := hle hv
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, zero_smul] at hmem
  exact hmem

/-- **`G_full ≤ balancedGroundEigenspace`.**  Every full-sector ground state has `Ŝ³ = 0`, hence (on
the `N̂ = Ne = 2k` sector) `N̂_↑ = N̂_↓ = k`, and its energy `E_full` equals the balanced minimum
`E_bal`; so it is a balanced ground state. -/
theorem attractiveHubbardFullSectorGround_le_balanced (k Ne : ℕ)
    (hNe : Ne = 2 * k) (hNe_even : Even Ne)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected) :
    attractiveHubbardFullSectorGround N Ne T U hT_symm ≤
      balancedGroundEigenspace k T U hT_symm := by
  intro v hv
  have hS3 := attractiveHubbardFullSectorGround_spinZ_eq_zero k Ne hNe hNe_even T U hT_symm
    hU_pos hT_conn hv
  obtain ⟨hH, hN⟩ := (mem_attractiveHubbardFullSectorGround_iff Ne T U hT_symm v).mp hv
  have hS3' : (fermionTotalSpinZ N).mulVec v = (0 : ℂ) • v := by rw [hS3, zero_smul]
  obtain ⟨hup, hdn⟩ := attractiveHubbard_up_down_mulVec_of_number_spinZ Ne (0 : ℂ) hN hS3'
  have hk : (Ne : ℂ) / 2 + 0 = (k : ℂ) := by rw [hNe]; push_cast; ring
  have hk' : (Ne : ℂ) / 2 - 0 = (k : ℂ) := by rw [hNe]; push_cast; ring
  rw [hk] at hup
  rw [hk'] at hdn
  have hEbal : hermitianMinEigenvalue (configSectorCompress_isHermitian
      (hubbardBalancedSectorPred N k) (attractiveHubbardHamiltonian_isHermitian T U hT_symm))
      = hermitianMinEigenvalue (configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
        (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) :=
    attractiveHubbard_balanced_energy_eq_number_sector k Ne hNe hNe_even T U hT_symm
  exact (mem_balancedGroundEigenspace_iff k T U hT_symm v).mpr ⟨by rw [hEbal]; exact hH, hup, hdn⟩

/-- **The full-sector ground eigenspace is the balanced singlet (Tasaki §10.2.1 Theorem 10.2).**
For an attractive Hubbard model with connected symmetric real hopping `T`, strictly attractive
`U > 0`, and even electron number `Ne = 2k`: the full `Ne`-electron ground eigenspace `G_full` is
nonempty, at most one-dimensional over `ℂ`, and every nonzero member is a spin singlet
`(Ŝ_tot)² = 0`.  This is the plain-space uniqueness+singlet milestone feeding the Euclidean
`IsUniqueGroundStateOn` assembly.

Proof: `G_full ≤ balancedGroundEigenspace` (`attractiveHubbardFullSectorGround_le_balanced`), so the
finrank bound and singlet property transfer from `balanced_ground_eigenspace_finrank_le_one` and
`balancedGround_totalSpinSquared_eigenvalue_zero`; the nonempty witness is the balanced ground state
`exists_attractive_balanced_ground`, which lies in `G_full`. -/
theorem attractiveHubbardFullSectorGround_unique_singlet (k Ne : ℕ)
    (hNe : Ne = 2 * k) (hNe_even : Even Ne)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected) :
    (∃ φ, φ ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm ∧ φ ≠ 0) ∧
      Module.finrank ℂ (attractiveHubbardFullSectorGround N Ne T U hT_symm) ≤ 1 ∧
      (∀ φ ∈ attractiveHubbardFullSectorGround N Ne T U hT_symm, φ ≠ 0 →
        (fermionTotalSpinSquared N).mulVec φ = 0) := by
  have hle := attractiveHubbardFullSectorGround_le_balanced k Ne hNe hNe_even T U hT_symm
    hU_pos hT_conn
  refine ⟨?_, ?_, ?_⟩
  · -- The balanced ground state lies in `G_full`.
    obtain ⟨φ, hφ0, hφup, hφdn, hφeig⟩ := exists_attractive_balanced_ground k T U hT_symm
    refine ⟨φ, ?_, hφ0⟩
    have hφN : (fermionTotalNumber (2 * N + 1)).mulVec φ = (Ne : ℂ) • φ := by
      rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec, hφup, hφdn, ← add_smul,
        show (k : ℂ) + (k : ℂ) = (Ne : ℂ) by rw [hNe]; push_cast; ring]
    have hEbal := attractiveHubbard_balanced_energy_eq_number_sector k Ne hNe hNe_even T U hT_symm
    exact (mem_attractiveHubbardFullSectorGround_iff Ne T U hT_symm φ).mpr
      ⟨by rw [← hEbal]; exact hφeig, hφN⟩
  · calc Module.finrank ℂ (attractiveHubbardFullSectorGround N Ne T U hT_symm)
        ≤ Module.finrank ℂ (balancedGroundEigenspace k T U hT_symm) :=
          Submodule.finrank_mono hle
      _ ≤ 1 := balanced_ground_eigenspace_finrank_le_one k T U hT_symm hU_pos hT_conn
  · intro φ hφ hφ0
    exact balancedGround_totalSpinSquared_eigenvalue_zero k T U hT_symm hU_pos hT_conn (hle hφ) hφ0

end LatticeSystem.Fermion
