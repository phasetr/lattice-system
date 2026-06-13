import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandOperators

/-!
# General flat-band ground-state annihilation and spectral decomposition (Tasaki §11.3.4)

Split out of `GeneralFlatBandOperators.lean` (build-speed refactor, 20-PR cadence): the
ground-state consequences of the flat-band frustration-free structure and the spectral
`ker T ⊕ range T` decomposition.  For a positive-semidefinite hopping `T` and `U > 0`, a flat-band
Hubbard ground state has no double occupancy and is annihilated by `Ĉ_σ(w)` for every `w` in the
range of `T` (the operator-algebraic premise of eq. (11.3.46)); the Hermitian spectral theorem then
splits the single-particle space into the flat band (`ker T`, zero eigenvalues) and its
orthocomplement (`range T`, nonzero eigenvalues).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.46).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {M : ℕ}

open scoped ComplexOrder in
/-- **No double occupancy for a general flat-band ground state** (Tasaki eq. (11.3.12), general
form): for a positive-semidefinite hopping `T` and `U > 0`, any vector with vanishing Hamiltonian
expectation satisfies `n̂_{x↑} n̂_{x↓} v = 0` at every site `x`.  The Rayleigh expectation splits
into the (PSD) kinetic part and `U` times the summed (PSD) double-occupancy expectations; all are
nonnegative and sum to zero, so each double-occupancy term vanishes, and the PSD kernel kills the
operator on `v`. -/
theorem generalFlatBand_groundState_doubleOccupancy_mulVec_eq_zero (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (x : Fin (M + 1)) :
    (hubbardDoubleOccupancy M x).mulVec v = 0 := by
  have hkin_nonneg : 0 ≤ rayleighOnVec (hubbardKinetic M T) v :=
    (hubbardKinetic_posSemidef_of_posSemidef M T hT).re_dotProduct_nonneg v
  have hint_nonneg : ∀ x' : Fin (M + 1),
      0 ≤ rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    fun x' => (hubbardDoubleOccupancy_posSemidef M x').re_dotProduct_nonneg v
  have hdec := hubbardHamiltonian_rayleighOnVec_decompose_general M T U v
  rw [hv] at hdec
  have hInt : (0 : ℝ) ≤ ∑ x' : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    Finset.sum_nonneg (fun x' _ => hint_nonneg x')
  have hIntZero : (∑ x' : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x') v) = 0 := by
    nlinarith [mul_nonneg hU.le hInt, hkin_nonneg, hdec]
  have hterm : rayleighOnVec (hubbardDoubleOccupancy M x) v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x' _ => hint_nonneg x')).mp hIntZero x
      (Finset.mem_univ x)
  exact posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero
    (hubbardDoubleOccupancy_posSemidef M x) hterm

open scoped ComplexOrder in
/-- **`ĉ_{x↓} ĉ_{x↑} v = 0`** for any general flat-band ground state `v` (the operator form of the
no-double-occupancy condition used in eq. (11.3.48)): from `n̂_{x↑} n̂_{x↓} v = 0` and the Gram
identity, by the positive-semidefinite kernel. -/
theorem generalFlatBand_groundState_doubleAnnihilation_mulVec_eq_zero (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (x : Fin (M + 1)) :
    (generalCDownUp M x).mulVec v = 0 := by
  have hdo := generalFlatBand_groundState_doubleOccupancy_mulVec_eq_zero M T U hT hU hv x
  rw [hubbardDoubleOccupancy_eq_conjTranspose_mul_self_general] at hdo
  exact conjTranspose_mul_self_mulVec_eq_zero hdo

open scoped ComplexOrder in
/-- **`ĉ_{x↓} ĉ_{x↑} Φ = 0` for any vector in the ground submodule**: the ground submodule sits
in the kernel of `Ĥ`, so its Rayleigh expectation vanishes and the no-double-occupancy kill
applies (Tasaki §11.3.4 — the eq.-(11.3.48) input phrased directly for ground states). -/
theorem generalCDownUp_mulVec_eq_zero_of_mem_groundSubmodule
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (x : Fin (M + 1)) :
    (generalCDownUp M x).mulVec Φ = 0 := by
  have hker : (hubbardHamiltonian M T (U : ℂ)).mulVec Φ = 0 := by
    have h := (Submodule.mem_inf.mp hΦ).1
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    exact h
  have hray : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) Φ = 0 := by
    rw [rayleighOnVec, hker, dotProduct_zero, Complex.zero_re]
  exact generalFlatBand_groundState_doubleAnnihilation_mulVec_eq_zero M T U hT hU hray x

/-- **Gram-sum factorization of the kinetic operator** for a factored hopping `T = Cᴴ·C`:
`hubbardKinetic M (Cᴴ·C) = Σ_σ Σ_k (Ĉ_σ(C_k))ᴴ (Ĉ_σ(C_k))`, the rows `C_k` of `C` smeared into
mode operators.  The general-`C` form of the kinetic-PSD factorization (no Hermitian assumption on
`C`); the engine for "ground state ⟹ annihilated by every row mode" toward eq. (11.3.46). -/
theorem hubbardKinetic_conjTranspose_mul_self_eq_gram_sum (M : ℕ)
    (C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) :
    hubbardKinetic M (Cᴴ * C)
      = ∑ σ : Fin 2, ∑ k : Fin (M + 1),
          (spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
            spinfulAnnihilationFromVector M (fun j => C k j) σ := by
  unfold hubbardKinetic
  refine Finset.sum_congr rfl fun σ _ => ?_
  symm
  calc ∑ k : Fin (M + 1),
          (spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
            spinfulAnnihilationFromVector M (fun j => C k j) σ
      = ∑ k : Fin (M + 1), ∑ i : Fin (M + 1), ∑ j : Fin (M + 1),
          (star (C k i) * C k j) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [spinfulAnnihilationFromVector_conjTranspose,
          spinfulCreation_mul_annihilationFromVector_expand]
        simp only [Pi.star_apply]
    _ = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ k : Fin (M + 1),
          (star (C k i) * C k j) •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (Cᴴ * C) i j •
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_smul]
        congr 1

open scoped ComplexOrder in
/-- **Ground-state annihilation by every row mode**: if the kinetic Rayleigh expectation of `v`
vanishes (for a factored hopping `T = Cᴴ·C`), then each smeared annihilation `Ĉ_σ(C_k) v = 0`.
Each Gram term `(Ĉ_σ(C_k))ᴴ Ĉ_σ(C_k)` is PSD with nonnegative expectation; they sum to zero, so
each vanishes, and the PSD kernel kills `Ĉ_σ(C_k) v`.  This is the operative consequence of the
flat-band ground condition toward eq. (11.3.46). -/
theorem spinfulAnnihilationFromVector_mulVec_eq_zero_of_kinetic_rayleigh_zero (M : ℕ)
    (C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (h : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0) (k : Fin (M + 1)) (σ : Fin 2) :
    (spinfulAnnihilationFromVector M (fun j => C k j) σ).mulVec v = 0 := by
  have hnonneg : ∀ (σ' : Fin 2) (k' : Fin (M + 1)),
      0 ≤ rayleighOnVec
        ((spinfulAnnihilationFromVector M (fun j => C k' j) σ')ᴴ *
          spinfulAnnihilationFromVector M (fun j => C k' j) σ') v :=
    fun σ' k' => (Matrix.posSemidef_conjTranspose_mul_self _).re_dotProduct_nonneg v
  rw [hubbardKinetic_conjTranspose_mul_self_eq_gram_sum, rayleighOnVec_sum] at h
  simp only [rayleighOnVec_sum] at h
  have hσ : (∑ k' : Fin (M + 1), rayleighOnVec
      ((spinfulAnnihilationFromVector M (fun j => C k' j) σ)ᴴ *
        spinfulAnnihilationFromVector M (fun j => C k' j) σ) v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun σ' _ => Finset.sum_nonneg fun k' _ => hnonneg σ' k')).mp h σ (Finset.mem_univ σ)
  have hterm : rayleighOnVec
      ((spinfulAnnihilationFromVector M (fun j => C k j) σ)ᴴ *
        spinfulAnnihilationFromVector M (fun j => C k j) σ) v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k' _ => hnonneg σ k')).mp hσ k (Finset.mem_univ k)
  have hker := posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero
    (Matrix.posSemidef_conjTranspose_mul_self _) hterm
  exact conjTranspose_mul_self_mulVec_eq_zero hker

/-- `Ĉ_σ` is additive in its single-particle state: `Ĉ_σ(φ + ψ) = Ĉ_σ(φ) + Ĉ_σ(ψ)`. -/
theorem spinfulAnnihilationFromVector_add (M : ℕ) (φ ψ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (φ + ψ) σ
      = spinfulAnnihilationFromVector M φ σ + spinfulAnnihilationFromVector M ψ σ := by
  unfold spinfulAnnihilationFromVector
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.add_apply, add_smul]

/-- `Ĉ_σ` is homogeneous in its single-particle state: `Ĉ_σ(a • φ) = a • Ĉ_σ(φ)`. -/
theorem spinfulAnnihilationFromVector_smul (M : ℕ) (a : ℂ) (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (a • φ) σ = a • spinfulAnnihilationFromVector M φ σ := by
  unfold spinfulAnnihilationFromVector
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.smul_apply, smul_eq_mul, ← smul_smul]

/-- `Ĉ_σ(0) = 0`. -/
@[simp] theorem spinfulAnnihilationFromVector_zero (M : ℕ) (σ : Fin 2) :
    spinfulAnnihilationFromVector M (0 : Fin (M + 1) → ℂ) σ = 0 := by
  unfold spinfulAnnihilationFromVector
  exact Finset.sum_eq_zero fun x _ => by rw [Pi.zero_apply, zero_smul]

/-- **Annihilation extends to any linear combination of states**: if `Ĉ_σ(φ_i) v = 0` for every
`i` in a finite family, then `Ĉ_σ(Σ_i a_i φ_i) v = 0` for any coefficients `a_i`. -/
theorem spinfulAnnihilationFromVector_linearCombination_mulVec_eq_zero (M : ℕ) {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (φ : ι → Fin (M + 1) → ℂ) (σ : Fin 2)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (h : ∀ i ∈ s, (spinfulAnnihilationFromVector M (φ i) σ).mulVec v = 0) :
    (spinfulAnnihilationFromVector M (∑ i ∈ s, a i • φ i) σ).mulVec v = 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, spinfulAnnihilationFromVector_add,
      spinfulAnnihilationFromVector_smul, Matrix.add_mulVec, Matrix.smul_mulVec,
      h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), smul_zero, add_zero]

open scoped ComplexOrder in
/-- **A flat-band ground state is annihilated by every row-space mode**: for `T = Cᴴ·C` and a
vector with vanishing kinetic Rayleigh expectation, `Ĉ_σ(Σ_k a_k C_k) v = 0` for any coefficients
`a` — i.e. `Ĉ_σ(w) v = 0` for every `w` in the row span of `C` (which is the range of `T`, the
orthocomplement of the flat band).  Combines the per-row kill with the linearity of `Ĉ_σ`. -/
theorem spinfulAnnihilation_rowSpan_mulVec_eq_zero (M : ℕ)
    (C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (h : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0) (σ : Fin 2)
    (a : Fin (M + 1) → ℂ) :
    (spinfulAnnihilationFromVector M (∑ k : Fin (M + 1), a k • (fun j => C k j)) σ).mulVec v = 0 :=
  spinfulAnnihilationFromVector_linearCombination_mulVec_eq_zero M Finset.univ a
    (fun k => fun j => C k j) σ
    (fun k _ => spinfulAnnihilationFromVector_mulVec_eq_zero_of_kinetic_rayleigh_zero M C h k σ)

open scoped ComplexOrder in
/-- **The kinetic Rayleigh expectation vanishes on a flat-band ground state**: for `T` PSD and
`U > 0`, if the full Hamiltonian expectation is zero then so is the kinetic one (the kinetic and
the `U`-weighted double-occupancy parts are both nonnegative and sum to zero). -/
theorem hubbardKinetic_rayleigh_zero_of_groundState (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) :
    rayleighOnVec (hubbardKinetic M T) v = 0 := by
  have hkin_nonneg : 0 ≤ rayleighOnVec (hubbardKinetic M T) v :=
    (hubbardKinetic_posSemidef_of_posSemidef M T hT).re_dotProduct_nonneg v
  have hint_nonneg : ∀ x' : Fin (M + 1),
      0 ≤ rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    fun x' => (hubbardDoubleOccupancy_posSemidef M x').re_dotProduct_nonneg v
  have hInt : (0 : ℝ) ≤ ∑ x' : Fin (M + 1), rayleighOnVec (hubbardDoubleOccupancy M x') v :=
    Finset.sum_nonneg (fun x' _ => hint_nonneg x')
  have hdec := hubbardHamiltonian_rayleighOnVec_decompose_general M T U v
  rw [hv] at hdec
  nlinarith [mul_nonneg hU.le hInt, hkin_nonneg, hdec]

open scoped ComplexOrder in
/-- **A flat-band ground state is annihilated by every range-`T` mode** (the operative content of
eq. (11.3.46)): for `T` PSD and `U > 0`, any vector with vanishing Hamiltonian expectation is
killed by `Ĉ_σ(T_k)` summed against any coefficients — i.e. by `Ĉ_σ(w)` for every `w` in the
range of `T = (ker T)^⊥`.  Factoring `T = Cᴴ·C` (positive square root), the kinetic Rayleigh
vanishes, so each Gram mode kills `v`, and the row span of `C` is the range of `T`. -/
theorem spinfulAnnihilation_rangeT_mulVec_eq_zero_of_groundState (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (σ : Fin 2) :
    ∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ, T = Cᴴ * C ∧
      ∀ a : Fin (M + 1) → ℂ,
        (spinfulAnnihilationFromVector M (∑ k : Fin (M + 1), a k • (fun j => C k j)) σ).mulVec v
          = 0 := by
  obtain ⟨C, hC, hTC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hT
  have hTCH : T = Cᴴ * C := by rw [hTC, hC.isHermitian.eq]
  refine ⟨C, hTCH, fun a => ?_⟩
  have hkin : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0 := by
    rw [← hTCH]; exact hubbardKinetic_rayleigh_zero_of_groundState M T U hT hU hv
  exact spinfulAnnihilation_rowSpan_mulVec_eq_zero M C hkin σ a

/-- The Hamiltonian Rayleigh expectation vanishes on any ground-submodule vector (it lies in the
kernel of `Ĥ`). -/
theorem hamiltonian_rayleigh_zero_of_mem_groundSubmodule
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) Φ = 0 := by
  have hker : (hubbardHamiltonian M T (U : ℂ)).mulVec Φ = 0 := by
    have h := (Submodule.mem_inf.mp hΦ).1
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    exact h
  rw [rayleighOnVec, hker, dotProduct_zero, Complex.zero_re]

open scoped ComplexOrder in
/-- **A ground-submodule vector is annihilated by every range-`T` mode** (eq. (11.3.46) premise,
packaged for the ground submodule): factoring `T = Cᴴ·C`, every `Ĉ_σ(Σ a_k C_k)` kills `Φ`. -/
theorem spinfulAnnihilation_rangeT_mulVec_eq_zero_of_mem_groundSubmodule
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U)
    (σ : Fin 2) :
    ∃ C : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ, T = Cᴴ * C ∧
      ∀ a : Fin (M + 1) → ℂ,
        (spinfulAnnihilationFromVector M (∑ k : Fin (M + 1), a k • (fun j => C k j)) σ).mulVec Φ
          = 0 :=
  spinfulAnnihilation_rangeT_mulVec_eq_zero_of_groundState M T U hT hU
    (hamiltonian_rayleigh_zero_of_mem_groundSubmodule T U hΦ) σ

open scoped ComplexOrder in
/-- **A flat-band ground state is annihilated by `Ĉ_σ(conj w)` for every `w ∈ range T`** — the
precise, square-root-free form of `spinfulAnnihilation_rangeT_mulVec_eq_zero_of_groundState`.
Since the smeared annihilator is `ℂ`-linear (not conjugate-linear), the natural killing space is
the row span of the positive square root `C` of `T = Cᴴ·C`, which equals `conj(range T)`: for any
`w`, writing `b = C·w`, the identity `star(T·w)_x = Σ_k C_{kx}·conj(b_k)` exhibits `star(T·w)` as
the row combination `Σ_k (star b)_k · C_k`, so `Ĉ_σ(star(T·w))` kills `v`.  For an **orthonormal**
eigenbasis the operator detecting occupation of a nonzero-eigenvalue mode `u` (`T·u = λu`, `λ≠0`,
so `u = T·(λ⁻¹u) ∈ range T`) is exactly `Ĉ_σ(conj u)`, so this is the form consumed by the
eq. (11.3.46) Fock-spanning step of the next PR. -/
theorem spinfulAnnihilation_starRangeT_mulVec_eq_zero_of_groundState (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (σ : Fin 2)
    (w : Fin (M + 1) → ℂ) :
    (spinfulAnnihilationFromVector M (star (T.mulVec w)) σ).mulVec v = 0 := by
  obtain ⟨C, hC, hTC⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hT
  have hTCH : T = Cᴴ * C := by rw [hTC, hC.isHermitian.eq]
  have hkin : rayleighOnVec (hubbardKinetic M (Cᴴ * C)) v = 0 := by
    rw [← hTCH]; exact hubbardKinetic_rayleigh_zero_of_groundState M T U hT hU hv
  have hrow := spinfulAnnihilation_rowSpan_mulVec_eq_zero M C hkin σ (star (C.mulVec w))
  have hvec : (∑ k : Fin (M + 1), (star (C.mulVec w)) k • (fun j => C k j))
      = star (T.mulVec w) := by
    funext x
    have hTx : (T.mulVec w) x = ∑ k : Fin (M + 1), star (C k x) * (C.mulVec w) k := by
      rw [hTCH, ← Matrix.mulVec_mulVec]; rfl
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, hTx, star_sum,
      star_mul', star_star]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rwa [hvec] at hrow

open scoped ComplexOrder in
/-- **A flat-band ground state is annihilated by `Ĉ_σ(conj u)` for every nonzero-eigenvalue
eigenvector `u` of `T`** (`T·u = λu`, `λ ≠ 0`).  This is the exact occupation-detection operator for
the orthonormal eigenbasis used in the eq. (11.3.46) Fock-spanning step: a ground state has no
occupation on any `range T` (nonzero-eigenvalue) mode.  Obtained from
`spinfulAnnihilation_starRangeT_mulVec_eq_zero_of_groundState` with `w = λ⁻¹ u`
(so `T·w = u`). -/
theorem spinfulAnnihilation_starEigenvector_mulVec_eq_zero_of_groundState (M : ℕ)
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (U : ℝ) (hT : T.PosSemidef) (hU : 0 < U)
    {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) v = 0) (σ : Fin 2)
    {lam : ℂ} (hlam : lam ≠ 0) {u : Fin (M + 1) → ℂ} (hu : T.mulVec u = lam • u) :
    (spinfulAnnihilationFromVector M (star u) σ).mulVec v = 0 := by
  have hw : T.mulVec (lam⁻¹ • u) = u := by
    rw [Matrix.mulVec_smul, hu, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have h := spinfulAnnihilation_starRangeT_mulVec_eq_zero_of_groundState M T U hT hU hv σ
    (lam⁻¹ • u)
  rwa [hw] at h

/-- **A nonzero-eigenvalue eigenvector lies in the range of the matrix** (`u = T·(λ⁻¹ u)`): the
single-particle modes orthogonal to the flat band `ker T` are exactly the range of `T`, the source
of the complement creation operators in the full Fock basis (toward eq. (11.3.46)). -/
theorem mem_range_mulVec_of_eigenvalue_ne_zero
    (T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) {lam : ℂ} (hlam : lam ≠ 0)
    {u : Fin (M + 1) → ℂ} (hu : T.mulVec u = lam • u) :
    ∃ w : Fin (M + 1) → ℂ, T.mulVec w = u :=
  ⟨lam⁻¹ • u, by rw [Matrix.mulVec_smul, hu, smul_smul, inv_mul_cancel₀ hlam, one_smul]⟩

/-- **Conjugate transpose of a smeared creation operator**: `(Ĉ†_σ(φ))ᴴ = Ĉ_σ(φ̄)` — the adjoint
of the `φ`-smeared creator annihilates the conjugated state (companion to
`spinfulAnnihilationFromVector_conjTranspose`). -/
theorem spinfulCreationFromVector_conjTranspose (M : ℕ)
    (φ : Fin (M + 1) → ℂ) (σ : Fin 2) :
    (spinfulCreationFromVector M φ σ)ᴴ = spinfulAnnihilationFromVector M (star φ) σ := by
  unfold spinfulCreationFromVector spinfulAnnihilationFromVector
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, fermionMultiCreation_conjTranspose]
  rfl

/-- **A zero-eigenvalue eigenvector lies in the flat band `ker T`**: the spectral basis splits the
single-particle space into the flat band (zero eigenvalues) and its orthocomplement `range T`
(nonzero eigenvalues), the basis for the full Fock decomposition toward eq. (11.3.46). -/
theorem eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j : Fin (M + 1))
    (hj : hT.eigenvalues j = 0) :
    T.mulVec (⇑(hT.eigenvectorBasis j)) = 0 := by
  rw [hT.mulVec_eigenvectorBasis, hj]
  exact zero_smul _ _

/-- **A nonzero-eigenvalue eigenvector lies in `range T`**: companion to
`eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero`. Together they classify every spectral basis
vector into the flat band `ker T` or its orthocomplement `range T`, the decomposition driving the
Fock-space spanning of eq. (11.3.46). -/
theorem eigenvectorBasis_mem_range_of_eigenvalue_ne_zero
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j : Fin (M + 1))
    (hj : hT.eigenvalues j ≠ 0) :
    ∃ w : Fin (M + 1) → ℂ, T.mulVec w = ⇑(hT.eigenvectorBasis j) := by
  refine mem_range_mulVec_of_eigenvalue_ne_zero T (lam := (hT.eigenvalues j : ℂ))
    (by exact_mod_cast hj) ?_
  rw [hT.mulVec_eigenvectorBasis]
  funext i
  simp [Complex.real_smul]

/-- **Spectral `ker T ⊕ range T` decomposition of any single-particle vector**: every
`v : Fin (M+1) → ℂ` splits as `v = v_ker + v_range` with `T v_ker = 0` (flat band) and
`v_range ∈ range T`. Obtained from the orthonormal eigenbasis (`OrthonormalBasis.sum_repr`)
partitioned by zero/nonzero eigenvalue. This is the completeness input that lets the range-`T`
annihilation conditions pin a ground state into the flat-band Fock sector (eq. 11.3.46). -/
theorem exists_ker_add_range_decomp {M : ℕ}
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (v : Fin (M + 1) → ℂ) :
    ∃ vk vr : Fin (M + 1) → ℂ,
      T.mulVec vk = 0 ∧ (∃ w, T.mulVec w = vr) ∧ v = vk + vr := by
  classical
  set c : Fin (M + 1) → ℂ := fun j => hT.eigenvectorBasis.repr (WithLp.toLp 2 v) j with hc
  refine ⟨∑ j ∈ Finset.univ.filter (fun j => hT.eigenvalues j = 0),
            c j • (⇑(hT.eigenvectorBasis j) : Fin (M + 1) → ℂ),
          ∑ j ∈ Finset.univ.filter (fun j => ¬ hT.eigenvalues j = 0),
            c j • (⇑(hT.eigenvectorBasis j) : Fin (M + 1) → ℂ), ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Matrix.mulVec_smul,
      eigenvectorBasis_mem_ker_of_eigenvalue_eq_zero hT j (Finset.mem_filter.mp hj).2, smul_zero]
  · have hmem : (∑ j ∈ Finset.univ.filter (fun j => ¬ hT.eigenvalues j = 0),
        c j • (⇑(hT.eigenvectorBasis j) : Fin (M + 1) → ℂ)) ∈
        LinearMap.range T.mulVecLin := by
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
      obtain ⟨w, hw⟩ :=
        eigenvectorBasis_mem_range_of_eigenvalue_ne_zero hT j (Finset.mem_filter.mp hj).2
      exact ⟨w, by rw [Matrix.mulVecLin_apply, hw]⟩
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, by rw [← Matrix.mulVecLin_apply]; exact hw⟩
  · have hsum : (∑ j, c j • (⇑(hT.eigenvectorBasis j) : Fin (M + 1) → ℂ)) = v := by
      have hrepr := hT.eigenvectorBasis.sum_repr (WithLp.toLp 2 v)
      apply_fun WithLp.ofLp at hrepr
      rw [WithLp.ofLp_sum, WithLp.ofLp_toLp] at hrepr
      simpa only [WithLp.ofLp_smul, hc] using hrepr
    rw [← hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => hT.eigenvalues j = 0)]

/-- **The smeared annihilation `Ĉ_σ(φ)` kills a μ-Slater state whose every occupied mode is
orthogonal to `φ`** — the kinetic building block toward the all-up μ-Slater being a flat-band
ground state.  Writing `Ĉ_σ(φ) = Σ_x φ(x) ĉ_{x,σ}` and peeling each site annihilation
(`generalFlatBand_siteAnnihilation_peel`), the action collects term-wise to
`Σ_i (-1)^i [σ = q_i.2] (Σ_x φ(x) μ_{q_i.1}(x)) |Slater(erase i)⟩`; when each occupied-mode overlap
`Σ_x φ(x) μ_{q.1}(x)` vanishes, every peel term vanishes. -/
theorem spinfulAnnihilationFromVector_mulVec_generalFlatBandSlaterState_eq_zero_of_orthogonal
    (μ : Fin (M + 1) → Fin (M + 1) → ℂ) (φ : Fin (M + 1) → ℂ) (σ : Fin 2)
    (qs : List (Fin (M + 1) × Fin 2))
    (h : ∀ q ∈ qs, ∑ x : Fin (M + 1), φ x * μ q.1 x = 0) :
    (spinfulAnnihilationFromVector M φ σ).mulVec (generalFlatBandSlaterState μ qs) = 0 := by
  unfold spinfulAnnihilationFromVector
  rw [Matrix.sum_mulVec]
  have hx : ∀ x : Fin (M + 1),
      (φ x • fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)).mulVec
          (generalFlatBandSlaterState μ qs)
        = ∑ i : Fin qs.length, φ x • generalFlatBandPeelTerm μ x σ qs i := fun x => by
    rw [Matrix.smul_mulVec, generalFlatBand_siteAnnihilation_peel, Finset.smul_sum]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  unfold generalFlatBandPeelTerm
  by_cases hc : (qs.get i).2 = σ
  · simp only [hc, if_true]
    have hrew : ∀ x : Fin (M + 1),
        φ x • ((-1 : ℂ) ^ (i : ℕ) • (μ (qs.get i).1 x •
            generalFlatBandSlaterState μ (qs.eraseIdx i)))
          = (φ x * μ (qs.get i).1 x) • ((-1 : ℂ) ^ (i : ℕ) •
            generalFlatBandSlaterState μ (qs.eraseIdx i)) := fun x => by
      simp only [smul_smul]; congr 1; ring
    rw [Finset.sum_congr rfl (fun x _ => hrew x), ← Finset.sum_smul,
      h (qs.get i) (List.get_mem qs i), zero_smul]
  · simp only [hc, if_false, zero_smul, smul_zero, Finset.sum_const_zero]

end LatticeSystem.Fermion
