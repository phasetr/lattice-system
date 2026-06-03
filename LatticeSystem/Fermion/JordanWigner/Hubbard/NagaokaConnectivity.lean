import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaPerronFrobenius

/-!
# Tasaki Theorem 11.7 (Nagaoka's theorem): the capstone (Tasaki §11.2.2)

Completes **Tasaki Theorem 11.7**.  With the `≤ N+1` upper bound from
`NagaokaPerronFrobenius.lean`, this file supplies the coefficient↔full bridge and
the SU(2) spin-multiplet lower bound, then assembles the theorem:

* [`tasakiCoeff_mulVec_eigen_of_full`] — a one-hole-supported full `Ĥ_eff`
  eigenvector yields a coefficient `M`-eigenvector (backward bridge).
* `fermionTotalSpinMinus` preserves the hard-core `N`-electron sector, so the
  tower `(Ŝ⁻)^k Φ_↑` is one-hole supported
  ([`spinMinusPow_pfFerroState_oneHole_supported`]).
* [`tasakiEffMatrix_ground_finrank_ge`] — the `≥ N+1` lower bound.
* [`nagaoka_theorem_11_7_degeneracy`] (degeneracy `= N+1 = 2 S_max + 1`) and
  [`nagaoka_theorem_11_7`] (every ground state has `S_tot = S_max`).

Split from the original monolithic `NagaokaConnectivity.lean` (refactor,
2026-06-04); the magnetization-sector/PF foundations now live in
`NagaokaMagnetizationSector.lean` and `NagaokaPerronFrobenius.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math.PerronFrobenius
  LatticeSystem.Math.CollatzWielandt Module

/-! ## Bridge: coefficient eigenvectors ↔ full `Ĥ_eff` ground states -/

/-- The Tasaki coefficient functional `⟨Φ_q, v⟩ = Σ_w Φ_q(w) v(w)`.  On a
one-hole-supported vector this recovers the Tasaki expansion coefficients. -/
noncomputable def tasakiCoeff (N : ℕ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    ((x : Fin (N + 1)) × HoleSpin N x) → ℂ :=
  fun q => ∑ w, tasakiState N q w * v w

/-- **Left inverse: the coefficient functional inverts the Tasaki expansion.**
`tasakiCoeff (Σ_p c_p Φ_p) = c` — the basis `Φ_q` being orthonormal.  Hence the
expansion `c ↦ Σ_p c_p Φ_p` is injective. -/
theorem tasakiCoeff_expansion (N : ℕ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    tasakiCoeff N (∑ p, c p • tasakiState N p) = c := by
  funext q
  unfold tasakiCoeff
  have hstep : ∀ w, tasakiState N q w * (∑ p, c p • tasakiState N p) w
      = ∑ p, c p * (tasakiState N q w * tasakiState N p w) := by
    intro w
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)
  rw [Finset.sum_congr rfl (fun w _ => hstep w), Finset.sum_comm]
  rw [show (∑ p, ∑ w, c p * (tasakiState N q w * tasakiState N p w))
      = ∑ p, c p * (∑ w, tasakiState N q w * tasakiState N p w) from
    Finset.sum_congr rfl (fun p _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_congr rfl (fun p _ => by rw [tasakiState_orthonormal])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ q (fun p => c p), if_pos (Finset.mem_univ q)]

/-- **Backward bridge (hardest step): a full one-hole `Ĥ_eff`-eigenvector gives a
coefficient `M`-eigenvector.**  If `Ĥ_eff v = E v` and `v` is supported on the
one-hole hard-core sector, then its Tasaki coefficients satisfy `M c = E c`.
Combines completeness (`v = Σ c_q Φ_q`), the operator lift (`Ĥ_eff (Σ c Φ) =
Σ (M c) Φ`) and the left-inverse `tasakiCoeff_expansion`. -/
theorem tasakiCoeff_mulVec_eigen_of_full (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) (E : ℂ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hsupp : ∀ w, ¬ IsOneHoleHardcoreConfig N w → v w = 0)
    (hv : (hubbardEffectiveHamiltonian N t U).mulVec v = E • v) :
    (tasakiEffMatrix N t U).mulVec (tasakiCoeff N v) = E • tasakiCoeff N v := by
  have hexp : v = ∑ q, tasakiCoeff N v q • tasakiState N q := tasaki_completeness N v hsupp
  -- `Ĥ_eff v = Σ (M c) Φ`, and `Ĥ_eff v = E v = Σ (E c) Φ`.
  have hlift : (hubbardEffectiveHamiltonian N t U).mulVec v
      = ∑ q, ((tasakiEffMatrix N t U).mulVec (tasakiCoeff N v)) q • tasakiState N q := by
    conv_lhs => rw [hexp]
    rw [hubbardEffectiveHamiltonian_mulVec_tasakiExpansion]
  have hEv : E • v = ∑ q, (E • tasakiCoeff N v) q • tasakiState N q := by
    conv_lhs => rw [hexp]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun q _ => by rw [Pi.smul_apply, smul_smul, smul_eq_mul])
  have hEq : (∑ q, ((tasakiEffMatrix N t U).mulVec (tasakiCoeff N v)) q • tasakiState N q)
      = ∑ q, (E • tasakiCoeff N v) q • tasakiState N q := by rw [← hlift, hv, hEv]
  -- Apply the left inverse to both Tasaki expansions.
  have hfin := congrArg (tasakiCoeff N) hEq
  rwa [tasakiCoeff_expansion, tasakiCoeff_expansion] at hfin

/-! ## The spin-lowering tower stays in the one-hole sector -/

/-- `Ŝ^-_tot` conserves the total particle number (it is `Σ c†_{i↓} c_{i↑}`). -/
theorem fermionTotalSpinMinus_commute_fermionTotalNumber (N : ℕ) :
    Commute (fermionTotalSpinMinus N) (fermionTotalNumber (2 * N + 1)) := by
  unfold fermionTotalSpinMinus
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  unfold fermionDownCreation fermionUpAnnihilation
  exact (fermionTotalNumber_commute_hopping (2 * N + 1)
    (spinfulIndex N i 1) (spinfulIndex N i 0)).symm

/-- `Ŝ^-_tot` preserves the hard-core (no-double-occupancy) subspace: it commutes
with the hard-core projection (adjoint of the `Ŝ^+_tot` version, using
`(Ŝ^+)ᴴ = Ŝ^-` and the projection's Hermiticity). -/
theorem fermionTotalSpinMinus_commute_hubbardHardcoreProjection (N : ℕ) :
    Commute (fermionTotalSpinMinus N) (hubbardHardcoreProjection N) := by
  have h := fermionTotalSpinPlus_commute_hubbardHardcoreProjection N
  have hP := hubbardHardcoreProjection_isHermitian N
  have hct := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    fermionTotalSpinPlus_conjTranspose, hP] at hct
  exact hct.symm

/-- `Ŝ^-_tot` maps the hard-core subspace into itself. -/
theorem fermionTotalSpinMinus_mulVec_mem_hardcore (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    (fermionTotalSpinMinus N).mulVec v ∈ hubbardHardcoreSubspace N := by
  have hself : (hubbardHardcoreProjection N).mulVec ((fermionTotalSpinMinus N).mulVec v)
      = (fermionTotalSpinMinus N).mulVec v := by
    rw [Matrix.mulVec_mulVec,
      (fermionTotalSpinMinus_commute_hubbardHardcoreProjection N).symm.eq,
      ← Matrix.mulVec_mulVec, hubbardHardcoreProjection_mulVec_eq_self_of_mem N hv]
  rw [← hself]
  exact hubbardHardcoreProjection_mulVec_mem N _

/-- `Ŝ^-_tot` preserves the total-particle-number eigenvalue. -/
theorem fermionTotalSpinMinus_mulVec_preserves_number (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (N : ℂ) • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec ((fermionTotalSpinMinus N).mulVec v)
      = (N : ℂ) • ((fermionTotalSpinMinus N).mulVec v) := by
  rw [Matrix.mulVec_mulVec,
    (fermionTotalSpinMinus_commute_fermionTotalNumber N).symm.eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- The tower `(Ŝ^-)^k v` stays in the hard-core subspace. -/
theorem fermionTotalSpinMinus_pow_mulVec_mem_hardcore (N : ℕ) (k : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    ((fermionTotalSpinMinus N) ^ k).mulVec v ∈ hubbardHardcoreSubspace N := by
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact fermionTotalSpinMinus_mulVec_mem_hardcore N ih

/-- The tower `(Ŝ^-)^k v` keeps the total-particle-number eigenvalue `N`. -/
theorem fermionTotalSpinMinus_pow_mulVec_preserves_number (N : ℕ) (k : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (N : ℂ) • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v)
      = (N : ℂ) • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  induction k with
  | zero => rwa [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact fermionTotalSpinMinus_mulVec_preserves_number N ih

/-- Each Tasaki basis state lies in the hard-core subspace. -/
theorem tasakiState_mem_hardcore (N : ℕ) (p : (x : Fin (N + 1)) × HoleSpin N x) :
    tasakiState N p ∈ hubbardHardcoreSubspace N := by
  rw [tasakiState, hubbardTasakiBasisState_eq_smul_basisVec]
  exact Submodule.smul_mem _ _
    (hubbardHardcoreBasisState_mem_hardcoreSubspace N p.1 p.2.val)

/-- The ferromagnetic ground state `pfFerroState` lies in the hard-core subspace. -/
theorem pfFerroState_mem_hardcore (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    pfFerroState N ξ ∈ hubbardHardcoreSubspace N := by
  unfold pfFerroState
  exact Submodule.sum_mem _ (fun x _ =>
    Submodule.smul_mem _ _ (tasakiState_mem_hardcore N _))

/-- `pfFerroState` is an `N`-electron state. -/
theorem fermionTotalNumber_mulVec_pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℂ) :
    (fermionTotalNumber (2 * N + 1)).mulVec (pfFerroState N ξ) =
      (N : ℂ) • pfFerroState N ξ := by
  unfold pfFerroState
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.mulVec_smul, fermionTotalNumber_mulVec_tasakiState, smul_comm]

/-- **The spin tower of `pfFerroState` is one-hole supported.**  `(Ŝ^-)^k Φ_↑`
stays in the hard-core `N`-electron sector, hence vanishes off the one-hole
hard-core configurations. -/
theorem spinMinusPow_pfFerroState_oneHole_supported (N : ℕ) (ξ : Fin (N + 1) → ℂ)
    (k : ℕ) (w : Fin (2 * N + 2) → Fin 2) (hw : ¬ IsOneHoleHardcoreConfig N w) :
    (((fermionTotalSpinMinus N) ^ k).mulVec (pfFerroState N ξ)) w = 0 :=
  mulVec_apply_eq_zero_of_not_oneHole N _
    (fermionTotalSpinMinus_pow_mulVec_mem_hardcore N k (pfFerroState_mem_hardcore N ξ))
    (fermionTotalSpinMinus_pow_mulVec_preserves_number N k
      (fermionTotalNumber_mulVec_pfFerroState N ξ)) w hw

/-- The Tasaki embedding's `mulVec` is the Tasaki expansion. -/
theorem tasakiEmbedding_mulVec_eq (N : ℕ)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ) :
    (tasakiEmbedding N).mulVec c = ∑ q, c q • tasakiState N q := by
  funext w
  simp only [Matrix.mulVec, dotProduct, tasakiEmbedding, Matrix.of_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun q _ => mul_comm _ _)

/-- **Lower bound (`≥ N+1`) from the ferromagnetic multiplet.**  The `N+1`
linearly independent tower states `(Ŝ^-)^k Φ_↑` are one-hole supported
`Ĥ_eff`-eigenvectors at the minimum `E`, so their Tasaki coefficients are `N+1`
linearly independent `M`-eigenvectors — hence the coefficient ground eigenspace
has dimension `≥ N+1`. -/
theorem tasakiEffMatrix_ground_finrank_ge (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    N + 1 ≤ finrank ℂ (End.eigenspace (Matrix.toLin'
      (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0))
      (((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
        (fun i j => (t i j : ℂ)) 0 (tasakiEffMatrix_hJ_of_real htsym)
        (by simp))) : ℝ) : ℂ)) := by
  have hJ := tasakiEffMatrix_hJ_of_real htsym
  have hU0 : star (0 : ℂ) = 0 := by simp
  obtain ⟨ξ, hξ_ne, hξ_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue
    (tasakiEffMatrixUp_isHermitian N (fun i j => (t i j : ℂ)) 0 hJ hU0)
  set E : ℂ := ((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
    (fun i j => (t i j : ℂ)) 0 hJ hU0) : ℝ) : ℂ) with hEdef
  have hv0_eig := hubbardEffectiveHamiltonian_mulVec_pfFerroState_of_eigen N
    (fun i j => (t i j : ℂ)) 0 (fun i => by simp [htdiag i]) ξ E hξ_eig
  obtain ⟨hLI, hdeg, _⟩ := weakNagaoka_spinMultiplet N (fun i j => (t i j : ℂ)) 0 hJ hU0
    (pfFerroState N ξ) E hv0_eig (fermionTotalSpinPlus_mulVec_pfFerroState N ξ)
    (fermionTotalSpinZ_mulVec_pfFerroState N ξ) (pfFerroState_ne_zero N ξ hξ_ne)
  set tower : Fin (N + 1) → (Fin (2 * N + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec (pfFerroState N ξ) with htower
  set cfn : Fin (N + 1) → ((x : Fin (N + 1)) × HoleSpin N x) → ℂ :=
    fun k => tasakiCoeff N (tower k) with hcfn
  set W := End.eigenspace (Matrix.toLin'
    (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0)) E with hWdef
  have hc_mem : ∀ k, cfn k ∈ W := by
    intro k
    rw [hWdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tasakiCoeff_mulVec_eigen_of_full N (fun i j => (t i j : ℂ)) 0 E (tower k)
      (spinMinusPow_pfFerroState_oneHole_supported N ξ k) (hdeg k)
  have hcLI : LinearIndependent ℂ cfn := by
    have htower_eq : tower = (Matrix.mulVecLin (tasakiEmbedding N)) ∘ cfn := by
      funext k
      rw [Function.comp_apply, Matrix.mulVecLin_apply, tasakiEmbedding_mulVec_eq]
      exact tasaki_completeness N (tower k)
        (spinMinusPow_pfFerroState_oneHole_supported N ξ k)
    rw [htower_eq] at hLI
    exact hLI.of_comp _
  have hWLI : LinearIndependent ℂ (fun k => (⟨cfn k, hc_mem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hcLI
  have := hWLI.fintype_card_le_finrank
  simpa using this

/-- **Tasaki Theorem 11.7 (degeneracy).**  Under the connectivity condition
(Definition 11.6) and `t ≥ 0`, the one-hole `Ĥ_eff` ground eigenspace (in the
Tasaki-coefficient representation) has dimension exactly `N + 1 = 2 S_max + 1`:
the ferromagnetic multiplet and nothing more.  Combines the Perron–Frobenius
upper bound (`≤ N+1`) with the spin-multiplet lower bound (`≥ N+1`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.7. -/
theorem nagaoka_theorem_11_7_degeneracy (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j) (hconn : nagaokaConnectivity N t) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0))
      (((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
        (fun i j => (t i j : ℂ)) 0 (tasakiEffMatrix_hJ_of_real htsym)
        (by simp))) : ℝ) : ℂ)) = N + 1 := by
  have hmateq : tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0
      = (tasakiEffReMatrix N t).map (algebraMap ℝ ℂ) :=
    tasakiEffMatrix_eq_map_tasakiEffReMatrix N t 0 htdiag
  have hE_eq : hermitianMinEigenvalue (isHermitian_map_ofReal_of_isSymm
        (tasakiEffReMatrix_isSymm N t htsym htdiag))
      = hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
        (fun i j => (t i j : ℂ)) 0 (tasakiEffMatrix_hJ_of_real htsym) (by simp)) := by
    have h1 : hermitianMinEigenvalue (isHermitian_map_ofReal_of_isSymm
          (tasakiEffReMatrix_isSymm N t htsym htdiag))
        = hermitianMinEigenvalue (tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) 0
          (tasakiEffMatrix_hJ_of_real htsym) (by simp)) := by
      rw [← rayleighInfMatrix_eq_hermitianMinEigenvalue,
        ← rayleighInfMatrix_eq_hermitianMinEigenvalue, hmateq]
    rw [h1]
    exact (hermitianMinEigenvalue_tasakiEffMatrixUp_eq N t 0 htsym htdiag hpos).symm
  refine le_antisymm ?_ ?_
  · rw [hmateq, ← hE_eq]
    exact tasakiEffMatrix_ground_finrank_le_N_add_one N t htsym htdiag hpos hconn
  · exact tasakiEffMatrix_ground_finrank_ge N t htsym htdiag

/-- **Tasaki Theorem 11.7 (saturated ferromagnetism).**  Under the connectivity
condition and `t ≥ 0`, *every* one-hole `Ĥ_eff` ground state has total spin
`S_tot = S_max`: its lifted full-space wavefunction is a `Ŝ_tot²`-eigenstate at
`S_max (S_max + 1)`.  Since the ground eigenspace is `(N+1)`-dimensional
(`nagaoka_theorem_11_7_degeneracy`) and the `(N+1)` ferromagnetic tower states
span it, any ground state is a tower combination, hence spin-`S_max`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Theorem 11.7. -/
theorem nagaoka_theorem_11_7 (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hpos : ∀ i j, 0 ≤ t i j) (hconn : nagaokaConnectivity N t)
    (c : ((x : Fin (N + 1)) × HoleSpin N x) → ℂ)
    (hc : (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0).mulVec c =
      (((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N (fun i j => (t i j : ℂ)) 0
        (tasakiEffMatrix_hJ_of_real htsym) (by simp))) : ℝ) : ℂ) • c) :
    (fermionTotalSpinSquared N).mulVec (∑ q, c q • tasakiState N q) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • (∑ q, c q • tasakiState N q) := by
  have hJ := tasakiEffMatrix_hJ_of_real htsym
  have hU0 : star (0 : ℂ) = 0 := by simp
  obtain ⟨ξ, hξ_ne, hξ_eig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue
    (tasakiEffMatrixUp_isHermitian N (fun i j => (t i j : ℂ)) 0 hJ hU0)
  set E : ℂ := ((hermitianMinEigenvalue (tasakiEffMatrixUp_isHermitian N
    (fun i j => (t i j : ℂ)) 0 hJ hU0) : ℝ) : ℂ) with hEdef
  have hv0_eig := hubbardEffectiveHamiltonian_mulVec_pfFerroState_of_eigen N
    (fun i j => (t i j : ℂ)) 0 (fun i => by simp [htdiag i]) ξ E hξ_eig
  obtain ⟨hLI, hdeg, hCas⟩ := weakNagaoka_spinMultiplet N (fun i j => (t i j : ℂ)) 0 hJ hU0
    (pfFerroState N ξ) E hv0_eig (fermionTotalSpinPlus_mulVec_pfFerroState N ξ)
    (fermionTotalSpinZ_mulVec_pfFerroState N ξ) (pfFerroState_ne_zero N ξ hξ_ne)
  set tower : Fin (N + 1) → (Fin (2 * N + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec (pfFerroState N ξ) with htower
  set cfn : Fin (N + 1) → ((x : Fin (N + 1)) × HoleSpin N x) → ℂ :=
    fun k => tasakiCoeff N (tower k) with hcfn
  set W := End.eigenspace (Matrix.toLin'
    (tasakiEffMatrix N (fun i j => (t i j : ℂ)) 0)) E with hWdef
  have hexpand : ∀ k, (tasakiEmbedding N).mulVec (cfn k) = tower k := by
    intro k
    rw [tasakiEmbedding_mulVec_eq]
    exact (tasaki_completeness N (tower k)
      (spinMinusPow_pfFerroState_oneHole_supported N ξ k)).symm
  have hc_mem : ∀ k, cfn k ∈ W := by
    intro k
    rw [hWdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact tasakiCoeff_mulVec_eigen_of_full N (fun i j => (t i j : ℂ)) 0 E (tower k)
      (spinMinusPow_pfFerroState_oneHole_supported N ξ k) (hdeg k)
  have hcLI : LinearIndependent ℂ cfn := by
    have htower_eq : tower = (Matrix.mulVecLin (tasakiEmbedding N)) ∘ cfn := by
      funext k; rw [Function.comp_apply, Matrix.mulVecLin_apply, hexpand]
    rw [htower_eq] at hLI
    exact hLI.of_comp _
  have hWLI : LinearIndependent ℂ (fun k => (⟨cfn k, hc_mem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hcLI
  have hcard : Fintype.card (Fin (N + 1)) = finrank ℂ W := by
    rw [Fintype.card_fin]
    exact (nagaoka_theorem_11_7_degeneracy N t htsym htdiag hpos hconn).symm
  have hspan := hWLI.span_eq_top_of_card_eq_finrank hcard
  -- the given eigenvector `c` lies in `W`, hence in the span of the tower coefficients.
  have hcW : c ∈ W := by rw [hWdef, End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hc
  have hmem : (⟨c, hcW⟩ : W) ∈ Submodule.span ℂ (Set.range fun k => (⟨cfn k, hc_mem k⟩ : W)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hc_eq : c = ∑ k, a k • cfn k := by
    have := congrArg (Subtype.val) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  -- lift to the full space: `Σ c_q Φ_q = Σ_k a_k tower_k`.
  have hlift : (∑ q, c q • tasakiState N q) = ∑ k, a k • tower k := by
    rw [← tasakiEmbedding_mulVec_eq, hc_eq, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.mulVec_smul, hexpand])
  rw [hlift, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mulVec_smul, hCas, smul_comm]


end LatticeSystem.Fermion
