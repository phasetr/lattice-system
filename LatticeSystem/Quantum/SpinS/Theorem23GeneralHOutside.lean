import LatticeSystem.Quantum.SpinS.Theorem23TotalLoweringNonvanishing
import LatticeSystem.Quantum.SpinS.Theorem23GlobalMinimality
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# General-`J` non-admissible-sector lower bound via the SU(2) inward ladder

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), general-`J`
`hOutside` thread, steps 2–3 (see `.self-local/docs/tasaki-2-5-lieb-mattis-hOutside-design.md`).

`tasaki23_general_hOutside` discharges, for an ARBITRARY connected bipartite
antiferromagnetic coupling `J`, the non-admissible-sector lower bound that the global
minimality engine `tasaki23_eigenvalue_ge_common` (#3733) takes as `hOutside`:

> in every sector `M ∉ tasaki23GroundStateSectors A N`, every dressed-sector eigenvalue
> `μM` is `≥` the admissible common energy `μ`.

Proof (SU(2) inward ladder, NOT reflection positivity): lift the sector eigenvector to the
full Hilbert space; if `M` is above the band raise it by `Ŝ⁺_tot`, if below lower it by
`Ŝ⁻_tot`, until it reaches the admissible band edge.  Each step commutes with `H`
(`heisenbergHamiltonianS_commute_totalSpinSOp{Plus,Minus}`, energy preserved) and is
non-zero (`totalSpinSOp{Plus,Minus}_mulVec_ne_zero_of_{neg,pos}_weight`, #3736, since the
intermediate weights have the right sign).  The landed eigenvector is non-zero in an
admissible sector, where the Collatz–Wielandt per-sector bound from `hcommon` gives
`μ ≤ μM`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Admissible-sector eigenvalue lower bound** (the admissible core of the minimality
engine, reused). A non-zero full-space `H`-eigenvector at `λ` supported in an admissible
sector `M'` has `μ ≤ λ`, where `μ` is the common energy of `hcommon`. -/
theorem tasaki23_admissible_eigenvector_ge
    (A : V → Bool) (N : ℕ) (c : ℝ)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ}
    (hcommon : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ))
    {M' : ℕ} (hM'_mem : M' ∈ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M')]
    {lam : ℝ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ_ne : Ψ ≠ 0)
    (hΨ_supp : ∀ σ, magSumS σ ≠ M' → Ψ σ = 0)
    (hΨ_eig : (heisenbergHamiltonianS J N).mulVec Ψ = (lam : ℂ) • Ψ) :
    μ ≤ lam := by
  classical
  have hW_ne : magSectorRestriction (M := M') Ψ ≠ 0 := by
    intro h
    rw [magSectorRestriction_eq_zero_iff_vanishes] at h
    apply hΨ_ne
    funext σ
    by_cases hσ : magSumS σ = M'
    · exact h σ hσ
    · exact hΨ_supp σ hσ
  have hW_eig : (heisenbergHamiltonianSMatrixOnMagSector J N M').mulVec
      (magSectorRestriction (M := M') Ψ) = (lam : ℂ) • magSectorRestriction (M := M') Ψ :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen J hΨ_eig
  obtain ⟨φ, hφ_ne, hφ⟩ :
      ∃ φ : magConfigS V N M' → ℝ, φ ≠ 0 ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M').mulVec φ = lam • φ := by
    by_cases hre : (fun σ => (magSectorRestriction (M := M') Ψ σ).re) =
        (0 : magConfigS V N M' → ℝ)
    · refine ⟨fun σ => (magSectorRestriction (M := M') Ψ σ).im, ?_,
        heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hW_eig⟩
      intro him
      apply hW_ne
      funext τ
      have hr := congrFun hre τ
      have hi := congrFun him τ
      simp only [Pi.zero_apply] at hr hi ⊢
      exact Complex.ext hr hi
    · exact ⟨fun σ => (magSectorRestriction (M := M') Ψ σ).re, hre,
        heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW_eig⟩
  obtain ⟨vM, hvM_pos, hReEig⟩ := hcommon M' hM'_mem
  refine heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive A N c
    hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hReEig ?_ hφ_ne hφ
  intro σ
  rw [← mul_assoc, marshallSignS_re_sq, one_mul]
  exact hvM_pos σ

/-- `H` commutes past one `Ŝ⁺_tot` on any vector. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_mulVec
    {J : V → V → ℂ} (Ψ : (V → Fin (N + 1)) → ℂ) :
    (heisenbergHamiltonianS J N).mulVec ((totalSpinSOpPlus V N).mulVec Ψ) =
      (totalSpinSOpPlus V N).mulVec ((heisenbergHamiltonianS J N).mulVec Ψ) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (heisenbergHamiltonianS_commute_totalSpinSOpPlus J).eq]

/-- `H` commutes past one `Ŝ⁻_tot` on any vector. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_mulVec
    {J : V → V → ℂ} (Ψ : (V → Fin (N + 1)) → ℂ) :
    (heisenbergHamiltonianS J N).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      (totalSpinSOpMinus V N).mulVec ((heisenbergHamiltonianS J N).mulVec Ψ) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (heisenbergHamiltonianS_commute_totalSpinSOpMinus J).eq]

/-- **Raising iterate stays non-zero, weight-shifted, and energy-preserving.** If all `k`
intermediate weights `w₀ + j` have negative real part, then `(Ŝ⁺_tot)^k Φ` is non-zero, lies
in `magSubspaceS V N (w₀ + k)`, and is still an `H`-eigenvector at `lam`. -/
theorem raise_iterate_ne_zero
    {J : V → V → ℂ} {lam : ℝ} :
    ∀ (k : ℕ) {w₀ : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}, Φ ≠ 0 →
      Φ ∈ magSubspaceS V N w₀ →
      (heisenbergHamiltonianS J N).mulVec Φ = (lam : ℂ) • Φ →
      (∀ j : ℕ, j < k → (w₀ + (j : ℂ)).re < 0) →
      ((totalSpinSOpPlus V N ^ k).mulVec Φ ≠ 0 ∧
        (totalSpinSOpPlus V N ^ k).mulVec Φ ∈ magSubspaceS V N (w₀ + (k : ℂ)) ∧
        (heisenbergHamiltonianS J N).mulVec ((totalSpinSOpPlus V N ^ k).mulVec Φ) =
          (lam : ℂ) • (totalSpinSOpPlus V N ^ k).mulVec Φ) := by
  intro k
  induction k with
  | zero => intro w₀ Φ hΦ_ne hmem heig _; simpa using ⟨hΦ_ne, hmem, heig⟩
  | succ k ih =>
    intro w₀ Φ hΦ_ne hmem heig hneg
    obtain ⟨hΨ_ne, hΨ_mem, hΨ_eig⟩ := ih hΦ_ne hmem heig
      (fun j hj => hneg j (Nat.lt_succ_of_lt hj))
    set Ψ := (totalSpinSOpPlus V N ^ k).mulVec Φ with hΨdef
    have hpow : (totalSpinSOpPlus V N ^ (k + 1)).mulVec Φ =
        (totalSpinSOpPlus V N).mulVec Ψ := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    have hwneg : (w₀ + (k : ℂ)).re < 0 := hneg k (Nat.lt_succ_self k)
    have hΨ_z : (totalSpinSOp3 V N).mulVec Ψ = (w₀ + (k : ℂ)) • Ψ :=
      (mem_magSubspaceS_iff _ Ψ).mp hΨ_mem
    refine ⟨?_, ?_, ?_⟩
    · rw [hpow]
      exact totalSpinSOpPlus_mulVec_ne_zero_of_neg_weight hΨ_ne hΨ_z hwneg
    · rw [hpow]
      have := totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem hΨ_mem
      rwa [show w₀ + (k : ℂ) + 1 = w₀ + ((k + 1 : ℕ) : ℂ) by push_cast; ring] at this
    · rw [hpow, heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_mulVec, hΨ_eig,
        Matrix.mulVec_smul]

/-- **Lowering iterate stays non-zero, weight-shifted, and energy-preserving** (mirror of
`raise_iterate_ne_zero`; intermediate weights `w₀ − j` have positive real part). -/
theorem lower_iterate_ne_zero
    {J : V → V → ℂ} {lam : ℝ} :
    ∀ (k : ℕ) {w₀ : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}, Φ ≠ 0 →
      Φ ∈ magSubspaceS V N w₀ →
      (heisenbergHamiltonianS J N).mulVec Φ = (lam : ℂ) • Φ →
      (∀ j : ℕ, j < k → 0 < (w₀ - (j : ℂ)).re) →
      ((totalSpinSOpMinus V N ^ k).mulVec Φ ≠ 0 ∧
        (totalSpinSOpMinus V N ^ k).mulVec Φ ∈ magSubspaceS V N (w₀ - (k : ℂ)) ∧
        (heisenbergHamiltonianS J N).mulVec ((totalSpinSOpMinus V N ^ k).mulVec Φ) =
          (lam : ℂ) • (totalSpinSOpMinus V N ^ k).mulVec Φ) := by
  intro k
  induction k with
  | zero => intro w₀ Φ hΦ_ne hmem heig _; simpa using ⟨hΦ_ne, hmem, heig⟩
  | succ k ih =>
    intro w₀ Φ hΦ_ne hmem heig hpos
    obtain ⟨hΨ_ne, hΨ_mem, hΨ_eig⟩ := ih hΦ_ne hmem heig
      (fun j hj => hpos j (Nat.lt_succ_of_lt hj))
    set Ψ := (totalSpinSOpMinus V N ^ k).mulVec Φ with hΨdef
    have hpow : (totalSpinSOpMinus V N ^ (k + 1)).mulVec Φ =
        (totalSpinSOpMinus V N).mulVec Ψ := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    have hwpos : 0 < (w₀ - (k : ℂ)).re := hpos k (Nat.lt_succ_self k)
    have hΨ_z : (totalSpinSOp3 V N).mulVec Ψ = (w₀ - (k : ℂ)) • Ψ :=
      (mem_magSubspaceS_iff _ Ψ).mp hΨ_mem
    refine ⟨?_, ?_, ?_⟩
    · rw [hpow]
      exact totalSpinSOpMinus_mulVec_ne_zero_of_pos_weight hΨ_ne hΨ_z hwpos
    · rw [hpow]
      have := totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem hΨ_mem
      rwa [show w₀ - (k : ℂ) - 1 = w₀ - ((k + 1 : ℕ) : ℂ) by push_cast; ring] at this
    · rw [hpow, heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_mulVec, hΨ_eig,
        Matrix.mulVec_smul]

omit [DecidableEq V] in
/-- Real part of the shifted weight `((card·N/2) − M) + j`. -/
theorem weight_add_re (M j : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) + (j : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) + (j : ℝ) := by
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]

omit [DecidableEq V] in
/-- Real part of the shifted weight `((card·N/2) − M) − j`. -/
theorem weight_sub_re (M j : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) - (j : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) - (j : ℝ) := by
  simp [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]

/-- **General-`J` non-admissible-sector lower bound** (the engine's `hOutside`, discharged via
the SU(2) inward ladder). For an arbitrary connected bipartite antiferromagnetic coupling
`J`, given the admissible common energy `μ` (`hcommon`), every eigenvalue `μM` of the dressed
sector matrix in a NON-admissible sector `M` satisfies `μ ≤ μM`. -/
theorem tasaki23_general_hOutside
    (A : V → Bool) (N : ℕ) (c : ℝ)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ}
    (hcommon : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ))
    {M : ℕ} (hM_non : M ∉ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {μM : ℝ} {φ : magConfigS V N M → ℝ}
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ) :
    μ ≤ μM := by
  classical
  set cardA := (Finset.univ.filter (fun x : V => A x = true)).card with hcardA
  set cardB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcardB
  -- Lift the real sector eigenvector to the full Hilbert space.
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal (J := J) N hJ_real hφ
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding J (fun σ => ((φ σ : ℝ) : ℂ))
    hComplex
  set Φ := magSectorEmbedding (fun σ => ((φ σ : ℝ) : ℂ)) with hΦdef
  have hΦ_ne : Φ ≠ 0 := by
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hφ_ne
    intro h0
    apply hτ
    have happ : Φ τ.1 = ((φ τ : ℝ) : ℂ) := by
      rw [hΦdef]; exact magSectorEmbedding_apply_subtype _ τ
    rw [h0] at happ
    simp only [Pi.zero_apply] at happ
    have := congrArg Complex.re happ
    simpa using this.symm
  have hΦ_mem : Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) :=
    magSectorEmbedding_mem_magSubspaceS (fun σ => ((φ σ : ℝ) : ℂ))
  -- `max·N ≤ card V · N` and `min·N ≤ card V · N` (admissibility of band endpoints).
  have hsum : cardA + cardB = Fintype.card V := tasaki23_card_filter_A_add_card_notA A
  have hmax_le_card : max cardA cardB ≤ Fintype.card V := by
    rw [← hsum]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  rw [tasaki23GroundStateSectors_not_mem_iff_lt_left_or_right_lt] at hM_non
  rcases hM_non with hlt | hgt
  · -- `M < min·N`: lower by `Ŝ⁻` for `k = min·N − M` steps to the left band edge `min·N`.
    set k := min cardA cardB * N - M with hk
    have hMle : M ≤ min cardA cardB * N := le_of_lt hlt
    have hkval : (min cardA cardB * N : ℕ) = M + k := by rw [hk]; omega
    have hneg : ∀ j : ℕ, j < k →
        0 < (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) - (j : ℂ)).re := by
      intro j hj
      rw [weight_sub_re]
      have h2 : ((min cardA cardB * N : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 := by
        have h2card : 2 * min cardA cardB ≤ Fintype.card V := by rw [← hsum]; omega
        have hcast : ((min cardA cardB * N : ℕ) : ℝ) = (min cardA cardB : ℝ) * (N : ℝ) := by
          push_cast; ring
        have h2r : (2 : ℝ) * (min cardA cardB : ℝ) ≤ (Fintype.card V : ℝ) := by
          exact_mod_cast h2card
        rw [hcast]; nlinarith [Nat.cast_nonneg (α := ℝ) N, h2r]
      have hjlt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
      have hkr : (M : ℝ) + (k : ℝ) = ((min cardA cardB * N : ℕ) : ℝ) := by
        exact_mod_cast hkval.symm
      nlinarith [h2, hjlt, hkr]
    obtain ⟨hΨ_ne, hΨ_mem, hΨ_eig⟩ := lower_iterate_ne_zero k hΦ_ne hΦ_mem hH hneg
    -- The landed vector lies in the left band-edge sector `min·N`.
    have hweight : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) - (k : ℂ) =
        ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((min cardA cardB * N : ℕ) : ℂ) := by
      rw [hkval]; push_cast; ring
    rw [hweight] at hΨ_mem
    haveI : Nonempty (magConfigS V N (min cardA cardB * N)) :=
      magConfigS_nonempty_of_le_card_mul
        (le_trans (Nat.mul_le_mul_right N (min_le_max)) (Nat.mul_le_mul_right N hmax_le_card))
    refine tasaki23_admissible_eigenvector_ge A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hcommon ?_ hΨ_ne (fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΨ_mem hσ)
      hΨ_eig
    rw [tasaki23GroundStateSectors_mem_iff]
    exact ⟨le_refl _, Nat.mul_le_mul_right N (min_le_max)⟩
  · -- `max·N < M`: raise by `Ŝ⁺` for `k = M − max·N` steps to the right band edge `max·N`.
    set k := M - max cardA cardB * N with hk
    have hMge : max cardA cardB * N ≤ M := le_of_lt hgt
    have hkval : M = max cardA cardB * N + k := by rw [hk]; omega
    have hneg : ∀ j : ℕ, j < k →
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) + (j : ℂ)).re < 0 := by
      intro j hj
      rw [weight_add_re]
      have h2 : (Fintype.card V : ℝ) * (N : ℝ) / 2 ≤ ((max cardA cardB * N : ℕ) : ℝ) := by
        have h2card : Fintype.card V ≤ 2 * max cardA cardB := by rw [← hsum]; omega
        have hcast : ((max cardA cardB * N : ℕ) : ℝ) = (max cardA cardB : ℝ) * (N : ℝ) := by
          push_cast; ring
        have h2r : (Fintype.card V : ℝ) ≤ (2 : ℝ) * (max cardA cardB : ℝ) := by
          exact_mod_cast h2card
        rw [hcast]; nlinarith [Nat.cast_nonneg (α := ℝ) N, h2r]
      have hjlt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
      have hkr : (M : ℝ) = ((max cardA cardB * N : ℕ) : ℝ) + (k : ℝ) := by
        exact_mod_cast hkval
      nlinarith [h2, hjlt, hkr]
    obtain ⟨hΨ_ne, hΨ_mem, hΨ_eig⟩ := raise_iterate_ne_zero k hΦ_ne hΦ_mem hH hneg
    have hweight : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) + (k : ℂ) =
        ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((max cardA cardB * N : ℕ) : ℂ) := by
      rw [hkval]; push_cast; ring
    rw [hweight] at hΨ_mem
    haveI : Nonempty (magConfigS V N (max cardA cardB * N)) :=
      magConfigS_nonempty_of_le_card_mul (Nat.mul_le_mul_right N hmax_le_card)
    refine tasaki23_admissible_eigenvector_ge A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hcommon ?_ hΨ_ne (fun σ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΨ_mem hσ)
      hΨ_eig
    rw [tasaki23GroundStateSectors_mem_iff]
    exact ⟨Nat.mul_le_mul_right N (min_le_max), le_refl _⟩

end LatticeSystem.Quantum
