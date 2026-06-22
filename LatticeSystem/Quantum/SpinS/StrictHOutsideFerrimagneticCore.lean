import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLM
import LatticeSystem.Quantum.SpinS.Theorem23TotalLowestWeightExistence
import LatticeSystem.Quantum.SpinS.ConnectedTheorem23
import LatticeSystem.Quantum.SpinS.ConnectedSectorFinrankLeOne
import LatticeSystem.Quantum.SpinS.CasimirSpectralLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23GeneralHOutside

/-!
# Strict outside-sector energy separation (ferrimagnetic case): foundation

Foundational layer extracted from `StrictHOutsideFerrimagnetic.lean` for build speed
(Tasaki §4.1 Theorem 4.4, Issue #4617 step 2).  This file holds the absolute-value
total-Casimir lower bound, the lowest-weight eigenvector existence, the ladder-injectivity
and backward Casimir-transfer helpers, and the per-sector strict ordering
`tasaki23_strict_hOutside_ferrimagnetic` (`|A| ≠ |B|` general ferrimagnetic case).

The connected-coupling wrapper `tasaki23_strict_hOutside_of_connected` and the full
mathematical narrative are documented in the capstone module
`StrictHOutsideFerrimagnetic.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §2.5 Theorem 2.3 (Marshall–Lieb–Mattis, p. 42) and §4.1
Theorem 4.4 (Shen–Qiu–Tian, chain (4.1.16), pp. 77–78).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Absolute-value total-Casimir lower bound -/

omit [DecidableEq V] in
/-- The real part of the magnetization value `s_max − k`. -/
private theorem sMaxSubRe (k : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - (k : ℝ) := by
  simp [Complex.sub_re, Complex.mul_re]

omit [DecidableEq V] in
/-- Real part of the shifted weight `((card·N/2) − M) − j` (local copy of the
private `Theorem23GeneralHOutside.weight_sub_re`). -/
private theorem weightSubRe (M j : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) - (j : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) - (j : ℝ) := by
  simp [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]

omit [DecidableEq V] in
/-- Real part of the shifted weight `((card·N/2) − M) + j` (local copy of the
private `Theorem23GeneralHOutside.weight_add_re`). -/
private theorem weightAddRe (M j : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) + (j : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) + (j : ℝ) := by
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]

/-- **Existence of a lowest-weight eigenvector, magnetization-tracking**: from a
non-zero `(Ŝ_tot)²`-eigenvector at `γ` in `magSubspaceS V N (s_max − k)`, lowering
with `Ŝ⁻_tot` produces a non-zero lowest-weight eigenvector at the same `γ` whose
magnetization `M'` satisfies `M'.re ≤ s_max − k` (the magnetization never
increases).  Lowering mirror of `exists_highestWeight_eigenvector_ge`. -/
private theorem exists_lowestWeight_eigenvector_le :
    ∀ (k : ℕ) {γ : ℂ} {w : (V → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      w ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)) →
      (totalSpinSSquared V N).mulVec w = γ • w →
      ∃ (M' : ℂ) (w' : (V → Fin (N + 1)) → ℂ),
        w' ≠ 0 ∧ w' ∈ magSubspaceS V N M' ∧
        (totalSpinSOpMinus V N).mulVec w' = 0 ∧
        (totalSpinSSquared V N).mulVec w' = γ • w' ∧
        M'.re ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 - (k : ℝ) := by
  -- Induct on the number of remaining lowering steps `Fintype.card V * N - k`.
  intro k
  induction hd : Fintype.card V * N - k using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    intro γ w hw_ne hw_mem hcas
    by_cases hker : (totalSpinSOpMinus V N).mulVec w = 0
    · refine ⟨_, w, hw_ne, hw_mem, hker, hcas, ?_⟩
      rw [sMaxSubRe]
    · -- Lower one step into `s_max − (k + 1)`.
      have hmem1 := totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem hw_mem
      have hidx : (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)) - 1 =
          ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((k + 1 : ℕ) : ℂ) := by
        push_cast; ring
      rw [hidx] at hmem1
      have hcas1 : (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec w) =
          γ • (totalSpinSOpMinus V N).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS totalSpinSSquared_commute_totalSpinSOpMinus hcas
      -- The step must be available: the bottom level `s_max − card·N` is killed.
      have hk_lt : k < Fintype.card V * N := by
        by_contra hge
        push Not at hge
        -- At or below the bottom level, `Ŝ⁻` annihilates `w`, contradicting `hker`.
        have hbot : magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)) - 1) = ⊥ := by
          apply magSubspaceS_eq_bot_of_not_in_spectrum
          intro σ hcontra
          have hval : magEigenvalueS σ =
              ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((k + 1 : ℕ) : ℂ) := by
            rw [hcontra]; push_cast; ring
          rw [magEigenvalueS_def] at hval
          have hsum_le : magSumS σ ≤ Fintype.card V * N := magSumS_le σ
          -- `center − magSumS = center − (k+1)` ⟹ `magSumS = k+1 > card·N`.
          have hcast : ((magSumS σ : ℕ) : ℂ) = ((k + 1 : ℕ) : ℂ) := sub_right_injective hval
          have : magSumS σ = k + 1 := by exact_mod_cast hcast
          omega
        rw [hidx] at hbot
        exact hker ((Submodule.eq_bot_iff _).mp hbot _ hmem1)
      obtain ⟨M', w', hw'_ne, hw'_mem, hw'_ker, hw'_cas, hM'_le⟩ :=
        ih (Fintype.card V * N - (k + 1)) (by omega) (k + 1) rfl hker hmem1 hcas1
      refine ⟨M', w', hw'_ne, hw'_mem, hw'_ker, hw'_cas, ?_⟩
      push_cast at hM'_le ⊢
      linarith

/-- **Total-Casimir magnetization lower bound, negative-weight side**: a non-zero
`(Ŝ_tot)²`-eigenvector at `γ` lying in `magSubspaceS V N M` with `M.re ≤ 0`
satisfies `M.re·(M.re−1) ≤ γ.re`.

Mirror of `totalSpinSSquared_eigenvalue_re_ge_of_mem_magSubspaceS` (which covers
`0 ≤ M.re`): here we lower with `Ŝ⁻_tot` to a lowest-weight vector whose Casimir
value is `M'·(M'−1)` with `M'.re ≤ M.re ≤ 0`. -/
private theorem totalSpinSSquared_eigenvalue_re_ge_neg_of_mem_magSubspaceS
    {γ M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hv_mem : v ∈ magSubspaceS V N M)
    (hM_np : M.re ≤ 0)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    M.re * (M.re - 1) ≤ γ.re := by
  classical
  -- `M` is an attained magnetization eigenvalue, so `M = s_max − magSumS σ`.
  have hMspec : ∃ σ : V → Fin (N + 1), magEigenvalueS σ = M := by
    by_contra h
    exact hv ((Submodule.eq_bot_iff _).mp
      (magSubspaceS_eq_bot_of_not_in_spectrum (not_exists.mp h)) v hv_mem)
  obtain ⟨σ, hσ⟩ := hMspec
  have hMeq : M = ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((magSumS σ : ℕ) : ℂ) := by
    rw [← hσ, magEigenvalueS_def]
  have hv_mem' : v ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((magSumS σ : ℕ) : ℂ)) := by
    rwa [← hMeq]
  obtain ⟨M', w', hw'_ne, hw'_mem, hw'_ker, hw'_cas, hM'_le⟩ :=
    exists_lowestWeight_eigenvector_le (magSumS σ) hv hv_mem' hcas
  -- γ = M' (M' − 1).
  have hlw := tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpMinus_eq_zero_of_mem_magSubspaceS
    hw'_mem hw'_ker
  have hsmul : γ • w' = (M' * (M' - 1)) • w' := hw'_cas.symm.trans hlw
  have hγ : γ = M' * (M' - 1) := by
    have := sub_eq_zero.mpr hsmul
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw'_ne
  -- M'.im = 0, and M'.re ≤ M.re.
  have hM'im : M'.im = 0 := by
    have : ∃ τ : V → Fin (N + 1), magEigenvalueS τ = M' := by
      by_contra h
      exact hw'_ne ((Submodule.eq_bot_iff _).mp
        (magSubspaceS_eq_bot_of_not_in_spectrum (not_exists.mp h)) w' hw'_mem)
    obtain ⟨τ, hτ⟩ := this
    rw [← hτ]; simp [magEigenvalueS_def]
  have hMre_le : M'.re ≤ M.re := by
    have hMre : M.re = (Fintype.card V : ℝ) * (N : ℝ) / 2 - (magSumS σ : ℝ) := by
      rw [hMeq, sMaxSubRe]
    rw [hMre]; exact hM'_le
  -- γ.re = M'.re (M'.re − 1).
  have hre : γ.re = M'.re * (M'.re - 1) := by
    rw [hγ]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hM'im]
    ring
  rw [hre]
  -- M'.re ≤ M.re ≤ 0 forces M'.re(M'.re−1) ≥ M.re(M.re−1).
  nlinarith [hMre_le, hM_np]

/-- **Absolute total-Casimir magnetization lower bound**: a non-zero
`(Ŝ_tot)²`-eigenvector at `γ` lying in `magSubspaceS V N M` (with `M` a real
weight, `M.im = 0`) satisfies `|M.re|·(|M.re|+1) ≤ γ.re`.  Combines the
non-negative-weight bound `totalSpinSSquared_eigenvalue_re_ge_of_mem_magSubspaceS`
with its negative-weight mirror. -/
private theorem totalSpinSSquared_eigenvalue_re_ge_abs_of_mem_magSubspaceS
    {γ M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hv_mem : v ∈ magSubspaceS V N M)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    |M.re| * (|M.re| + 1) ≤ γ.re := by
  rcases le_total 0 M.re with hpos | hneg
  · have h := totalSpinSSquared_eigenvalue_re_ge_of_mem_magSubspaceS hv hv_mem hpos hcas
    rwa [abs_of_nonneg hpos]
  · have h := totalSpinSSquared_eigenvalue_re_ge_neg_of_mem_magSubspaceS hv hv_mem hneg hcas
    rw [abs_of_nonpos hneg]
    nlinarith [h]

/-! ## Outside-sector arithmetic -/

omit [DecidableEq V] in
/-- **Outside-sector centered-weight bound**: if `M` lies outside the admissible
interval `tasaki23GroundStateSectors A N = [min·N, max·N]`, then the centered
weight `center − M` (with `center = |V|·N/2`) has absolute value strictly greater
than the predicted total spin `S_tot = ||A|−|¬A||·N/2`. -/
private theorem abs_centered_weight_gt_predictedTotalSpin_of_not_mem
    (A : V → Bool) (N M : ℕ)
    (hM_non : M ∉ tasaki23GroundStateSectors (V := V) A N) :
    tasaki23PredictedTotalSpin (V := V) A N <
      |(Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)| := by
  classical
  set cA := (Finset.univ.filter (fun x : V => A x = true)).card with hcA
  set cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcB
  have hsum : cA + cB = Fintype.card V := tasaki23_card_filter_A_add_card_notA A
  -- Predicted spin in real terms.
  have hStot : tasaki23PredictedTotalSpin (V := V) A N =
      |(cA : ℝ) - (cB : ℝ)| * ((N : ℝ) / 2) := rfl
  rw [tasaki23GroundStateSectors_not_mem_iff_lt_left_or_right_lt] at hM_non
  have hcardR : (Fintype.card V : ℝ) = (cA : ℝ) + (cB : ℝ) := by exact_mod_cast hsum.symm
  rcases hM_non with hlt | hgt
  · -- `M < min·N`: centered weight `center − M > S_tot`.
    have hMlt : (M : ℝ) < (min cA cB : ℝ) * (N : ℝ) := by
      have h : (M : ℝ) < ((min cA cB * N : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at h; exact h
    have hpos : 0 ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) := by
      have hmin_le : (min cA cB : ℝ) * (N : ℝ) ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 := by
        rw [hcardR]
        have : (min cA cB : ℝ) ≤ ((cA : ℝ) + (cB : ℝ)) / 2 := by
          rcases le_total (cA : ℝ) (cB : ℝ) with h | h
          · rw [min_eq_left h]; linarith
          · rw [min_eq_right h]; linarith
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      linarith
    rw [abs_of_nonneg hpos, hStot]
    have hStot_le : |(cA : ℝ) - (cB : ℝ)| * ((N : ℝ) / 2) =
        (Fintype.card V : ℝ) * (N : ℝ) / 2 - (min cA cB : ℝ) * (N : ℝ) := by
      rw [hcardR]
      rcases le_total (cA : ℝ) (cB : ℝ) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    rw [hStot_le]; linarith
  · -- `max·N < M`: centered weight `center − M < −S_tot`, so abs `> S_tot`.
    have hMgt : (max cA cB : ℝ) * (N : ℝ) < (M : ℝ) := by
      have h : ((max cA cB * N : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hgt
      push_cast at h; exact h
    have hneg : (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) ≤ 0 := by
      have hmax_ge : (Fintype.card V : ℝ) * (N : ℝ) / 2 ≤ (max cA cB : ℝ) * (N : ℝ) := by
        rw [hcardR]
        have : ((cA : ℝ) + (cB : ℝ)) / 2 ≤ (max cA cB : ℝ) := by
          rcases le_total (cA : ℝ) (cB : ℝ) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      linarith
    rw [abs_of_nonpos hneg, hStot]
    have hStot_eq : |(cA : ℝ) - (cB : ℝ)| * ((N : ℝ) / 2) =
        (max cA cB : ℝ) * (N : ℝ) - (Fintype.card V : ℝ) * (N : ℝ) / 2 := by
      rw [hcardR]
      rcases le_total (cA : ℝ) (cB : ℝ) with h | h
      · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
    rw [hStot_eq]; linarith

/-! ## Backward Casimir transfer through the ladder -/

/-- **Lowering iterate is injective on a positive-weight magnetization sector**: if
`x ∈ magSubspaceS V N w₀`, every intermediate lowering weight `w₀ − j`
(`j < k`) has positive real part, and `(Ŝ⁻_tot)^k · x = 0`, then `x = 0`.
This is the contrapositive of the non-vanishing iterate `lower_iterate_ne_zero`
(taking `J = 0` so the energy hypothesis is vacuous). -/
private theorem totalSpinSOpMinus_pow_mulVec_eq_zero_imp_eq_zero
    {k : ℕ} {w₀ : ℂ} {x : (V → Fin (N + 1)) → ℂ}
    (hx_mem : x ∈ magSubspaceS V N w₀)
    (hpos : ∀ j : ℕ, j < k → 0 < (w₀ - (j : ℂ)).re)
    (hkill : (totalSpinSOpMinus V N ^ k).mulVec x = 0) :
    x = 0 := by
  by_contra hx_ne
  have hx_eig : (heisenbergHamiltonianS (fun _ _ => (0 : ℂ)) N).mulVec x =
      ((0 : ℝ) : ℂ) • x := by
    rw [heisenbergHamiltonianS_zero, Matrix.zero_mulVec, Complex.ofReal_zero, zero_smul]
  obtain ⟨hne, _, _⟩ :=
    lower_iterate_ne_zero (V := V) (N := N) (J := fun _ _ => (0 : ℂ)) (lam := (0 : ℝ)) k
      hx_ne hx_mem hx_eig hpos
  exact hne hkill

/-- **Raising iterate is injective on a negative-weight magnetization sector**:
mirror of `totalSpinSOpMinus_pow_mulVec_eq_zero_imp_eq_zero`. -/
private theorem totalSpinSOpPlus_pow_mulVec_eq_zero_imp_eq_zero
    {k : ℕ} {w₀ : ℂ} {x : (V → Fin (N + 1)) → ℂ}
    (hx_mem : x ∈ magSubspaceS V N w₀)
    (hneg : ∀ j : ℕ, j < k → (w₀ + (j : ℂ)).re < 0)
    (hkill : (totalSpinSOpPlus V N ^ k).mulVec x = 0) :
    x = 0 := by
  by_contra hx_ne
  have hx_eig : (heisenbergHamiltonianS (fun _ _ => (0 : ℂ)) N).mulVec x =
      ((0 : ℝ) : ℂ) • x := by
    rw [heisenbergHamiltonianS_zero, Matrix.zero_mulVec, Complex.ofReal_zero, zero_smul]
  obtain ⟨hne, _, _⟩ :=
    raise_iterate_ne_zero (V := V) (N := N) (J := fun _ _ => (0 : ℂ)) (lam := (0 : ℝ)) k
      hx_ne hx_mem hx_eig hneg
  exact hne hkill

/-- **Backward Casimir transfer, lowering direction**: if `Φ ∈ magSubspaceS V N w₀`,
all intermediate lowering weights `w₀ − j` (`j < k`) are positive, and the landed
vector `(Ŝ⁻_tot)^k · Φ` is a `(Ŝ_tot)²`-eigenvector at `γ`, then `Φ` itself is a
`(Ŝ_tot)²`-eigenvector at `γ`.  Uses that `(Ŝ_tot)²` commutes with `(Ŝ⁻_tot)^k`
and injectivity of the lowering iterate on the positive-weight sector. -/
private theorem totalSpinSSquared_mulVec_eq_of_lower_landed_casimir
    {k : ℕ} {w₀ γ : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ_mem : Φ ∈ magSubspaceS V N w₀)
    (hpos : ∀ j : ℕ, j < k → 0 < (w₀ - (j : ℂ)).re)
    (hland_cas : (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N ^ k).mulVec Φ) =
      γ • (totalSpinSOpMinus V N ^ k).mulVec Φ) :
    (totalSpinSSquared V N).mulVec Φ = γ • Φ := by
  -- `x := Ŝ²Φ − γΦ` lies in the same sector and is killed by `(Ŝ⁻)^k`.
  have hx_mem : (totalSpinSSquared V N).mulVec Φ - γ • Φ ∈ magSubspaceS V N w₀ :=
    Submodule.sub_mem _ (totalSpinSSquared_mulVec_mem_magSubspaceS (N := N) w₀ hΦ_mem)
      (Submodule.smul_mem _ _ hΦ_mem)
  have hcomm := (totalSpinSSquared_commute_totalSpinSOpMinus_pow (V := V) (N := N) k).symm
  have hswap : (totalSpinSOpMinus V N ^ k).mulVec ((totalSpinSSquared V N).mulVec Φ) =
      (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N ^ k).mulVec Φ) := by
    rw [Matrix.mulVec_mulVec, hcomm, Matrix.mulVec_mulVec]
  have hkill : (totalSpinSOpMinus V N ^ k).mulVec
      ((totalSpinSSquared V N).mulVec Φ - γ • Φ) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hswap, hland_cas]
    abel
  have hx_zero := totalSpinSOpMinus_pow_mulVec_eq_zero_imp_eq_zero hx_mem hpos hkill
  rwa [sub_eq_zero] at hx_zero

/-- **Backward Casimir transfer, raising direction**: mirror of
`totalSpinSSquared_mulVec_eq_of_lower_landed_casimir`. -/
private theorem totalSpinSSquared_mulVec_eq_of_raise_landed_casimir
    {k : ℕ} {w₀ γ : ℂ} {Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ_mem : Φ ∈ magSubspaceS V N w₀)
    (hneg : ∀ j : ℕ, j < k → (w₀ + (j : ℂ)).re < 0)
    (hland_cas : (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N ^ k).mulVec Φ) =
      γ • (totalSpinSOpPlus V N ^ k).mulVec Φ) :
    (totalSpinSSquared V N).mulVec Φ = γ • Φ := by
  have hx_mem : (totalSpinSSquared V N).mulVec Φ - γ • Φ ∈ magSubspaceS V N w₀ :=
    Submodule.sub_mem _ (totalSpinSSquared_mulVec_mem_magSubspaceS (N := N) w₀ hΦ_mem)
      (Submodule.smul_mem _ _ hΦ_mem)
  have hcomm := (totalSpinSSquared_commute_totalSpinSOpPlus_pow (V := V) (N := N) k).symm
  have hswap : (totalSpinSOpPlus V N ^ k).mulVec ((totalSpinSSquared V N).mulVec Φ) =
      (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N ^ k).mulVec Φ) := by
    rw [Matrix.mulVec_mulVec, hcomm, Matrix.mulVec_mulVec]
  have hkill : (totalSpinSOpPlus V N ^ k).mulVec
      ((totalSpinSSquared V N).mulVec Φ - γ • Φ) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hswap, hland_cas]
    abel
  have hx_zero := totalSpinSOpPlus_pow_mulVec_eq_zero_imp_eq_zero hx_mem hneg hkill
  rwa [sub_eq_zero] at hx_zero

/-! ## Sector-PF Casimir-value transfer (predicted, non-zero) -/

/-- **Casimir-value transfer along a one-dimensional sector ground line**: if the
full Heisenberg `μ`-eigenspace restricted to sector `M` is at most one-dimensional
and contains a non-zero sector-supported vector `Φ0` with total-Casimir eigenvalue
`γ`, then every other sector-supported full eigenvector `Ψ` at `μ` also has
total-Casimir eigenvalue `γ`.  Value-parametrized generalization of
`heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_zero_of_sector_pf_zero_casimir`
(`γ = 0`). -/
private theorem heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_of_sector_pf_casimir
    (J : V → V → ℂ) (M : ℕ) (μ γ : ℂ)
    {Φ0 Ψ : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = μ • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = γ • Φ0)
    (hΨ_eig : (heisenbergHamiltonianS J N).mulVec Ψ = μ • Ψ)
    (hΨ_mem : Ψ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M)) μ) ≤ 1) :
    (totalSpinSSquared V N).mulVec Ψ = γ • Ψ := by
  classical
  set E := End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
    with hEdef
  set Asub :=
    magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ))
    with hAdef
  have hline : finrank ℂ ↥(E ⊓ Asub) ≤ 1 := by
    subst E
    subst Asub
    exact heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
      (Λ := V) (N := N) J M μ h_sector_pf
  have hΦ0_in : Φ0 ∈ E ⊓ Asub := by
    refine ⟨?_, ?_⟩
    · change Φ0 ∈ End.eigenspace
        (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΦ0_eig
    · rw [hAdef]; exact hΦ0_mem
  have hΨ_in : Ψ ∈ E ⊓ Asub := by
    refine ⟨?_, ?_⟩
    · change Ψ ∈ End.eigenspace
        (Matrix.toLin' (heisenbergHamiltonianS (Λ := V) J N)) μ
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΨ_eig
    · rw [hAdef]; exact hΨ_mem
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hline
  obtain ⟨a, ha⟩ := hv ⟨Φ0, hΦ0_in⟩
  obtain ⟨b, hb⟩ := hv ⟨Ψ, hΨ_in⟩
  have ha' : a • (v : (V → Fin (N + 1)) → ℂ) = Φ0 := by
    have h := congrArg ((↑) : ↥(E ⊓ Asub) → (V → Fin (N + 1)) → ℂ) ha
    simpa using h
  have hb' : b • (v : (V → Fin (N + 1)) → ℂ) = Ψ := by
    have h := congrArg ((↑) : ↥(E ⊓ Asub) → (V → Fin (N + 1)) → ℂ) hb
    simpa using h
  have ha_ne : a ≠ 0 := by
    intro h0; apply hΦ0_ne; rw [← ha', h0, zero_smul]
  have hΨ_eq : Ψ = (b * a⁻¹) • Φ0 := by
    rw [← hb', ← ha', smul_smul]
    have hscalar : (b * a⁻¹) * a = b := by
      rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]
    rw [hscalar]
  rw [hΨ_eq, Matrix.mulVec_smul, hΦ0_cas, smul_comm]

/-- **Lowering-landed predicted-Casimir bridge**: lowering a non-zero full
Heisenberg `μ`-eigenvector `Φ` (from sector `M` for `k` valid steps) lands in
sector `M + k` non-zero with total-Casimir eigenvalue `γ`, given the edge witness
`Φ0` at Casimir `γ` and edge finrank `≤ 1`.  Value-parametrized generalization of
`heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_eq_zero_of_sector_pf`. -/
private theorem heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_casimir
    (J : V → V → ℂ) (M k : ℕ) (μ : ℝ) (γ : ℂ)
    {Φ0 Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = γ • Φ0)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_mem : Φ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hpos : ∀ j : ℕ, j < k →
      0 < ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) - (j : ℂ)).re)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N (M + k))) (μ : ℂ)) ≤ 1) :
    ((totalSpinSOpMinus V N ^ k).mulVec Φ ≠ 0) ∧
      (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N ^ k).mulVec Φ) =
        γ • (totalSpinSOpMinus V N ^ k).mulVec Φ := by
  classical
  obtain ⟨hland_ne, hland_mem, hland_eig⟩ :=
    lower_iterate_ne_zero (V := V) (N := N) (J := J) (lam := μ) k
      hΦ_ne hΦ_mem hΦ_eig hpos
  have hidx : ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ) - (k : ℂ) =
      ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ) := by push_cast; ring
  have hland_mem' :
      (totalSpinSOpMinus V N ^ k).mulVec Φ ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)) := by
    rwa [hidx] at hland_mem
  refine ⟨hland_ne, ?_⟩
  exact heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_of_sector_pf_casimir
    (V := V) (N := N) J (M + k) (μ : ℂ) γ
    hΦ0_ne hΦ0_eig hΦ0_mem hΦ0_cas hland_eig hland_mem' h_sector_pf

/-- **Raising-landed predicted-Casimir bridge**: raising mirror of
`heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_casimir`. -/
private theorem heisenbergHamiltonianS_totalSpinSSquared_mulVec_raise_landed_casimir
    (J : V → V → ℂ) (M k : ℕ) (μ : ℝ) (γ : ℂ)
    {Φ0 Φ : (V → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = γ • Φ0)
    (hΦ_ne : Φ ≠ 0)
    (hΦ_mem : Φ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)))
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hneg : ∀ j : ℕ, j < k →
      ((((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)) + (j : ℂ)).re < 0)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M)) (μ : ℂ)) ≤ 1) :
    ((totalSpinSOpPlus V N ^ k).mulVec Φ ≠ 0) ∧
      (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N ^ k).mulVec Φ) =
        γ • (totalSpinSOpPlus V N ^ k).mulVec Φ := by
  classical
  obtain ⟨hland_ne, hland_mem, hland_eig⟩ :=
    raise_iterate_ne_zero (V := V) (N := N) (J := J) (lam := μ) k
      hΦ_ne hΦ_mem hΦ_eig hneg
  have hland_mem' :
      (totalSpinSOpPlus V N ^ k).mulVec Φ ∈
        magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) := by
    have hidx : ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ) + (k : ℂ) =
        ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ) := by push_cast; ring
    rwa [hidx] at hland_mem
  refine ⟨hland_ne, ?_⟩
  exact heisenbergHamiltonianS_totalSpinSSquared_mulVec_eq_of_sector_pf_casimir
    (V := V) (N := N) J M (μ : ℂ) γ
    hΦ0_ne hΦ0_eig hΦ0_mem hΦ0_cas hland_eig hland_mem' h_sector_pf

/-! ## Predicted-Casimir / outside-weight contradiction -/

omit [DecidableEq V] in
/-- **Predicted Casimir is strictly below the outside-sector Casimir lower bound**:
for a sector `M ∉ tasaki23GroundStateSectors A N`, with centered weight
`w = center − M`, the predicted Casimir value `S_tot(S_tot+1)` is strictly less
than `|w|·(|w|+1)`. -/
private theorem tasaki23PredictedCasimirValue_lt_abs_centered_weight_of_not_mem
    (A : V → Bool) (N M : ℕ)
    (hM_non : M ∉ tasaki23GroundStateSectors (V := V) A N) :
    tasaki23PredictedCasimirValue (V := V) A N <
      |(Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)| *
        (|(Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ)| + 1) := by
  have hgt := abs_centered_weight_gt_predictedTotalSpin_of_not_mem (V := V) A N M hM_non
  have hStot_nn : 0 ≤ tasaki23PredictedTotalSpin (V := V) A N := by
    rw [tasaki23PredictedTotalSpin]
    positivity
  rw [tasaki23PredictedCasimirValue]
  nlinarith [hgt, hStot_nn]

/-- **Strict outside-sector ordering (ferrimagnetic), from the predicted-Casimir
ladder obstruction**.  General-`|A| ≠ |B|` analogue of
`tasaki23_strict_hOutside_of_card_eq_zero_casimir_ladder_obstruction`: the
non-strict `hOutside` bound `μ ≤ μM` from `tasaki23_general_hOutside` is upgraded
to a STRICT bound `μ < μM` for any non-admissible sector `M`, using the
predicted-Casimir band-edge witness and the SU(2) Casimir lower bound.

The band edge into which the inward ladder lands is `min·N` (when `M < min·N`,
lowering direction, witness `Φ0_min`) or `max·N` (when `max·N < M`, raising
direction, witness `Φ0_max`).  Each edge witness is a non-zero full Heisenberg
`μ`-eigenvector in the edge sector with total-Casimir eigenvalue the predicted
value, and the edge eigenspace is one-dimensional. -/
theorem tasaki23_strict_hOutside_ferrimagnetic
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
    -- Left band-edge (`min·N`) predicted-Casimir witness + finrank.
    {Φ0_min : (V → Fin (N + 1)) → ℂ}
    (hΦ0min_ne : Φ0_min ≠ 0)
    (hΦ0min_eig : (heisenbergHamiltonianS J N).mulVec Φ0_min = (μ : ℂ) • Φ0_min)
    (hΦ0min_mem : Φ0_min ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
      ((min (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N : ℕ) : ℂ)))
    (hΦ0min_cas : (totalSpinSSquared V N).mulVec Φ0_min =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ0_min)
    (h_pf_min : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
        (min (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N))) (μ : ℂ)) ≤ 1)
    -- Right band-edge (`max·N`) predicted-Casimir witness + finrank.
    {Φ0_max : (V → Fin (N + 1)) → ℂ}
    (hΦ0max_ne : Φ0_max ≠ 0)
    (hΦ0max_eig : (heisenbergHamiltonianS J N).mulVec Φ0_max = (μ : ℂ) • Φ0_max)
    (hΦ0max_mem : Φ0_max ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
      ((max (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N : ℕ) : ℂ)))
    (hΦ0max_cas : (totalSpinSSquared V N).mulVec Φ0_max =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ0_max)
    (h_pf_max : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
        (max (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N))) (μ : ℂ)) ≤ 1)
    {M : ℕ}
    (hM_non : M ∉ tasaki23GroundStateSectors (V := V) A N)
    [Nonempty (magConfigS V N M)]
    {μM : ℝ} {φ : magConfigS V N M → ℝ}
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ) :
    μ < μM := by
  classical
  set cardA := (Finset.univ.filter (fun x : V => A x = true)).card with hcardA
  set cardB := (Finset.univ.filter (fun x : V => (! A x) = true)).card with hcardB
  -- Non-strict bound first.
  have hle : μ ≤ μM :=
    tasaki23_general_hOutside A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hcommon hM_non hφ_ne hφ
  -- Kill the equality case `μ = μM`.
  have hne : μ ≠ μM := by
    intro hμ_eq
    -- Lift `φ` to a full Heisenberg `μ`-eigenvector `Φ` in centered weight `center − M`.
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
        rw [hΦdef]; exact magSectorEmbedding_apply_subtype _ τ
      rw [h0] at happ
      simp only [Pi.zero_apply] at happ
      have := congrArg Complex.re happ
      simpa using this.symm
    have hΦ_mem :
        Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
      rw [hΦdef]; exact magSectorEmbedding_mem_magSubspaceS (fun σ => ((φ σ : ℝ) : ℂ))
    have hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ := by
      rw [hΦdef]; simpa [hμ_eq] using hHμM
    -- Setup for the SU(2)/Casimir contradiction.
    set p : ℝ := tasaki23PredictedCasimirValue (V := V) A N with hpdef
    have hsum : cardA + cardB = Fintype.card V := tasaki23_card_filter_A_add_card_notA A
    have hmax_le_card : max cardA cardB ≤ Fintype.card V := by
      rw [← hsum]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    -- The pulled-back predicted Casimir on `Φ`.
    have hΦ_cas : (totalSpinSSquared V N).mulVec Φ = (p : ℂ) • Φ := by
      rw [tasaki23GroundStateSectors_not_mem_iff_lt_left_or_right_lt] at hM_non
      rcases hM_non with hlt | hgt
      · -- `M < min·N`: lower `k = min·N − M` steps to the left band edge.
        set k := min cardA cardB * N - M with hk
        have hMle : M ≤ min cardA cardB * N := le_of_lt hlt
        have hkval : (min cardA cardB * N : ℕ) = M + k := by rw [hk]; omega
        have hpos : ∀ j : ℕ, j < k →
            0 < (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) - (j : ℂ)).re := by
          intro j hj
          rw [weightSubRe]
          have h2 : ((min cardA cardB * N : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 := by
            have h2card : 2 * min cardA cardB ≤ Fintype.card V := by rw [← hsum]; omega
            have hcast : ((min cardA cardB * N : ℕ) : ℝ) =
                (min cardA cardB : ℝ) * (N : ℝ) := by push_cast; ring
            have h2r : (2 : ℝ) * (min cardA cardB : ℝ) ≤ (Fintype.card V : ℝ) := by
              exact_mod_cast h2card
            rw [hcast]; nlinarith [Nat.cast_nonneg (α := ℝ) N, h2r]
          have hjlt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
          have hkr : (M : ℝ) + (k : ℝ) = ((min cardA cardB * N : ℕ) : ℝ) := by
            exact_mod_cast hkval.symm
          nlinarith [h2, hjlt, hkr]
        -- The landed vector at the edge has predicted Casimir (finrank ≤ 1 pinning).
        have hΦ0min_mem' : Φ0_min ∈ magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - ((M + k : ℕ) : ℂ)) := by
          rw [show (M + k : ℕ) = min cardA cardB * N by omega]; exact hΦ0min_mem
        have h_pf_min' : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N (M + k))) (μ : ℂ)) ≤ 1 := by
          rw [show (M + k : ℕ) = min cardA cardB * N by omega]; exact h_pf_min
        obtain ⟨_hland_ne, hland_cas⟩ :=
          heisenbergHamiltonianS_totalSpinSSquared_mulVec_lower_landed_casimir
            (V := V) (N := N) J M k μ (p : ℂ) hΦ0min_ne hΦ0min_eig hΦ0min_mem' hΦ0min_cas
            hΦ_ne hΦ_mem hΦ_eig hpos h_pf_min'
        -- Pull predicted Casimir back to `Φ`.
        exact totalSpinSSquared_mulVec_eq_of_lower_landed_casimir
          (V := V) (N := N) (k := k)
          (w₀ := ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) (γ := (p : ℂ))
          hΦ_mem hpos hland_cas
      · -- `max·N < M`: raise `k = M − max·N` steps to the right band edge.
        set k := M - max cardA cardB * N with hk
        have hMge : max cardA cardB * N ≤ M := le_of_lt hgt
        have hkval : M = max cardA cardB * N + k := by rw [hk]; omega
        have hneg : ∀ j : ℕ, j < k →
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((max cardA cardB * N + k : ℕ) : ℂ) +
              (j : ℂ)).re < 0 := by
          intro j hj
          rw [show ((max cardA cardB * N + k : ℕ) : ℂ) = (M : ℂ) by exact_mod_cast hkval.symm]
          rw [weightAddRe]
          have h2 : (Fintype.card V : ℝ) * (N : ℝ) / 2 ≤ ((max cardA cardB * N : ℕ) : ℝ) := by
            have h2card : Fintype.card V ≤ 2 * max cardA cardB := by rw [← hsum]; omega
            have hcast : ((max cardA cardB * N : ℕ) : ℝ) =
                (max cardA cardB : ℝ) * (N : ℝ) := by push_cast; ring
            have h2r : (Fintype.card V : ℝ) ≤ (2 : ℝ) * (max cardA cardB : ℝ) := by
              exact_mod_cast h2card
            rw [hcast]; nlinarith [Nat.cast_nonneg (α := ℝ) N, h2r]
          have hjlt : (j : ℝ) < (k : ℝ) := by exact_mod_cast hj
          have hkr : (M : ℝ) = ((max cardA cardB * N : ℕ) : ℝ) + (k : ℝ) := by
            exact_mod_cast hkval
          nlinarith [h2, hjlt, hkr]
        have hΦ_mem' :
            Φ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) -
              ((max cardA cardB * N + k : ℕ) : ℂ)) := by
          rw [show ((max cardA cardB * N + k : ℕ) : ℂ) = (M : ℂ) by exact_mod_cast hkval.symm]
          exact hΦ_mem
        obtain ⟨_hland_ne, hland_cas⟩ :=
          heisenbergHamiltonianS_totalSpinSSquared_mulVec_raise_landed_casimir
            (V := V) (N := N) J (max cardA cardB * N) k μ (p : ℂ)
            hΦ0max_ne hΦ0max_eig hΦ0max_mem hΦ0max_cas hΦ_ne hΦ_mem' hΦ_eig hneg h_pf_max
        -- Pull predicted Casimir back to `Φ`.
        have hneg' : ∀ j : ℕ, j < k →
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) + (j : ℂ)).re < 0 := by
          intro j hj
          have := hneg j hj
          rwa [show ((max cardA cardB * N + k : ℕ) : ℂ) = (M : ℂ) by exact_mod_cast hkval.symm]
            at this
        exact totalSpinSSquared_mulVec_eq_of_raise_landed_casimir
          (V := V) (N := N) (k := k)
          (w₀ := ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) (γ := (p : ℂ))
          hΦ_mem hneg' hland_cas
    -- Casimir lower bound vs. predicted-value contradiction.
    have habs := totalSpinSSquared_eigenvalue_re_ge_abs_of_mem_magSubspaceS
      (V := V) (N := N) hΦ_ne hΦ_mem hΦ_cas
    have hweight_re :
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)).re =
          (Fintype.card V : ℝ) * (N : ℝ) / 2 - (M : ℝ) := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [hweight_re] at habs
    have hp_re : ((p : ℝ) : ℂ).re = p := Complex.ofReal_re p
    rw [hp_re] at habs
    have hlt := tasaki23PredictedCasimirValue_lt_abs_centered_weight_of_not_mem
      (V := V) A N M hM_non
    rw [← hpdef] at hlt
    linarith
  exact lt_of_le_of_ne hle hne

end LatticeSystem.Quantum
