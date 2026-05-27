import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyArithEq
import LatticeSystem.Quantum.SpinS.Theorem23Sectors

/-!
# A minimal-energy joint eigenvector has the predicted total Casimir

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a).

A joint `(Ŝ_tot)²`/`(Ŝ_A)²`/`(Ŝ_¬A)²`-eigenvector whose toy energy attains the predicted
minimum `E` has total Casimir exactly `tasaki23PredictedCasimirValue A N`.  This pins
the toy ground state (at every admissible sector) to the predicted total spin: the toy
minimum-energy bound (#3725) forces `(γ_tot − γ_A − γ_B).re = E`, and the equality form
of the arithmetic core (#3727) forces the sublattice spins to the corner `(s_A, s_B)`,
whence `γ_tot.re = (s_A−s_B)(s_A−s_B+1) = tasaki23PredictedCasimirValue`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- The predicted Casimir value equals `(s_A−s_B)(s_A−s_B+1)` in the canonical
orientation `|¬A| ≤ |A|`. -/
theorem tasaki23PredictedCasimirValue_eq_sub (A : V → Bool)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card) :
    tasaki23PredictedCasimirValue (V := V) A N =
      (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
          ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) + 1) := by
  unfold tasaki23PredictedCasimirValue tasaki23PredictedTotalSpin
  have hcard : ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) ≤
      ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) := by exact_mod_cast horient
  rw [abs_of_nonneg (by linarith)]
  ring

/-- **A minimal-energy joint eigenvector has the predicted total Casimir** (for
`|¬A| ≤ |A|`, non-degenerate `s_B > 0`): if the joint `(Ŝ_tot)²`/`(Ŝ_A)²`/`(Ŝ_¬A)²`-
eigenvector `ψ` (eigenvalues `γ_tot, γ_A, γ_B`) has toy energy `(γ_tot − γ_A − γ_B).re ≤ E`
(the predicted minimum), then `γ_tot = tasaki23PredictedCasimirValue A N`. -/
theorem toy_joint_eigenvector_totalCasimir_eq_predicted (A : V → Bool) (k : ℕ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    {γ_tot γ_A γ_B : ℂ} {ψ : (V → Fin (N + 1)) → ℂ} (hψ_ne : ψ ≠ 0)
    (hψ_mem : ψ ∈ magSubspaceS V N ((k : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)))
    (htot : (totalSpinSSquared V N).mulVec ψ = γ_tot • ψ)
    (hA : (sublatticeSpinSquaredS N A).mulVec ψ = γ_A • ψ)
    (hB : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ψ = γ_B • ψ)
    (henergy : (γ_tot - γ_A - γ_B).re ≤
      (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
          ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) + 1) -
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1)) :
    γ_tot = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) := by
  set sA : ℝ := ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 with hsA
  set sB : ℝ := ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2
    with hsB_def
  have hsA0 : 0 ≤ sA := by rw [hsA]; positivity
  have hsB0 : 0 ≤ sB := le_of_lt hsB
  -- Energy attains the minimum E exactly.
  have hge := toy_joint_eigenvector_energy_re_ge A k horient hψ_ne hψ_mem htot hA hB
  have henergy_eq : (γ_tot - γ_A - γ_B).re = (sA - sB) * ((sA - sB) + 1) -
      sA * (sA + 1) - sB * (sB + 1) := le_antisymm henergy hge
  -- Casimir eigenvalues are real and in [0, s(s+1)].
  have hA0 : 0 ≤ γ_A.re := sublatticeSpinSquaredS_eigenvalue_re_nonneg A hψ_ne hA
  have hAle : γ_A.re ≤ sA * (sA + 1) := sublatticeSpinSquaredS_eigenvalue_re_le_sA A hψ_ne hA
  have hB0 : 0 ≤ γ_B.re := sublatticeSpinSquaredS_eigenvalue_re_nonneg (fun x => ! A x) hψ_ne hB
  have hBle : γ_B.re ≤ sB * (sB + 1) :=
    sublatticeSpinSquaredS_eigenvalue_re_le_sA (fun x => ! A x) hψ_ne hB
  have hA_im : γ_A.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq (sublatticeSpinSquaredS_isHermitian (N := N) A) hA hψ_ne)
  have hB_im : γ_B.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq
        (sublatticeSpinSquaredS_isHermitian (N := N) (fun x => ! A x)) hB hψ_ne)
  have htot_im : γ_tot.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq (totalSpinSSquared_isHermitian (Λ := V) (N := N)) htot hψ_ne)
  -- Extract spins a, b and rewrite the Casimir eigen-equations.
  obtain ⟨a, ha0, haA, ha⟩ :
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ sA ∧ a * (a + 1) = γ_A.re := by
    have h4 : 0 ≤ 1 + 4 * γ_A.re := by linarith
    refine ⟨(Real.sqrt (1 + 4 * γ_A.re) - 1) / 2, ?_, ?_, ?_⟩
    · have : (1 : ℝ) ≤ Real.sqrt (1 + 4 * γ_A.re) := by
        have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * γ_A.re by linarith)
        rwa [Real.sqrt_one] at this
      linarith
    · nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (1 + 4 * γ_A.re), hAle]
    · nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (1 + 4 * γ_A.re)]
  obtain ⟨b, hb0, hbB, hb⟩ :
      ∃ b : ℝ, 0 ≤ b ∧ b ≤ sB ∧ b * (b + 1) = γ_B.re := by
    have h4 : 0 ≤ 1 + 4 * γ_B.re := by linarith
    refine ⟨(Real.sqrt (1 + 4 * γ_B.re) - 1) / 2, ?_, ?_, ?_⟩
    · have : (1 : ℝ) ≤ Real.sqrt (1 + 4 * γ_B.re) := by
        have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * γ_B.re by linarith)
        rwa [Real.sqrt_one] at this
      linarith
    · nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (1 + 4 * γ_B.re), hBle]
    · nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (1 + 4 * γ_B.re)]
  have hA' : (sublatticeSpinSquaredS N A).mulVec ψ = ((a * (a + 1) : ℝ) : ℂ) • ψ := by
    rw [hA]; congr 1; rw [ha]; exact Complex.ext rfl (by rw [Complex.ofReal_im]; exact hA_im)
  have hB' : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ψ =
      ((b * (b + 1) : ℝ) : ℂ) • ψ := by
    rw [hB]; congr 1; rw [hb]; exact Complex.ext rfl (by rw [Complex.ofReal_im]; exact hB_im)
  -- Coupled bound + the energy equality force `f(a,b) = f(s_A,s_B)`.
  have hcoupled : |a - b| * (|a - b| + 1) ≤ γ_tot.re :=
    totalSpinSSquared_re_ge_coupled A k ha0 hb0 hψ_ne hψ_mem htot hA' hB'
  have hre : (γ_tot - γ_A - γ_B).re = γ_tot.re - a * (a + 1) - b * (b + 1) := by
    rw [Complex.sub_re, Complex.sub_re, ha, hb]
  have hBA : sB ≤ sA := by
    rw [hsA, hsB_def]
    have hc : ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) := by exact_mod_cast horient
    nlinarith [hc, (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  have harith : (sA - sB) * ((sA - sB) + 1) - sA * (sA + 1) - sB * (sB + 1) ≤
      |a - b| * (|a - b| + 1) - a * (a + 1) - b * (b + 1) :=
    tasaki23_toy_min_energy_arith a b sA sB ha0 hb0 haA hbB hBA
  have hf_eq : |a - b| * (|a - b| + 1) - a * (a + 1) - b * (b + 1) =
      (sA - sB) * ((sA - sB) + 1) - sA * (sA + 1) - sB * (sB + 1) := by
    rw [hre] at henergy_eq
    linarith [hcoupled, harith, henergy_eq]
  -- Strict arithmetic: (a, b) = (s_A, s_B).
  obtain ⟨ha_eq, hb_eq⟩ := tasaki23_toy_min_energy_arith_eq a b sA sB ha0 hb0 haA hbB hsB hf_eq
  -- γ_tot.re = (s_A − s_B)(s_A − s_B + 1) = predicted.
  have hγre : γ_tot.re = (sA - sB) * ((sA - sB) + 1) := by
    have h := henergy_eq
    rw [hre, ha_eq, hb_eq] at h
    linear_combination h
  -- Conclude γ_tot = predicted (real).
  rw [tasaki23PredictedCasimirValue_eq_sub A horient]
  apply Complex.ext
  · rw [Complex.ofReal_re, ← hsA, ← hsB_def]; exact hγre
  · rw [Complex.ofReal_im]; exact htot_im

end LatticeSystem.Quantum
