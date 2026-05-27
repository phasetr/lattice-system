import LatticeSystem.Quantum.SpinS.Theorem23CoupledLowerBound
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeCasimirNonneg
import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyArith
import LatticeSystem.Quantum.SpinS.SublatticeCasimirSpectralBound

/-!
# The toy-Hamiltonian minimum-energy bound `Ĥ_toy ≥ E`

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) —
assembling the coupled total-spin lower bound (#3723) with the arithmetic core (#3716).

A simultaneous eigenvector of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` (eigenvalues
`γ_tot, γ_A, γ_B`) at a magnetization level has toy energy
`(γ_tot − γ_A − γ_B).re ≥ E`, where
`E = (s_A−s_B)(s_A−s_B+1) − s_A(s_A+1) − s_B(s_B+1)` (the predicted toy minimum).
Writing the (non-negative, ≤ `s(s+1)`) sublattice Casimir eigenvalues as `a(a+1)`,
`b(b+1)` (real spins `0 ≤ a ≤ s_A`, `0 ≤ b ≤ s_B`), the coupled bound gives
`γ_tot.re ≥ |a−b|(|a−b|+1)`, hence
`(γ_tot − γ_A − γ_B).re ≥ |a−b|(|a−b|+1) − a(a+1) − b(b+1) = f(a,b) ≥ f(s_A,s_B) = E`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Extract a real spin `0 ≤ a ≤ s` with `a(a+1) = γ` from a Casimir eigenvalue
`0 ≤ γ ≤ s(s+1)`. -/
private theorem exists_spin_of_casimir {γ s : ℝ} (hs : 0 ≤ s) (hγ0 : 0 ≤ γ)
    (hγs : γ ≤ s * (s + 1)) : ∃ a : ℝ, 0 ≤ a ∧ a ≤ s ∧ a * (a + 1) = γ := by
  have h4 : 0 ≤ 1 + 4 * γ := by linarith
  refine ⟨(Real.sqrt (1 + 4 * γ) - 1) / 2, ?_, ?_, ?_⟩
  · have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + 4 * γ) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * γ by linarith)
      rwa [Real.sqrt_one] at this
    linarith
  · nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (1 + 4 * γ)]
  · have hsq := Real.sq_sqrt h4
    nlinarith [hsq, Real.sqrt_nonneg (1 + 4 * γ)]

/-- **Toy minimum-energy bound**: a joint `(Ŝ_tot)²`/`(Ŝ_A)²`/`(Ŝ_¬A)²`-eigenvector `ψ`
(eigenvalues `γ_tot, γ_A, γ_B`) in the magnetization level `k − |V|·N/2` has toy energy
`(γ_tot − γ_A − γ_B).re ≥ E`, the predicted toy minimum. -/
theorem toy_joint_eigenvector_energy_re_ge (A : V → Bool) (k : ℕ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    {γ_tot γ_A γ_B : ℂ} {ψ : (V → Fin (N + 1)) → ℂ} (hψ_ne : ψ ≠ 0)
    (hψ_mem : ψ ∈ magSubspaceS V N ((k : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)))
    (htot : (totalSpinSSquared V N).mulVec ψ = γ_tot • ψ)
    (hA : (sublatticeSpinSquaredS N A).mulVec ψ = γ_A • ψ)
    (hB : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ψ = γ_B • ψ) :
    (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
            ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) + 1) -
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
        ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
          (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 + 1) ≤
      (γ_tot - γ_A - γ_B).re := by
  set sA : ℝ := ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 with hsA
  set sB : ℝ := ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2
    with hsB
  have hsA0 : 0 ≤ sA := by rw [hsA]; positivity
  have hsB0 : 0 ≤ sB := by rw [hsB]; positivity
  have hBA : sB ≤ sA := by
    rw [hsA, hsB]
    have : ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) := by exact_mod_cast horient
    have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith [this, hN]
  -- Sublattice Casimir eigenvalues are real and in [0, s(s+1)].
  have hA0 : 0 ≤ γ_A.re := sublatticeSpinSquaredS_eigenvalue_re_nonneg A hψ_ne hA
  have hAle : γ_A.re ≤ sA * (sA + 1) := sublatticeSpinSquaredS_eigenvalue_re_le_sA A hψ_ne hA
  have hB0 : 0 ≤ γ_B.re := sublatticeSpinSquaredS_eigenvalue_re_nonneg (fun x => ! A x) hψ_ne hB
  have hBle : γ_B.re ≤ sB * (sB + 1) :=
    sublatticeSpinSquaredS_eigenvalue_re_le_sA (fun x => ! A x) hψ_ne hB
  -- γ_A, γ_B are real.
  have hA_im : γ_A.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq (sublatticeSpinSquaredS_isHermitian (N := N) A) hA hψ_ne)
  have hB_im : γ_B.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq
        (sublatticeSpinSquaredS_isHermitian (N := N) (fun x => ! A x)) hB hψ_ne)
  -- Extract spins a, b.
  obtain ⟨a, ha0, haA, ha⟩ := exists_spin_of_casimir hsA0 hA0 hAle
  obtain ⟨b, hb0, hbB, hb⟩ := exists_spin_of_casimir hsB0 hB0 hBle
  -- Rewrite the Casimir eigen-equations in `a(a+1)`, `b(b+1)` form.
  have hA' : (sublatticeSpinSquaredS N A).mulVec ψ = ((a * (a + 1) : ℝ) : ℂ) • ψ := by
    rw [hA]; congr 1; rw [ha]; exact Complex.ext rfl (by rw [Complex.ofReal_im]; exact hA_im)
  have hB' : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ψ =
      ((b * (b + 1) : ℝ) : ℂ) • ψ := by
    rw [hB]; congr 1; rw [hb]; exact Complex.ext rfl (by rw [Complex.ofReal_im]; exact hB_im)
  -- Coupled lower bound.
  have hcoupled : |a - b| * (|a - b| + 1) ≤ γ_tot.re :=
    totalSpinSSquared_re_ge_coupled A k ha0 hb0 hψ_ne hψ_mem htot hA' hB'
  -- Arithmetic core.
  have harith : (sA - sB) * ((sA - sB) + 1) - sA * (sA + 1) - sB * (sB + 1) ≤
      |a - b| * (|a - b| + 1) - a * (a + 1) - b * (b + 1) :=
    tasaki23_toy_min_energy_arith a b sA sB ha0 hb0 haA hbB hBA
  -- Combine: (γ_tot − γ_A − γ_B).re = γ_tot.re − a(a+1) − b(b+1).
  have hre : (γ_tot - γ_A - γ_B).re = γ_tot.re - a * (a + 1) - b * (b + 1) := by
    rw [Complex.sub_re, Complex.sub_re, ha, hb]
  rw [hre]
  linarith [hcoupled, harith]

end LatticeSystem.Quantum
