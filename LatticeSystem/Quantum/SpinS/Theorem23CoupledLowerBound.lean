import LatticeSystem.Quantum.SpinS.Theorem23TotalLowestWeightExistence
import LatticeSystem.Quantum.SpinS.Theorem23SublatticeMagBoundOneSide
import LatticeSystem.Quantum.SpinS.Theorem23Casimir

/-!
# The coupled total-spin lower bound `(Ŝ_tot)² ≥ |a−b|(|a−b|+1)`

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 3b — the Clebsch–Gordan triangle inequality (see
`.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

On the joint sublattice-Casimir eigenspace `W_{a,b}` (`(Ŝ_A)² = a(a+1)`,
`(Ŝ_¬A)² = b(b+1)`), every `(Ŝ_tot)²`-eigenvalue is `≥ |a−b|(|a−b|+1)`.  Reducing to a
total lowest weight `w'` (#3722) at the same three eigenvalues, the one-sided
magnetization bound (#3721) applied to both `A` and `¬A` gives `M.re ≤ b−a` and
`M.re ≤ a−b`, i.e. `|M.re| ≥ |a−b|`; the total lowest-weight Casimir relation
`(Ŝ_tot)² w' = M(M−1) w'` then gives `γ.re = M.re² − M.re ≥ |a−b|(|a−b|+1)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Coupled total-spin lower bound** (Clebsch–Gordan triangle inequality): a non-zero
`(Ŝ_tot)²`-eigenvector `ψ` (eigenvalue `γ`) in the magnetization level `k − |V|·N/2`
that is also an `(Ŝ_A)²`- and `(Ŝ_¬A)²`-eigenvector at `a(a+1)` and `b(b+1)`
(`a, b ≥ 0`) satisfies `|a − b|(|a − b| + 1) ≤ γ.re`. -/
theorem totalSpinSSquared_re_ge_coupled (A : V → Bool) (k : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {γ : ℂ} {ψ : (V → Fin (N + 1)) → ℂ} (hψ_ne : ψ ≠ 0)
    (hψ_mem : ψ ∈ magSubspaceS V N ((k : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)))
    (hγ : (totalSpinSSquared V N).mulVec ψ = γ • ψ)
    (hα : (sublatticeSpinSquaredS N A).mulVec ψ = ((a * (a + 1) : ℝ) : ℂ) • ψ)
    (hβ : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec ψ =
      ((b * (b + 1) : ℝ) : ℂ) • ψ) :
    |a - b| * (|a - b| + 1) ≤ γ.re := by
  -- Reduce to a total lowest weight w' at the same three eigenvalues.
  obtain ⟨M, w, hw_ne, hw_mem, hw_ker, hw_γ, hw_α, hw_β⟩ :=
    exists_total_lowestWeight_joint A k hψ_ne hψ_mem hγ hα hβ
  have hztot : (totalSpinSOp3 V N).mulVec w = M • w := (mem_magSubspaceS_iff M w).mp hw_mem
  -- One-sided bounds from `A` and (by the `¬A` mirror) from `¬A`.
  have hMA : M.re ≤ b - a :=
    totalLowestWeight_re_le_complement_sub A ha hb hw_ne hztot hw_ker hw_α hw_β
  have hβ' : (sublatticeSpinSquaredS N (fun x => ! (! A x))).mulVec w =
      ((a * (a + 1) : ℝ) : ℂ) • w := by
    have hnotnot : (fun x => ! (! A x)) = A := by funext x; simp
    rw [hnotnot]; exact hw_α
  have hMB : M.re ≤ a - b :=
    totalLowestWeight_re_le_complement_sub (fun x => ! A x) hb ha hw_ne hztot hw_ker hw_β hβ'
  -- Hence |a − b| ≤ −M.re, i.e. M.re ≤ −|a − b|.
  have habs : |a - b| ≤ -M.re := abs_le.mpr ⟨by linarith, by linarith⟩
  -- Total lowest-weight Casimir: γ = M(M−1); M is real.
  have hcas : (totalSpinSSquared V N).mulVec w = (M * (M - 1)) • w :=
    tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpMinus_eq_zero_of_mem_magSubspaceS hw_mem hw_ker
  have hγM : γ = M * (M - 1) :=
    smul_left_injective ℂ hw_ne (hw_γ.symm.trans hcas)
  have hM_im : M.im = 0 :=
    Complex.conj_eq_iff_im.mp
      (isHermitian_eigenvalue_star_eq (totalSpinSOp3_isHermitian V N) hztot hw_ne)
  have hγ_re : γ.re = M.re * M.re - M.re := by
    rw [hγM]
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      hM_im, mul_zero, sub_zero]
    ring
  rw [hγ_re]
  nlinarith [habs, abs_nonneg (a - b)]

end LatticeSystem.Quantum
