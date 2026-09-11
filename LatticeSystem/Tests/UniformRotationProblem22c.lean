import LatticeSystem.Quantum.UniformRotationProblem22c

/-!
# Tests: Tasaki Problem 2.2.c, the rotated `|↑⟩₁|↓⟩₂` is determined by `n` alone (pp. 23-24)

Pins the exact public name/signature of the Problem 2.2.c capstone
`tasaki_problem_2_2_c_rotated_upDown_eq` before it exists (Red), plus non-vacuity and
non-triviality controls that are provable already from existing API (so the fixture type-checks
independently of the capstone) and fail the same way (`Unknown identifier`) only via **R0**, the
capstone shim, until the module is implemented.

* **R0** the capstone shim: restates the full `∀`-closed signature and closes it with the (not yet
  existing) capstone name, pinning every hypothesis/conclusion shape — the admissible class as a
  `Submonoid.closure` of the exponential global rotations, the same-`n` hypothesis at both sites,
  the pairwise conclusion.
* **PC1a/PC1b** non-vacuity: two distinct class members with the same `n = e₃` (`U = 1`,
  `V = exp(−iπ Ŝ_tot^{(3)})`) belong to the admissible class, so the capstone's conclusion is not
  vacuously true of an empty relation.
* **PC2** the value `V.mulVec |↑↓⟩ = |↑↓⟩`, computed independently of the capstone from the
  two-site `π`-rotation entries directly, confirming the value the capstone must reproduce.
* **NC1** widening the target vector to `|↑↑⟩` (`M_tot ≠ 0`) makes the analogous statement false:
  `V = exp(−iπ Ŝ_tot^{(3)})` sends `|↑↑⟩` to `−|↑↑⟩`, so the same-`n` rotation class does *not*
  fix every vector — the target `|↑↓⟩` (`M_tot = 0`) is load-bearing.
* **NC2** widening the admissible class from the footnote-16 closure to all of
  `unitary (ManyBodyOp (Fin 2))` makes the statement false: `U = 1` and `V = −1` are both unitary,
  both act as scalars (hence commute with every `Ŝ_x^{(3)}`, satisfying the conjugation hypothesis
  vacuously with `n = e₃`), yet `V` sends `|↑↓⟩` to `−|↑↓⟩ ≠ |↑↓⟩`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, Problem 2.2.c, pp. 23-24 (footnote 16, p. 23; footnote 17, p. 24; solution p. 496,
eq. (S.16)); eq. (2.2.11), p. 22.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Quantum Matrix

/-! ## R0: the capstone shim -/

/-- R0: the capstone's full `∀`-closed signature, closed by the public name. Pins the admissible
class (`Submonoid.closure` of the exponential global rotations `exp(−iθ Ŝ_tot^{(α)})`), the
same-`n` conjugation hypothesis at both sites `x : Fin 2`, and the pairwise conclusion
`U.mulVec |↑↓⟩ = V.mulVec |↑↓⟩`. -/
example : ∀ (n : Fin 3 → ℝ) {U V : ManyBodyOp (Fin 2)},
    U ∈ Submonoid.closure (Set.range fun p : Fin 3 × ℝ =>
      NormedSpace.exp ((-(Complex.I * (p.2 : ℂ))) •
        ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] p.1)) →
    V ∈ Submonoid.closure (Set.range fun p : Fin 3 × ℝ =>
      NormedSpace.exp ((-(Complex.I * (p.2 : ℂ))) •
        ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] p.1)) →
    (∀ x : Fin 2, U * onSite x spinHalfOp3 * Matrix.conjTranspose U =
      onSite x (spinHalfDotVec fun α => (n α : ℂ))) →
    (∀ x : Fin 2, V * onSite x spinHalfOp3 * Matrix.conjTranspose V =
      onSite x (spinHalfDotVec fun α => (n α : ℂ))) →
    U.mulVec (basisVec upDown) = V.mulVec (basisVec upDown) :=
  tasaki_problem_2_2_c_rotated_upDown_eq

/-! ## PC1 / PC2: non-vacuity at `n = e₃` -/

/-- PC1a: `U = 1` is an admissible rotation for `n = ![0, 0, 1]` (the empty product of the
footnote-16 class, `one_mem`). -/
example : (1 : ManyBodyOp (Fin 2)) ∈ Submonoid.closure (Set.range fun p : Fin 3 × ℝ =>
      NormedSpace.exp ((-(Complex.I * (p.2 : ℂ))) •
        ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] p.1)) :=
  one_mem _

/-- PC1b: `V = exp(−iπ Ŝ_tot^{(3)})` is an admissible rotation for the same `n = ![0, 0, 1]`
(a generator of the footnote-16 class, axis `α = 2` i.e. the book's axis `3`, angle `θ = π`). -/
example : NormedSpace.exp ((-(Complex.I * ((Real.pi : ℝ) : ℂ))) •
      ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] (2 : Fin 3))
    ∈ Submonoid.closure (Set.range fun p : Fin 3 × ℝ =>
      NormedSpace.exp ((-(Complex.I * (p.2 : ℂ))) •
        ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] p.1)) :=
  Submonoid.subset_closure ⟨(2, Real.pi), rfl⟩

/-- PC2: the value the capstone must reproduce at `n = e₃`, computed independently of the
capstone, from the two-site `π`-rotation entries directly: `V.mulVec |↑↓⟩ = |↑↓⟩`. -/
example : NormedSpace.exp ((-(Complex.I * ((Real.pi : ℝ) : ℂ))) •
      totalSpinHalfOp3 (Fin 2)) *ᵥ basisVec upDown = basisVec upDown := by
  rw [← totalSpinHalfRot3_eq_exp, totalSpinHalfRot3_two_site]
  funext τ
  rw [onSite_zero_mul_one_mulVec_basisVec, spinHalfRot3_pi, basisVec_apply, upDown_zero,
    upDown_one]
  generalize ha : τ 0 = a
  generalize hb : τ 1 = b
  fin_cases a <;> fin_cases b <;>
    simp_all [spinHalfOp3, pauliZ, upDown, funext_iff, Fin.forall_fin_two]
  ring_nf
  simp [Complex.I_sq]

/-! ## NC1: `M_tot = 0` (the target `|↑↓⟩`) is load-bearing -/

/-- NC1: at the `M_tot ≠ 0` configuration `|↑↑⟩`, `V = exp(−iπ Ŝ_tot^{(3)})` (an admissible
rotation for `n = e₃`, by PC1b) sends `|↑↑⟩` to `−|↑↑⟩`; hence the same-`n` rotation class does
*not* fix every two-site basis vector, and the target `|↑↓⟩` of the capstone is load-bearing. -/
example : NormedSpace.exp ((-(Complex.I * ((Real.pi : ℝ) : ℂ))) •
      totalSpinHalfOp3 (Fin 2)) *ᵥ basisVec (fun _ : Fin 2 => (0 : Fin 2))
      = -(basisVec (fun _ : Fin 2 => (0 : Fin 2))) := by
  rw [← totalSpinHalfRot3_eq_exp, totalSpinHalfRot3_two_site]
  funext τ
  rw [onSite_zero_mul_one_mulVec_basisVec, spinHalfRot3_pi, Pi.neg_apply, basisVec_apply]
  generalize ha : τ 0 = a
  generalize hb : τ 1 = b
  fin_cases a <;> fin_cases b <;>
    simp_all [spinHalfOp3, pauliZ, funext_iff, Fin.forall_fin_two]
  ring_nf
  simp [Complex.I_sq]

/-! ## NC2: the footnote-16 class restriction is load-bearing -/

/-- NC2: widening the admissible class to all unitaries makes the statement false: `U = 1` and
`V = −1` are both unitary, both act as scalars, and both satisfy the same-`n` conjugation
hypothesis vacuously with `n = e₃`, yet `V` sends `|↑↓⟩` to `−|↑↓⟩ ≠ |↑↓⟩`. -/
example : ¬ (∀ {U V : ManyBodyOp (Fin 2)},
    U ∈ unitary (ManyBodyOp (Fin 2)) →
    V ∈ unitary (ManyBodyOp (Fin 2)) →
    (∀ x : Fin 2, U * onSite x spinHalfOp3 * Matrix.conjTranspose U =
      onSite x (spinHalfDotVec fun α => ((![0, 0, 1] : Fin 3 → ℝ) α : ℂ))) →
    (∀ x : Fin 2, V * onSite x spinHalfOp3 * Matrix.conjTranspose V =
      onSite x (spinHalfDotVec fun α => ((![0, 0, 1] : Fin 3 → ℝ) α : ℂ))) →
    U.mulVec (basisVec upDown) = V.mulVec (basisVec upDown)) := by
  intro h
  have hn : spinHalfDotVec (fun α => ((![0, 0, 1] : Fin 3 → ℝ) α : ℂ)) = spinHalfOp3 := by
    unfold spinHalfDotVec
    simp
  have hU1 : (1 : ManyBodyOp (Fin 2)) ∈ unitary (ManyBodyOp (Fin 2)) := one_mem _
  have hVneg1 : (-1 : ManyBodyOp (Fin 2)) ∈ unitary (ManyBodyOp (Fin 2)) :=
    Unitary.mem_iff.mpr ⟨by rw [star_neg, star_one, neg_mul_neg, one_mul],
      by rw [star_neg, star_one, neg_mul_neg, one_mul]⟩
  have hUhyp : ∀ x : Fin 2, (1 : ManyBodyOp (Fin 2)) * onSite x spinHalfOp3 *
      Matrix.conjTranspose (1 : ManyBodyOp (Fin 2)) =
      onSite x (spinHalfDotVec fun α => ((![0, 0, 1] : Fin 3 → ℝ) α : ℂ)) := by
    intro x
    rw [hn, one_mul, Matrix.conjTranspose_one, mul_one]
  have hVhyp : ∀ x : Fin 2, (-1 : ManyBodyOp (Fin 2)) * onSite x spinHalfOp3 *
      Matrix.conjTranspose (-1 : ManyBodyOp (Fin 2)) =
      onSite x (spinHalfDotVec fun α => ((![0, 0, 1] : Fin 3 → ℝ) α : ℂ)) := by
    intro x
    rw [hn]
    have hct : Matrix.conjTranspose (-1 : ManyBodyOp (Fin 2)) = -1 := by
      rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
    rw [hct]
    simp only [neg_mul, mul_neg, one_mul, mul_one]
    exact neg_neg (onSite x spinHalfOp3 : ManyBodyOp (Fin 2))
  have hUV := h hU1 hVneg1 hUhyp hVhyp
  rw [Matrix.one_mulVec] at hUV
  have hVm : ((-1 : ManyBodyOp (Fin 2))).mulVec (basisVec upDown) = -(basisVec upDown) := by
    show ((-(1 : ManyBodyOp (Fin 2))).mulVec (basisVec upDown)) = _
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hVm] at hUV
  have hUV' := congrFun hUV upDown
  rw [Pi.neg_apply, basisVec_self] at hUV'
  norm_num at hUV'

end LatticeSystem.Tests
