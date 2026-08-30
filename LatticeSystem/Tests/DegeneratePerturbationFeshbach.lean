import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationFeshbach
import LatticeSystem.Tests.DegeneratePerturbationWitness

/-!
# Test coverage for the exact Feshbach equivalence (Tasaki Lemma 10.1)

Pins the API contract of the declarations that
`Math/MatrixAnalysis/DegeneratePerturbationFeshbach.lean` adds on top of
`DegeneratePerturbationReducedResolvent.lean`:

1. `secondOrderEffectiveHamiltonian_isHermitian` (C1) — Hermiticity of the second-order
   effective Hamiltonian, generic in its third argument (serves both `Ĥeff` and `K(λ,E)`).
2. `toEuclideanLin_secondOrderEffectiveHamiltonian_mem_matrixKernel` (C2) — the second-order
   effective Hamiltonian preserves `ker Ĥ₀` (range ⊆ `ker Ĥ₀`).
3. `perturbedHamiltonian_eigenvector_iff` (C3) — the exact Feshbach equivalence: an eigenvector
   `Φ + Γ` (`Φ ∈ ker Ĥ₀`, `Γ ∈ (ker Ĥ₀)ᗮ`) of `Ĥ(λ)` exists iff `Γ` is the resolvent
   reconstruction from `Φ` and `Φ` solves the multiplicative eigen-equation `λ² K Φ = E Φ`
   (eq. (10.1.15)/(10.1.17)/(10.1.21) combined into a single `↔`).
4. `perturbedHamiltonian_eigenvector_eq_zero_of_starProjection_eq_zero` (C4) — an eigenvector of
   `Ĥ(λ)` whose `P̂₀`-component vanishes is itself zero (kernel-triviality form of the
   `Ξ ↦ P̂₀Ξ` injectivity on the eigenspace).
5. `norm_sub_secondOrderEffectiveHamiltonian_le` (C5) — the sharp operator-norm bound
   `‖K u − Ĥeff u‖ ≤ v² (|λ|v + |E|) ‖u‖ / (g (g − |λ|v − |E|))`.
6. `norm_sub_secondOrderEffectiveHamiltonian_le_abs_mul` (C6) — the explicit-constant bound
   `‖K u − Ĥeff u‖ ≤ (4v³/g²) |λ| ‖u‖` under `0 < g`, `|E| ≤ |λ|v` and `4|λ|v ≤ g`.

Also machine-checks the `λ = E = 0` degeneration of C3's `K` to eq. (10.1.20)'s `Ĥeff` (reusing
`IsReducedInverse.unique`), and two `Fin 1` counterexamples showing that `hFirstOrder`
and `Γ ∈ (matrixKernel H0)ᗮ` are each independently load-bearing in C3:
dropping either hypothesis produces a genuine (not merely unproved) failure of the
forward direction, witnessed concretely via `Submodule.starProjection_top`. The `Fin 1`
scaffolding those two counterexamples run on lives in `Tests/DegeneratePerturbationWitness.lean`,
shared with the trial-state test file's `V = 0` corner.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationFeshbach

open LatticeSystem.Math Matrix
open LatticeSystem.Tests.DegeneratePerturbationWitness
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins **C1**: the second-order effective Hamiltonian is Hermitian whenever `V̂` and the third
argument (`Ĥ₀⁻¹` or the reduced resolvent `R`) are. -/
example {H0 V M : Matrix n n ℂ} (hV : V.IsHermitian) (hM : M.IsHermitian) :
    (secondOrderEffectiveHamiltonian H0 V M).IsHermitian :=
  secondOrderEffectiveHamiltonian_isHermitian hV hM

/-- Pins **C2**: the second-order effective Hamiltonian preserves `ker Ĥ₀` — its range lies
inside `matrixKernel H0`, for every choice of the third argument `M`. -/
example {H0 V M : Matrix n n ℂ} (x : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V M) x ∈ matrixKernel H0 :=
  toEuclideanLin_secondOrderEffectiveHamiltonian_mem_matrixKernel (H0 := H0) (V := V) (M := M) x

/-- Pins **C3**: the exact Feshbach equivalence. For `Φ ∈ ker Ĥ₀` and `Γ ∈ (ker Ĥ₀)ᗮ`, `Φ + Γ`
is an `E`-eigenvector of `Ĥ(λ)` iff `Γ = −λ R(λ,E) V̂ Φ` and `λ² K(λ,E) Φ = E Φ`, where
`K(λ,E) = secondOrderEffectiveHamiltonian H0 V R` and `R = R(λ,E)` is a reduced inverse of the
compression `A(λ,E) = reducedPerturbedHamiltonian H0 V lam E`. -/
example {H0 V R : Matrix n n ℂ} {lam E : ℝ}
    (hH0 : H0.IsHermitian)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (hPA : kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
      = kernelProjectionMatrix H0)
    {Φ Γ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0) (hΓ : Γ ∈ (matrixKernel H0)ᗮ) :
    Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ)
      ↔ Γ = -(lam : ℂ) • Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ)
        ∧ ((lam : ℂ) ^ 2) • Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ
          = (E : ℂ) • Φ :=
  perturbedHamiltonian_eigenvector_iff hH0 hFirstOrder hR hPA hΦ hΓ

/-- Pins **C4**: an eigenvector of `Ĥ(λ)` whose `P̂₀`-component vanishes is zero (the
kernel-triviality form of injectivity of `Ξ ↦ P̂₀Ξ` on the eigenspace). -/
example {H0 V R : Matrix n n ℂ} {lam E : ℝ}
    (hH0 : H0.IsHermitian)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (hPA : kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
      = kernelProjectionMatrix H0)
    {Ξ : EuclideanSpace ℂ n}
    (hΞ : Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) Ξ = (E : ℂ) • Ξ)
    (hP : (matrixKernel H0).starProjection Ξ = 0) :
    Ξ = 0 :=
  perturbedHamiltonian_eigenvector_eq_zero_of_starProjection_eq_zero
    hH0 hFirstOrder hR hPA hΞ hP

/-- Pins **C5**: the sharp operator-norm bound between the exact `K(λ,E)` and the `λ = E = 0`
effective Hamiltonian `Ĥeff`. -/
example {H0 V H0inv R : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian) (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) u
        - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) u‖
      ≤ v ^ 2 * (|lam| * v + |E|) * ‖u‖ / (g * (g - |lam| * v - |E|)) :=
  norm_sub_secondOrderEffectiveHamiltonian_le hH0 hInv0 hgap hv hsmall hR u

/-- Pins **C6**: the explicit-constant bound `‖K u − Ĥeff u‖ ≤ (4v³/g²) |λ| ‖u‖`, under
`0 < g`, `|E| ≤ |λ|v` and `4|λ|v ≤ g` (`hsmall` of C5 is derived, not assumed). -/
example {H0 V H0inv R : Matrix n n ℂ} {lam E g v : ℝ}
    (hH0 : H0.IsHermitian) (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hgpos : 0 < g) (hEle : |E| ≤ |lam| * v) (hsmall4 : 4 * (|lam| * v) ≤ g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R)
    (u : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) u
        - Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) u‖
      ≤ (4 * v ^ 3 / g ^ 2) * |lam| * ‖u‖ :=
  norm_sub_secondOrderEffectiveHamiltonian_le_abs_mul hH0 hInv0 hgap hv hgpos hEle hsmall4 hR u

/-- **`λ = E = 0` degeneration**: at `λ = E = 0` the compression `A(0,0)` is `Ĥ₀` itself
(PR-2's `reducedPerturbedHamiltonian_eq`), so uniqueness of the reduced inverse forces
`R(0,0) = Ĥ₀⁻¹`, hence `K(0,0) = secondOrderEffectiveHamiltonian H0 V R` *is literally*
`Ĥeff = secondOrderEffectiveHamiltonian H0 V H0inv` — the reading the module doc comment
claims for eq. (10.1.20). -/
example {H0 V H0inv R : Matrix n n ℂ} (hH0 : H0.IsHermitian)
    (hInv0 : IsReducedInverse H0 H0inv)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V 0 0) R) :
    secondOrderEffectiveHamiltonian H0 V R = secondOrderEffectiveHamiltonian H0 V H0inv := by
  have h00 : reducedPerturbedHamiltonian H0 V 0 0 = H0 := by
    rw [reducedPerturbedHamiltonian_eq hH0]
    simp
  rw [h00] at hR
  rw [hR.unique hInv0]

/-- **`hFirstOrder` is load-bearing in C3**: at `n = Fin 1`, take
`H0 = 0`, `V = 1`, `lam = E = 1`, `R = 0` (a reduced inverse of `A(1,1) = 0`, since `P̂₀ = 1`
collapses the compression). Then `Φ = e₀ ∈ ker Ĥ₀ = ⊤`, `Γ = 0 ∈ (ker Ĥ₀)ᗮ`, and
`Ξ := Φ + Γ = e₀` genuinely is a `1`-eigenvector of `Ĥ(1) = 0 + 1 • 1 = 1`; every hypothesis of
C3 holds *except* `hFirstOrder` (`P̂₀ V P̂₀ = 1 * 1 * 1 = 1 ≠ 0`), and C3's forward direction would
force the second conjunct `K Φ = E Φ`, i.e. `0 = e₀`, a genuine falsehood (`K = 0` since `R = 0`)
— so `hFirstOrder` cannot be dropped. -/
example :
    ∃ (H0 V R : Matrix (Fin 1) (Fin 1) ℂ) (lam E : ℝ) (Φ Γ : EuclideanSpace ℂ (Fin 1)),
      H0.IsHermitian ∧
      IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R ∧
      kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
        = kernelProjectionMatrix H0 ∧
      Φ ∈ matrixKernel H0 ∧ Γ ∈ (matrixKernel H0)ᗮ ∧
      kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 ≠ 0 ∧
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ) ∧
      ¬ ((lam : ℂ) ^ 2) • Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V R) Φ
          = (E : ℂ) • Φ := by
  set e0 : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℂ) with he0
  have he0ne : e0 ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℂ (Fin 1) => x 0) h
    simp [he0] at this
  have hA : reducedPerturbedHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 1 = 0 := by
    rw [reducedPerturbedHamiltonian, perturbedHamiltonian, fin1_kernelProjectionMatrix_zero_eq_one]
    simp
  refine ⟨0, 1, 0, 1, 1, e0, 0, Matrix.isHermitian_zero, ?_, ?_,
    by simp [fin1_matrixKernel_zero_eq_top], by simp, ?_, ?_, ?_⟩
  · rw [hA]
    exact ⟨by simp [fin1_kernelProjectionMatrix_zero_eq_one],
      by simp [fin1_kernelProjectionMatrix_zero_eq_one], by simp, by simp,
      Matrix.isHermitian_zero⟩
  · rw [hA, fin1_kernelProjectionMatrix_zero_eq_one]
  · rw [fin1_kernelProjectionMatrix_zero_eq_one]
    intro h
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    simp at this
  · simp [perturbedHamiltonian]
  · have hK0 : Matrix.toEuclideanLin
        (secondOrderEffectiveHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 1
          (0 : Matrix (Fin 1) (Fin 1) ℂ)) e0 = 0 := by
      simp [secondOrderEffectiveHamiltonian]
    rw [hK0, smul_zero, Complex.ofReal_one, one_smul]
    exact fun h => he0ne h.symm

/-- **`Γ ∈ (ker Ĥ₀)ᗮ` is load-bearing in C3**: at `n = Fin 1`, take
`H0 = V = 0`, `lam = E = 0`, `R = 0` (a reduced inverse of `A(0,0) = 0`). Since `ker Ĥ₀ = ⊤`,
`(ker Ĥ₀)ᗮ = ⊥`, so `Γ := e₀ ∉ (ker Ĥ₀)ᗮ`. With `Φ = 0 ∈ ker Ĥ₀`, `Ξ := Φ + Γ = e₀` is a genuine
`0`-eigenvector of `Ĥ(0) = 0` (the zero operator kills everything); every hypothesis of C3 holds
*except* `Γ ∈ (ker Ĥ₀)ᗮ`, and the forced reconstruction `Γ = -(0:ℂ) • ⋯ = 0` is false since
`Γ = e₀ ≠ 0` — so this membership hypothesis cannot be dropped either. -/
example :
    ∃ (H0 V R : Matrix (Fin 1) (Fin 1) ℂ) (lam E : ℝ) (Φ Γ : EuclideanSpace ℂ (Fin 1)),
      H0.IsHermitian ∧
      IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R ∧
      kernelProjectionMatrix (reducedPerturbedHamiltonian H0 V lam E)
        = kernelProjectionMatrix H0 ∧
      Φ ∈ matrixKernel H0 ∧ Γ ∉ (matrixKernel H0)ᗮ ∧
      kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0 ∧
      Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam) (Φ + Γ) = (E : ℂ) • (Φ + Γ) ∧
      ¬ Γ = -(lam : ℂ) • Matrix.toEuclideanLin R (Matrix.toEuclideanLin V Φ) := by
  set e0 : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single (0 : Fin 1) (1 : ℂ) with he0
  have he0ne : e0 ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℂ (Fin 1) => x 0) h
    simp [he0] at this
  have hA : reducedPerturbedHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 0 = 0 := by
    rw [reducedPerturbedHamiltonian, perturbedHamiltonian, fin1_kernelProjectionMatrix_zero_eq_one]
    simp
  refine ⟨0, 0, 0, 0, 0, 0, e0, Matrix.isHermitian_zero, ?_, ?_,
    by simp [fin1_matrixKernel_zero_eq_top], ?_, ?_, ?_, ?_⟩
  · rw [hA]
    exact ⟨by simp [fin1_kernelProjectionMatrix_zero_eq_one],
      by simp [fin1_kernelProjectionMatrix_zero_eq_one], by simp, by simp,
      Matrix.isHermitian_zero⟩
  · rw [hA, fin1_kernelProjectionMatrix_zero_eq_one]
  · rw [fin1_matrixKernel_zero_eq_top]
    simp [he0ne]
  · rw [fin1_kernelProjectionMatrix_zero_eq_one]
    simp
  · simp [perturbedHamiltonian]
  · simpa using he0ne

end LatticeSystem.Tests.DegeneratePerturbationFeshbach
