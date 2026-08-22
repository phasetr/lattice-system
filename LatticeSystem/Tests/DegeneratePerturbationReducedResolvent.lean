import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationReducedResolvent

/-!
# Test coverage for the reduced resolvent `R(λ,E)` (Tasaki Lemma 10.1, PR-2)

Pins the API contract of the declarations that
`Math/MatrixAnalysis/DegeneratePerturbationReducedResolvent.lean` adds on top of
`DegeneratePerturbation.lean`'s `IsReducedInverse` (see
`.self-local/reports/design-lemma101-pr2-reduced-resolvent.md` §3b):

1. `exists_isReducedInverse_of_isHermitian` (N1) — every Hermitian matrix has a reduced inverse.
2. `reducedPerturbedHamiltonian` / `_isHermitian` / `_eq` (N2) — the compressed operator
   `A(λ,E) = Q(Ĥ(λ) − E)Q`, its Hermiticity, and its expansion `H0 + λ QVQ − E Q`.
3. `matrixKernel_reducedPerturbedHamiltonian` (N4) — `ker A(λ,E) = ker Ĥ₀` under the smallness
   hypothesis `|λ|v + |E| < g`.
4. `exists_isReducedInverse_reducedPerturbedHamiltonian` (N5) — the reduced inverse `R(λ,E)`
   of `A(λ,E)` exists and obeys the operator-norm bound `‖R u‖ ≤ ‖u‖ / (g − |λ|v − |E|)`.
5. `norm_sub_reducedInverse_le` (N6) — the resolvent-difference bound
   `‖(R − Ĥ₀⁻¹) u‖ ≤ (|λ|v + |E|) ‖u‖ / (g (g − |λ|v − |E|))`.
6. `IsReducedInverse.unique` — a reduced inverse is unique, so `Ĥ₀⁻¹` and `R(λ,E)` name
   well-defined matrices.

Also machine-checks a concrete `Fin 2` inhabitation of `IsReducedInverse` via N1
(design report §6.3, fallback form), and a `Fin 1` counterexample showing that the smallness
hypothesis `|λ|v + |E| < g` of N4 is sharp: the conclusion already fails at the boundary
`|λ|v + |E| = g`, and the boundary equation is itself part of the machine-checked statement.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationReducedResolvent

open LatticeSystem.Math Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins **N1**: every Hermitian matrix has a reduced inverse. -/
example {A : Matrix n n ℂ} (hA : A.IsHermitian) : ∃ R, IsReducedInverse A R :=
  exists_isReducedInverse_of_isHermitian hA

/-- Pins **N2** (Hermiticity of the compression `A(λ,E) = Q(Ĥ(λ) − E)Q`). -/
example {H0 V : Matrix n n ℂ} (lam E : ℝ) (hH0 : H0.IsHermitian) (hV : V.IsHermitian) :
    (reducedPerturbedHamiltonian H0 V lam E).IsHermitian :=
  reducedPerturbedHamiltonian_isHermitian hH0 hV lam E

/-- Pins **N2** (expansion `A(λ,E) = Ĥ₀ + λ Q V̂ Q − E Q`). -/
example {H0 V : Matrix n n ℂ} (lam E : ℝ) (hH0 : H0.IsHermitian) :
    reducedPerturbedHamiltonian H0 V lam E
      = H0 + (lam : ℂ) •
          ((1 - kernelProjectionMatrix H0) * V * (1 - kernelProjectionMatrix H0))
        - (E : ℂ) • (1 - kernelProjectionMatrix H0) :=
  reducedPerturbedHamiltonian_eq hH0 lam E

/-- **`λ = E = 0` sanity check**: the compression degenerates to `Ĥ₀` itself (by the N2 expansion
at `lam = 0`, `E = 0`), so uniqueness of the reduced inverse forces *every* `R(0,0)` to be Tasaki's
`Ĥ₀⁻¹` (design report §6.2). This is the implicit step behind reading
`K(λ,E) = −P̂₀V̂R(λ,E)V̂P̂₀` as eq. (10.1.20) at `λ = E = 0`. -/
example {H0 V H0inv R : Matrix n n ℂ} (hH0 : H0.IsHermitian)
    (hInv0 : IsReducedInverse H0 H0inv)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V 0 0) R) :
    R = H0inv := by
  have h00 : reducedPerturbedHamiltonian H0 V 0 0 = H0 := by
    rw [reducedPerturbedHamiltonian_eq hH0]
    simp
  rw [h00] at hR
  exact hR.unique hInv0

/-- Pins **N4**: under the smallness hypothesis `|λ|v + |E| < g`, the kernel of the compressed
operator `A(λ,E)` coincides with `ker Ĥ₀`. -/
example {H0 V : Matrix n n ℂ} (lam E : ℝ) {g v : ℝ}
    (hH0 : H0.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    matrixKernel (reducedPerturbedHamiltonian H0 V lam E) = matrixKernel H0 :=
  matrixKernel_reducedPerturbedHamiltonian hH0 hgap hv hsmall

/-- Pins **N5**: existence of the reduced resolvent `R(λ,E)` together with its operator-norm
bound `‖R u‖ ≤ ‖u‖ / (g − |λ|v − |E|)`. -/
example {H0 V : Matrix n n ℂ} (lam E : ℝ) {g v : ℝ}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    ∃ R, IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R ∧
      ∀ u : EuclideanSpace ℂ n,
        ‖Matrix.toEuclideanLin R u‖ ≤ ‖u‖ / (g - |lam| * v - |E|) :=
  exists_isReducedInverse_reducedPerturbedHamiltonian hH0 hV hgap hv hsmall

/-- Pins **N6**: the resolvent-difference bound
`‖(R(λ,E) − Ĥ₀⁻¹) u‖ ≤ (|λ|v + |E|) ‖u‖ / (g (g − |λ|v − |E|))`. -/
example {H0 V H0inv R : Matrix n n ℂ} (lam E : ℝ) {g v : ℝ}
    (hH0 : H0.IsHermitian) (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R) :
    ∀ u : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin R u - Matrix.toEuclideanLin H0inv u‖
        ≤ (|lam| * v + |E|) * ‖u‖ / (g * (g - |lam| * v - |E|)) :=
  norm_sub_reducedInverse_le hH0 hInv0 hgap hv hsmall hR

/-- **Concrete inhabitation of `IsReducedInverse` at `n = Fin 2`** (design report §6.3, fallback
form — answers the PR-1 review follow-up with a genuinely non-vacuous witness): the diagonal
matrix `H0 = diag(0,1)` is Hermitian, so N1 exhibits a reduced inverse for it. -/
example : ∃ R, IsReducedInverse (Matrix.diagonal ![(0 : ℂ), 1]) R := by
  have hH0 : (Matrix.diagonal ![(0 : ℂ), 1]).IsHermitian := by
    refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
    fin_cases i <;> simp [isSelfAdjoint_iff]
  exact exists_isReducedInverse_of_isHermitian hH0

/-- **The smallness hypothesis of N4 is load-bearing, and sharp** (design report §6.4). For the
`1 × 1` identity `Ĥ₀ = 1` (gap `g = 1`, `ker Ĥ₀ = ⊥`) with `V̂ = 0` (`v = 0`), `λ = 0` and `E = 1`,
the compression `A(0,1) = Ĥ₀ − 1` is zero, so its kernel is all of the space while `ker Ĥ₀ = ⊥`.
Every hypothesis of `matrixKernel_reducedPerturbedHamiltonian` except `hsmall` holds here, and the
conjuncts `0 < g` and `|λ|v + |E| = g` machine-check that the failure occurs already at the
boundary — so weakening `hsmall` from `<` to `≤` would make N4 false. -/
example : ∃ (H0 V : Matrix (Fin 1) (Fin 1) ℂ) (lam E g v : ℝ),
    H0.IsHermitian ∧
    (∀ u : EuclideanSpace ℂ (Fin 1), u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u))) ∧
    (∀ u : EuclideanSpace ℂ (Fin 1), ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖) ∧
    0 < g ∧ |lam| * v + |E| = g ∧
    matrixKernel (reducedPerturbedHamiltonian H0 V lam E) ≠ matrixKernel H0 := by
  have hone : ∀ u : EuclideanSpace ℂ (Fin 1),
      Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℂ) u = u := by
    intro u
    simp
  have hker : matrixKernel (1 : Matrix (Fin 1) (Fin 1) ℂ) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [← hone x]
    exact LinearMap.mem_ker.mp hx
  have hP : kernelProjectionMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    refine Matrix.toEuclideanLin.injective ?_
    rw [toEuclideanLin_kernelProjectionMatrix, hker, map_zero]
    ext x
    simp
  have hA : reducedPerturbedHamiltonian (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 1 = 0 := by
    rw [reducedPerturbedHamiltonian, perturbedHamiltonian, hP]
    simp
  refine ⟨1, 0, 0, 1, 1, 0, Matrix.isHermitian_one, fun u _ => ?_, fun u => by simp,
    by norm_num, by norm_num, ?_⟩
  · rw [hone u, inner_self_eq_norm_sq_to_K]
    have hre : ((‖u‖ : ℂ) ^ 2).re = ‖u‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp [hre]
  · rw [hA, hker, matrixKernel, LinearMap.ker_eq_top.mpr (map_zero Matrix.toEuclideanLin)]
    exact top_ne_bot

end LatticeSystem.Tests.DegeneratePerturbationReducedResolvent
