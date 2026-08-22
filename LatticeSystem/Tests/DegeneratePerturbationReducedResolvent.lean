import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationReducedResolvent

/-!
# Test coverage for the reduced resolvent `R(λ,E)` (Tasaki Lemma 10.1, PR-2)

Pins the API contract of the six declarations that
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

Also machine-checks a concrete `Fin 2` inhabitation of `IsReducedInverse` via N1
(design report §6.3, fallback form).

Design report §6.4 (`hsmall` load-bearing counterexample) is **not** pinned here: exhibiting it
needs the `H2`/`H3` hoists (`toEuclideanLin_one_sub_apply`,
`toEuclideanLin_kernelProjectionMatrix`) that this same PR adds to `DegeneratePerturbation.lean`,
so it is deferred to the Green phase once those hoists exist (design report §5 pitfall P-a flags
`H3` as the one step with real API-shape risk; do not attempt it test-first without the hoists in
hand).
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

/-- **`λ = E = 0` sanity check**: the compression degenerates to `Ĥ₀` itself, i.e. `R(0,0)` is
Tasaki's `Ĥ₀⁻¹` (design report §6.2). Follows from the N2 expansion by `lam = 0`, `E = 0`. -/
example {H0 V : Matrix n n ℂ} (hH0 : H0.IsHermitian) :
    reducedPerturbedHamiltonian H0 V 0 0 = H0 := by
  rw [reducedPerturbedHamiltonian_eq hH0]
  simp

/-- Pins **N4**: under the smallness hypothesis `|λ|v + |E| < g`, the kernel of the compressed
operator `A(λ,E)` coincides with `ker Ĥ₀`. -/
example {H0 V : Matrix n n ℂ} (lam E : ℝ) {g v : ℝ}
    (hH0 : H0.IsHermitian) (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    matrixKernel (reducedPerturbedHamiltonian H0 V lam E) = matrixKernel H0 :=
  matrixKernel_reducedPerturbedHamiltonian hH0 hH0pos hV hgap hv hsmall

/-- Pins **N5**: existence of the reduced resolvent `R(λ,E)` together with its operator-norm
bound `‖R u‖ ≤ ‖u‖ / (g − |λ|v − |E|)`. -/
example {H0 V : Matrix n n ℂ} (lam E : ℝ) {g v : ℝ}
    (hH0 : H0.IsHermitian) (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g) :
    ∃ R, IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R ∧
      ∀ u : EuclideanSpace ℂ n,
        ‖Matrix.toEuclideanLin R u‖ ≤ ‖u‖ / (g - |lam| * v - |E|) :=
  exists_isReducedInverse_reducedPerturbedHamiltonian hH0 hH0pos hV hgap hv hsmall

/-- Pins **N6**: the resolvent-difference bound
`‖(R(λ,E) − Ĥ₀⁻¹) u‖ ≤ (|λ|v + |E|) ‖u‖ / (g (g − |λ|v − |E|))`. -/
example {H0 V H0inv R : Matrix n n ℂ} (lam E : ℝ) {g v : ℝ}
    (hH0 : H0.IsHermitian) (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hInv0 : IsReducedInverse H0 H0inv)
    (hgap : ∀ u : EuclideanSpace ℂ n, u ∈ (matrixKernel H0)ᗮ →
      g * ‖u‖ ^ 2 ≤ RCLike.re (inner ℂ u (Matrix.toEuclideanLin H0 u)))
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hsmall : |lam| * v + |E| < g)
    (hR : IsReducedInverse (reducedPerturbedHamiltonian H0 V lam E) R) :
    ∀ u : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin R u - Matrix.toEuclideanLin H0inv u‖
        ≤ (|lam| * v + |E|) * ‖u‖ / (g * (g - |lam| * v - |E|)) :=
  norm_sub_reducedInverse_le hH0 hH0pos hV hInv0 hgap hv hsmall hR

/-- **Concrete inhabitation of `IsReducedInverse` at `n = Fin 2`** (design report §6.3, fallback
form — answers the PR-1 review follow-up with a genuinely non-vacuous witness): the diagonal
matrix `H0 = diag(0,1)` is Hermitian, so N1 exhibits a reduced inverse for it. -/
example : ∃ R, IsReducedInverse (Matrix.diagonal ![(0 : ℂ), 1]) R := by
  have hH0 : (Matrix.diagonal ![(0 : ℂ), 1]).IsHermitian := by
    refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
    fin_cases i <;> simp [isSelfAdjoint_iff]
  exact exists_isReducedInverse_of_isHermitian hH0

end LatticeSystem.Tests.DegeneratePerturbationReducedResolvent
