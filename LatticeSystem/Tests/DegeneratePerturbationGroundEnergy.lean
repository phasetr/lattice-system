import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbationGroundEnergy
import LatticeSystem.Tests.DegeneratePerturbationWitness

/-!
# Test coverage for the trial-state variational bound (Tasaki Lemma 10.1, PR-4)

Pins the API contract of the declarations that
`Math/MatrixAnalysis/DegeneratePerturbationGroundEnergy.lean` is designed to add on top of
`DegeneratePerturbation.lean` (PR-1 only; see
`.self-local/reports/design-lemma101-pr4-variational-bound.md` §4):

1. `IsGroundEigenvalueOn.mul_norm_sq_le` (B1) — the variational principle in the arc's own
   vocabulary: on an invariant subspace, the ground eigenvalue lower-bounds the energy quadratic
   form.
2. `exists_isGroundEigenvalueOn` (B2) — existence of a ground eigenvalue on any nonzero
   Hermitian-invariant subspace.
3. `perturbedHamiltonian_isHermitian` (B3) — `Ĥ(λ) = Ĥ₀ + λV̂` is Hermitian whenever `Ĥ₀` and `V̂`
   are.
4. `toEuclideanLin_perturbedHamiltonian_trialVector` (L1) — the exact residual
   `Ĥ(λ)(Φ − λĤ₀⁻¹V̂Φ) = −λ²V̂(Ĥ₀⁻¹V̂Φ)`, i.e. eq. (10.1.18) made exact.
5. `inner_trialVector_perturbedHamiltonian` (L2) — the exact energy identity
   `⟪Ψ, Ĥ(λ)Ψ⟫ = λ²⟪Φ, ĤeffΦ⟫ + λ³⟪u, V̂u⟫` for the trial vector `Ψ = Φ − λu`, `u = Ĥ₀⁻¹V̂Φ`.
6. `exists_const_isGroundEigenvalue_perturbedHamiltonian_le` (L4) — **the PR's headline
   result**: the variational upper bound `Elam ≤ λ²Eeff + c₃λ³` for `0 < λ ≤ 1`.
7. `abs_isGroundEigenvalue_perturbedHamiltonian_le` (L5) — the two-sided energy bound
   `|Elam| ≤ λv`, fused, drop-in for PR-3's `perturbedHamiltonian_eigenvector_iff` consumer
   (C6's `hEle` hypothesis).

**Provenance honesty (design report §1, risk R6).** Tasaki's proof of Lemma 10.1 (pp. 346–347)
contains *no* variational estimate: its analytic input is the unproved continuity/Rellich–Kato
sentence "there are exactly `D₀` … eigenstates … depend[ing] continuously on `λ`". None of the
seven declarations pinned below is a transcription of that argument. They are this arc's
**elementary replacement** for it — built from the trial vector of eq. (10.1.18) and the plain
Rayleigh–Ritz variational principle (B1/B2) — and every test below must be read as testing *that
replacement*, not as testing "Tasaki's proof, formalized". The capstone
`tasaki_lemma_10_1_degenerate_perturbation` is assembled from this layer in
`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean`.

Also machine-checks two instances built from explicit matrices:

* the **`V = 0` corner** (design report §8, item 2): at `H0 = V = H0inv = 0` (`n = Fin 1`),
  `matrixKernel 0 = ⊤`, `hFirstOrder` holds trivially, and L1's residual identity degenerates to
  `0 = 0`, exercising the degenerate `ker Ĥ₀ = ⊤` branch;
* the **two-site witness** (`n = Fin 2`): `Ĥ₀ = diag(0,1)`, `V̂ = offdiag(1,1)`,
  `Ĥ₀⁻¹ = diag(0,1)`, `Φeff = e₀`, for which `ker Ĥ₀ = ℂe₀`, `P̂₀ = diag(1,0)`,
  `Ĥeff = diag(−1,0)`, `Eeff = −1` and `u = e₁`. It is the `β = γ` symmetric subspace of the
  singlet sector of Tasaki's two-electron two-site Hubbard model (pp. 341–342, eq. (10.1.1)) at
  `U = 1`, `t = λ/2`, with `Ĥ₀` the on-site interaction and `V̂` the hopping. It discharges the
  *entire* hypothesis bundle of L4 and L5 on explicit data, so neither statement is vacuous; fused
  with B2 (which supplies the ground eigenvalue) both become unconditional. The design report
  placed this witness in PR-6 and recorded either placement as defensible (§10, item 4); it is
  built here.

**Not covered here (deliberately, per the design report):**
* Any counterexample family showing `lam ≤ 1` is load-bearing in L4 — the design report classifies
  it as a convenience, not a soundness guard (§8 item 3), so none is supplied; the pin for L4
  already quantifies over every `0 < lam ≤ 1`, including `lam = 1`.
* A pin of L4's constant inside the API: L4 packages `c₃` existentially (design report §10,
  item 2), so the closed form `c₃ = |re⟪u, V̂u⟫| + |Eeff|‖u‖²` is checked only at the two-site
  witness, where it evaluates to `1` and the resulting bound `E ≤ −λ² + λ³` is machine-checked
  from B1 and L2 directly.

**Which witness helpers are not `private`.** `Tests/DegeneratePerturbationUniqueness.lean` (PR-5,
design report §7 pitfall P-g) instantiates its own pins on the same two-site model, and rebuilding
those matrices there would be a duplicate declaration. The eleven declarations it consumes —
`twoSiteH0`, `twoSiteV`, `twoSiteGround`, `twoSite_matrixKernel`, `twoSite_ground_mem`,
`twoSite_norm_ground`, `twoSite_h0_posSemidef`, `twoSite_v_isHermitian`,
`twoSite_isReducedInverse`, `twoSite_firstOrder`, `twoSite_effective_eigenvector` — are therefore
exposed; everything else below is `private`, being internal to this file's own computations. The
`Fin 1` scaffolding shared with `Tests/DegeneratePerturbationFeshbach.lean` lives in
`Tests/DegeneratePerturbationWitness.lean`.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationGroundEnergy

open LatticeSystem.Math Matrix
open LatticeSystem.Tests.DegeneratePerturbationWitness
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins **B1**: the variational principle. If `H` is Hermitian and preserves `K`, then the
ground eigenvalue `E` of `H` on `K` lower-bounds the energy quadratic form `re ⟪w, Hw⟫` on `K`. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E : ℝ}
    (hH : H.IsHermitian) (hK : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K)
    (hE : IsGroundEigenvalueOn K H E) :
    ∀ w ∈ K, E * ‖w‖ ^ 2 ≤ RCLike.re (inner ℂ w (Matrix.toEuclideanLin H w)) :=
  IsGroundEigenvalueOn.mul_norm_sq_le hH hK hE

/-- Pins **B2**: a nonzero Hermitian-invariant subspace has a ground eigenvalue. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hK : ∀ v ∈ K, Matrix.toEuclideanLin H v ∈ K) (hKbot : K ≠ ⊥) :
    ∃ E : ℝ, IsGroundEigenvalueOn K H E :=
  exists_isGroundEigenvalueOn hH hK hKbot

/-- Pins **B3**: `Ĥ(λ) = Ĥ₀ + λV̂` is Hermitian whenever `Ĥ₀` and `V̂` are. -/
example {H0 V : Matrix n n ℂ} {lam : ℝ} (hH0 : H0.IsHermitian) (hV : V.IsHermitian) :
    (perturbedHamiltonian H0 V lam).IsHermitian :=
  perturbedHamiltonian_isHermitian hH0 hV

/-- Pins **L1**: the exact residual of the trial vector `Ψ = Φ − λĤ₀⁻¹V̂Φ` (eq. (10.1.18) made
exact), for `Φ ∈ ker Ĥ₀` with vanishing first-order term and `H0inv` a reduced inverse of `Ĥ₀`. -/
example {H0 V H0inv : Matrix n n ℂ} {lam : ℝ}
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hInv : IsReducedInverse H0 H0inv)
    {Φ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0) :
    Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam)
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
      = -((lam : ℂ) ^ 2) • Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ)) :=
  toEuclideanLin_perturbedHamiltonian_trialVector hΦ hFirstOrder hInv

/-- Pins **L2**: the exact energy identity `⟪Ψ, Ĥ(λ)Ψ⟫ = λ²⟪Φ, ĤeffΦ⟫ + λ³⟪u, V̂u⟫` for the trial
vector `Ψ = Φ − λu`, `u = Ĥ₀⁻¹V̂Φ`, with no eigenvalue/normalisation hypothesis on `Φ`. -/
example {H0 V H0inv : Matrix n n ℂ} {lam : ℝ}
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hInv : IsReducedInverse H0 H0inv)
    {Φ : EuclideanSpace ℂ n} (hΦ : Φ ∈ matrixKernel H0) :
    (inner ℂ
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
        (Matrix.toEuclideanLin (perturbedHamiltonian H0 V lam)
          (Φ - (lam : ℂ) • Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))) : ℂ)
      = (lam : ℂ) ^ 2
          * (inner ℂ Φ
              (Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φ) : ℂ)
        + (lam : ℂ) ^ 3
          * (inner ℂ (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ))
              (Matrix.toEuclideanLin V (Matrix.toEuclideanLin H0inv (Matrix.toEuclideanLin V Φ)))
              : ℂ) :=
  inner_trialVector_perturbedHamiltonian hΦ hFirstOrder hInv

/-- Pins **L4**, the PR's headline result: the trial-state variational upper bound
`Elam ≤ λ²Eeff + c₃λ³` for every `0 < λ ≤ 1`, given a normalized eigenvector `Φeff` of `Ĥeff`
inside `ker Ĥ₀` with eigenvalue `Eeff`. Neither uniqueness of `Φeff` nor minimality of `Eeff` is
assumed. This is the arc's elementary replacement for Tasaki's unproved continuity input (see the
module doc, provenance honesty). -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff) :
    ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ lam E : ℝ, 0 < lam → lam ≤ 1 →
      IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
        (perturbedHamiltonian H0 V lam) E →
      E ≤ lam ^ 2 * Eeff + c₃ * lam ^ 3 :=
  exists_const_isGroundEigenvalue_perturbedHamiltonian_le hH0 hV hInv hFirstOrder hΦeff hnorm hEeff

/-- **L4 instantiated at `λ = 1`** (design report §8 item 3: `lam ≤ 1` is a convenience, not a
soundness guard that needs a dedicated counterexample family). This is a direct corollary of the
pin above, kept as a separate `example` only to record that the bound is genuinely usable at the
right endpoint `λ = 1`, not merely in some open neighbourhood of `0`. -/
example {H0 V H0inv : Matrix n n ℂ} {Eeff E : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0 : H0.IsHermitian) (hV : V.IsHermitian) (hInv : IsReducedInverse H0 H0inv)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1)
    (hEeff : Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian H0 V H0inv) Φeff
      = (Eeff : ℂ) • Φeff)
    (hE : IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V 1) E) :
    ∃ c₃ : ℝ, 0 ≤ c₃ ∧ E ≤ Eeff + c₃ := by
  obtain ⟨c₃, hc₃nonneg, hbound⟩ :=
    exists_const_isGroundEigenvalue_perturbedHamiltonian_le hH0 hV hInv hFirstOrder hΦeff hnorm
      hEeff
  refine ⟨c₃, hc₃nonneg, ?_⟩
  have := hbound 1 E one_pos le_rfl hE
  simpa using this

/-- Pins **L5**: the fused two-sided energy bound `|Elam| ≤ λv`, drop-in for PR-3's Feshbach
consumer (`perturbedHamiltonian_eigenvector_iff`'s C6-style `hEle` hypothesis). -/
example {H0 V : Matrix n n ℂ} {v lam E : ℝ} {Φeff : EuclideanSpace ℂ n}
    (hH0pos : H0.PosSemidef) (hV : V.IsHermitian)
    (hv : ∀ u : EuclideanSpace ℂ n, ‖Matrix.toEuclideanLin V u‖ ≤ v * ‖u‖)
    (hFirstOrder : kernelProjectionMatrix H0 * V * kernelProjectionMatrix H0 = 0)
    (hΦeff : Φeff ∈ matrixKernel H0) (hnorm : ‖Φeff‖ = 1) (hlam : 0 < lam)
    (hE : IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ n))
      (perturbedHamiltonian H0 V lam) E) :
    |E| ≤ lam * v :=
  abs_isGroundEigenvalue_perturbedHamiltonian_le hH0pos hV hv hFirstOrder hΦeff hnorm hlam hE

/-- The zero matrix is trivially a reduced inverse of itself: `ker 0 = ⊤`, so the kernel
projection is the identity and every field of `IsReducedInverse` collapses to `0 = 0`. -/
private theorem fin1_isReducedInverse_zero_zero :
    IsReducedInverse (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  refine ⟨?_, ?_, ?_, ?_, Matrix.isHermitian_zero⟩ <;>
    simp [fin1_kernelProjectionMatrix_zero_eq_one]

/-- **`V = 0` corner** (design report §8 item 2): at `H0 = V = H0inv = 0` on `n = Fin 1`,
`matrixKernel 0 = ⊤`, `hFirstOrder` holds trivially, and L1's exact residual identity
degenerates to `Ĥ(λ)Φ = 0 = −λ²•0`. Exercises the degenerate `ker Ĥ₀ = ⊤` branch that the
two-site non-vacuity witness built below does not cover, its kernel being the proper line
`ℂe₀`. -/
example {lam : ℝ} {Φ : EuclideanSpace ℂ (Fin 1)}
    (hΦ : Φ ∈ matrixKernel (0 : Matrix (Fin 1) (Fin 1) ℂ)) :
    Matrix.toEuclideanLin (perturbedHamiltonian (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 lam)
        (Φ - (lam : ℂ) • Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ) Φ))
      = -((lam : ℂ) ^ 2) • Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ)
          (Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ)
            (Matrix.toEuclideanLin (0 : Matrix (Fin 1) (Fin 1) ℂ) Φ)) :=
  toEuclideanLin_perturbedHamiltonian_trialVector hΦ (by simp) fin1_isReducedInverse_zero_zero

/-! ### The two-site witness (`n = Fin 2`; Tasaki pp. 341–342, eq. (10.1.1))

`Ĥ₀ = diag(0,1)`, `V̂ = offdiag(1,1)`, `Ĥ₀⁻¹ = diag(0,1)`, `Φeff = e₀`: the smallest model with a
nonzero perturbation obeying `P̂₀V̂P̂₀ = 0`. It is the `β = γ` symmetric subspace of the singlet
sector (eq. (10.1.3)) of the book's two-electron two-site Hubbard model at `U = 1`, `t = λ/2`,
where `e₀` is the singly occupied singlet, `e₁` the symmetric doubly occupied state at interaction
energy `U`, and `V̂` the hopping; correspondingly `λ²Eeff = −λ²` reproduces the book's
`E_GS ≃ −4t²/U`. Every hypothesis of L4 and L5 is discharged on this data below, which is what
makes those two statements non-vacuous. -/

/-- The witness unperturbed Hamiltonian `Ĥ₀ = diag(0,1)`: kernel `ℂe₀`, unit gap above it. Since
`Ĥ₀` acts as the identity on `(ker Ĥ₀)ᗮ = ℂe₁`, it is also its own reduced inverse
(`twoSite_isReducedInverse`). -/
noncomputable def twoSiteH0 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The witness perturbation `V̂ = offdiag(1,1)`, which exchanges `e₀` and `e₁`. -/
noncomputable def twoSiteV : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The kernel projection `P̂₀ = diag(1,0)` of the witness, identified with
`kernelProjectionMatrix twoSiteH0` in `twoSite_kernelProjectionMatrix`. -/
private noncomputable def twoSiteProj : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The witness effective ground state `Φeff = e₀`, a unit vector spanning `ker Ĥ₀`. -/
noncomputable def twoSiteGround : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The witness first-order correction `u = Ĥ₀⁻¹V̂Φeff = e₁` (see
`twoSite_reducedInverse_v_ground`). -/
private noncomputable def twoSiteExcited : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

/-- `Φeff = e₀` is a unit vector, as L4 and L5 require. -/
theorem twoSite_norm_ground : ‖twoSiteGround‖ = 1 := by
  rw [twoSiteGround, EuclideanSpace.single, PiLp.norm_single]
  simp

/-- `u = e₁` is a unit vector, so the closed form `c₃ = |re⟪u, V̂u⟫| + |Eeff|‖u‖²` reduces to
`|re⟪u, V̂u⟫| + |Eeff|` at the witness. -/
private theorem twoSite_norm_excited : ‖twoSiteExcited‖ = 1 := by
  rw [twoSiteExcited, EuclideanSpace.single, PiLp.norm_single]
  simp

/-- `ker Ĥ₀ = ℂe₀`: the second coordinate of `Ĥ₀x` is `x 1`, so `Ĥ₀x = 0` pins `x` to the
`e₀`-axis. -/
theorem twoSite_matrixKernel : matrixKernel twoSiteH0 = ℂ ∙ twoSiteGround := by
  ext x
  simp only [matrixKernel, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have h1 : (Matrix.toEuclideanLin twoSiteH0 x) 1 = 0 := by rw [hx]; rfl
    rw [toEuclideanLin_apply_coord] at h1
    simp [twoSiteH0, Fin.sum_univ_two] at h1
    refine ⟨x 0, ?_⟩
    refine PiLp.ext ?_
    intro i
    fin_cases i <;> simp [twoSiteGround, h1]
  · rintro ⟨c, rfl⟩
    refine PiLp.ext ?_
    intro i
    rw [toEuclideanLin_apply_coord]
    fin_cases i <;> simp [twoSiteH0, twoSiteGround]

/-- `P̂₀ = diag(1,0)`: the star projection onto the line `ℂe₀` is `w ↦ ⟪e₀, w⟫ • e₀`, whose matrix
in the standard orthonormal basis has the single entry `1` at `(0,0)`. -/
private theorem twoSite_kernelProjectionMatrix :
    kernelProjectionMatrix twoSiteH0 = twoSiteProj := by
  ext x y
  rw [kernelProjectionMatrix_apply, twoSite_matrixKernel,
    Submodule.starProjection_unit_singleton ℂ twoSite_norm_ground]
  fin_cases x <;> fin_cases y <;>
    simp [twoSiteProj, twoSiteGround, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]

/-- `Φeff = e₀` lies in `ker Ĥ₀`, the membership hypothesis of L4 and L5. -/
theorem twoSite_ground_mem : twoSiteGround ∈ matrixKernel twoSiteH0 := by
  rw [twoSite_matrixKernel]
  exact Submodule.mem_span_singleton_self _

/-- `Ĥ₀ = diag(0,1)` is Hermitian. -/
private theorem twoSite_h0_isHermitian : twoSiteH0.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoSiteH0, Matrix.conjTranspose_apply]

/-- `V̂ = offdiag(1,1)` is Hermitian. -/
theorem twoSite_v_isHermitian : twoSiteV.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoSiteV, Matrix.conjTranspose_apply]

/-- The first-order term vanishes: `P̂₀V̂P̂₀ = diag(1,0)·offdiag(1,1)·diag(1,0) = 0`, because `V̂`
maps the kernel line into its orthogonal complement. -/
theorem twoSite_firstOrder :
    kernelProjectionMatrix twoSiteH0 * twoSiteV * kernelProjectionMatrix twoSiteH0 = 0 := by
  rw [twoSite_kernelProjectionMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSiteProj, twoSiteV, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Ĥ₀` is its own reduced inverse: `diag(0,1)² = diag(0,1) = 1 − P̂₀` and
`P̂₀ diag(0,1) = 0`. -/
theorem twoSite_isReducedInverse : IsReducedInverse twoSiteH0 twoSiteH0 := by
  refine ⟨?_, ?_, ?_, ?_, twoSite_h0_isHermitian⟩ <;>
    rw [twoSite_kernelProjectionMatrix] <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [twoSiteH0, twoSiteProj, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second-order effective Hamiltonian of the witness is `Ĥeff = diag(−1,0)`
(eq. (10.1.20) evaluated on the two-site model). -/
private theorem twoSite_secondOrderEffectiveHamiltonian :
    secondOrderEffectiveHamiltonian twoSiteH0 twoSiteV twoSiteH0 = !![-1, 0; 0, 0] := by
  rw [secondOrderEffectiveHamiltonian, twoSite_kernelProjectionMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSiteH0, twoSiteProj, twoSiteV]

/-- `Φeff = e₀` is an eigenvector of `Ĥeff = diag(−1,0)` with eigenvalue `Eeff = −1`: the
eigenvalue hypothesis of L4 at the witness. -/
theorem twoSite_effective_eigenvector :
    Matrix.toEuclideanLin (secondOrderEffectiveHamiltonian twoSiteH0 twoSiteV twoSiteH0)
        twoSiteGround
      = ((-1 : ℝ) : ℂ) • twoSiteGround := by
  rw [twoSite_secondOrderEffectiveHamiltonian]
  refine PiLp.ext ?_
  intro i
  rw [toEuclideanLin_apply_coord]
  fin_cases i <;> simp [twoSiteGround]

/-- `Ĥ₀ = diag(0,1)` is positive semidefinite, the extra hypothesis L5 imposes on `Ĥ₀`. -/
theorem twoSite_h0_posSemidef : twoSiteH0.PosSemidef := by
  have hd : twoSiteH0 = Matrix.diagonal ![0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoSiteH0, Matrix.diagonal]
  rw [hd, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> simp

/-- `v = 1` is an operator bound for `V̂`, which merely swaps the two coordinates: L5's `hv` at the
witness. -/
private theorem twoSite_v_opBound (u : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanLin twoSiteV u‖ ≤ 1 * ‖u‖ := by
  have h0 : (Matrix.toEuclideanLin twoSiteV u) 0 = u 1 := by
    rw [toEuclideanLin_apply_coord]; simp [twoSiteV]
  have h1 : (Matrix.toEuclideanLin twoSiteV u) 1 = u 0 := by
    rw [toEuclideanLin_apply_coord]; simp [twoSiteV]
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, h0, h1]
  rw [add_comm]

/-- The witness first-order correction is `u = Ĥ₀⁻¹V̂Φeff = e₁`. -/
private theorem twoSite_reducedInverse_v_ground :
    Matrix.toEuclideanLin twoSiteH0 (Matrix.toEuclideanLin twoSiteV twoSiteGround)
      = twoSiteExcited := by
  refine PiLp.ext fun i => ?_
  rw [toEuclideanLin_apply_coord]
  fin_cases i <;>
    simp [twoSiteH0, twoSiteV, twoSiteGround, twoSiteExcited, toEuclideanLin_apply_coord,
      Fin.sum_univ_two]

/-- `⟪Φeff, u⟫ = ⟪e₀, e₁⟫ = 0`: the orthogonality that makes `‖Ψ‖² = 1 + λ²`. -/
private theorem twoSite_inner_ground_excited : (inner ℂ twoSiteGround twoSiteExcited : ℂ) = 0 := by
  simp [twoSiteGround, twoSiteExcited, EuclideanSpace.inner_single_right]

/-- `⟪u, V̂u⟫ = ⟪e₁, e₀⟫ = 0`: the `λ³` coefficient of the exact trial energy vanishes at the
witness, so the closed form leaves `c₃ = |Eeff| ‖u‖² = 1`. -/
private theorem twoSite_inner_excited_v_excited :
    (inner ℂ twoSiteExcited (Matrix.toEuclideanLin twoSiteV twoSiteExcited) : ℂ) = 0 := by
  have h : Matrix.toEuclideanLin twoSiteV twoSiteExcited = twoSiteGround := by
    refine PiLp.ext fun i => ?_
    rw [toEuclideanLin_apply_coord]
    fin_cases i <;> simp [twoSiteV, twoSiteGround, twoSiteExcited]
  rw [h, twoSiteGround, twoSiteExcited, EuclideanSpace.inner_single_right]
  simp

/-- **L2 at the witness**: the trial vector `Ψ = e₀ − λe₁` has exact energy
`⟪Ψ, Ĥ(λ)Ψ⟫ = −λ²`, matching `λ²Eeff` with `Eeff = −1` because the `λ³` term vanishes. -/
private theorem twoSite_trial_energy (lam : ℝ) :
    (inner ℂ (twoSiteGround - (lam : ℂ) • twoSiteExcited)
        (Matrix.toEuclideanLin (perturbedHamiltonian twoSiteH0 twoSiteV lam)
          (twoSiteGround - (lam : ℂ) • twoSiteExcited)) : ℂ)
      = -((lam : ℂ) ^ 2) := by
  have h := inner_trialVector_perturbedHamiltonian (H0 := twoSiteH0) (V := twoSiteV)
    (H0inv := twoSiteH0) (lam := lam) twoSite_ground_mem twoSite_firstOrder
    twoSite_isReducedInverse
  rw [twoSite_reducedInverse_v_ground] at h
  rw [h, twoSite_effective_eigenvector, inner_smul_right, twoSite_inner_excited_v_excited,
    twoSiteGround, EuclideanSpace.inner_single_right]
  simp

/-- The trial vector of the witness has squared norm `‖e₀ − λe₁‖² = 1 + λ²`. -/
private theorem twoSite_trial_norm_sq (lam : ℝ) :
    ‖twoSiteGround - (lam : ℂ) • twoSiteExcited‖ ^ 2 = 1 + lam ^ 2 := by
  have hns : ‖((lam : ℂ)) • twoSiteExcited‖ ^ 2 = lam ^ 2 * ‖twoSiteExcited‖ ^ 2 := by
    rw [norm_smul, mul_pow]
    simp [sq_abs]
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, twoSite_inner_ground_excited, mul_zero,
    twoSite_norm_ground, hns, twoSite_norm_excited]
  simp

/-- **L4 at the witness, non-vacuously.** Every hypothesis of L4 is discharged on the two-site
data, and B2 supplies the ground eigenvalue, so the statement is unconditional: for every
`0 < λ ≤ 1` the perturbed Hamiltonian `Ĥ(λ) = diag(0,1) + λ offdiag(1,1)` *has* a ground
eigenvalue, and it obeys `E ≤ λ²Eeff + c₃λ³ = −λ² + c₃λ³`. -/
example : ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
    ∃ E : ℝ, IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
      (perturbedHamiltonian twoSiteH0 twoSiteV lam) E ∧ E ≤ -(lam ^ 2) + c₃ * lam ^ 3 := by
  obtain ⟨c₃, hc₃, hbound⟩ :=
    exists_const_isGroundEigenvalue_perturbedHamiltonian_le twoSite_h0_isHermitian
      twoSite_v_isHermitian twoSite_isReducedInverse twoSite_firstOrder twoSite_ground_mem
      twoSite_norm_ground twoSite_effective_eigenvector
  refine ⟨c₃, hc₃, fun lam hlam hlam1 => ?_⟩
  obtain ⟨E, hE⟩ := exists_isGroundEigenvalueOn
    (perturbedHamiltonian_isHermitian twoSite_h0_isHermitian twoSite_v_isHermitian)
    (fun _ _ => Submodule.mem_top) top_ne_bot
  refine ⟨E, hE, ?_⟩
  have := hbound lam E hlam hlam1 hE
  linarith

/-- **The closed form of `c₃`, evaluated at the witness.** L4 packages its constant existentially,
so the documented closed form `c₃ = |re⟪u, V̂u⟫| + |Eeff| ‖u‖²` is pinned here instead: at the
two-site data it is `0 + 1·1 = 1`, and the bound `E ≤ −λ² + λ³` with *that* explicit constant
holds. The proof reruns L4's argument concretely — B1 applied to the trial vector, whose exact
energy is `−λ²` (L2) and whose squared norm is `1 + λ²` — so it also checks the two identities the
constant comes from. The exact ground energy of `Ĥ(λ) = !![0, λ; λ, 1]` is `(1 − √(1+4λ²))/2`,
which is the book's `E_GS = {U − √(U²+16t²)}/2` (pp. 341–342) at `U = 1`, `t = λ/2`; its expansion
`−λ² + λ⁴ + O(λ⁶)` shows the bound's leading `λ²` coefficient is sharp, while the whole `λ³` term
is slack (at `λ = 1` the bound reads `0` against the exact `(1 − √5)/2 ≈ −0.618`). -/
example (lam E : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hE : IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
      (perturbedHamiltonian twoSiteH0 twoSiteV lam) E) :
    E ≤ -(lam ^ 2) + 1 * lam ^ 3 := by
  have hB1 := IsGroundEigenvalueOn.mul_norm_sq_le
    (perturbedHamiltonian_isHermitian twoSite_h0_isHermitian twoSite_v_isHermitian)
    (fun _ _ => Submodule.mem_top) hE (twoSiteGround - (lam : ℂ) • twoSiteExcited)
    Submodule.mem_top
  rw [twoSite_trial_energy, twoSite_trial_norm_sq] at hB1
  have hre : RCLike.re (-((lam : ℂ) ^ 2)) = -(lam ^ 2) := by
    rw [RCLike.re_to_complex, ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.ofReal_re]
  rw [hre] at hB1
  nlinarith [hB1, mul_nonneg (pow_pos hlam 3).le (sub_nonneg.mpr hlam1), pow_pos hlam 5]

/-- **L5 at the witness, non-vacuously.** `Ĥ₀ = diag(0,1) ≥ 0` and `v = 1` bounds `V̂`, so the
two-sided estimate applies to the two-site model: for every `λ > 0` a ground eigenvalue exists and
satisfies `|E| ≤ λ`. -/
example (lam : ℝ) (hlam : 0 < lam) :
    ∃ E : ℝ, IsGroundEigenvalueOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
      (perturbedHamiltonian twoSiteH0 twoSiteV lam) E ∧ |E| ≤ lam := by
  obtain ⟨E, hE⟩ := exists_isGroundEigenvalueOn
    (perturbedHamiltonian_isHermitian twoSite_h0_isHermitian twoSite_v_isHermitian)
    (fun _ _ => Submodule.mem_top) top_ne_bot
  refine ⟨E, hE, ?_⟩
  have := abs_isGroundEigenvalue_perturbedHamiltonian_le twoSite_h0_posSemidef
    twoSite_v_isHermitian twoSite_v_opBound twoSite_firstOrder twoSite_ground_mem
    twoSite_norm_ground hlam hE
  linarith

end LatticeSystem.Tests.DegeneratePerturbationGroundEnergy
