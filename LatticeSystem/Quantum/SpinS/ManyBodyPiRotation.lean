import LatticeSystem.Quantum.SpinS.MultiSiteCore
import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Math.MatrixAnalysis.NoncommProd
import LatticeSystem.Math.MatrixAnalysis.AnticommutingEigenvectorOrthogonality

/-!
# Many-body `π` rotations and Tasaki Problem 2.2.a

The global rotation operator of Tasaki eq. (2.2.11), p. 22,

  `Û_θ^{(α)} := exp[−iθ Ŝ_tot^{(α)}] = ∏_{x ∈ Λ} exp[−iθ Ŝ_x^{(α)}]`,

specialised to `θ = π`, where each factor is the closed-form single-site `π` rotation `û_α` of
`Quantum/SpinS/SpinSPiRotation.lean` (eq. (2.1.29), p. 19).  The site factors commute, so the
lattice product is a `Finset.noncommProd`.

**Tasaki Problem 2.2.a, p. 23 (`[solution → p. 496]`).**  For `α ≠ β` the two global rotations
commute when `|Λ|S` is an integer and anticommute when it is a half-odd integer; in the latter
case every eigenstate `|Φ⟩` of `Û_π^{(α)}` is orthogonal to `Û_π^{(β)}|Φ⟩`.  With `N = 2S`, the
dichotomy `|Λ|S ∈ ℤ` versus `|Λ|S ∈ ℤ + 1/2` is the parity of `|Λ| · N`.

Both parities descend from one master identity, `Û^{(β)}Û^{(α)} = (−1)^{|Λ|N} Û^{(α)}Û^{(β)}`,
which lifts the single-site sign of eq. (2.1.25), p. 18, through the `|Λ|`-fold product.

Only `[Fintype Λ]` and `[DecidableEq Λ]` are assumed (both forced by `Finset.univ` and by
`onSiteS`); `Λ` may be empty, in which case `|Λ| · N = 0` is even and the anticommuting statements
are vacuous by their own hypotheses.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, Problem 2.2.a, p. 23, `[solution → p. 496]`; eq. (2.2.11), p. 22; §2.1,
eq. (2.1.25), p. 18, and eq. (2.1.29), p. 19.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## The lattice product of a single-site operator -/

/-- The site-wise product `∏_{x ∈ Λ} onSiteS x U` of a single-site matrix `U`, formed as a
`Finset.noncommProd` because distinct-site embeddings commute (`onSiteS_mul_onSiteS_of_ne`).  This
is the general-spin analogue of the private `totalSpinHalfRotOf` of
`Quantum/TotalSpin/Rotation.lean`, which lives on the spin-`1/2` configuration type and cannot be
shared. -/
private noncomputable def manyBodySPiRotationOf (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ManyBodyOpS Λ N :=
  (Finset.univ : Finset Λ).noncommProd (fun x => onSiteS x U)
    (fun _ _ _ _ hxy => onSiteS_mul_onSiteS_of_ne hxy _ _)

/-- Lattice products multiply site-wise: the product of the lattice products of `U` and `V` is the
lattice product of `U * V`. -/
private theorem manyBodySPiRotationOf_mul (U V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodySPiRotationOf Λ N U * manyBodySPiRotationOf Λ N V
      = manyBodySPiRotationOf Λ N (U * V) := by
  unfold manyBodySPiRotationOf
  rw [← Finset.noncommProd_mul_distrib
    (s := (Finset.univ : Finset Λ))
    (f := fun x : Λ => onSiteS x U)
    (g := fun x : Λ => onSiteS x V)
    (comm_ff := fun _ _ _ _ hxy => onSiteS_mul_onSiteS_of_ne hxy _ _)
    (comm_gg := fun _ _ _ _ hxy => onSiteS_mul_onSiteS_of_ne hxy _ _)
    (comm_gf := fun _ _ _ _ hxy => onSiteS_mul_onSiteS_of_ne hxy _ _)]
  refine Finset.noncommProd_congr rfl ?_ _
  intro x _
  exact onSiteS_mul_onSiteS_same x U V

/-- A scalar on the single-site factor is raised to the number of sites: this is the step that
turns the single-site sign of eq. (2.1.25), p. 18, into the `|Λ|`-fold sign of Problem 2.2.a. -/
private theorem manyBodySPiRotationOf_smul (c : ℂ)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodySPiRotationOf Λ N (c • U)
      = (c ^ Fintype.card Λ) • manyBodySPiRotationOf Λ N U := by
  have hone : manyBodySPiRotationOf Λ N (c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))
      = (c ^ Fintype.card Λ) • (1 : ManyBodyOpS Λ N) := by
    unfold manyBodySPiRotationOf
    rw [Finset.noncommProd_eq_pow_card _ _ _ (c • (1 : ManyBodyOpS Λ N))
      (fun x _ => by rw [onSiteS_smul, onSiteS_one]), smul_pow, one_pow, Finset.card_univ]
  have hsplit : c • U = (c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) * U := by
    rw [smul_mul_assoc, Matrix.one_mul]
  rw [hsplit, ← manyBodySPiRotationOf_mul, hone, Matrix.smul_mul, Matrix.one_mul]

/-! ## The global `π` rotations of eq. (2.2.11) -/

/-- **Tasaki eq. (2.2.11), p. 22, at `θ = π`**: the global `π` rotation
`Û_π^{(α)} = ∏_{x ∈ Λ} exp(−iπ Ŝ_x^{(α)})` about the axis selected by `α : Fin 3`. -/
noncomputable def manyBodySPiRotation (α : Fin 3) : ManyBodyOpS Λ N :=
  manyBodySPiRotationOf Λ N (spinSPiRotationAxis N α)

/-- **The master sign identity of Tasaki Problem 2.2.a, p. 23**: for distinct axes, swapping the
two global `π` rotations costs `(−1)^{|Λ|·2S}`.  Each of the `|Λ|` site factors contributes the
single-site sign of eq. (2.1.25), p. 18. -/
theorem manyBodySPiRotation_swap_mul_of_ne {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α
      = ((-1 : ℂ) ^ (Fintype.card Λ * N)) •
          (manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β) := by
  simp only [manyBodySPiRotation]
  rw [manyBodySPiRotationOf_mul, manyBodySPiRotationOf_mul,
    spinSPiRotationAxis_swap_mul_of_ne h, manyBodySPiRotationOf_smul, ← pow_mul,
    Nat.mul_comm N (Fintype.card Λ)]

end LatticeSystem.Quantum
