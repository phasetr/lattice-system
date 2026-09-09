import LatticeSystem.Quantum.SpinS.ManyBodyPiRotation
import LatticeSystem.Quantum.SpinS.ManyBodyTensorConj
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis2
import LatticeSystem.Quantum.SpinS.TotalSpin
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The many-body lift of the `π` rotations: Tasaki eq. (2.2.11), p. 22

Tasaki *defines* the global rotation operator by

  `Û_θ^{(α)} := exp[−iθ Ŝ_tot^{(α)}] = ∏_{x ∈ Λ} exp[−iθ Ŝ_x^{(α)}]`  (eq. (2.2.11), p. 22),

the second equality being asserted in the same display.  This module proves that equality at
`θ = π` and combines it with the single-site closed forms of eq. (2.1.34), p. 20
(`spinSPiRotationAxis_eq_exp` of `Quantum/SpinS/SpinSPiRotationExpAxis2.lean`), so that the
closed-form global rotation `manyBodySPiRotation` of `Quantum/SpinS/ManyBodyPiRotation.lean` is
identified with the operator exponential `exp(−iπ Ŝ_tot^{(α)})` the book writes.  Tasaki
Problem 2.2.a, p. 23 (`[solution → p. 496]`) — commutation, anticommutation and eigenvector
orthogonality for distinct axes — is then restated on the exponential objects.

The route is axis-independent and uses no property of `Ŝ^{(α)}`: the site embedding `onSiteS x`
is a continuous unital ring homomorphism, hence commutes with the matrix exponential
(`onSiteS_exp`); a many-body tensor is the noncommutative product of the site embeddings of its
factors (`manyBodyTensorS_eq_noncommProd`); and the exponential of a sum of site embeddings,
which commute pairwise across distinct sites, is that product (`manyBodyTensorS_const_exp`).
The products are `Finset.noncommProd` because the many-body operators do not commute in general
and `Λ` carries no order.

The capstone `manyBodySPiRotation_eq_exp` is uniform in the axis `α : Fin 3`, its right-hand
side being written with the inline vector `![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N,
totalSpinSOp3 Λ N] α`, which is by definition `totalSpinSOpVec Λ N α` of
`Quantum/SpinS/CartesianAxis.lean`.

Only `[Fintype Λ]` and `[DecidableEq Λ]` are assumed; `Λ` may be empty, in which case both sides
of the capstone are the identity and the odd-parity statements are vacuous.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, eq. (2.2.11), p. 22, and Problem 2.2.a, p. 23, `[solution → p. 496]`; §2.1,
eq. (2.1.34), p. 20.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## The site embedding and the matrix exponential -/

set_option backward.isDefEq.respectTransparency false in
/-- The site embedding commutes with the matrix exponential, `ι_x(exp A) = exp(ι_x A)`: `onSiteS i`
is a unital ring homomorphism, and it is continuous because it is linear between
finite-dimensional spaces, so the exponential series is mapped term by term.

Matrices carry no canonical norm, so the norm needed to run the series is supplied for the length
of the proof term by the scoped operator-norm instances; the `set_option` is an
elaboration-transparency option (not a lint suppression) required for the resulting defeq check
between the canonical Pi-product topology on matrices and the metric topology of those
instances, and mathlib carries it on every lemma of this shape. -/
theorem onSiteS_exp (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    onSiteS i (NormedSpace.exp A) = NormedSpace.exp (onSiteS i A) :=
  open scoped Matrix.Norms.Operator in
    NormedSpace.map_exp (onSiteSRingHom i)
      (LinearMap.continuous_of_finiteDimensional (onSiteSLinearMap i)) A

/-! ## A many-body tensor as a product of site embeddings -/

/-- A tensor whose factors outside a finite set `s` are the identity is the noncommutative product
over `s` of the site embeddings of the remaining factors.  The induction on `s` is the general form
of the printed remark that operators at different sites commute (below eq. (2.2.5), p. 21): each
step peels off one site with `manyBodyTensorS_mul`, the base case being the all-identity tensor. -/
private theorem manyBodyTensorS_piecewise_eq_noncommProd
    (W : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (s : Finset Λ)
    (comm : (↑s : Set Λ).Pairwise
      (fun x y => Commute (onSiteS x (W x) : ManyBodyOpS Λ N) (onSiteS y (W y)))) :
    manyBodyTensorS (s.piecewise W (fun _ => 1))
      = s.noncommProd (fun x => onSiteS x (W x)) comm := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.noncommProd_empty]
      simpa using manyBodyTensorS_one (Λ := Λ) (N := N)
  | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, ← ih, Finset.piecewise_insert,
        onSiteS_eq_manyBodyTensorS, manyBodyTensorS_mul]
      congr 1
      funext x
      by_cases hx : x = a
      · subst hx
        rw [Function.update_self, Function.update_self, Finset.piecewise_eq_of_notMem _ _ _ ha,
          mul_one]
      · rw [Function.update_of_ne hx, Function.update_of_ne hx, one_mul]

/-- **A many-body tensor is the product of the site embeddings of its factors**,
`⊗_{x ∈ Λ} W_x = ∏_{x ∈ Λ} ι_x(W_x)`, the product being taken as `Finset.noncommProd` since `Λ`
carries no order and the many-body operators need not commute; the factors here do commute
pairwise because they act on distinct sites. -/
theorem manyBodyTensorS_eq_noncommProd (W : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (comm : (↑(Finset.univ : Finset Λ) : Set Λ).Pairwise
      (fun x y => Commute (onSiteS x (W x) : ManyBodyOpS Λ N) (onSiteS y (W y)))) :
    manyBodyTensorS W = Finset.univ.noncommProd (fun x => onSiteS x (W x)) comm := by
  have hW : (Finset.univ : Finset Λ).piecewise W (fun _ => 1) = W := by
    funext x
    exact Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_univ x)
  conv_lhs => rw [← hW]
  exact manyBodyTensorS_piecewise_eq_noncommProd W Finset.univ comm

/-! ## The many-body lift of eq. (2.2.11), p. 22 -/

/-- **The crux of eq. (2.2.11), p. 22**: the uniform tensor of a single-site exponential is the
exponential of the total (site-summed) operator, `⊗_{x ∈ Λ} exp(A) = exp(Σ_{x ∈ Λ} ι_x(A))`.  The
site embeddings commute across distinct sites, so the exponential of their sum factors into the
noncommutative product of the site exponentials, and each factor is a site embedding of `exp A` by
`onSiteS_exp`.  No property of `A` is used. -/
theorem manyBodyTensorS_const_exp (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyTensorS (fun _ : Λ => NormedSpace.exp A)
      = NormedSpace.exp (∑ x : Λ, onSiteS x A : ManyBodyOpS Λ N) := by
  rw [Matrix.exp_sum_of_commute (Finset.univ : Finset Λ)
      (fun x => (onSiteS x A : ManyBodyOpS Λ N))
      (fun _ _ _ _ hxy => onSiteS_commute_of_ne hxy A A),
    manyBodyTensorS_eq_noncommProd (fun _ : Λ => NormedSpace.exp A)
      (fun _ _ _ _ hxy => onSiteS_commute_of_ne hxy _ _)]
  exact Finset.noncommProd_congr rfl (fun x _ => onSiteS_exp x A) _

/-- Scalars pull out of a sum of site embeddings.  This is the step identifying
`Σ_{x ∈ Λ} ι_x(−iπ Ŝ^{(α)})` with `−iπ Ŝ_tot^{(α)}` for the total spin operator of
eq. (2.2.7), p. 22. -/
theorem sum_onSiteS_smul (c : ℂ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (∑ x : Λ, onSiteS x (c • A) : ManyBodyOpS Λ N) = c • ∑ x : Λ, onSiteS x A := by
  simp only [onSiteS_smul, Finset.smul_sum]

/-- **Tasaki eq. (2.2.11), p. 22, at `θ = π`**: the global `π` rotation about the axis `α : Fin 3`,
defined in `Quantum/SpinS/ManyBodyPiRotation.lean` as the lattice tensor of the closed-form
single-site rotations of eq. (2.1.34), p. 20, is the operator exponential
`Û_π^{(α)} = exp(−iπ Ŝ_tot^{(α)})` of the total spin operator of eq. (2.2.7), p. 22.

The right-hand side selects the axis with the inline vector `![totalSpinSOp1 Λ N,
totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α`, which is by definition `totalSpinSOpVec Λ N α` of
`Quantum/SpinS/CartesianAxis.lean`, so a consumer holding the latter bridges by `rfl`. -/
theorem manyBodySPiRotation_eq_exp (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) (α : Fin 3) :
    manyBodySPiRotation Λ N α =
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α)) := by
  rw [manyBodySPiRotation]
  simp only [spinSPiRotationAxis_eq_exp]
  rw [manyBodyTensorS_const_exp, sum_onSiteS_smul]
  congr 1
  congr 1
  fin_cases α <;> rfl

/-! ## Tasaki Problem 2.2.a, p. 23, on the exponential objects -/

/-- **Tasaki Problem 2.2.a (a), p. 23** in the book's own notation: when `|Λ|S` is an integer —
equivalently `|Λ|·2S` even — the global rotations `exp(−iπ Ŝ_tot^{(α)})` about distinct axes
commute.  The content is the closed-form statement of `Quantum/SpinS/ManyBodyPiRotation.lean`,
transported along eq. (2.2.11), p. 22. -/
theorem manyBodySPiRotationExp_commute_of_even (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)
    (hc : Even (Fintype.card Λ * N)) {α β : Fin 3} (h : α ≠ β) :
    NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α)) *
        NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) •
            (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] β)) =
      NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) •
            (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] β)) *
        NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) •
            (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α)) := by
  simp only [← manyBodySPiRotation_eq_exp]
  exact manyBodySPiRotation_commute_of_even Λ N hc h

/-- **Tasaki Problem 2.2.a (b), p. 23** in the book's own notation: when `|Λ|S` is a half-odd
integer — equivalently `|Λ|·2S` odd — the global rotations `exp(−iπ Ŝ_tot^{(α)})` about distinct
axes anticommute. -/
theorem manyBodySPiRotationExp_anticommute_of_odd (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)
    (hc : Odd (Fintype.card Λ * N)) {α β : Fin 3} (h : α ≠ β) :
    NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α)) *
        NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) •
            (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] β)) =
      -(NormedSpace.exp
            (-(((Real.pi : ℂ) * Complex.I)) •
              (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] β)) *
          NormedSpace.exp
            (-(((Real.pi : ℂ) * Complex.I)) •
              (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α))) := by
  simp only [← manyBodySPiRotation_eq_exp]
  exact manyBodySPiRotation_anticommute_of_odd Λ N hc h

/-- **Tasaki Problem 2.2.a (c), p. 23 (`[solution → p. 496]`)** in the book's own notation: for
half-odd-integer `|Λ|S` and distinct axes, every eigenvector `Φ ≠ 0` of `exp(−iπ Ŝ_tot^{(α)})` is
orthogonal to `exp(−iπ Ŝ_tot^{(β)})Φ`. -/
theorem tasaki_problem_2_2_a_exp_eigenvector_orthogonal (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (N : ℕ) (hc : Odd (Fintype.card Λ * N)) {α β : Fin 3} (h : α ≠ β)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : Φ ≠ 0) {lam : ℂ}
    (heig : Matrix.mulVec
      (NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α))) Φ = lam • Φ) :
    star Φ ⬝ᵥ
        Matrix.mulVec
          (NormedSpace.exp
            (-(((Real.pi : ℂ) * Complex.I)) •
              (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] β))) Φ = 0 := by
  simp only [← manyBodySPiRotation_eq_exp] at heig ⊢
  exact tasaki_problem_2_2_a_eigenvector_orthogonal Λ N hc h hΦ heig

end LatticeSystem.Quantum
