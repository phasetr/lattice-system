import LatticeSystem.Quantum.SpinS.ManyBodyTensorS
import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Math.MatrixAnalysis.AnticommutingEigenvectorOrthogonality

/-!
# Many-body `π` rotations and Tasaki Problem 2.2.a

The global rotation operator of Tasaki eq. (2.2.11), p. 22,

  `Û_θ^{(α)} := exp[−iθ Ŝ_tot^{(α)}] = ∏_{x ∈ Λ} exp[−iθ Ŝ_x^{(α)}]`,

specialised to `θ = π`, where each factor is the closed-form single-site `π` rotation `û_α` of
`Quantum/SpinS/SpinSPiRotation.lean` (eq. (2.1.29), p. 19).  The site factors act on disjoint
tensor slots, so the lattice product is the many-body tensor `⊗_{x ∈ Λ} û_α` of
`Quantum/SpinS/ManyBodyTensorS.lean`.

**What is formalised, and what is not.**  As in `Quantum/SpinS/SpinSPiRotation.lean`, the
rotations are *defined* by their closed-form matrices — the eq. (2.1.24)/(2.1.25)-level algebra of
a phase `(−i)^{2S}` times a real involution.  The identification of the axis-`3` closed form
`spinSPiRotation3` with `exp(−iπ Ŝ^{(3)})` at general `S` is now proved,
`spinSPiRotation3_eq_spinSRot3_pi` of `Quantum/SpinS/SpinSPiRotationExpAxis3.lean` (Tasaki
eq. (2.1.34) / Problem 2.1.g, p. 20); the identification for axes `1` and `2`, and its lift through
`manyBodyTensorS` to the many-body `Û_π^{(α)}` of this file, remain **not** formalised — no
declaration in this chain mentions `Matrix.exp` or `NormedSpace.exp`.  Exponential rotations and
bridges do exist elsewhere in the repository — `spinSRot3 N θ = exp(−iθ Ŝ^{(3)})` of
`Quantum/SpinS/Problem25cZAxisRotationInput.lean`, whose closed form `spinSRot3_eq_diagonal` and
general-`S` many-body bridge `manyBodyTensorS_spinSRot3_eq_exp_totalSpinSOp3` are proved in
`Quantum/SpinS/Problem25cZAxisRotationCommutation.lean`, and `spinSRot1 N θ = exp(−iθ Ŝ^{(1)})`
of `Quantum/SpinS/SpinSRotation1.lean`, which carries no closed form; the general-`S` global
exponentials `saturatedGlobalRot2` / `saturatedGlobalRot3` about the axes `2` and `3` of
`Quantum/SpinS/SaturatedCoherentAmplitude.lean`; the general-`S` twist bridge
`lsmTwistOperator_eq_diagonal` of `Quantum/SpinS/LiebSchultzMattisProof.lean`; and the spin-`1/2`
`totalSpinHalfRot{1,2,3}_eq_exp` of `Quantum/TotalSpin/Rotation.lean` — of these only
`spinSRot3` is related to the closed forms used here, through the axis-`3` identification of the
single-site factor `spinSPiRotationAxis` above; the axes `1`, `2` and the many-body
`manyBodySPiRotation` lift stay unrelated.  The exponentials written above and below are the
book's notation for the closed-form matrices, not (outside axis `3` at the single-site level) a
proved equality.

At `S = 1` (`N = 2`) the same operator is also built as the whole-chain `piRotationS` of
`Quantum/SpinS/KennedyTasakiTransformation.lean`, from the real involution `1 − 2(Ŝ^{(α)})²`.
That construction is the same operator, but the equality is not proved here: nothing on the
critical path of Problem 2.2.a needs it.

**Tasaki Problem 2.2.a, p. 23 (`[solution → p. 496]`).**  For `α ≠ β` the two global rotations
commute when `|Λ|S` is an integer and anticommute when it is a half-odd integer; in the latter
case every eigenstate `|Φ⟩` of `Û_π^{(α)}` is orthogonal to `Û_π^{(β)}|Φ⟩`.  With `N = 2S`, the
dichotomy `|Λ|S ∈ ℤ` versus `|Λ|S ∈ ℤ + 1/2` is the parity of `|Λ| · N`.

Both parities descend from one master identity, `Û^{(β)}Û^{(α)} = (−1)^{|Λ|N} Û^{(α)}Û^{(β)}`,
which lifts the single-site sign of eq. (2.1.25), p. 18, through the `|Λ|`-fold product.

Only `[Fintype Λ]` and `[DecidableEq Λ]` are assumed (both forced by `Finset.univ` and by the
many-body operator type); `Λ` may be empty, in which case `|Λ| · N = 0` is even and the
anticommuting statements are vacuous by their own hypotheses.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, Problem 2.2.a, p. 23, `[solution → p. 496]`; eq. (2.2.11), p. 22; §2.1,
eq. (2.1.25), p. 18, and eq. (2.1.29), p. 19.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## The lattice product of a single-site operator -/

omit [DecidableEq Λ] in
/-- A scalar on the single-site factor of a uniform lattice tensor is raised to the number of
sites: this is the step that turns the single-site sign of eq. (2.1.25), p. 18, into the
`|Λ|`-fold sign of Problem 2.2.a. -/
private theorem manyBodyTensorS_const_smul (c : ℂ)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyTensorS (fun _ : Λ => c • U)
      = (c ^ Fintype.card Λ) • manyBodyTensorS (fun _ : Λ => U) := by
  ext σ' σ
  simp only [manyBodyTensorS_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

/-! ## The global `π` rotations of eq. (2.2.11) -/

/-- **Tasaki eq. (2.2.11), p. 22, at `θ = π`**: the global `π` rotation `Û_π^{(α)}` about the axis
selected by `α : Fin 3`, as the uniform lattice tensor `⊗_{x ∈ Λ} û_α` of the closed-form
single-site factor.  The book writes it `∏_{x ∈ Λ} exp(−iπ Ŝ_x^{(α)})`; the exponential
identification is notation here, not a formalised equality (see the module header). -/
noncomputable def manyBodySPiRotation (α : Fin 3) : ManyBodyOpS Λ N :=
  manyBodyTensorS (fun _ : Λ => spinSPiRotationAxis N α)

/-- **The master sign identity of Tasaki Problem 2.2.a, p. 23**: for distinct axes, swapping the
two global `π` rotations costs `(−1)^{|Λ|·2S}`.  Each of the `|Λ|` site factors contributes the
single-site sign of eq. (2.1.25), p. 18. -/
theorem manyBodySPiRotation_swap_mul_of_ne {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α
      = ((-1 : ℂ) ^ (Fintype.card Λ * N)) •
          (manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β) := by
  have hβα : manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α
      = manyBodyTensorS
          (fun _ : Λ => spinSPiRotationAxis N β * spinSPiRotationAxis N α) :=
    manyBodyTensorS_mul _ _
  have hαβ : manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β
      = manyBodyTensorS
          (fun _ : Λ => spinSPiRotationAxis N α * spinSPiRotationAxis N β) :=
    manyBodyTensorS_mul _ _
  rw [hβα, hαβ, spinSPiRotationAxis_swap_mul_of_ne h, manyBodyTensorS_const_smul, ← pow_mul,
    Nat.mul_comm N (Fintype.card Λ)]

/-- **Tasaki Problem 2.2.a (a), p. 23.**  When `|Λ|S` is an integer — equivalently `|Λ|·2S` is
even — the global `π` rotations about distinct axes commute. -/
theorem manyBodySPiRotation_commute_of_even (hc : Even (Fintype.card Λ * N))
    {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β
      = manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α := by
  rw [manyBodySPiRotation_swap_mul_of_ne Λ N h.symm, hc.neg_one_pow, one_smul]

/-- **Tasaki Problem 2.2.a (b), p. 23.**  When `|Λ|S` is a half-odd integer — equivalently
`|Λ|·2S` is odd — the global `π` rotations about distinct axes anticommute. -/
theorem manyBodySPiRotation_anticommute_of_odd (hc : Odd (Fintype.card Λ * N))
    {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β
      = -(manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α) := by
  rw [manyBodySPiRotation_swap_mul_of_ne Λ N h.symm, hc.neg_one_pow, neg_one_smul]

/-- Each global `π` rotation is unitary: the adjoint of a lattice tensor is the tensor of the
site-wise adjoints, and each site factor is unitary. -/
theorem manyBodySPiRotation_conjTranspose_mul_self (α : Fin 3) :
    (manyBodySPiRotation Λ N α).conjTranspose * manyBodySPiRotation Λ N α = 1 := by
  have hu : (spinSPiRotationAxis N α).conjTranspose * spinSPiRotationAxis N α = 1 := by
    have hmem := spinSPiRotationAxis_mem_unitaryGroup N α
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    exact hmem
  rw [manyBodySPiRotation, manyBodyTensorS_conjTranspose, manyBodyTensorS_mul]
  simp only [hu]
  exact manyBodyTensorS_one

/-- **Tasaki Problem 2.2.a (c), p. 23 (`[solution → p. 496]`).**  For half-odd-integer `|Λ|S` and
distinct axes, every eigenvector `Φ ≠ 0` of `Û_π^{(α)}` is orthogonal to `Û_π^{(β)}Φ`.  The two
rotations anticommute by (b) and each is an isometry, so the generic `|λ| = 1` argument of
`Math/MatrixAnalysis/AnticommutingEigenvectorOrthogonality.lean` applies. -/
theorem tasaki_problem_2_2_a_eigenvector_orthogonal (hc : Odd (Fintype.card Λ * N))
    {α β : Fin 3} (h : α ≠ β) {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : Φ ≠ 0) {lam : ℂ}
    (heig : (manyBodySPiRotation Λ N α).mulVec Φ = lam • Φ) :
    star Φ ⬝ᵥ (manyBodySPiRotation Λ N β).mulVec Φ = 0 :=
  Matrix.dotProduct_mulVec_eq_zero_of_anticommute_eigenvector
    (manyBodySPiRotation_conjTranspose_mul_self Λ N α)
    (manyBodySPiRotation_anticommute_of_odd Λ N hc h.symm) hΦ heig

end LatticeSystem.Quantum
