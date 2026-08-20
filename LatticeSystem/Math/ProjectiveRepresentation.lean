import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Projective representations and the coboundary criterion

Tasaki's §8.3.5 setting for symmetry actions on a single-site (or bond) space: a group `G` acts by
operators `v̂(g)` that are unitary or antiunitary, and that compose only up to a phase,
`v̂(g) v̂(h) = e^{iφ̃(g,h)} v̂(gh)` (eq. (8.3.42)).  The representation is *trivial* when it is a
genuine representation up to a `g`-dependent phase, and the content of this module is that
triviality is equivalent to the phase function being a coboundary in the sense of eq. (8.3.43).

The unitary/antiunitary dichotomy is carried by a sign character `s : G →* ℤˣ` and encoded on
matrices by entrywise complex conjugation (eq. (8.3.40)), so no antilinear-operator theory is
needed: with the book's case distinction `v̂(g) = û(g)` for `ε(g) = 1` and `v̂(g) = û(g) K̂` for
`ε(g) = -1`, where `K̂ X = X* K̂` and `K̂² = 1`, eq. (8.3.42) is equivalent to the matrix identity
`û(g) · C_g[û(h)] = e^{iφ̃(g,h)} û(gh)`.  The same encoding is used for the antiunitary case of
Wigner's theorem in `LatticeSystem.Math.WignerTheorem`.

Phases live in mathlib's `Circle` rather than in `ℝ`: `Circle.exp : ℝ → Circle` is surjective, so
`∃ ψ : G → Circle` is equivalent to the book's `∃ ψ̃ : G → ℝ`, while the book's "mod 2π" becomes
definitional equality and the twist `s(g)·ψ̃(h)` becomes the uniform `ψ h ^ (s g : ℤ)` (on the
circle, inversion is complex conjugation).  Everything is stated for an arbitrary index type `D`,
since the book applies the notion both to the single-spin space and to the bond space.

`IsPhaseCoboundary` is the mathlib predicate `IsMulCoboundary₂` for the coefficient group
`M = Circle` with the `s`-twisted action `z ↦ z ^ (s g : ℤ)`; it is spelled out here because that
action is data-dependent (it varies with `s`) and because the cocycle condition — the other half of
the group-cohomological package — is explicitly not used in this part of the book.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.), §8.3.5,
eqs. (8.3.40)–(8.3.43), pp. 277–278.
-/

namespace LatticeSystem.Math

variable {G : Type*} [Group G] {D : Type*} [Fintype D] [DecidableEq D]

/-- The scalar part of the operation `C_g` of eq. (8.3.40): the identity for the sign `ε = 1`
(unitary case) and complex conjugation for `ε = -1` (antiunitary case). -/
def signConj (ε : ℤˣ) : ℂ →+* ℂ :=
  if ε = 1 then RingHom.id ℂ else starRingEnd ℂ

/-- The operation `C_g` of eq. (8.3.40) on matrices: entrywise application of `signConj`, i.e. the
identity for `ε = 1` and entrywise complex conjugation for `ε = -1`. -/
def signConjMatrix (ε : ℤˣ) : Matrix D D ℂ →+* Matrix D D ℂ :=
  (signConj ε).mapMatrix

/-- On phases, `C_g` is the sign-indexed power `z ↦ z ^ ε`: the identity for `ε = 1` and inversion
for `ε = -1`, since inversion and complex conjugation agree on the unit circle. -/
lemma signConj_circle (ε : ℤˣ) (z : Circle) :
    signConj ε (z : ℂ) = ((z ^ (ε : ℤ) : Circle) : ℂ) := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · simp [signConj]
  · rw [signConj, if_neg (by decide : (-1 : ℤˣ) ≠ 1), ← Circle.coe_inv_eq_conj]
    simp

/-- `signConjMatrix` is homogeneous for the twisted scalar action: pulling a scalar out of an
entrywise conjugation conjugates the scalar. -/
lemma signConjMatrix_smul (ε : ℤˣ) (z : ℂ) (X : Matrix D D ℂ) :
    signConjMatrix ε (z • X) = signConj ε z • signConjMatrix ε X := by
  ext i j
  simp [signConjMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, map_mul]

/-! ## Entrywise conjugation: involutivity, adjoint, unitaries, spectrum, rank

The operation `C_g` of eq. (8.3.40) is a ring homomorphism that is only *conjugate* linear, so the
usual linear-algebra transport lemmas have to be recorded by hand.  They are what carries the
injectivity of a matrix product state to its symmetry-transformed partner (§8.3.4, p. 265).
-/

/-- At the unitary sign `ε = 1` the scalar twist of eq. (8.3.40) is the identity. -/
lemma signConj_one_apply (z : ℂ) : signConj 1 z = z := by
  simp [signConj]

/-- At the antiunitary sign `ε = -1` the scalar twist of eq. (8.3.40) is complex conjugation. -/
lemma signConj_neg_one_apply (z : ℂ) : signConj (-1) z = starRingEnd ℂ z := by
  simp [signConj]

/-- At the unitary sign `ε = 1` the matrix twist of eq. (8.3.40) is the identity. -/
lemma signConjMatrix_one_apply (X : Matrix D D ℂ) : signConjMatrix 1 X = X := by
  simp [signConjMatrix, signConj]

/-- At the antiunitary sign `ε = -1` the matrix twist of eq. (8.3.40) is entrywise complex
conjugation. -/
lemma signConjMatrix_neg_one_apply (X : Matrix D D ℂ) :
    signConjMatrix (-1) X = X.map (starRingEnd ℂ) := by
  ext i j
  simp [signConjMatrix, signConj]

/-- The scalar twist is an involution, since complex conjugation is. -/
lemma signConj_signConj (ε : ℤˣ) (z : ℂ) : signConj ε (signConj ε z) = z := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · simp [signConj_one_apply]
  · simp [signConj_neg_one_apply]

/-- The matrix twist is an involution. -/
lemma signConjMatrix_signConjMatrix (ε : ℤˣ) (X : Matrix D D ℂ) :
    signConjMatrix ε (signConjMatrix ε X) = X := by
  ext i j
  simp [signConjMatrix, signConj_signConj]

/-- The scalar twist is an isometry: `|C_g[z]| = |z|`. -/
lemma norm_signConj (ε : ℤˣ) (z : ℂ) : ‖signConj ε z‖ = ‖z‖ := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · rw [signConj_one_apply]
  · rw [signConj_neg_one_apply, RCLike.norm_conj]

/-- The matrix twist commutes with the adjoint: `C_g[X]† = C_g[X†]`. -/
lemma signConjMatrix_conjTranspose (ε : ℤˣ) (X : Matrix D D ℂ) :
    (signConjMatrix ε X).conjTranspose = signConjMatrix ε X.conjTranspose := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · rw [signConjMatrix_one_apply, signConjMatrix_one_apply]
  · ext i j
    simp [signConjMatrix_neg_one_apply, Matrix.conjTranspose_apply]

/-- The matrix twist preserves unitarity, since it is a ring homomorphism commuting with the
adjoint.  The twisted mixing matrix `C_g[u]` of the *inverse* symmetry transport is therefore again
unitary, which is what lets the spanning conditions be pulled back along it (§8.3.4, p. 265). -/
lemma signConjMatrix_mem_unitaryGroup (ε : ℤˣ) {X : Matrix D D ℂ}
    (hX : X ∈ Matrix.unitaryGroup D ℂ) : signConjMatrix ε X ∈ Matrix.unitaryGroup D ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hX ⊢
  rw [Matrix.star_eq_conjTranspose, signConjMatrix_conjTranspose, ← map_mul,
    ← Matrix.star_eq_conjTranspose, hX, map_one]

/-- The matrix twist moves the spectrum by the scalar twist: `μ` is an eigenvalue of `C_g[X]`
exactly when `C_g[μ]` is an eigenvalue of `X`. -/
lemma mem_spectrum_signConjMatrix_iff (ε : ℤˣ) (X : Matrix D D ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ (signConjMatrix ε X) ↔ signConj ε μ ∈ spectrum ℂ X := by
  have hkey : algebraMap ℂ (Matrix D D ℂ) μ - signConjMatrix ε X =
      signConjMatrix ε (algebraMap ℂ (Matrix D D ℂ) (signConj ε μ) - X) := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      signConjMatrix_smul, map_one, signConj_signConj]
  rw [spectrum.mem_iff, spectrum.mem_iff, hkey]
  refine not_congr ⟨fun h => ?_, fun h => h.map (signConjMatrix ε)⟩
  simpa [signConjMatrix_signConjMatrix] using h.map (signConjMatrix ε)

section Rank

open scoped ComplexOrder

/-- The matrix twist preserves the rank: entrywise conjugation is the composition of the adjoint
with the transpose, and both preserve the rank. -/
private lemma rank_signConjMatrix (ε : ℤˣ) (X : Matrix D D ℂ) :
    (signConjMatrix ε X).rank = X.rank := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · rw [signConjMatrix_one_apply]
  · have hmap : signConjMatrix (-1 : ℤˣ) X = X.conjTranspose.transpose := by
      ext i j
      simp [signConjMatrix_neg_one_apply, Matrix.conjTranspose_apply]
    rw [hmap, Matrix.rank_transpose, Matrix.rank_conjTranspose]

/-- The matrix twist preserves the dimension of the kernel of the associated linear map.  Applied
to `Ã - λ` this is what transports the simplicity of the transfer eigenvalue `λ`. -/
lemma finrank_ker_mulVecLin_signConjMatrix (ε : ℤˣ) (X : Matrix D D ℂ) :
    Module.finrank ℂ (LinearMap.ker (signConjMatrix ε X).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker X.mulVecLin) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (signConjMatrix ε X).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  have hrank : Module.finrank ℂ (LinearMap.range (signConjMatrix ε X).mulVecLin) =
      Module.finrank ℂ (LinearMap.range X.mulVecLin) := rank_signConjMatrix ε X
  omega

end Rank

/-- **Projective representation** (eqs. (8.3.41)–(8.3.42)).  A family of unitaries `u : G → Matrix`
with `u 1 = 1`, together with a sign character `s` recording for each `g` whether `v̂(g)` is unitary
(`s g = 1`) or antiunitary (`s g = -1`), composes up to the phase `φ`:
`û(g) · C_g[û(h)] = e^{iφ̃(g,h)} û(gh)`.  The normalisation `u 1 = 1` is part of the book's setup
(p. 277); it does not follow from the composition law. -/
def IsProjectiveRep (u : G → Matrix D D ℂ) (s : G →* ℤˣ) (φ : G → G → Circle) : Prop :=
  (∀ g, u g ∈ Matrix.unitaryGroup D ℂ) ∧ u 1 = 1 ∧
    ∀ g h, u g * signConjMatrix (s g) (u h) = (φ g h : ℂ) • u (g * h)

/-- **Trivial projective representation** (p. 278).  `u` is trivial when it is a genuine
representation `v` up to a `g`-dependent phase, `û(g) = e^{iψ̃(g)} v̂₀(g)`.  The book's genuine
representation `v̂₀` (`v̂₀(e) = 1̂`, `v̂₀(g)v̂₀(h) = v̂₀(gh)`) is exactly `IsProjectiveRep v s 1`,
the projective representation with identically trivial phase. -/
def IsTrivialProjectiveRep (u : G → Matrix D D ℂ) (s : G →* ℤˣ) : Prop :=
  ∃ (v : G → Matrix D D ℂ) (ψ : G → Circle), IsProjectiveRep v s 1 ∧ ∀ g, u g = (ψ g : ℂ) • v g

/-- **Coboundary phase function** (eq. (8.3.43)).  `φ` is a coboundary when it comes from a gauge
`ψ : G → Circle` as `φ̃(g,h) = ψ̃(g) + s(g)ψ̃(h) − ψ̃(gh)` (mod 2π), written multiplicatively
with the sign entering as the exponent `s g`. -/
def IsPhaseCoboundary (s : G →* ℤˣ) (φ : G → G → Circle) : Prop :=
  ∃ ψ : G → Circle, ∀ g h, φ g h = ψ g * ψ h ^ (s g : ℤ) * (ψ (g * h))⁻¹

/-- A unitary matrix over a nonempty index type determines the scalar it is scaled by. -/
private lemma smul_left_cancel_of_unitary [Nonempty D] {A : Matrix D D ℂ}
    (hA : A ∈ Matrix.unitaryGroup D ℂ) {z w : ℂ} (h : z • A = w • A) : z = w := by
  have hAA : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hA
  have h' : z • (A * star A) = w • (A * star A) := by
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, h]
  rw [hAA] at h'
  obtain ⟨i⟩ := ‹Nonempty D›
  simpa using congrFun (congrFun h' i) i

/-- Scaling a unitary by a phase keeps it unitary. -/
lemma circle_smul_mem_unitaryGroup (z : Circle) {A : Matrix D D ℂ}
    (hA : A ∈ Matrix.unitaryGroup D ℂ) : (z : ℂ) • A ∈ Matrix.unitaryGroup D ℂ := by
  have hz : (z : ℂ) * star (z : ℂ) = 1 := by
    rw [← starRingEnd_apply, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel,
      Circle.coe_one]
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA, hz, one_smul]

/-- The phase of a projective representation is trivial at the identity pair, since `u 1 = 1`. -/
private lemma phase_self_one [Nonempty D] {u : G → Matrix D D ℂ} {s : G →* ℤˣ}
    {φ : G → G → Circle} (hu : IsProjectiveRep u s φ) : φ 1 1 = 1 := by
  obtain ⟨-, hone, hmul⟩ := hu
  have h := hmul 1 1
  simp only [mul_one, hone, map_one] at h
  have h1 : ((1 : Circle) : ℂ) • (1 : Matrix D D ℂ) =
      ((φ 1 1 : Circle) : ℂ) • (1 : Matrix D D ℂ) := by
    rw [Circle.coe_one, one_smul]
    exact h
  exact (Circle.coe_injective (smul_left_cancel_of_unitary (Submonoid.one_mem _) h1)).symm

/-- **Tasaki §8.3.5, eq. (8.3.43).**  A projective representation is trivial — a genuine
representation up to a `g`-dependent phase — if and only if its phase function is a coboundary,
`φ̃(g,h) = ψ̃(g) + s(g)ψ̃(h) − ψ̃(gh)`.  The forward direction is the book's derivation of (8.3.43)
from triviality; the converse is the book's "any projective representation whose phase function
satisfies (8.3.43) is trivial" (p. 278).  Nonemptiness of the index type is needed because on an
empty type all matrices coincide and the phase is not recoverable. -/
theorem isTrivialProjectiveRep_iff_isPhaseCoboundary [Nonempty D] {u : G → Matrix D D ℂ}
    {s : G →* ℤˣ} {φ : G → G → Circle} (hu : IsProjectiveRep u s φ) :
    IsTrivialProjectiveRep u s ↔ IsPhaseCoboundary s φ := by
  have hφ11 : φ 1 1 = 1 := phase_self_one hu
  obtain ⟨huUnit, huOne, huMul⟩ := hu
  constructor
  · rintro ⟨v, ψ, ⟨hvUnit, -, hvMul⟩, huv⟩
    refine ⟨ψ, fun g h => ?_⟩
    have key := huMul g h
    rw [huv g, huv h, huv (g * h), signConjMatrix_smul, signConj_circle, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hvMul g h, Pi.one_apply, Pi.one_apply, Circle.coe_one,
      one_smul, smul_smul] at key
    have hsc := smul_left_cancel_of_unitary (hvUnit (g * h)) key
    have hcirc : ψ g * ψ h ^ (s g : ℤ) = φ g h * ψ (g * h) :=
      Circle.coe_injective (by rw [Circle.coe_mul, Circle.coe_mul]; exact hsc)
    rw [hcirc, mul_inv_cancel_right]
  · rintro ⟨ψ, hψ⟩
    have hψone : ψ 1 = 1 := by
      have h := hψ 1 1
      simp only [hφ11, map_one, Units.val_one, zpow_one, mul_one, mul_inv_cancel_right] at h
      exact h.symm
    refine ⟨fun g => (((ψ g)⁻¹ : Circle) : ℂ) • u g, ψ,
      ⟨fun g => circle_smul_mem_unitaryGroup _ (huUnit g), ?_, fun g h => ?_⟩, fun g => ?_⟩
    · change (((ψ 1)⁻¹ : Circle) : ℂ) • u 1 = (1 : Matrix D D ℂ)
      rw [hψone, inv_one, Circle.coe_one, one_smul, huOne]
    · have hscal : (ψ g)⁻¹ * (ψ h)⁻¹ ^ (s g : ℤ) * φ g h = (ψ (g * h))⁻¹ := by
        rw [hψ g h, inv_zpow, ← mul_inv, inv_mul_cancel_left]
      change (((ψ g)⁻¹ : Circle) : ℂ) • u g *
          signConjMatrix (s g) ((((ψ h)⁻¹ : Circle) : ℂ) • u h) =
          ((1 : G → G → Circle) g h : ℂ) • ((((ψ (g * h))⁻¹ : Circle) : ℂ) • u (g * h))
      rw [signConjMatrix_smul, signConj_circle, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        huMul g h, smul_smul, ← Circle.coe_mul, ← Circle.coe_mul, hscal, Pi.one_apply,
        Pi.one_apply, Circle.coe_one, one_smul]
    · rw [smul_smul, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_smul]

end LatticeSystem.Math
