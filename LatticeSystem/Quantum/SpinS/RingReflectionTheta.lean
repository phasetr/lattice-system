/-
The reflection map `θ` on the even-ring operator algebra (foundation for Tasaki §4.1 Theorem 4.2).

The bond reflection `ringReflect` of `Fin (2n)` (`RingBondReflection.lean`) induces a configuration
reflection `ρ σ = σ ∘ ringReflect` and, via the reflection-plus-complex-conjugation prescription, an
**antilinear `*`-automorphism** `θ` of `ManyBodyOpS (Fin (2n)) N`:
`θ(A) σ τ = conj (A (ρ σ) (ρ τ))`.
This is the map underlying the reflection-positivity condition `0 ≤ Re ⟨θ(A) · A⟩` of the
Dyson–Lieb–Simon / Shastry argument.  Here we record `θ` and its algebraic properties
(conjugate-linearity, multiplicativity, unitality, involutivity, compatibility with the conjugate
transpose).
-/
import LatticeSystem.Quantum.SpinS.RingBondReflection

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The **configuration reflection** induced by the ring bond reflection: `(ρ σ) i = σ (r i)`. -/
def ringConfigReflect (n N : ℕ) (σ : Fin (2 * n) → Fin (N + 1)) : Fin (2 * n) → Fin (N + 1) :=
  fun i => σ (ringReflect n i)

/-- The configuration reflection is an involution (lifted from `ringReflect_involutive`). -/
theorem ringConfigReflect_involutive (n N : ℕ) :
    Function.Involutive (ringConfigReflect n N) := by
  intro σ
  funext i
  simp only [ringConfigReflect, ringReflect_involutive n i]

/-- The configuration reflection as an equivalence (used to reindex sums over configurations). -/
def ringConfigReflectEquiv (n N : ℕ) : (Fin (2 * n) → Fin (N + 1)) ≃ (Fin (2 * n) → Fin (N + 1)) :=
  Function.Involutive.toPerm _ (ringConfigReflect_involutive n N)

@[simp] theorem ringConfigReflectEquiv_apply (n N : ℕ) (σ : Fin (2 * n) → Fin (N + 1)) :
    ringConfigReflectEquiv n N σ = ringConfigReflect n N σ := rfl

/-- The **reflection map** `θ` on `ManyBodyOpS (Fin (2n)) N`: reflect the row/column configurations
and complex-conjugate the entry, `θ(A) σ τ = conj (A (ρ σ) (ρ τ))`. -/
def ringReflectionThetaS (n N : ℕ) (A : ManyBodyOpS (Fin (2 * n)) N) :
    ManyBodyOpS (Fin (2 * n)) N :=
  Matrix.of fun σ τ =>
    starRingEnd ℂ (A (ringConfigReflect n N σ) (ringConfigReflect n N τ))

@[simp] theorem ringReflectionThetaS_apply (A : ManyBodyOpS (Fin (2 * n)) N)
    (σ τ : Fin (2 * n) → Fin (N + 1)) :
    ringReflectionThetaS n N A σ τ
      = starRingEnd ℂ (A (ringConfigReflect n N σ) (ringConfigReflect n N τ)) := rfl

/-- `θ` is additive. -/
theorem ringReflectionThetaS_add (A B : ManyBodyOpS (Fin (2 * n)) N) :
    ringReflectionThetaS n N (A + B) = ringReflectionThetaS n N A + ringReflectionThetaS n N B := by
  ext σ τ
  simp [ringReflectionThetaS, map_add]

/-- `θ` is **conjugate-linear**: `θ(c • A) = conj c • θ(A)`. -/
theorem ringReflectionThetaS_smul (c : ℂ) (A : ManyBodyOpS (Fin (2 * n)) N) :
    ringReflectionThetaS n N (c • A) = (starRingEnd ℂ c) • ringReflectionThetaS n N A := by
  ext σ τ
  simp [ringReflectionThetaS, map_mul]

/-- `θ` preserves the identity. -/
theorem ringReflectionThetaS_one :
    ringReflectionThetaS n N (1 : ManyBodyOpS (Fin (2 * n)) N) = 1 := by
  ext σ τ
  simp only [ringReflectionThetaS_apply, Matrix.one_apply,
    (ringConfigReflect_involutive n N).injective.eq_iff]
  split <;> simp

/-- `θ` is **multiplicative** (a homomorphism): `θ(A * B) = θ(A) * θ(B)`.  The reflection bijection
reindexes the matrix-product sum, and complex conjugation distributes over the sum and product. -/
theorem ringReflectionThetaS_mul (A B : ManyBodyOpS (Fin (2 * n)) N) :
    ringReflectionThetaS n N (A * B) = ringReflectionThetaS n N A * ringReflectionThetaS n N B := by
  ext σ τ
  simp only [ringReflectionThetaS_apply, Matrix.mul_apply, map_sum]
  rw [← Equiv.sum_comp (ringConfigReflectEquiv n N)
      (fun μ => starRingEnd ℂ (A (ringConfigReflect n N σ) μ * B μ (ringConfigReflect n N τ)))]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [ringConfigReflectEquiv_apply, map_mul]

/-- `θ` is an involution: `θ (θ A) = A`. -/
theorem ringReflectionThetaS_involutive (n N : ℕ) :
    Function.Involutive (ringReflectionThetaS n N) := by
  intro A
  ext σ τ
  simp only [ringReflectionThetaS_apply, Complex.conj_conj,
    (ringConfigReflect_involutive n N) σ, (ringConfigReflect_involutive n N) τ]

/-- `θ` commutes with the conjugate transpose: `θ(Aᴴ) = (θ A)ᴴ` — so `θ` is a `*`-automorphism. -/
theorem ringReflectionThetaS_conjTranspose (A : ManyBodyOpS (Fin (2 * n)) N) :
    ringReflectionThetaS n N (Matrix.conjTranspose A)
      = Matrix.conjTranspose (ringReflectionThetaS n N A) := by
  ext σ τ
  simp only [ringReflectionThetaS_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.conj_conj]

end LatticeSystem.Quantum
