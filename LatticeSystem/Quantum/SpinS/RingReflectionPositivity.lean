/-
Reflection positivity: the left-half subalgebra and the RP functional predicate
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 3).

The bond reflection of `Fin (2n)` splits the ring into a left half `{0,…,n−1}` and a right half
`{n,…,2n−1}`.  An operator is *left-supported* when it acts trivially on the right half (its matrix
entries vanish unless the two configurations agree on every right-half site).  A functional `φ` is
*reflection positive* when `0 ≤ Re φ(θ(A)·A)` for every left-supported `A`, where `θ` is the
reflection map of `RingReflectionTheta.lean`.  This file records the left-support predicate, its
closure properties, the fact that `θ` sends left-supported operators to right-supported ones, and the
RP functional predicate.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionHamiltonian

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- An operator on the ring `Fin (2n)` is **supported on the left half** `{0,…,n−1}` when its matrix
entries vanish whenever the row/column configurations differ on some right-half site `i` (`n ≤ i`):
such an operator acts trivially on the right half. -/
def SupportedOnLeftS (n N : ℕ) (A : ManyBodyOpS (Fin (2 * n)) N) : Prop :=
  ∀ σ τ : Fin (2 * n) → Fin (N + 1), A σ τ ≠ 0 → ∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ i = τ i

/-- The zero operator is left-supported. -/
theorem SupportedOnLeftS.zero : SupportedOnLeftS n N 0 := by
  intro σ τ h; simp at h

/-- The identity is left-supported. -/
theorem SupportedOnLeftS.one : SupportedOnLeftS n N 1 := by
  intro σ τ h i _
  by_contra hne
  rw [Matrix.one_apply] at h
  rw [if_neg (fun he => hne (by rw [he]))] at h
  exact h rfl

/-- A sum of left-supported operators is left-supported. -/
theorem SupportedOnLeftS.add {A B : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    SupportedOnLeftS n N (A + B) := by
  intro σ τ h i hi
  by_contra hne
  have : A σ τ = 0 := by
    by_contra hA0; exact hne (hA σ τ hA0 i hi)
  have : B σ τ = 0 := by
    by_contra hB0; exact hne (hB σ τ hB0 i hi)
  simp_all [Matrix.add_apply]

/-- A scalar multiple of a left-supported operator is left-supported. -/
theorem SupportedOnLeftS.smul {A : ManyBodyOpS (Fin (2 * n)) N} (c : ℂ)
    (hA : SupportedOnLeftS n N A) : SupportedOnLeftS n N (c • A) := by
  intro σ τ h i hi
  rw [Matrix.smul_apply, smul_eq_mul] at h
  exact hA σ τ (right_ne_zero_of_mul h) i hi

/-- A product of left-supported operators is left-supported. -/
theorem SupportedOnLeftS.mul {A B : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    SupportedOnLeftS n N (A * B) := by
  intro σ τ h i hi
  rw [Matrix.mul_apply] at h
  obtain ⟨μ, _, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [hA σ μ (left_ne_zero_of_mul hμ) i hi, hB μ τ (right_ne_zero_of_mul hμ) i hi]

/-- A single-site operator at a **left** site (`x < n`) is left-supported. -/
theorem onSiteS_supportedOnLeft {x : Fin (2 * n)} (hx : (x : ℕ) < n)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : SupportedOnLeftS n N (onSiteS x A) := by
  intro σ τ h i hi
  rw [onSiteS_apply] at h
  by_cases hcond : ∀ k, k ≠ x → σ k = τ k
  · exact hcond i (by rintro rfl; omega)
  · rw [if_neg hcond] at h; exact absurd rfl h

/-- **`θ` sends a left-supported operator to a right-supported one**: if `A` is left-supported then
`θ(A)` vanishes whenever the configurations differ on some **left**-half site (`i < n`).  This is
key compatibility making `θ(A)·A` the cross term of a reflection-positive decomposition. -/
theorem SupportedOnLeftS.theta_right {A : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) :
    ∀ σ τ : Fin (2 * n) → Fin (N + 1), ringReflectionThetaS n N A σ τ ≠ 0 →
      ∀ i : Fin (2 * n), (i : ℕ) < n → σ i = τ i := by
  intro σ τ h i hi
  rw [ringReflectionThetaS_apply] at h
  have hne : A (ringConfigReflect n N σ) (ringConfigReflect n N τ) ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have := hA _ _ hne (ringReflect n i) (by simp only [ringReflect_val]; omega)
  simpa only [ringConfigReflect, ringReflect_involutive n i] using this

/-- **Reflection-positive functional.**  A functional `φ` on the ring operator algebra is reflection
positive (with respect to the bond reflection `θ`) when `0 ≤ Re φ(θ(A)·A)` for every left-supported
`A`.  This is the positivity at the heart of the Dyson–Lieb–Simon / Shastry argument. -/
def ReflectionPositiveFunctionalS (n N : ℕ)
    (φ : ManyBodyOpS (Fin (2 * n)) N → ℂ) : Prop :=
  ∀ A : ManyBodyOpS (Fin (2 * n)) N, SupportedOnLeftS n N A →
    0 ≤ (φ (ringReflectionThetaS n N A * A)).re

end LatticeSystem.Quantum
