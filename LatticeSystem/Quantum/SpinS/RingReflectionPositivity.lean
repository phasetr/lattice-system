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

/-- An operator on the ring `Fin (2n)` is **supported on the left half** `{0,…,n−1}` — i.e. it lies
in the subalgebra `B(H_left) ⊗ I_right` — when (1) its matrix entries vanish unless the row/column
configurations agree on every right-half site (it preserves the right half), and (2) the entry
depends only on the **left**-half restrictions of the configurations, not on the common right-half
value (it acts as the identity on the right half).  The two conditions together characterize the
left-half subalgebra, the domain of the reflection-positivity condition. -/
def SupportedOnLeftS (n N : ℕ) (A : ManyBodyOpS (Fin (2 * n)) N) : Prop :=
  (∀ σ τ : Fin (2 * n) → Fin (N + 1), A σ τ ≠ 0 → ∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ i = τ i)
    ∧ (∀ σ τ σ' τ' : Fin (2 * n) → Fin (N + 1),
        (∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ i = τ i) →
        (∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ' i = τ' i) →
        (∀ i : Fin (2 * n), (i : ℕ) < n → σ i = σ' i) →
        (∀ i : Fin (2 * n), (i : ℕ) < n → τ i = τ' i) → A σ τ = A σ' τ')

/-- The zero operator is left-supported. -/
theorem SupportedOnLeftS.zero : SupportedOnLeftS n N 0 :=
  ⟨fun σ τ h _ _ => by simp at h, fun _ _ _ _ _ _ _ _ => rfl⟩

/-- The identity is left-supported (it is `I_left ⊗ I_right`). -/
theorem SupportedOnLeftS.one : SupportedOnLeftS n N (1 : ManyBodyOpS (Fin (2 * n)) N) := by
  refine ⟨fun σ τ h i _ => ?_, fun σ τ σ' τ' hστ hσ'τ' hσσ' hττ' => ?_⟩
  · by_contra hne
    rw [Matrix.one_apply, if_neg (fun he => hne (by rw [he]))] at h
    exact h rfl
  · simp only [Matrix.one_apply]
    by_cases heq : σ = τ
    · rw [if_pos heq, if_pos (funext fun i => ?_)]
      rcases lt_or_ge (i : ℕ) n with hi | hi
      · rw [← hσσ' i hi, ← hττ' i hi, congrFun heq i]
      · rw [← hσ'τ' i hi]
    · rw [if_neg heq, if_neg (fun he => heq (funext fun i => ?_))]
      rcases lt_or_ge (i : ℕ) n with hi | hi
      · rw [hσσ' i hi, hττ' i hi, congrFun he i]
      · rw [hστ i hi]

/-- A sum of left-supported operators is left-supported. -/
theorem SupportedOnLeftS.add {A B : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    SupportedOnLeftS n N (A + B) := by
  refine ⟨fun σ τ h i hi => ?_, fun σ τ σ' τ' h1 h2 h3 h4 => ?_⟩
  · by_contra hne
    have hA0 : A σ τ = 0 := by by_contra hA0; exact hne (hA.1 σ τ hA0 i hi)
    have hB0 : B σ τ = 0 := by by_contra hB0; exact hne (hB.1 σ τ hB0 i hi)
    rw [Matrix.add_apply, hA0, hB0, add_zero] at h; exact h rfl
  · rw [Matrix.add_apply, Matrix.add_apply, hA.2 σ τ σ' τ' h1 h2 h3 h4,
      hB.2 σ τ σ' τ' h1 h2 h3 h4]

/-- A scalar multiple of a left-supported operator is left-supported. -/
theorem SupportedOnLeftS.smul {A : ManyBodyOpS (Fin (2 * n)) N} (c : ℂ)
    (hA : SupportedOnLeftS n N A) : SupportedOnLeftS n N (c • A) := by
  refine ⟨fun σ τ h i hi => hA.1 σ τ (right_ne_zero_of_mul (by rwa [Matrix.smul_apply,
    smul_eq_mul] at h)) i hi, fun σ τ σ' τ' h1 h2 h3 h4 => ?_⟩
  rw [Matrix.smul_apply, Matrix.smul_apply, hA.2 σ τ σ' τ' h1 h2 h3 h4]

/-- A single-site operator at a **left** site (`x < n`) is left-supported. -/
theorem onSiteS_supportedOnLeft {x : Fin (2 * n)} (hx : (x : ℕ) < n)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : SupportedOnLeftS n N (onSiteS x A) := by
  refine ⟨fun σ τ h i hi => ?_, fun σ τ σ' τ' h1 h2 h3 h4 => ?_⟩
  · rw [onSiteS_apply] at h
    by_cases hcond : ∀ k, k ≠ x → σ k = τ k
    · exact hcond i (by rintro rfl; omega)
    · rw [if_neg hcond] at h; exact absurd rfl h
  · rw [onSiteS_apply, onSiteS_apply, h3 x hx, h4 x hx]
    congr 1
    apply propext
    constructor
    · intro hc k hk
      rcases lt_or_ge (k : ℕ) n with hkn | hkn
      · rw [← h3 k hkn, ← h4 k hkn]; exact hc k hk
      · rw [← h2 k hkn]
    · intro hc k hk
      rcases lt_or_ge (k : ℕ) n with hkn | hkn
      · rw [h3 k hkn, h4 k hkn]; exact hc k hk
      · rw [← h1 k hkn]

/-- **`θ` sends a left-supported operator to a right-supported one**: if `A` is left-supported then
`θ(A)` vanishes whenever the configurations differ on some **left**-half site (`i < n`).  This is
the key compatibility making `θ(A)·A` the cross term of a reflection-positive decomposition. -/
theorem SupportedOnLeftS.theta_right {A : ManyBodyOpS (Fin (2 * n)) N}
    (hA : SupportedOnLeftS n N A) :
    ∀ σ τ : Fin (2 * n) → Fin (N + 1), ringReflectionThetaS n N A σ τ ≠ 0 →
      ∀ i : Fin (2 * n), (i : ℕ) < n → σ i = τ i := by
  intro σ τ h i hi
  rw [ringReflectionThetaS_apply] at h
  have hne : A (ringConfigReflect n N σ) (ringConfigReflect n N τ) ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have := hA.1 _ _ hne (ringReflect n i) (by simp only [ringReflect_val]; omega)
  simpa only [ringConfigReflect, ringReflect_involutive n i] using this

/-- **Reflection-positive functional.**  A functional `φ` on the ring operator algebra is reflection
positive (with respect to the bond reflection `θ`) when `0 ≤ Re φ(θ(A)·A)` for every left-supported
`A`.  This is the positivity at the heart of the Dyson–Lieb–Simon / Shastry argument. -/
def ReflectionPositiveFunctionalS (n N : ℕ)
    (φ : ManyBodyOpS (Fin (2 * n)) N → ℂ) : Prop :=
  ∀ A : ManyBodyOpS (Fin (2 * n)) N, SupportedOnLeftS n N A →
    0 ≤ (φ (ringReflectionThetaS n N A * A)).re

end LatticeSystem.Quantum
