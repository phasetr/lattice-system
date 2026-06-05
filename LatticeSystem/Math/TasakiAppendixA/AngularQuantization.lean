import LatticeSystem.Math.TasakiAppendixA.AngularLadder
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Tasaki Appendix A.3: quantization of angular momentum (Lemma A.15 integrality, Theorem A.13)

Building on the ladder (Lemma A.14, `AngularLadder.lean`) and the spin bound (Lemma A.15 part 1,
`angMom_abs_le_J`, `−J ≤ M ≤ J`), this file proves the **integrality** half of Lemma A.15 and the
headline **Theorem A.13** (`J = n/2` for a non-negative integer `n`).

The argument is the textbook *ladder termination*: starting from a nonzero `H_{J,M}` state `Φ`,
repeatedly applying `Ĵ⁺` produces nonzero states in `H_{J,M+1}, H_{J,M+2}, …` as long as the
magnetic number stays strictly below `J`.  By the spin bound the magnetic number can never exceed
`J`, so the only way the iteration is consistent is that some integer step lands exactly on `J`,
i.e. `J − M ∈ ℤ≥0` (`angMom_sub_mem_nat`).  Applying the same lemma to the gauge-reflected
operators `(Ĵ⁽¹⁾, −Ĵ⁽²⁾, −Ĵ⁽³⁾)` (which satisfy the same `su(2)` relations and flip `M ↦ −M`) gives
`J + M ∈ ℤ≥0`.  Adding, `2J = (J−M) + (J+M) ∈ ℤ≥0`, hence `J = n/2` (`angMom_J_eq_half_nat`,
Theorem A.13).

All proved (axiom-free).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.3, Theorem A.13 / Lemma A.15, pp. 471–472.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d] (J1 J2 J3 : Matrix d d ℂ)

/-- The state obtained by applying the raising operator `Ĵ⁺ = Ĵ⁽¹⁾ + i Ĵ⁽²⁾` exactly `k` times to
`Φ`.  Used for the ladder-termination argument behind the angular-momentum quantization. -/
noncomputable def raiseIter (J1 J2 : Matrix d d ℂ) : ℕ → (d → ℂ) → (d → ℂ)
  | 0, Φ => Φ
  | (k + 1), Φ => (J1 + Complex.I • J2).mulVec (raiseIter J1 J2 k Φ)

omit [DecidableEq d] in
/-- `Ĵ⁺` applied `k` times keeps `Φ` inside `H_{J,M+k}`: the iterate is a joint eigenvector of `Ĵ²`
(eigenvalue `J(J+1)`, unchanged) and of `Ĵ⁽³⁾` (eigenvalue `M + k`).  Proved by induction on `k`
from `angRaise_mem_eigenspace`. -/
theorem raiseIter_eigenspace (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1) (h31 : J3 * J1 - J1 * J3 = Complex.I • J2)
    {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    ∀ k : ℕ,
      (J1 * J1 + J2 * J2 + J3 * J3).mulVec (raiseIter J1 J2 k Φ)
          = ((Jr * (Jr + 1) : ℝ) : ℂ) • raiseIter J1 J2 k Φ ∧
        J3.mulVec (raiseIter J1 J2 k Φ) = ((M + k : ℝ) : ℂ) • raiseIter J1 J2 k Φ := by
  intro k
  induction k with
  | zero => refine ⟨hsq, ?_⟩; simpa using h3
  | succ k ih =>
    obtain ⟨ihsq, ih3⟩ := ih
    have hmem := angRaise_mem_eigenspace J1 J2 J3 h12 h23 h31 (Jr := Jr) (M := M + k) ihsq ih3
    rw [show raiseIter J1 J2 (k + 1) Φ
          = (J1 + Complex.I • J2).mulVec (raiseIter J1 J2 k Φ) from rfl]
    refine ⟨hmem.1, ?_⟩
    rw [hmem.2]
    congr 1
    push_cast
    ring

omit [DecidableEq d] in
/-- `Ĵ⁺` applied `k` times stays nonzero as long as every intermediate magnetic number `M + i`
(`i < k`) is strictly below `J`.  Proved by induction on `k` from the ladder non-vanishing
(`angRaise_mulVec_ne_zero`), using `raiseIter_eigenspace` for the eigenvalues at each step. -/
theorem raiseIter_ne_zero (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1) (h31 : J3 * J1 - J1 * J3 = Complex.I • J2)
    {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) (hΦ : Φ ≠ 0) (hlb : -Jr ≤ M) :
    ∀ k : ℕ, (∀ i : ℕ, i < k → M + (i : ℝ) < Jr) → raiseIter J1 J2 k Φ ≠ 0 := by
  intro k
  induction k with
  | zero => intro _; exact hΦ
  | succ k ih =>
    intro hstep
    have ihne := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨psq, p3⟩ := raiseIter_eigenspace J1 J2 J3 h12 h23 h31 hsq h3 k
    have hub : M + (k : ℝ) < Jr := hstep k (Nat.lt_succ_self k)
    have hlb' : -Jr ≤ M + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact angRaise_mulVec_ne_zero J1 J2 J3 h12 psq p3 ihne hlb' hub

omit [DecidableEq d] in
/-- **Tasaki Lemma A.15 (integrality, `J − M ∈ ℤ≥0`).**  On a *nonzero* `H_{J,M}` state
(self-adjoint `Ĵ⁽ᵅ⁾`, `J ≥ 0`), the difference `J − M` is a non-negative integer.  Ladder
termination: were `J − M` non-integral, applying `Ĵ⁺` exactly `⌊J−M⌋ + 1` times would keep every
intermediate magnetic number below `J` (hence the iterate nonzero), yet its magnetic number
`M + ⌊J−M⌋ + 1 > J` would violate the spin bound `angMom_abs_le_J`. -/
theorem angMom_sub_mem_nat (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) {Φ : d → ℂ} {Jr M : ℝ} (hΦ : Φ ≠ 0) (hJ : 0 ≤ Jr)
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    ∃ n : ℕ, Jr - M = (n : ℝ) := by
  obtain ⟨hMlb, hMub⟩ := angMom_abs_le_J J1 J2 J3 h1 h2 h12 hΦ hJ hsq h3
  refine ⟨⌊Jr - M⌋₊, ?_⟩
  by_contra hne
  have hle : ((⌊Jr - M⌋₊ : ℕ) : ℝ) ≤ Jr - M := Nat.floor_le (by linarith)
  have hlt : ((⌊Jr - M⌋₊ : ℕ) : ℝ) < Jr - M := lt_of_le_of_ne hle (fun h => hne h.symm)
  have hstep : ∀ i : ℕ, i < ⌊Jr - M⌋₊ + 1 → M + (i : ℝ) < Jr := by
    intro i hi
    have hile : (i : ℝ) ≤ (⌊Jr - M⌋₊ : ℕ) := by exact_mod_cast Nat.lt_succ_iff.mp hi
    nlinarith [hile, hlt]
  have hne0 :=
    raiseIter_ne_zero J1 J2 J3 h12 h23 h31 hsq h3 hΦ hMlb (⌊Jr - M⌋₊ + 1) hstep
  obtain ⟨psq, p3⟩ := raiseIter_eigenspace J1 J2 J3 h12 h23 h31 hsq h3 (⌊Jr - M⌋₊ + 1)
  obtain ⟨_, hub'⟩ := angMom_abs_le_J J1 J2 J3 h1 h2 h12 hne0 hJ psq p3
  have hfloor := Nat.lt_floor_add_one (Jr - M)
  push_cast at hub' hfloor
  linarith

omit [DecidableEq d] in
/-- **Tasaki Theorem A.13 (quantization of angular momentum, `J = n/2`).**  On a *nonzero*
`H_{J,M}` state (self-adjoint `Ĵ⁽ᵅ⁾` with the `su(2)` relations, `J ≥ 0`), the total-spin label `J`
is a non-negative half-integer: `J = n/2` for some `n : ℕ`.  From Lemma A.15, both `J − M` and
`J + M` are non-negative integers — the latter via `angMom_sub_mem_nat` for the gauge-reflected
operators `(Ĵ⁽¹⁾, −Ĵ⁽²⁾, −Ĵ⁽³⁾)`, which satisfy the same relations with `M ↦ −M`.  Adding,
`2J = (J − M) + (J + M) ∈ ℤ≥0`. -/
theorem angMom_J_eq_half_nat (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) {Φ : d → ℂ} {Jr M : ℝ} (hΦ : Φ ≠ 0) (hJ : 0 ≤ Jr)
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    ∃ n : ℕ, Jr = (n : ℝ) / 2 := by
  -- `J − M ∈ ℤ≥0` (raising direction).
  obtain ⟨nsub, hsub⟩ := angMom_sub_mem_nat J1 J2 J3 h1 h2 h12 h23 h31 hΦ hJ hsq h3
  -- Gauge-reflected operators `(Ĵ⁽¹⁾, −Ĵ⁽²⁾, −Ĵ⁽³⁾)` satisfy the same `su(2)` relations.
  have h12' : J1 * (-J2) - (-J2) * J1 = Complex.I • (-J3) := by
    rw [show J1 * (-J2) - (-J2) * J1 = -(J1 * J2 - J2 * J1) by noncomm_ring, h12, smul_neg]
  have h23' : (-J2) * (-J3) - (-J3) * (-J2) = Complex.I • J1 := by
    rw [show (-J2) * (-J3) - (-J3) * (-J2) = J2 * J3 - J3 * J2 by noncomm_ring, h23]
  have h31' : (-J3) * J1 - J1 * (-J3) = Complex.I • (-J2) := by
    rw [show (-J3) * J1 - J1 * (-J3) = -(J3 * J1 - J1 * J3) by noncomm_ring, h31, smul_neg]
  have hsq' : (J1 * J1 + (-J2) * (-J2) + (-J3) * (-J3)).mulVec Φ
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ := by
    rw [show J1 * J1 + (-J2) * (-J2) + (-J3) * (-J3) = J1 * J1 + J2 * J2 + J3 * J3 by noncomm_ring]
    exact hsq
  have h3' : (-J3).mulVec Φ = ((-M : ℝ) : ℂ) • Φ := by
    rw [Matrix.neg_mulVec, h3]; push_cast; module
  -- `J + M ∈ ℤ≥0` (lowering direction = reflected raising).
  obtain ⟨nadd, hadd⟩ :=
    angMom_sub_mem_nat J1 (-J2) (-J3) h1 h2.neg h12' h23' h31' hΦ hJ hsq' h3'
  refine ⟨nsub + nadd, ?_⟩
  push_cast
  linarith

end LatticeSystem.Math
