/-
General range-`r` locality bound for the order-operator double commutator.

Tasaki Problem 3.4.a, eq. (3.4.13), generalises the bond-local double-commutator estimate
eq. (3.4.11) from a Hamiltonian and order operator built from bonds to ones built from *every*
site, each local term acting only within coordinate sup-norm distance `r` of its own site:

`⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ ≤ 4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.

The estimate is the two-window kernel of `Quantum/SpinS/LocalDoubleCommutatorBound.lean` at the
inner bound `m₁ = (2r+1)^d` and the outer bound `m₂ = (4r+1)^d`, both supplied by the single
counting lemma of `Math/Combinatorics/CoordinateBall.lean`, followed by the operator-norm bound on
the expectation in a unit vector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501; operator-norm properties
(A.2.5)/(A.2.6), p. 463.
-/
import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound
import LatticeSystem.Math.Combinatorics.CoordinateBall

namespace LatticeSystem.Quantum

open Matrix
open LatticeSystem.Math

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Tasaki Problem 3.4.a, eq. (3.4.13), pp. 67-68 (printed solution p. 501)** — for a Hamiltonian
`Ĥ = Σ_{x∈Λ} ĥ_x` and an order operator `Ô_L = Σ_{x∈Λ} ô_x` whose local terms are range-`r`, and a
normalized state `Φ`,
`⟨Φ|[Ô_L,[Ĥ,Ô_L]]|Φ⟩ ≤ 4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.

Sites carry integer coordinates through the injective `pos`, and Tasaki's unqualified `|x - y| ≤ r`
is read as the coordinate sup-norm ball `coordSupBall`, the weaker locality hypothesis and the
reading under which the printed counts are exact.  Locality itself is expressed, as in
eqs. (3.4.9)-(3.4.11), by commutation hypotheses rather than a support predicate: `hHloc` says
`ĥ_x` commutes with `ô_z` for `z` outside the `r`-ball around `x`, and `hOloc` says `ô_z` commutes
with `[ĥ_x, ô_y]` for `z` outside the `2r`-ball and `y` inside the `r`-ball.  These are the two
support conditions the printed solution states before counting; the counting and the norm
bookkeeping are what is proved here.

The `r`-ball is the *inner* window and the `2r`-ball the *outer* one, so the counts enter as
`m₁ = (2r+1)^d` and `m₂ = (4r+1)^d` respectively.  No self-adjointness is assumed, so the
expectation is taken on its real part; conditions (3.4.3) and (3.4.4) are unused; neither `1 ≤ d`
nor `1 ≤ L` is needed, and `|Λ_L| = L^d` enters only as the inequality `hΛ`. -/
theorem tasaki_problem_3_4_a_doubleCommutator_expectation_le {d : ℕ}
    (pos : Λ → (Fin d → ℤ)) (hpos : Function.Injective pos)
    (h o : Λ → ManyBodyOpS Λ N) (r L : ℕ) (h₀ o₀ : ℝ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hHloc : ∀ x z : Λ, z ∉ coordSupBall pos r x → Commute (h x) (o z))
    (hOloc : ∀ x z : Λ, z ∉ coordSupBall pos (2 * r) x →
      ∀ y ∈ coordSupBall pos r x, Commute (o z) (h x * o y - o y * h x))
    (hnh : ∀ x : Λ, manyBodyOperatorNormS (h x) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hΛ : (Fintype.card Λ : ℝ) ≤ (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x : Λ, o x) * ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
          - ((∑ x : Λ, h x) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ x : Λ, h x))
            * (∑ x : Λ, o x)) Φ
      ≤ 4 * (2 * (r : ℝ) + 1) ^ d * (4 * (r : ℝ) + 1) ^ d * h₀ * o₀ ^ 2 * (L : ℝ) ^ d := by
  have hcard₁ : ∀ b ∈ (Finset.univ : Finset Λ), (coordSupBall pos r b).card ≤ (2 * r + 1) ^ d :=
    fun b _ => card_coordSupBall_le pos hpos r b
  have hcard₂ : ∀ b ∈ (Finset.univ : Finset Λ),
      (coordSupBall pos (2 * r) b).card ≤ (4 * r + 1) ^ d := by
    intro b _
    have he : 2 * (2 * r) + 1 = 4 * r + 1 := by ring
    have hb := card_coordSupBall_le pos hpos (2 * r) b
    rwa [he] at hb
  have hker := manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows
    (Finset.univ : Finset Λ) h o (coordSupBall pos r) (coordSupBall pos (2 * r))
    h₀ o₀ ((2 * r + 1) ^ d) ((4 * r + 1) ^ d)
    (fun b _ z hz => hHloc b z hz) (fun b _ x hx z hz => hOloc b x hx z hz)
    (fun b _ => hnh b) hno ho₀ hcard₁ hcard₂
  refine le_trans (le_trans (le_abs_self _) (expectation_abs_le_manyBodyOperatorNormS _ hΦ)) ?_
  refine le_trans hker ?_
  rw [Finset.card_univ]
  have hK : (0 : ℝ)
      ≤ 4 * (((2 * r + 1) ^ d : ℕ) : ℝ) * (((4 * r + 1) ^ d : ℕ) : ℝ) * h₀ * o₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) hh₀) (sq_nonneg o₀)
  calc 4 * (((2 * r + 1) ^ d : ℕ) : ℝ) * (((4 * r + 1) ^ d : ℕ) : ℝ) * h₀ * o₀ ^ 2
        * (Fintype.card Λ : ℝ)
      ≤ 4 * (((2 * r + 1) ^ d : ℕ) : ℝ) * (((4 * r + 1) ^ d : ℕ) : ℝ) * h₀ * o₀ ^ 2
        * ((L : ℝ) ^ d) := mul_le_mul_of_nonneg_left hΛ hK
    _ = 4 * (2 * (r : ℝ) + 1) ^ d * (4 * (r : ℝ) + 1) ^ d * h₀ * o₀ ^ 2 * (L : ℝ) ^ d := by
        push_cast
        ring

end LatticeSystem.Quantum
