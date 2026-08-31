/-
General range-`r` locality bound for the order-operator double commutator.

Tasaki Problem 3.4.a generalises the bond-local double-commutator estimate eq. (3.4.11) from a
Hamiltonian and order operator built from bonds to ones built from *every* site, each local term
acting only on sites within distance `r` of its own site.  That premise is a statement about
operator *support*, so it is taken here as one: `ĥ_x` and `ô_x` are `SupportedOnS` on the radius-`r`
ball of `x`, and the commutation relations the estimate needs are derived from disjointness of
supports (`commute_of_supportedOnS_disjoint`) rather than assumed alongside the premise.

Deriving them fixes the two windows.  A nonzero `[ĥ_x, ô_y]` forces the two `r`-balls to meet, so
`y` ranges over the `2r`-ball of `x`; the commutator is supported in `B_r(x) ∪ B_r(y) ⊆ B_{3r}(x)`,
so a non-commuting `ô_z` has `z` in the `4r`-ball of `x`.  On the periodic lattice `Λ_L = Fin d →
Fin L` with the torus sup-distance those windows contain at most `(4r+1)^d` and `(8r+1)^d` sites,
giving

`⟨Φ|[Ô_L,[Ĥ,Ô_L]]|Φ⟩ ≤ 4 (4r+1)^d (8r+1)^d h₀ o₀² L^d`.

Tasaki's printed solution instead counts over `|x−y| ≤ r` and `|x−z| ≤ 2r`, giving the smaller
constant `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.  Those index ranges do not follow from the range-`r`
premise, and the printed constant is neither proved nor refuted here: what is proved is the bound
above, which is what the premise yields.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §2.1 p. 52 (periodic lattice), §3.4, Problem 3.4.a, statement pp. 67-68, printed solution
p. 501; operator-norm properties (A.2.5)/(A.2.6), p. 463.
-/
import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound
import LatticeSystem.Quantum.SpinS.OperatorSupport
import LatticeSystem.Quantum.SpinS.TorusSupDistance

namespace LatticeSystem.Quantum

open Matrix
open LatticeSystem.Math

section Abstract

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Range-`r` double-commutator norm bound** over an abstract `ℕ`-valued site distance.  For
`Ĥ = Σ_x ĥ_x` and `Ô = Σ_x ô_x` whose local terms are supported on the radius-`r` ball of their own
site,
`‖[Ô,[Ĥ,Ô]]‖ ≤ 4 m₁ m₂ h₀ o₀² |Λ|`,
where `m₁` bounds the number of sites in a `2r`-ball and `m₂` the number in a `4r`-ball.

The two windows are forced by the support premise, not chosen: `ĥ_b` commutes with every `ô_z`
whose site lies outside the `2r`-ball of `b`, because then the two `r`-balls are disjoint; and
`ô_x` commutes with `[ĥ_b, ô_z]` for `z` in the `2r`-ball whenever `x` lies outside the `4r`-ball,
because `dist x z > 2r` follows from `dist x b > 4r` and `dist z b ≤ 2r` by the triangle
inequality.  Swapping the roles of the two windows leaves this last step underivable.

Only symmetry and the triangle inequality are required of `dist`, and only `0 ≤ o₀` of the norm
bounds: `0 ≤ h₀` is not needed, nor is self-adjointness of any operator. -/
theorem manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal
    (dist : Λ → Λ → ℕ)
    (hsymm : ∀ a b, dist a b = dist b a)
    (htri : ∀ a b c, dist a c ≤ dist a b + dist b c)
    (h o : Λ → ManyBodyOpS Λ N) (r : ℕ) (h₀ o₀ : ℝ) (m₁ m₂ : ℕ)
    (hsh : ∀ x, SupportedOnS (siteBall dist r x) (h x))
    (hso : ∀ x, SupportedOnS (siteBall dist r x) (o x))
    (hnh : ∀ x, manyBodyOperatorNormS (h x) ≤ h₀)
    (hno : ∀ x, manyBodyOperatorNormS (o x) ≤ o₀)
    (ho₀ : 0 ≤ o₀)
    (hm₁ : ∀ b : Λ, (siteBall dist (2 * r) b).card ≤ m₁)
    (hm₂ : ∀ b : Λ, (siteBall dist (4 * r) b).card ≤ m₂) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b : Λ, h b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b : Λ, h b))
          - ((∑ b : Λ, h b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b : Λ, h b))
            * (∑ x : Λ, o x))
      ≤ 4 * (m₁ : ℝ) * (m₂ : ℝ) * h₀ * o₀ ^ 2 * (Fintype.card Λ : ℝ) := by
  have hfar : ∀ a b : Λ, 2 * r < dist a b → Commute (h a) (o b) := fun a b hab =>
    commute_of_supportedOnS_disjoint (hsh a) (hso b) (disjoint_siteBall_of_lt hsymm htri hab)
  have hfaroo : ∀ a b : Λ, 2 * r < dist a b → Commute (o a) (o b) := fun a b hab =>
    commute_of_supportedOnS_disjoint (hso a) (hso b) (disjoint_siteBall_of_lt hsymm htri hab)
  have hW : ∀ b ∈ (Finset.univ : Finset Λ), ∀ z ∉ siteBall dist (2 * r) b,
      Commute (h b) (o z) := by
    intro b _ z hz
    have hzb : 2 * r < dist z b := Nat.lt_of_not_le fun hle => hz (mem_siteBall.mpr hle)
    exact hfar b z (by rw [hsymm b z]; exact hzb)
  have hWW : ∀ b ∈ (Finset.univ : Finset Λ), ∀ x ∉ siteBall dist (4 * r) b,
      ∀ z ∈ siteBall dist (2 * r) b, Commute (o x) (h b * o z - o z * h b) := by
    intro b _ x hx z hz
    have hxb : 4 * r < dist x b := Nat.lt_of_not_le fun hle => hx (mem_siteBall.mpr hle)
    have hzb : dist z b ≤ 2 * r := mem_siteBall.mp hz
    have hxz : 2 * r < dist x z := by
      have hxzb := htri x z b
      omega
    have c1 : Commute (o x) (h b) := (hfar b x (by rw [hsymm b x]; omega)).symm
    have c2 : Commute (o x) (o z) := hfaroo x z hxz
    exact (c1.mul_right c2).sub_right (c2.mul_right c1)
  have hker := manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows
    (Finset.univ : Finset Λ) h o (siteBall dist (2 * r)) (siteBall dist (4 * r))
    h₀ o₀ m₁ m₂ hW hWW (fun b _ => hnh b) hno ho₀
    (fun b _ => hm₁ b) (fun b _ => hm₂ b)
  rwa [Finset.card_univ] at hker

end Abstract

/-- **Tasaki Problem 3.4.a, pp. 67-68, with the constant the range-`r` premise yields (not
eq. (3.4.13) as printed, solution p. 501)** — on the periodic
lattice `Λ_L = Fin d → Fin L`, for a Hamiltonian `Ĥ = Σ_x ĥ_x` and an order operator
`Ô_L = Σ_x ô_x` whose local terms are supported on the radius-`r` torus sup-distance ball of their
own site, and a normalized state `Φ`,
`⟨Φ|[Ô_L,[Ĥ,Ô_L]]|Φ⟩ ≤ 4 (4r+1)^d (8r+1)^d h₀ o₀² L^d`.

Locality is the book's premise itself — each local term *acts only on* the sites of its `r`-ball —
so the commutation relations the estimate uses are derived, not assumed.  Doing so fixes the
windows at `2r` and `4r` and hence the constant; Tasaki's printed solution counts over `r` and `2r`
instead, and the resulting smaller constant `4 (2r+1)^d (4r+1)^d h₀ o₀² L^d` is neither proved nor
refuted here.  The distance is the torus sup-distance, matching the periodic identification of
`Λ_L` and reading the unqualified `|x − y| ≤ r` in the sup norm, which is the weaker hypothesis.

No self-adjointness is assumed, so the expectation is taken on its real part; conditions (3.4.3)
and (3.4.4) are unused; `0 ≤ h₀`, `1 ≤ d` and `1 ≤ L` are not needed, and `|Λ_L| = L^d` is an
identity here rather than a hypothesis. -/
theorem tasaki_problem_3_4_a_doubleCommutator_expectation_le (d L N r : ℕ)
    (h o : (Fin d → Fin L) → ManyBodyOpS (Fin d → Fin L) N) (h₀ o₀ : ℝ)
    {Φ : ((Fin d → Fin L) → Fin (N + 1)) → ℂ}
    (hsh : ∀ x, SupportedOnS (siteBall (torusSupDist d L) r x) (h x))
    (hso : ∀ x, SupportedOnS (siteBall (torusSupDist d L) r x) (o x))
    (hnh : ∀ x, manyBodyOperatorNormS (h x) ≤ h₀)
    (hno : ∀ x, manyBodyOperatorNormS (o x) ≤ o₀)
    (ho₀ : 0 ≤ o₀)
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x, o x) * ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b))
          - ((∑ b, h b) * (∑ x, o x) - (∑ x, o x) * (∑ b, h b)) * (∑ x, o x)) Φ
      ≤ 4 * (4 * (r : ℝ) + 1) ^ d * (8 * (r : ℝ) + 1) ^ d * h₀ * o₀ ^ 2 * (L : ℝ) ^ d := by
  have hm₁ : ∀ b : Fin d → Fin L,
      (siteBall (torusSupDist d L) (2 * r) b).card ≤ (4 * r + 1) ^ d := by
    intro b
    have hb := card_siteBall_torusSupDist_le d L (2 * r) b
    have he : 2 * (2 * r) + 1 = 4 * r + 1 := by ring
    rwa [he] at hb
  have hm₂ : ∀ b : Fin d → Fin L,
      (siteBall (torusSupDist d L) (4 * r) b).card ≤ (8 * r + 1) ^ d := by
    intro b
    have hb := card_siteBall_torusSupDist_le d L (4 * r) b
    have he : 2 * (4 * r) + 1 = 8 * r + 1 := by ring
    rwa [he] at hb
  have hker := manyBodyOperatorNormS_doubleCommutator_le_of_rangeLocal
    (torusSupDist d L) (torusSupDist_comm d L) (torusSupDist_triangle d L) h o r h₀ o₀
    ((4 * r + 1) ^ d) ((8 * r + 1) ^ d) hsh hso hnh hno ho₀ hm₁ hm₂
  refine le_trans (le_trans (le_abs_self _) (expectation_abs_le_manyBodyOperatorNormS _ hΦ)) ?_
  refine le_trans hker (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  ring

end LatticeSystem.Quantum
