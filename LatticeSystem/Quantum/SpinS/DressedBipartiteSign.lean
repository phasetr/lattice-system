import LatticeSystem.Quantum.SpinS.AxisSwapLadderEntry
import LatticeSystem.Quantum.SpinS.MarshallSign

/-!
# Marshall dressing flips real non-negative entries to non-positive on bipartite bonds

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For a bipartite bond `x ≠ y` with `x ∈ A`, `y ∉ A` (or vice versa) and configurations agreeing
off `{x, y}` with an **odd** total shift on the `A`-site, the Marshall sign product
`marshallSignS A σ · marshallSignS A σ'` equals `−1`.  Hence any operator with real, non-negative
config-basis entries acquires a **non-positive** real part after Marshall dressing.

Crucially this holds for BOTH the transverse hop (`Ŝ⁺_x Ŝ⁻_y`: raise at `x`, lower at `y`) and
the parity hop (`Ŝ⁺_x Ŝ⁺_y`: raise at both) — in either case any `±1` move on the `A`-site `x`
makes `(σ' x).val + (σ x).val = 2(σ x).val ± 1` odd.  This is the joint sign-consistency that
makes the whole Marshall-dressed axis-swapped Hamiltonian off-diagonal-non-positive (case (i)).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

/-- Marshall dressing turns a real non-negative entry into a non-positive one across a bipartite
bond with the `A`-site at `x` (`A x = true`, `A y = false`) and an odd shift at `x`. -/
theorem dressed_entry_re_nonpos_bipartite_x
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hxod : Odd ((σ' x).val + (σ x).val))
    {z : ℂ} (hznn : 0 ≤ z.re) :
    (marshallSignS A σ * marshallSignS A σ' * z).re ≤ 0 := by
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'),
    marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h hxod,
    neg_one_mul, Complex.neg_re]
  linarith

/-- Marshall dressing turns a real non-negative entry into a non-positive one across a bipartite
bond with the `A`-site at `y` (`A x = false`, `A y = true`) and an odd shift at `y`. -/
theorem dressed_entry_re_nonpos_bipartite_y
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : Λ → Fin (N + 1)} (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hyod : Odd ((σ' y).val + (σ y).val))
    {z : ℂ} (hznn : 0 ≤ z.re) :
    (marshallSignS A σ * marshallSignS A σ' * z).re ≤ 0 := by
  rw [mul_comm (marshallSignS A σ) (marshallSignS A σ'),
    marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h hyod,
    neg_one_mul, Complex.neg_re]
  linarith

end LatticeSystem.Quantum
