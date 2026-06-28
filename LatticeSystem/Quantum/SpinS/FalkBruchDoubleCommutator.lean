/-
The concrete ground-state Falk–Bruch inequality via the double commutator
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Combining the abstract Falk–Bruch inequality (with `K = H − E₀`) and the double commutator =
variational energy identity, the squared expectation of `A²` in a ground state is bounded by the
double commutator (oscillator strength) times the susceptibility:
`2 (Re⟨Φ, A² Φ⟩)² ≤ Re⟨Φ, [A, [H, A]] Φ⟩ · Re⟨y, A Φ⟩`,
where `y` is a potential for `A Φ` (`(H − E₀) y = A Φ`).  For the staggered order parameter the left
side is `2⟨Ô²⟩²`, the first factor on the right is the (bounded) f-sum-rule oscillator strength, and
the susceptibility `Re⟨y, ÔΦ⟩` is controlled by reflection positivity — the route to `⟨Ô²⟩ ≤ C·L`.
-/
import LatticeSystem.Quantum.SpinS.HermitianSubMinPosSemidef
import LatticeSystem.Quantum.SpinS.DoubleCommutatorVariational

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- **Concrete ground-state Falk–Bruch inequality.**  For a Hermitian `H`, `A`, a ground-state
eigenvector `Φ` (eigenvalue `E₀ = hermitianMinEigenvalue`), and a potential `y` for `A Φ`
(`(H − E₀) y = A Φ`), `2 (Re⟨Φ, A² Φ⟩)² ≤ Re⟨Φ, [A, [H, A]] Φ⟩ · Re⟨y, A Φ⟩`. -/
theorem falkBruch_double_commutator {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H A : Matrix n n ℂ} {Φ y : n → ℂ} (hH : H.IsHermitian) (hA : A.IsHermitian)
    (hΦ : H.mulVec Φ = (hermitianMinEigenvalue hH : ℂ) • Φ)
    (hy : (H - (hermitianMinEigenvalue hH : ℂ) • (1 : Matrix n n ℂ)).mulVec y = A.mulVec Φ) :
    2 * (star Φ ⬝ᵥ (A * A).mulVec Φ).re ^ 2
      ≤ (star Φ ⬝ᵥ (A * (H * A - A * H) - (H * A - A * H) * A).mulVec Φ).re
        * (star y ⬝ᵥ A.mulVec Φ).re := by
  set K := H - (hermitianMinEigenvalue hH : ℂ) • (1 : Matrix n n ℂ) with hK
  -- ⟨Φ, A² Φ⟩ = ⟨AΦ, AΦ⟩
  have hAA : star Φ ⬝ᵥ (A * A).mulVec Φ = star (A.mulVec Φ) ⬝ᵥ A.mulVec Φ := by
    rw [hermitian_dotProduct_shift hA]
  -- ⟨Φ, [A,[H,A]] Φ⟩ = 2 ⟨AΦ, K AΦ⟩
  have hDC : star Φ ⬝ᵥ (A * (H * A - A * H) - (H * A - A * H) * A).mulVec Φ
      = 2 * (star (A.mulVec Φ) ⬝ᵥ K.mulVec (A.mulVec Φ)) := by
    rw [double_commutator_ground_state_eq hH hA hΦ, hK, Matrix.sub_mulVec, dotProduct_sub,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    ring
  have hfb := falkBruch_of_mulVec_eq (hermitianSubMin_posSemidef hH) hy
  rw [hAA, hDC, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  nlinarith [hfb]

end LatticeSystem.Quantum
