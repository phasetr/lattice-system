/-
The squared staggered order parameter is bounded by `O(L)` times the susceptibility
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Combining the ground-state Falk–Bruch inequality `2(Re⟨Φ,Ô²Φ⟩)² ≤ ⟨Φ,[Ô,[Ĥ,Ô]]Φ⟩·Re⟨y,ÔΦ⟩` with the
`O(L)` oscillator-strength bound `|⟨Φ,[Ô,[Ĥ,Ô]]Φ⟩| ≤ 12N³·L`, and using that both factors are
nonnegative, the squared staggered order parameter of a ground state is bounded by `O(L)` times the
static susceptibility: `2(Re⟨Φ,Ô²Φ⟩)² ≤ 12N³·L·Re⟨y,ÔΦ⟩`.  This reduces Corollary 4.3 to the
susceptibility bound `Re⟨y,ÔΦ⟩ ≤ C·L` (the reflection-positivity infrared bound): if the
susceptibility is `O(L)` then `⟨Ô²⟩ ≤ √(6N³C)·L`, so `⟨(Ô/L)²⟩ → 0`.
-/
import LatticeSystem.Quantum.SpinS.OscillatorStrengthBound
import LatticeSystem.Quantum.SpinS.FalkBruchDoubleCommutator
import LatticeSystem.Quantum.SpinS.DysonLiebSimon
import LatticeSystem.Quantum.SpinS.HeisenbergCore

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- The ring nearest-neighbor coupling is real-valued (`0`/`1`), hence self-conjugate. -/
theorem ringCoupling_self_star (L : ℕ) (x y : Fin L) :
    star (ringCoupling L x y) = ringCoupling L x y := by
  unfold ringCoupling; split <;> simp

/-- **The squared staggered order parameter is bounded by `O(L)` times the susceptibility.**  For a
ground state `Φ` of the zero-field ring (eigenvalue `hermitianMinEigenvalue`) and a potential `y`
for `ÔΦ` (`(Ĥ − E₀) y = ÔΦ`), `2 (Re⟨Φ, Ô² Φ⟩)² ≤ 12 N³ · L · Re⟨y, ÔΦ⟩`. -/
theorem staggeredOrder_sq_le_susceptibility (L N : ℕ) (hL : 2 ≤ L) (hN : 1 ≤ N)
    {Φ y : (Fin L → Fin (N + 1)) → ℂ} (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦ : (heisenbergHamiltonianS (ringCoupling L) N).mulVec Φ
        = (hermitianMinEigenvalue
            (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ) • Φ)
    (hy : (heisenbergHamiltonianS (ringCoupling L) N
          - (hermitianMinEigenvalue
              (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ)
            • (1 : ManyBodyOpS (Fin L) N)).mulVec y
        = (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ) :
    haveI : NeZero L := ⟨by omega⟩
    2 * (star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N
            * staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re ^ 2
      ≤ 12 * (N : ℝ) ^ 3 * (L : ℝ)
        * (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re := by
  haveI : NeZero L := ⟨by omega⟩
  set hH := heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N with hHdef
  set hA := staggeredOrderOpS_isHermitian (ringStaggeredSublattice L) N with hAdef
  -- Falk–Bruch: `2⟨Ô²⟩² ≤ osc · χ`
  have hfb := falkBruch_double_commutator hH hA hΦ hy
  -- oscillator strength `osc ≤ 12 N³ L`
  have hosc : (star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N
        * (heisenbergHamiltonianS (ringCoupling L) N
            * staggeredOrderOpS (ringStaggeredSublattice L) N
          - staggeredOrderOpS (ringStaggeredSublattice L) N
            * heisenbergHamiltonianS (ringCoupling L) N)
      - (heisenbergHamiltonianS (ringCoupling L) N
            * staggeredOrderOpS (ringStaggeredSublattice L) N
          - staggeredOrderOpS (ringStaggeredSublattice L) N
            * heisenbergHamiltonianS (ringCoupling L) N)
        * staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re
      ≤ 12 * (N : ℝ) ^ 3 * (L : ℝ) :=
    le_of_abs_le (oscillatorStrength_abs_le L N hL hN hΦnorm)
  -- susceptibility `χ = Re⟨y, ÔΦ⟩ ≥ 0` (potential of a PSD operator)
  have hχ :
      0 ≤ (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re := by
    have hpsd := (hermitianSubMin_posSemidef hH).dotProduct_mulVec_nonneg y
    rw [hy] at hpsd
    exact (Complex.le_def.1 hpsd).1
  -- combine: `2⟨Ô²⟩² ≤ osc · χ ≤ 12 N³ L · χ`
  refine le_trans hfb ?_
  exact mul_le_mul_of_nonneg_right hosc hχ

end LatticeSystem.Quantum
