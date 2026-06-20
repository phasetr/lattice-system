import LatticeSystem.Quantum.SpinS.SU2ExpectationLadderInvariant
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.Theorem23Local

/-!
# Iterated SU(2)-invariant expectation ladder invariance
(Issue #4604, iterated form of `su2_expectationRatioRe_ladder_invariant`)

The merged single-step result `su2_expectationRatioRe_ladder_invariant` shows that
for an SU(2)-invariant operator `O` (commuting with both total ladder operators
`Ŝ⁺_tot`, `Ŝ⁻_tot`) and a joint `Ŝ³_tot` / Casimir `(Ŝ_tot)²` eigenvector `v`, the
real Rayleigh quotient `⟨v, O v⟩.re / ‖v‖²` is preserved by one lowering step
`v ↦ Ŝ⁻_tot v` (when that step is non-vanishing).

Here we extend this to the iterated lowering `(Ŝ⁻_tot)^k`: the real expectation
ratio along `(Ŝ⁻_tot)^k v` coincides with the ratio along `v` itself, for every
`k : ℕ` for which the `k`-fold lowering is non-vanishing.

The proof is by induction on `k`.
- `k = 0`: `(Ŝ⁻_tot)^0 = 1` and `mulVec` is the identity, so both sides are equal.
- `k+1`: write `w := (Ŝ⁻_tot)^k v`.  The vector `w` is again a joint eigenvector,
  `Ŝ³_tot w = (m − k) • w` (each lowering lowers the `Ŝ³_tot` weight by one;
  `totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_weight` below, proved by induction
  from the single-step shift `totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_eigenvec`)
  and `(Ŝ_tot)² w = γ • w` (`totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_of_eigenvec`).
  Since `(Ŝ⁻_tot)^{k+1} v = Ŝ⁻_tot w ≠ 0`, the single-step invariance applied to `w`
  gives `ratio((Ŝ⁻_tot)^{k+1} v) = ratio(w)`, and the induction hypothesis gives
  `ratio(w) = ratio(v)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4 (Theorem 4.4) and §2.5 (Lieb–Mattis / SU(2) ladder structure).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Iterated `Ŝ³_tot` weight of a lowered eigenvector.** If `Ŝ³_tot v = m • v`,
then for every `k : ℕ` the `k`-fold lowered vector `(Ŝ⁻_tot)^k v` is again an
`Ŝ³_tot`-eigenvector at the lowered weight `m − k`:

  `Ŝ³_tot ((Ŝ⁻_tot)^k v) = (m − k) • (Ŝ⁻_tot)^k v`.

Proved by induction on `k` from the single-step shift
`totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_eigenvec`. -/
private theorem totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_weight
    {m : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v) (k : ℕ) :
    (totalSpinSOp3 V N).mulVec (((totalSpinSOpMinus V N) ^ k).mulVec v) =
      (m - (k : ℂ)) • ((totalSpinSOpMinus V N) ^ k).mulVec v := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, sub_zero]
    exact hz
  | succ k ih =>
    -- `(Ŝ⁻)^{k+1} v = Ŝ⁻ ((Ŝ⁻)^k v)`; apply the single-step shift to `(Ŝ⁻)^k v`.
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_eigenvec ih]
    push_cast
    congr 1
    ring

/-- **Iterated SU(2)-invariant real-expectation-ratio ladder invariance.** Let
`O : ManyBodyOpS V N` commute with both total ladder operators
(`hOplus : Commute O Ŝ⁺_tot`, `hOminus : Commute O Ŝ⁻_tot`), and let `v` be a joint
`Ŝ³_tot` / Casimir eigenvector (`Ŝ³_tot v = m • v`, `(Ŝ_tot)² v = γ • v`).  For every
`k : ℕ` for which the `k`-fold lowering is non-vanishing (`(Ŝ⁻_tot)^k v ≠ 0`), the
real Rayleigh quotient of `O` is preserved by the iterated lowering:

  `⟨(Ŝ⁻)^k v, O (Ŝ⁻)^k v⟩.re / ⟨(Ŝ⁻)^k v, (Ŝ⁻)^k v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re`,

where `⟨a, b⟩ := star a ⬝ᵥ b`.  Proved by induction on `k`, applying the single-step
`su2_expectationRatioRe_ladder_invariant` to the joint eigenvector `(Ŝ⁻_tot)^k v`. -/
theorem su2_expectationRatioRe_ladder_iterate_invariant (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v)
    (k : ℕ) (hne : ((totalSpinSOpMinus V N) ^ k).mulVec v ≠ 0) :
    (star (((totalSpinSOpMinus V N) ^ k).mulVec v) ⬝ᵥ
          (O.mulVec (((totalSpinSOpMinus V N) ^ k).mulVec v))).re /
        (star (((totalSpinSOpMinus V N) ^ k).mulVec v) ⬝ᵥ
          (((totalSpinSOpMinus V N) ^ k).mulVec v)).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    -- `w := (Ŝ⁻)^k v`; the next step is `(Ŝ⁻)^{k+1} v = Ŝ⁻ w`.
    set w : (V → Fin (N + 1)) → ℂ := ((totalSpinSOpMinus V N) ^ k).mulVec v with hwdef
    -- Express `(Ŝ⁻)^{k+1} v` as `Ŝ⁻ w`.
    have hstep : ((totalSpinSOpMinus V N) ^ (k + 1)).mulVec v =
        (totalSpinSOpMinus V N).mulVec w := by
      rw [hwdef, pow_succ', ← Matrix.mulVec_mulVec]
    -- `Ŝ⁻ w ≠ 0` from the non-vanishing hypothesis on the `(k+1)`-fold lowering.
    have hne_step : (totalSpinSOpMinus V N).mulVec w ≠ 0 := by
      rw [← hstep]; exact hne
    -- If the `(k+1)`-step is non-zero, then the `k`-step `w` is also non-zero.
    have hw_ne : w ≠ 0 := by
      intro h0
      apply hne_step
      rw [h0, Matrix.mulVec_zero]
    -- `w` is a joint `Ŝ³_tot` eigenvector at weight `m − k`.
    have hz_w : (totalSpinSOp3 V N).mulVec w = (m - (k : ℂ)) • w :=
      totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_weight hz k
    -- `w` keeps the Casimir eigenvalue `γ`.
    have hcas_w : (totalSpinSSquared V N).mulVec w = γ • w :=
      totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_of_eigenvec N k hcas
    -- Single-step invariance applied to `w`:
    --   `ratio(Ŝ⁻ w) = ratio(w)`.
    have hsingle := su2_expectationRatioRe_ladder_invariant O hOplus hOminus
      hz_w hcas_w hne_step
    -- Rewrite the `(k+1)`-fold ratio as the single step on `w`, then chain with IH.
    rw [hstep, hsingle]
    exact ih hw_ne

end LatticeSystem.Quantum
