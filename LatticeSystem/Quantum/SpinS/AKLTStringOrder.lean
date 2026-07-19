import LatticeSystem.Quantum.SpinS.AKLTStringOrderCovariance

/-!
# Tasaki §7.2.1: AKLT string order in all three axes

The explicit periodic spin-one AKLT matrix-product state has den
Nijs--Rommelse string order `4/9` in every spin axis. The finite axis-three
transfer calculation is transported to the other axes by exact finite-volume
covariance.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer, 2020, §7.2.1, corrected eqs. (7.2.6)--(7.2.8),
pp. 193--194.
-/

namespace LatticeSystem.Quantum

/-- Tasaki §7.2.1, corrected eqs. (7.2.6)--(7.2.8), pp. 193--194:
the periodic spin-one AKLT VBS state has string order `4/9` in every axis. -/
theorem aklt_string_order_7_2_8 :
    ∀ α : Fin 3, ∀ ε : ℝ, 0 < ε →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
          ∀ x y : Fin L,
            0 < x.val →
            x.val < y.val →
            y.val - x.val = d →
            |stringCorrelationAxisS α x y (akltVBSState L)
                - (4 / 9 : ℝ)| < ε := by
  intro α ε hε
  obtain ⟨L₀, hL₀, haxisThree⟩ :=
    AKLTStringOrder.Internal.axis3Epsilon ε hε
  refine ⟨0, ?_⟩
  intro d hd
  refine ⟨L₀, ?_⟩
  intro L hL x y hx hxy hdistance
  rw [AKLTStringOrder.Internal.stringCorrelationAxisS_akltVBSState_eq_three α L
    (le_trans hL₀ hL) x y hxy]
  exact haxisThree L hL x y hx hxy

end LatticeSystem.Quantum
