import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetization

/-!
# Equal-magnetisation reachability (Tasaki §2.5 p. 42 Proposition)

This module formalises Tasaki's "Proposition" on p. 42:

  **Proposition.** Let the lattice `(Λ, B)` be connected. Then any
  spin configurations `σ` and `σ'` with `σ̄ = σ̄'` are connected,
  i.e., there is a sequence of single-edge bond swaps converting
  `σ` to `σ'`.

The argument is the `N = 1` reading of the spin-`S` raise/lower
reachability `raiseLowerReachableS_of_connected`: equal magnetisation is
equal `magSumS` (`magnetization_eq_iff_magSumS_eq`), a raise/lower step in
`Fin 2` is a bond swap (`swapStep_of_raiseLowerStepS`), and reachability
transports along the step-relation implication. The empty lattice, which
the spin-`S` statement excludes through `G.Connected`, is handled
separately: there is only one configuration.

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 42 (Proposition in "Proof of Property (iii)").
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Tasaki §2.5 p. 42 Proposition.** For a connected graph `G`,
any two configurations `σ` and `σ'` with the same total
magnetisation are connected by a sequence of single-edge bond swaps.

Proof: on a non-empty `Λ` the preconnected `G` is connected, the
magnetisation equality is the `magSumS` equality of the spin-`S`
development at `N = 1`, and `raiseLowerReachableS_of_connected` produces a
chain of raise/lower steps, each of which is a bond swap. On an empty `Λ`
the two configurations are equal. -/
theorem swapReachable_of_eq_magnetization
    {G : SimpleGraph Λ} (hG : G.Preconnected) :
    ∀ (σ σ' : Λ → Fin 2),
      magnetization Λ σ = magnetization Λ σ' →
      SwapReachable G σ σ' := by
  intro σ σ' hmag
  rcases isEmpty_or_nonempty Λ with hΛ | hΛ
  · have hσ : σ = σ' := funext fun x => (IsEmpty.false x).elim
    rw [hσ]
    exact SwapReachable.refl G σ'
  · exact Relation.ReflTransGen.mono (fun _ _ hstep => swapStep_of_raiseLowerStepS hstep)
      (raiseLowerReachableS_of_connected (N := 1) G (G.connected_iff.mpr ⟨hG, hΛ⟩)
        ((magnetization_eq_iff_magSumS_eq σ σ').mp hmag))

end LatticeSystem.Quantum
