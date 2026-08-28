import LatticeSystem.Quantum.SpinS.SaturatedCoherentAmplitude

/-!
# Test coverage for Tasaki Problem 2.4.b — coherent-state one-site product form

Signature pin for the declarations `saturatedCoherentAmp` and `saturatedCoherentState_zero_apply`
of the foundation module `LatticeSystem/Quantum/SpinS/SaturatedCoherentAmplitude.lean`: the
saturated-ferromagnet coherent state `Ξ_{θ,0}` at each configuration `σ` equals the product over
sites of the one-site amplitude `amp N θ (σ x) = √C(N, σ x) · cos(θ/2)^{N − σ x} · sin(θ/2)^{σ x}`.
That product form is eq. (S.18) of the solution to Problem 2.4.c (Tasaki, *Physics and Mathematics
of Quantum Many-Body Systems*, statement p. 34, solution p. 497, stated there for `S = 1/2`), taken
at `φ = 0`; it is the foundation for Problem 2.4.b (statement p. 34, solution pp. 496-497,
eq. (S.17)), whose solution expands `Û_θ^{(2)} Φ↑ = Σ_M c_M Φ_M` and needs every `c_M`
to be nonzero.
The fixtures fix the exact name, binder order, hypothesis set (no expansion or magnetization
hypothesis) of `saturatedCoherentState_zero_apply`, and pin two concrete instances (`|Λ| = 1` and
`|Λ| = 2`, both at `N = 1`) that exercise the up/down amplitudes and the site-product structure.
-/

namespace LatticeSystem.Tests.Problem24b

open LatticeSystem.Quantum

/-! ## Signature pin: no extra hypothesis beyond the standing spin-`S` assumptions -/

/-- **Signature pin.** For any site set `V` (`Fintype`, `DecidableEq` only) and spin data `N`, any
angle `θ`, and any configuration `σ`, the coherent state at `φ = 0` factorizes as the site-product
of one-site amplitudes. This fixture pins `saturatedCoherentState_zero_apply`'s exact name, binder
order (`V N` implicit-typeclass, `θ σ` explicit) and hypothesis set: no expansion hypothesis, no
magnetization hypothesis, no coefficient-nonzero hypothesis, and in particular no `Nonempty V` —
supplying an instance the capstone does not need would make this pin accept a strengthened
hypothesis set. -/
example {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (θ : ℝ) (σ : V → Fin (N + 1)) :
    saturatedCoherentState V N θ 0 σ = ∏ x : V, saturatedCoherentAmp N θ (σ x) :=
  saturatedCoherentState_zero_apply θ σ

/-! ## `|Λ| = 1`, `N = 1` fixture: the two one-site amplitudes -/

/-- **All-up amplitude at `|Λ| = 1`.** The single-site coherent state at the all-up configuration
equals `cos(θ/2)`, the `j = 0` amplitude. -/
example (θ : ℝ) :
    saturatedCoherentState (Fin 1) 1 θ 0 (fun _ => 0) = Complex.cos (θ / 2) := by
  rw [saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-- **All-down amplitude at `|Λ| = 1`.** The single-site coherent state at the all-down
configuration equals `sin(θ/2)`, the `j = 1` amplitude. -/
example (θ : ℝ) :
    saturatedCoherentState (Fin 1) 1 θ 0 (fun _ => 1) = Complex.sin (θ / 2) := by
  rw [saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-! ## `|Λ| = 2`, `N = 1` fixture: the site-product over three configurations -/

/-- **All-up product at `|Λ| = 2`.** Both sites up: the coherent-state value is `cos(θ/2)^2`, the
product of two `j = 0` amplitudes. -/
example (θ : ℝ) :
    saturatedCoherentState (Fin 2) 1 θ 0 (fun _ => 0)
      = Complex.cos (θ / 2) * Complex.cos (θ / 2) := by
  rw [saturatedCoherentState_zero_apply, Fin.prod_univ_two]
  simp [saturatedCoherentAmp]

/-- **Mixed product at `|Λ| = 2`.** Site `0` up, site `1` down: the coherent-state value is
`cos(θ/2) · sin(θ/2)`, the product of a `j = 0` and a `j = 1` amplitude. -/
example (θ : ℝ) :
    saturatedCoherentState (Fin 2) 1 θ 0 (fun x => if x = 0 then 0 else 1)
      = Complex.cos (θ / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentState_zero_apply, Fin.prod_univ_two]
  simp [saturatedCoherentAmp]

/-- **All-down product at `|Λ| = 2`.** Both sites down: the coherent-state value is `sin(θ/2)^2`,
the product of two `j = 1` amplitudes. -/
example (θ : ℝ) :
    saturatedCoherentState (Fin 2) 1 θ 0 (fun _ => 1)
      = Complex.sin (θ / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentState_zero_apply, Fin.prod_univ_two]
  simp [saturatedCoherentAmp]

end LatticeSystem.Tests.Problem24b
