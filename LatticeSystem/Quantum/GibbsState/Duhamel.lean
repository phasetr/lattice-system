import LatticeSystem.Quantum.GibbsState
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Duhamel (Kubo) static isothermal susceptibility

Following Tasaki *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.5 (p. 368), the finite-temperature static
(isothermal) susceptibility of a canonical-ensemble system is the
fluctuation–dissipation / Duhamel two-point function

  `χ_{AB}(β) = ∫₀^β ( ⟨A(τ) B⟩_β − ⟨A⟩_β ⟨B⟩_β ) dτ`,

where `A(τ) = e^{τ H} A e^{-τ H}` is the imaginary-time (Wick-rotated)
Heisenberg evolution of `A` by Euclidean time `τ`. This is exactly the
second derivative `−∂²/∂s² (β⁻¹ log Tr e^{-β(H − sA)})` of the
free-energy-type functional obtained by adding a source `sA` to `H`, so
`χ_{AB}` is the physical static susceptibility (the prefactor is `1`; no
extra `β` or `1/β` appears).

The integrand is the connected two-point correlation, a scalar built from
the existing `gibbsExpectation`, so only a `ℂ`-valued `intervalIntegral`
is needed here (no matrix-valued Bochner integral).

This generic, model-agnostic module underlies the Hubbard-model charge and
pairing susceptibilities of Tasaki Theorem 10.11 (Kubo–Kishi).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The imaginary-time (Wick-rotated) Heisenberg evolution of an operator
`A` by Euclidean time `τ`: `A(τ) = e^{τ H} A e^{-τ H}` (Tasaki §10.2.5,
the Duhamel integrand of eqs. (10.2.53)/(10.2.54)). In our convention
`gibbsExp β H = e^{-β H}`, so `gibbsExp (-τ) H = e^{τ H}` supplies the
left factor and `gibbsExp τ H = e^{-τ H}` the right factor. -/
noncomputable def imagTimeEvolve (H : ManyBodyOp Λ) (τ : ℝ) (A : ManyBodyOp Λ) :
    ManyBodyOp Λ :=
  gibbsExp (-τ) H * A * gibbsExp τ H

/-- The **Duhamel (Kubo) static isothermal susceptibility**
`χ_{AB}(β) = ∫₀^β (⟨A(τ) B⟩_β − ⟨A⟩_β ⟨B⟩_β) dτ` (Tasaki §10.2.5, p. 368,
the fluctuation–dissipation form of the second-derivative susceptibilities
of eqs. (10.2.53)/(10.2.54)). The integrand is the connected imaginary-time
two-point correlation of `A` and `B` in the Gibbs state of `H`. -/
noncomputable def duhamelStaticSusceptibility (β : ℝ) (H A B : ManyBodyOp Λ) : ℂ :=
  ∫ τ in (0 : ℝ)..β,
    (gibbsExpectation β H (imagTimeEvolve H τ A * B)
      - gibbsExpectation β H A * gibbsExpectation β H B)

end LatticeSystem.Quantum
