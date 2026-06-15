import LatticeSystem.Quantum.SpinS.AKLT

/-!
# Tasaki §8.3.6: a rigorous index theorem and the SPT phase transition (Theorem 8.8)

Because different SPT phases are not distinguished by any local order parameter, proving that a
**phase transition** must occur between them is genuinely hard — standard statistical-mechanics
methods do not apply.  Tasaki's 2018 index theorem settles it for the explicit interpolation
(eq. (8.3.55))
`Ĥ_s = s Σ_x [Ŝ_x·Ŝ_{x+1} + ⅓(Ŝ_x·Ŝ_{x+1})²] + (1−s) Σ_x (Ŝ_x^{(3)})²`,
which linearly connects the **trivial** Hamiltonian (8.1.2) (product ground state, at `s = 0`, in
the
large-`D` phase) to the **AKLT** Hamiltonian (7.1.1) (VBS ground state, at `s = 1`, in the Haldane
phase).  Every `Ĥ_s` has all three protecting symmetries (S1)–(S3), so the SPT picture predicts a
topological phase transition at some intermediate `s`.

**Theorem 8.8** (Tasaki): the model (8.3.55) in its infinite-volume limit undergoes a phase
transition — there is an intermediate `s ∈ (0,1)` at which the model is **either** gapless, **or**
has
more than one ground state, **or** exhibits a discontinuity in the ground-state expectation value
of a
local operator.

The interpolating Hamiltonian is *defined concretely* (reusing `akltHamiltonianS`).  The three
infinite-volume alternatives are honest uninterpreted markers acting on the *family* of
finite-volume
Hamiltonians `L ↦ Ĥ_s` (the phase transition is a property of the `L ↑ ∞` limit, not of any fixed
`L`); Theorem 8.8, proved by Tasaki via an index theorem, is a documented axiom that keeps the
faithful three-way disjunction.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.6, Theorem 8.8, eqs. (8.3.55), pp. 280–284; H. Tasaki, Phys. Rev. Lett. **121**, 140604
(2018); Y. Ogata, Trans. Amer. Math. Soc. Ser. B **8**, 39 (2021).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **SPT interpolating Hamiltonian** (eq. (8.3.55)) `Ĥ_s = s Ĥ_AKLT + (1−s) Σ_x (Ŝ_x^{(3)})²`:
the linear path from the trivial Hamiltonian (8.1.2) at `s = 0` (product ground state, large-`D`
phase) to the AKLT Hamiltonian (7.1.1) at `s = 1` (VBS ground state, Haldane phase).  Every `Ĥ_s`
keeps all three protecting symmetries. -/
noncomputable def sptInterpolatingHamiltonianS (L : ℕ) (s : ℝ) : ManyBodyOpS (Fin L) 2 :=
  (s : ℂ) • akltHamiltonianS L +
    ((1 - s : ℝ) : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2

/-- **Infinite-volume gaplessness marker** `IsGaplessInInfiniteVolume H`: the family of
finite-volume
Hamiltonians `H L` has a vanishing spectral gap in the `L ↑ ∞` limit.  An uninterpreted predicate.
-/
axiom IsGaplessInInfiniteVolume (H : (L : ℕ) → ManyBodyOpS (Fin L) 2) : Prop

/-- **Infinite-volume ground-state degeneracy marker** `HasMultipleGroundStatesInInfiniteVolume H`:
the family `H L` has more than one ground state in the `L ↑ ∞` limit.  An uninterpreted predicate.
-/
axiom HasMultipleGroundStatesInInfiniteVolume (H : (L : ℕ) → ManyBodyOpS (Fin L) 2) : Prop

/-- **Infinite-volume local-expectation discontinuity marker**
`HasLocalExpectationDiscontinuityInInfiniteVolume H`: the family `H L` exhibits a discontinuity in
the `L ↑ ∞` ground-state expectation value of some local operator.  An uninterpreted predicate. -/
axiom HasLocalExpectationDiscontinuityInInfiniteVolume (H : (L : ℕ) → ManyBodyOpS (Fin L) 2) : Prop

/-- **Tasaki Theorem 8.8 (rigorous SPT phase transition / index theorem), AXIOM.**  The
interpolating
model (8.3.55) in its infinite-volume limit undergoes a phase transition: there is an
**intermediate**
`s ∈ (0,1)` at which the family `L ↦ Ĥ_s` is **either** gapless (`IsGaplessInInfiniteVolume`),
**or**
has more than one ground state (`HasMultipleGroundStatesInInfiniteVolume`), **or** exhibits a
discontinuity in the ground-state expectation of a local operator
(`HasLocalExpectationDiscontinuityInInfiniteVolume`).  Since `Ĥ_0` is in the trivial large-`D` phase
and `Ĥ_1` is the AKLT/VBS Haldane phase, this is a genuine topological phase transition.  Proved by
Tasaki (2018) as a corollary of his index theorem; recorded as a documented axiom. -/
axiom tasaki_theorem_8_8 :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      (IsGaplessInInfiniteVolume (fun L => sptInterpolatingHamiltonianS L s) ∨
        HasMultipleGroundStatesInInfiniteVolume (fun L => sptInterpolatingHamiltonianS L s) ∨
        HasLocalExpectationDiscontinuityInInfiniteVolume
          (fun L => sptInterpolatingHamiltonianS L s))

end LatticeSystem.Quantum
