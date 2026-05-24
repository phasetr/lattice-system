import LatticeSystem.Quantum.SpinS.Theorem23SectorExistenceInterval
import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import LatticeSystem.Quantum.SpinS.Theorem23IntervalCasimirMinimality
import LatticeSystem.Quantum.SpinS.Theorem23Local
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference
import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceMarshall
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderLoweringInvariant
import LatticeSystem.Quantum.SpinS.TotalSpinSSquaredMaxEigenspaceEqSpanLadder

/-!
# Tasaki §2.5 Theorem 2.3 outside-ground API

This module contains outside-ground lower-bound callbacks and common-energy
final packaging wrappers for the Tasaki §2.5 Theorem 2.3 proof chain. It
imports the interval-Casimir minimality suffix split from
`Theorem23IntervalCasimir.lean` so the base interval-chain module does not
accumulate the outside-ground and final-packaging API tail. The source
predicted-Casimir final-wrapper suffix is split into
`Theorem23OutsideGroundPredictedCasimir.lean`, the threaded predicted-Casimir
final-wrapper suffix is split into
`Theorem23OutsideGroundPredictedCasimirThreaded.lean`, the conditional
left-endpoint predicted-GS final-wrapper suffix is split into
`Theorem23OutsideGroundConditional.lean`, and the left-endpoint threaded
predicted-GS and lowered-Marshall final-wrapper suffix is split into
`Theorem23OutsideGroundPredictedGS.lean`.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector ground-energy lower callback**:
for each nonempty sector outside the admissible interval, the common energy
`μ` is no larger than the Marshall-positive sector ground-representative
energy supplied by the per-sector Theorem 2.2 wrapper.

The Perron-Frobenius bridge turns this callback into a full outside-sector
real spectral lower bound. -/
def tasaki23OutsideGroundEnergyLowerCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c μ : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M ∉ tasaki23GroundStateSectors (V := V) A N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      μ ≤ μM

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector ground-energy lower family**:
after the adjacent-sector chain chooses the common energy `μ`, this
callback supplies the outside-sector lower-bound API at that same `μ`.

This names the final higher-level input used by the threaded
outside-ground wrappers, where `μ` is not an explicit argument but is
produced by the common-energy chain. -/
def tasaki23OutsideGroundEnergyLowerFamilyCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ {μ : ℝ},
    tasaki23CommonEnergyChain (V := V) A J N c μ →
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector admissible-reach callback**:
for each Marshall-positive Theorem 2.2 representative in a sector outside
`tasaki23GroundStateSectors`, the ladder construction reaches a nonzero
sector eigenvector at the same eigenvalue in some admissible sector.

This names the remaining ladder-reach task separately from the final
outside-ground lower-bound comparison: once such an admissible-sector
eigenvector at `μM` is available, the common-energy chain on admissible
sectors proves `μ ≤ μM`. -/
def tasaki23OutsideGroundAdmissibleReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M ∉ tasaki23GroundStateSectors (V := V) A N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Φ : magConfigS V N K → ℂ,
          Φ ≠ 0 ∧
          (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec Φ =
            (μM : ℂ) • Φ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector admissible full-reach
callback**: this variant records the ladder output before projecting it
back to a magnetization-sector coordinate space.  For each outside-sector
Marshall-positive representative, the ladder construction reaches a
nonzero full-space eigenvector at the same eigenvalue whose magnetization
belongs to an admissible sector. -/
def tasaki23OutsideGroundAdmissibleFullReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M ∉ tasaki23GroundStateSectors (V := V) A N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Ψ : (V → Fin (N + 1)) → ℂ,
          Ψ ≠ 0 ∧
          Ψ ∈
            magSubspaceS V N
              (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (K : ℂ)) ∧
          (heisenbergHamiltonianS J N).mulVec Ψ = (μM : ℂ) • Ψ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left iterated-ladder full-reach callback**:
for an outside sector left of the admissible interval, the total-spin
lowering ladder can be iterated until it reaches a nonzero full-space
vector in an admissible magnetization sector.  The Lean bridge proves the
magnetization support and eigenvalue preservation from this non-zeroness
input. -/
def tasaki23OutsideGroundLeftIteratedLadderFullReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ k : ℕ,
          K = M + k ∧
          ((totalSpinSOpMinus V N) ^ k).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right iterated-ladder full-reach callback**:
for an outside sector right of the admissible interval, the total-spin
raising ladder can be iterated until it reaches a nonzero full-space
vector in an admissible magnetization sector. -/
def tasaki23OutsideGroundRightIteratedLadderFullReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ k : ℕ,
          M = K + k ∧
          ((totalSpinSOpPlus V N) ^ k).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left iterated-ladder Casimir callback**:
for an outside sector left of the admissible interval, the chosen admissible
target and ladder length come with a total-Casimir eigenvalue for the source
Marshall-positive vector that avoids every intermediate lowering-kernel
Casimir value.  The local Casimir ladder lemma then proves the required
iterated non-zeroness. -/
def tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ k : ℕ,
          K = M + k ∧
          ∃ γ : ℂ,
            (totalSpinSSquared V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              γ • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
            ∀ j : ℕ, j < k →
              γ ≠
                ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - (j : ℂ)) *
                  (((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) -
                      (j : ℂ)) - 1)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right iterated-ladder Casimir callback**:
for an outside sector right of the admissible interval, the chosen admissible
target and ladder length come with a total-Casimir eigenvalue for the source
Marshall-positive vector that avoids every intermediate raising-kernel
Casimir value. -/
def tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ k : ℕ,
          M = K + k ∧
          ∃ γ : ℂ,
            (totalSpinSSquared V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              γ • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
            ∀ j : ℕ, j < k →
              γ ≠
                ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) + (j : ℂ)) *
                  (((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) +
                      (j : ℂ)) + 1)

omit [DecidableEq V] in
/-- **Saturated total-Casimir lowering endpoint mismatch**: before the
bottom magnetization `|V| * N`, the saturated-ferromagnet total-Casimir
value cannot equal the lowering-kernel value at sector coordinate `M`. -/
theorem saturatedFerromagnetCasimirEigenvalueS_ne_lowering_kernel_value_of_lt_card_mul
    (N M : ℕ) (hM : M < Fintype.card V * N) :
    saturatedFerromagnetCasimirEigenvalueS V N ≠
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)) := by
  intro h
  have hre := congrArg Complex.re h
  unfold saturatedFerromagnetCasimirEigenvalueS at hre
  norm_num at hre
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  have hM_lt : (M : ℝ) < (Fintype.card V * N : ℕ) := by
    exact_mod_cast hM
  nlinarith [show ((Fintype.card V : ℝ) * (N : ℝ)) =
      (Fintype.card V * N : ℕ) by norm_num]

omit [DecidableEq V] in
/-- **Saturated total-Casimir raising endpoint mismatch**: after the top
magnetization `0`, the saturated-ferromagnet total-Casimir value cannot
equal the raising-kernel value at sector coordinate `M`. -/
theorem saturatedFerromagnetCasimirEigenvalueS_ne_raising_kernel_value_of_pos_of_le_card_mul
    (N M : ℕ) (hM : 0 < M) (hM_le : M ≤ Fintype.card V * N) :
    saturatedFerromagnetCasimirEigenvalueS V N ≠
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) + 1)) := by
  intro h
  have hre := congrArg Complex.re h
  unfold saturatedFerromagnetCasimirEigenvalueS at hre
  norm_num at hre
  have hM_pos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hM_le : (M : ℝ) ≤ (Fintype.card V * N : ℕ) := by
    exact_mod_cast hM_le
  nlinarith [show ((Fintype.card V : ℝ) * (N : ℝ)) =
      (Fintype.card V * N : ℕ) by norm_num]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-Casimir source callback**:
for an outside sector left of the admissible interval, the source
Marshall-positive vector lies in the saturated-ferromagnet total-Casimir
eigenspace.  This is the max-Casimir input needed to discharge the left
iterated-ladder Casimir full-reach callback. -/
def tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        saturatedFerromagnetCasimirEigenvalueS V N •
          magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-Casimir source callback**:
for an outside sector right of the admissible interval, the source
Marshall-positive vector lies in the saturated-ferromagnet total-Casimir
eigenspace.  This is the max-Casimir input needed to discharge the right
iterated-ladder Casimir full-reach callback. -/
def tasaki23OutsideGroundRightSaturatedCasimirSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        saturatedFerromagnetCasimirEigenvalueS V N •
          magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-Heisenberg source callback**:
for an outside sector left of the admissible interval, the source
Marshall-positive vector is an eigenvector of `H_J` at the saturated
ferromagnet energy.  Together with the saturated-Casimir source callback,
this is exactly the source-vector input needed for the saturated joint
eigenspace. -/
def tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        saturatedFerromagnetEigenvalueS (V := V) J N •
          magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-Heisenberg source callback**:
for an outside sector right of the admissible interval, the source
Marshall-positive vector is an eigenvector of `H_J` at the saturated
ferromagnet energy.  Together with the saturated-Casimir source callback,
this is exactly the source-vector input needed for the saturated joint
eigenspace. -/
def tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        saturatedFerromagnetEigenvalueS (V := V) J N •
          magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated source-energy callback**:
for an outside sector left of the admissible interval, the source
Marshall-positive eigenvalue `μM` is the saturated-ferromagnet Heisenberg
energy.  Combined with the source eigenvector equation, this scalar
identification supplies the left saturated-Heisenberg source callback. -/
def tasaki23OutsideGroundLeftSaturatedEnergySourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      (μM : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated source-energy callback**:
for an outside sector right of the admissible interval, the source
Marshall-positive eigenvalue `μM` is the saturated-ferromagnet Heisenberg
energy.  Combined with the source eigenvector equation, this scalar
identification supplies the right saturated-Heisenberg source callback. -/
def tasaki23OutsideGroundRightSaturatedEnergySourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      (μM : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-Heisenberg source from
saturated source energy**: the source eigenvector equation at `μM` becomes
the saturated-Heisenberg source equation once `μM` is identified with the
saturated-ferromagnet Heisenberg energy. -/
theorem tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback_of_saturated_energy_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedEnergySourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  have hμ :
      (μM : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N :=
    hleft M hM_left hμM_lt hv_pos hΦ
  simpa [hμ] using hΦ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-Heisenberg source from
saturated source energy**: the source eigenvector equation at `μM` becomes
the saturated-Heisenberg source equation once `μM` is identified with the
saturated-ferromagnet Heisenberg energy. -/
theorem tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback_of_saturated_energy_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightSaturatedEnergySourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  have hμ :
      (μM : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N :=
    hright M hM_right hμM_lt hv_pos hΦ
  simpa [hμ] using hΦ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-span source callback**:
for an outside sector left of the admissible interval, the source
Marshall-positive vector lies in the span of the saturated ferromagnetic
total-spin ladder.  The maximum-Casimir eigenspace identification converts
this concrete span input to the saturated-Casimir source callback. -/
def tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range (ladderIterateUp V N))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-span source callback**:
for an outside sector right of the admissible interval, the source
Marshall-positive vector lies in the span of the saturated ferromagnetic
total-spin ladder.  The maximum-Casimir eigenspace identification converts
this concrete span input to the saturated-Casimir source callback. -/
def tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range (ladderIterateUp V N))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-joint source callback**:
for an outside sector left of the admissible interval, the source
Marshall-positive vector lies in the saturated-ferromagnet joint eigenspace.
The Tasaki §2.4 ladder-span identification converts this source-vector input
to the saturated-ladder-span source callback. -/
def tasaki23OutsideGroundLeftSaturatedJointSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        saturatedFerromagnetJointEigenspace (V := V) J N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-joint source callback**:
for an outside sector right of the admissible interval, the source
Marshall-positive vector lies in the saturated-ferromagnet joint eigenspace.
The Tasaki §2.4 ladder-span identification converts this source-vector input
to the saturated-ladder-span source callback. -/
def tasaki23OutsideGroundRightSaturatedJointSourceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        saturatedFerromagnetJointEigenspace (V := V) J N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-joint reference callback**:
for an outside sector left of the admissible interval, provide a strictly
Marshall-positive real sector vector whose full embedding lies in the
saturated-ferromagnet joint eigenspace, together with a real representative of
the saturated Heisenberg eigenvalue.

The source-vector/eigenvalue bridge below uses this reference and the
Marshall-positive uniqueness theorem in the sector to prove that any
Marshall-positive source eigenvector in the same sector is itself in the
saturated joint eigenspace. -/
def tasaki23OutsideGroundLeftSaturatedJointReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∃ (μsat : ℝ) (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) ∈
        saturatedFerromagnetJointEigenspace (V := V) J N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-joint reference callback**:
right-side analogue of
`tasaki23OutsideGroundLeftSaturatedJointReferenceCallback`.  It supplies a
Marshall-positive saturated joint reference vector in each nonempty sector
right of the admissible interval, with a real representative of the saturated
Heisenberg eigenvalue. -/
def tasaki23OutsideGroundRightSaturatedJointReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∃ (μsat : ℝ) (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) ∈
        saturatedFerromagnetJointEigenspace (V := V) J N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder reference callback**:
left-side saturated reference callback with the joint-eigenspace membership
replaced by concrete membership in the span of the saturated total-spin
ladder.  The Tasaki §2.4 saturated joint-eigenspace/span identification turns
this into the saturated joint reference callback. -/
def tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∃ (μsat : ℝ) (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range (ladderIterateUp V N))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder reference callback**:
right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback`.  It asks for a
strictly Marshall-positive saturated reference vector in the concrete ladder
span in every outside sector right of the admissible interval. -/
def tasaki23OutsideGroundRightSaturatedLadderReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∃ (μsat : ℝ) (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range (ladderIterateUp V N))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated joint reference from ladder
reference**: the saturated-ferromagnet joint eigenspace is the span of
`ladderIterateUp`, so a left outside-sector saturated ladder reference is a
saturated joint reference. -/
theorem tasaki23OutsideGroundLeftSaturatedJointReferenceCallback_of_saturated_ladder_reference
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N := by
  intro M _ hM_left
  obtain ⟨μsat, w, hμsat, hw_pos, hw_span⟩ := hleft M hM_left
  refine ⟨μsat, w, hμsat, hw_pos, ?_⟩
  rwa [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp
    (V := V) (N := N) J]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated joint reference from ladder
reference**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedJointReferenceCallback_of_saturated_ladder_reference`. -/
theorem tasaki23OutsideGroundRightSaturatedJointReferenceCallback_of_saturated_ladder_reference
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hright :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N := by
  intro M _ hM_right
  obtain ⟨μsat, w, hμsat, hw_pos, hw_span⟩ := hright M hM_right
  refine ⟨μsat, w, hμsat, hw_pos, ?_⟩
  rwa [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp
    (V := V) (N := N) J]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-iterate reference
callback**: left-side saturated reference callback in which the reference
embedding lies in the singleton span of the sector ladder iterate
`ladderIterateUp V N ⟨M, _⟩`.  This is the concrete sector-level version of
the saturated ladder-reference callback. -/
def tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∃ (hM_range : M < Fintype.card V * N + 1) (μsat : ℝ)
        (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ {ladderIterateUp V N ⟨M, hM_range⟩}

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-iterate reference
callback**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback`. -/
def tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∃ (hM_range : M < Fintype.card V * N + 1) (μsat : ℝ)
        (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ {ladderIterateUp V N ⟨M, hM_range⟩}

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-iterate
Marshall-positive reference callback**: left-side concrete reference-vector
callback asserting that the strictly Marshall-positive sector embedding is
exactly the sector ladder iterate `ladderIterateUp V N ⟨M, _⟩`.  This is the
coordinate-level boundary for discharging the singleton-span iterate reference
callback. -/
def tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∃ (hM_range : M < Fintype.card V * N + 1) (μsat : ℝ)
        (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) =
        ladderIterateUp V N ⟨M, hM_range⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-iterate
Marshall-positive reference callback**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback`. -/
def tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveReferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∃ (hM_range : M < Fintype.card V * N + 1) (μsat : ℝ)
        (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) =
        ladderIterateUp V N ⟨M, hM_range⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-iterate
Marshall-positive coefficient callback**: left-side coordinate-level
reference callback asserting that every sector coefficient of
`ladderIterateUp V N ⟨M, _⟩` is the corresponding Marshall sign times a
strictly positive real weight.  The magnetization-subspace support of the
ladder iterate then upgrades this pointwise sector equality to the full
zero-extended reference-vector equality. -/
def tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∃ (hM_range : M < Fintype.card V * N + 1) (μsat : ℝ)
        (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      ∀ τ : magConfigS V N M,
        ladderIterateUp V N ⟨M, hM_range⟩ τ.1 =
          (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-iterate
Marshall-positive coefficient callback**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback`. -/
def tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∃ (hM_range : M < Fintype.card V * N + 1) (μsat : ℝ)
        (w : magConfigS V N M → ℝ),
      (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N ∧
      (∀ τ, 0 < w τ) ∧
      ∀ τ : magConfigS V N M,
        ladderIterateUp V N ⟨M, hM_range⟩ τ.1 =
          (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left Marshall-positive reference from
Marshall-positive coefficients**: pointwise sector coefficients of the
ladder iterate determine the zero-extended sector embedding because the
iterate lies in the corresponding magnetization subspace. -/
theorem tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback_of_marshall_positive_coefficients
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback
        (V := V) A J N) :
    tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback
        (V := V) A J N := by
  intro M _ hM_left
  obtain ⟨hM_range, μsat, w, hμsat, hw_pos, hcoeff⟩ := hleft M hM_left
  refine ⟨hM_range, μsat, w, hμsat, hw_pos, ?_⟩
  let Ψ : (V → Fin (N + 1)) → ℂ := ladderIterateUp V N ⟨M, hM_range⟩
  have hΨ_mem :
      Ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    change ladderIterateUp V N ⟨M, hM_range⟩ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))
    unfold ladderIterateUp
    exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS (V := V) (N := N) M
  have hsector :
      (fun τ : magConfigS V N M =>
        (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) =
        magSectorRestriction (M := M) Ψ := by
    funext τ
    exact (hcoeff τ).symm
  rw [hsector]
  exact magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
    (V := V) (N := N) (M := M) hΨ_mem

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right Marshall-positive reference from
Marshall-positive coefficients**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback_of_marshall_positive_coefficients`. -/
theorem tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveReferenceCallback_of_marshall_positive_coefficients
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hright :
      tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback
        (V := V) A J N) :
    tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveReferenceCallback
        (V := V) A J N := by
  intro M _ hM_right
  obtain ⟨hM_range, μsat, w, hμsat, hw_pos, hcoeff⟩ := hright M hM_right
  refine ⟨hM_range, μsat, w, hμsat, hw_pos, ?_⟩
  let Ψ : (V → Fin (N + 1)) → ℂ := ladderIterateUp V N ⟨M, hM_range⟩
  have hΨ_mem :
      Ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    change ladderIterateUp V N ⟨M, hM_range⟩ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))
    unfold ladderIterateUp
    exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS (V := V) (N := N) M
  have hsector :
      (fun τ : magConfigS V N M =>
        (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) =
        magSectorRestriction (M := M) Ψ := by
    funext τ
    exact (hcoeff τ).symm
  rw [hsector]
  exact magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
    (V := V) (N := N) (M := M) hΨ_mem

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-iterate coefficient
successor site-sum formula**: if the `M`-sector iterate has the
Marshall-signed coefficient form, then the next iterate is obtained by
applying `Ŝ^-_tot` to the corresponding zero-extended sector vector and
expanding that action as a sum of single-site lowering contributions.

This is the recursive coefficient boundary immediately preceding the
strict-positivity argument for the weights of `ladderIterateUp V N ⟨M+1, _⟩`. -/
theorem tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientSuccSiteSum
    (A : V → Bool) (N M : ℕ)
    (hM_succ : M + 1 < Fintype.card V * N + 1)
    (w : magConfigS V N M → ℝ)
    (hcoeff : ∀ τ : magConfigS V N M,
      ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ τ.1 =
        (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)) :
    ∀ τ : magConfigS V N (M + 1),
      ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1 =
        ∑ x : V,
          ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)))) τ.1 := by
  intro τ
  let Ψ : (V → Fin (N + 1)) → ℂ :=
    ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩
  have hΨ_mem :
      Ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    change ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))
    unfold ladderIterateUp
    exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS (V := V) (N := N) M
  have hsector :
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) =
        magSectorRestriction (M := M) Ψ := by
    funext σ
    exact (hcoeff σ).symm
  have hfull :
      magSectorEmbedding
          (fun σ : magConfigS V N M =>
            (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) =
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ := by
    rw [hsector]
    exact magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
      (V := V) (N := N) (M := M) hΨ_mem
  calc
    ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1 =
        ((totalSpinSOpMinus V N).mulVec
          (ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩)) τ.1 := by
      rw [totalSpinSOpMinus_mulVec_ladderIterateUp_interior
        (V := V) (N := N) ⟨M, Nat.lt_of_succ_lt hM_succ⟩ hM_succ]
    _ =
        ((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)))) τ.1 := by
      rw [hfull]
    _ = ∑ x : V,
          ((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)))) τ.1 := by
      exact totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum
        (V := V) (N := N)
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) τ.1

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-iterate successor
Marshall-positive coefficients**: lowerable positive-source coefficient
dominance for the `M`-sector weights produces strictly positive
Marshall-signed weights for the successor iterate
`ladderIterateUp V N ⟨M+1, _⟩`.

This packages the strict-positivity half after the successor site-sum
recursion. The new weight is the signed real part of the successor
coefficient; realness follows from lowering a real Marshall-signed
embedding, and positivity follows from the existing lowerable
coefficient-dominance bridge. -/
theorem tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientSucc_of_positive_source_lowerable_coefficient_lt
    (A : V → Bool) (N M : ℕ)
    (hM_succ : M + 1 < Fintype.card V * N + 1)
    (w : magConfigS V N M → ℝ)
    (hcoeff : ∀ σ : magConfigS V N M,
      ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
        (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))
    (hdominates : ∀ τ : magConfigS V N (M + 1),
      (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
        ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    ∃ w_succ : magConfigS V N (M + 1) → ℝ,
      (∀ τ : magConfigS V N (M + 1), 0 < w_succ τ) ∧
        ∀ τ : magConfigS V N (M + 1),
          ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1 =
            (((marshallSignS A τ.1).re * w_succ τ : ℝ) : ℂ) := by
  let Φ : magConfigS V N M → ℂ :=
    fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)
  let Ψ : (V → Fin (N + 1)) → ℂ :=
    ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩
  have hΨ_mem :
      Ψ ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    change ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))
    unfold ladderIterateUp
    exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS (V := V) (N := N) M
  have hsector :
      Φ = magSectorRestriction (M := M) Ψ := by
    funext σ
    exact (hcoeff σ).symm
  have hfull :
      magSectorEmbedding Φ =
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ := by
    rw [hsector]
    exact magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
      (V := V) (N := N) (M := M) hΨ_mem
  have hsucc_full :
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) =
        ladderIterateUp V N ⟨M + 1, hM_succ⟩ := by
    rw [hfull]
    exact totalSpinSOpMinus_mulVec_ladderIterateUp_interior
      (V := V) (N := N) ⟨M, Nat.lt_of_succ_lt hM_succ⟩ hM_succ
  let w_succ : magConfigS V N (M + 1) → ℝ :=
    fun τ => (marshallSignS A τ.1).re *
      (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).re
  refine ⟨w_succ, ?_, ?_⟩
  · intro τ
    have hpos :
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)))) τ.1).re :=
      tasaki23_lowered_marshall_pos_of_positive_source_lowerable_coefficient_lt
        (V := V) (N := N) A w hdominates τ
    change 0 < (marshallSignS A τ.1).re *
      (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).re
    simpa [Φ] using hpos.trans_eq (by rw [hsucc_full])
  · intro τ
    have hsucc_im :
        (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).im = 0 := by
      rw [← hsucc_full]
      exact totalSpinSOpMinus_mulVec_marshallSignedEmbedding_im_zero
        (V := V) (N := N) A w τ.1
    have hsign_sq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    apply Complex.ext
    · simp only [Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      calc
        (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).re =
            1 * (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).re := by ring
        _ =
            ((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) *
              (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).re := by
            rw [hsign_sq]
        _ =
            (marshallSignS A τ.1).re *
              ((marshallSignS A τ.1).re *
                (ladderIterateUp V N ⟨M + 1, hM_succ⟩ τ.1).re) := by ring
    · simp [hsucc_im]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-iterate top coefficient**:
the top saturated ladder iterate `ladderIterateUp V N ⟨0, _⟩` has the
Marshall-positive coefficient form on the `M = 0` sector, with the constant
weight `1`.

The `M = 0` sector contains only the all-up configuration, whose Marshall sign
is `+1`.  This is the base case for the coefficient induction along the
saturated total-spin lowering ladder. -/
theorem tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientZero
    (A : V → Bool) (N : ℕ) :
    ∃ w0 : magConfigS V N 0 → ℝ,
      (∀ τ : magConfigS V N 0, 0 < w0 τ) ∧
        ∀ τ : magConfigS V N 0,
          ladderIterateUp V N ⟨0, Nat.succ_pos (Fintype.card V * N)⟩ τ.1 =
            (((marshallSignS A τ.1).re * w0 τ : ℝ) : ℂ) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro τ
    norm_num
  · intro τ
    have hτ : τ.1 = allAlignedConfigS V N 0 :=
      magConfigS_zero_eq_allAlignedConfigS τ
    calc
      ladderIterateUp V N ⟨0, Nat.succ_pos (Fintype.card V * N)⟩ τ.1 =
          allAlignedStateS V N (0 : Fin (N + 1)) τ.1 := by
        simp [ladderIterateUp]
      _ = 1 := by
        rw [hτ]
        simp [allAlignedStateS]
      _ = (((marshallSignS A τ.1).re * (1 : ℝ) : ℝ) : ℂ) := by
        rw [hτ]
        have hsign : marshallSignS A (allAlignedConfigS V N 0) = 1 := by
          simpa [allAlignedConfigS] using
            (marshallSignS_const_zero (V := V) (N := N) A)
        simp [hsign]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-iterate coefficient
induction boundary**: a positive coefficient formula at the top sector,
together with lowerable positive-source coefficient dominance at every
successor step, supplies strictly positive Marshall-signed coefficients for
every saturated ladder iterate.

This packages the successor theorem into the whole ladder chain.  The base
case is the all-up sector supplied by a separate normalization input, and the
successor step is exactly
`tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientSucc_of_positive_source_lowerable_coefficient_lt`. -/
theorem tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_zero_and_successor_dominance
    (A : V → Bool) (N : ℕ)
    (hzero :
      ∃ w0 : magConfigS V N 0 → ℝ,
        (∀ τ : magConfigS V N 0, 0 < w0 τ) ∧
          ∀ τ : magConfigS V N 0,
            ladderIterateUp V N ⟨0, Nat.succ_pos (Fintype.card V * N)⟩ τ.1 =
              (((marshallSignS A τ.1).re * w0 τ : ℝ) : ℂ))
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    ∀ M : ℕ, (hM_range : M < Fintype.card V * N + 1) →
      ∃ w : magConfigS V N M → ℝ,
        (∀ τ : magConfigS V N M, 0 < w τ) ∧
          ∀ τ : magConfigS V N M,
            ladderIterateUp V N ⟨M, hM_range⟩ τ.1 =
              (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ) := by
  intro M
  induction M with
  | zero =>
      intro hM_range
      simpa using hzero
  | succ M ih =>
      intro hM_succ
      obtain ⟨w, hw_pos, hcoeff⟩ := ih (Nat.lt_of_succ_lt hM_succ)
      exact
        tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientSucc_of_positive_source_lowerable_coefficient_lt
          (V := V) (A := A) (N := N) (M := M) hM_succ w hcoeff
          (hdominates M hM_succ w hcoeff)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-iterate coefficient
family from successor dominance**: lowerable positive-source coefficient
dominance at every successor step is enough to construct strictly positive
Marshall-signed coefficients for every saturated ladder iterate.

This is the closed induction form: the top-sector coefficient is discharged by
`tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientZero`,
and all remaining sectors are handled by the successor dominance step. -/
theorem tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_successor_dominance
    (A : V → Bool) (N : ℕ)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    ∀ M : ℕ, (hM_range : M < Fintype.card V * N + 1) →
      ∃ w : magConfigS V N M → ℝ,
        (∀ τ : magConfigS V N M, 0 < w τ) ∧
          ∀ τ : magConfigS V N M,
            ladderIterateUp V N ⟨M, hM_range⟩ τ.1 =
              (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ) :=
  tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_zero_and_successor_dominance
    (V := V) A N
    (tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientZero
      (V := V) A N)
    hdominates

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 saturated-ladder-iterate coefficient
family from explicit lowerable dominance**: dominance of the attached sums of
explicit lowerable positive-source predecessor coefficients supplies the
successor-dominance input for the closed coefficient induction. -/
theorem tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_lowerable_attach_sum_dominance
    (A : V → Bool) (N : ℕ)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    ∀ M : ℕ, (hM_range : M < Fintype.card V * N + 1) →
      ∃ w : magConfigS V N M → ℝ,
        (∀ τ : magConfigS V N M, 0 < w τ) ∧
          ∀ τ : magConfigS V N M,
            ladderIterateUp V N ⟨M, hM_range⟩ τ.1 =
              (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ) :=
  tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_successor_dominance
    (V := V) A N
    (fun M hM_succ w hcoeff τ =>
      tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
        (V := V) (N := N) A w τ (hdominates M hM_succ w hcoeff τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-iterate coefficient
callback from successor dominance**: the closed coefficient induction supplies
the left outside-sector coefficient callback once the saturated
Heisenberg eigenvalue is represented by a real scalar. -/
theorem tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_successor_dominance
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback
      (V := V) A J N := by
  intro M _ hM_left
  have hA_card :
      (Finset.univ.filter (fun x : V => A x = true)).card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using
      (Finset.card_filter_le (s := (Finset.univ : Finset V)) (p := fun x : V => A x = true))
  have hmin_card :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) ≤
        Fintype.card V := by
    exact le_trans (Nat.min_le_left _ _) hA_card
  have hM_range : M < Fintype.card V * N + 1 := by
    exact Nat.lt_succ_of_lt
      (lt_of_lt_of_le hM_left (Nat.mul_le_mul_right N hmin_card))
  obtain ⟨μsat, hμsat_eq⟩ := hμsat
  obtain ⟨w, hw_pos, hcoeff⟩ :=
    tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_successor_dominance
      (V := V) A N hdominates M hM_range
  exact ⟨hM_range, μsat, w, hμsat_eq, hw_pos, hcoeff⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-iterate coefficient
callback from explicit lowerable dominance**: left-side callback wrapper using
attached sums of explicit lowerable predecessor coefficients as the remaining
coefficient-dominance input. -/
theorem tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_lowerable_attach_sum_dominance
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback
      (V := V) A J N :=
  tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_successor_dominance
    (V := V) A (J := J) N hμsat
    (fun M hM_succ w hcoeff τ =>
      tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
        (V := V) (N := N) A w τ (hdominates M hM_succ w hcoeff τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-iterate coefficient
callback from successor dominance**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_successor_dominance`.
The sector nonemptiness supplies the global bound `M ≤ |V| * N`, hence the
range proof needed by `ladderIterateUp`. -/
theorem tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_successor_dominance
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient w τ x) :
    tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback
      (V := V) A J N := by
  intro M hM_nonempty _hM_right
  let τ : magConfigS V N M := Classical.choice hM_nonempty
  have hM_le : M ≤ Fintype.card V * N := by
    have hτ_le : magSumS τ.1 ≤ Fintype.card V * N := magSumS_le τ.1
    simpa [τ.2] using hτ_le
  have hM_range : M < Fintype.card V * N + 1 := Nat.lt_succ_of_le hM_le
  obtain ⟨μsat, hμsat_eq⟩ := hμsat
  obtain ⟨w, hw_pos, hcoeff⟩ :=
    tasaki23OutsideGroundSaturatedLadderIterateMarshallPositiveCoefficientFamily_of_successor_dominance
      (V := V) A N hdominates M hM_range
  exact ⟨hM_range, μsat, w, hμsat_eq, hw_pos, hcoeff⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-iterate coefficient
callback from explicit lowerable dominance**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_lowerable_attach_sum_dominance`. -/
theorem tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_lowerable_attach_sum_dominance
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback
      (V := V) A J N :=
  tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_successor_dominance
    (V := V) A (J := J) N hμsat
    (fun M hM_succ w hcoeff τ =>
      tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
        (V := V) (N := N) A w τ (hdominates M hM_succ w hcoeff τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left singleton-span iterate reference from a
Marshall-positive ladder iterate equality**: equality with the sector
`ladderIterateUp` vector places the reference embedding in its singleton
span. -/
theorem tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback_of_marshall_positive_reference
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback
        (V := V) A J N) :
    tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N := by
  intro M _ hM_left
  obtain ⟨hM_range, μsat, w, hμsat, hw_pos, hw_eq⟩ := hleft M hM_left
  refine ⟨hM_range, μsat, w, hμsat, hw_pos, ?_⟩
  rw [hw_eq]
  exact Submodule.subset_span (Set.mem_singleton _)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right singleton-span iterate reference from a
Marshall-positive ladder iterate equality**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback_of_marshall_positive_reference`. -/
theorem tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback_of_marshall_positive_reference
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hright :
      tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveReferenceCallback
        (V := V) A J N) :
    tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N := by
  intro M _ hM_right
  obtain ⟨hM_range, μsat, w, hμsat, hw_pos, hw_eq⟩ := hright M hM_right
  refine ⟨hM_range, μsat, w, hμsat, hw_pos, ?_⟩
  rw [hw_eq]
  exact Submodule.subset_span (Set.mem_singleton _)

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- Expanding the callback target with a dependent singleton ladder span needs extra reduction.
/-- **Tasaki §2.5 Theorem 2.3 left saturated ladder reference from a sector
ladder iterate reference**: the singleton span of the sector ladder iterate is
contained in the span of all saturated ladder iterates. -/
theorem tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N := by
  intro M _ hM_left
  obtain ⟨hM_range, μsat, w, hμsat, hw_pos, hw_single⟩ := hleft M hM_left
  refine ⟨μsat, w, hμsat, hw_pos, ?_⟩
  exact (ladderIterateUp_singleton_span_le_span_range (V := V) N ⟨M, hM_range⟩)
    hw_single

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- Expanding the callback target with a dependent singleton ladder span needs extra reduction.
/-- **Tasaki §2.5 Theorem 2.3 right saturated ladder reference from a sector
ladder iterate reference**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference`. -/
theorem tasaki23OutsideGroundRightSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hright :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N := by
  intro M _ hM_right
  obtain ⟨hM_range, μsat, w, hμsat, hw_pos, hw_single⟩ := hright M hM_right
  refine ⟨μsat, w, hμsat, hw_pos, ?_⟩
  exact (ladderIterateUp_singleton_span_le_span_range (V := V) N ⟨M, hM_range⟩)
    hw_single

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated source-energy from joint
source**: the saturated joint source-vector input gives the
`H_J`-eigenvalue equation at the saturated ferromagnet energy.  Comparing it
with the existing source eigenvector equation and using strict
Marshall-positivity to rule out the zero vector identifies the scalar source
energy. -/
theorem tasaki23OutsideGroundLeftSaturatedEnergySourceCallback_of_saturated_joint_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftSaturatedEnergySourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hjoint : Φ ∈ saturatedFerromagnetJointEigenspace (V := V) J N :=
    hleft M hM_left hμM_lt hv_pos hΦ
  have hHmem :
      Φ ∈ Module.End.eigenspace (heisenbergHamiltonianS J N).mulVecLin
        (saturatedFerromagnetEigenvalueS (V := V) J N) :=
    (Submodule.mem_inf.mp hjoint).1
  have hH : (heisenbergHamiltonianS J N).mulVec Φ =
      saturatedFerromagnetEigenvalueS (V := V) J N • Φ := by
    rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hHmem
  have hsmul : (μM : ℂ) • Φ =
      saturatedFerromagnetEigenvalueS (V := V) J N • Φ :=
    hΦ.symm.trans hH
  by_contra hne
  have hΦ_ne : Φ ≠ 0 :=
    tasaki23_marshallPositive_magSectorEmbedding_ne_zero (V := V) A hv_pos
  apply hΦ_ne
  have hzero :
      ((μM : ℂ) - saturatedFerromagnetEigenvalueS (V := V) J N) • Φ = 0 := by
    rw [sub_smul, hsmul, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated source-energy from joint
source**: the saturated joint source-vector input gives the
`H_J`-eigenvalue equation at the saturated ferromagnet energy.  Comparing it
with the existing source eigenvector equation and using strict
Marshall-positivity to rule out the zero vector identifies the scalar source
energy. -/
theorem tasaki23OutsideGroundRightSaturatedEnergySourceCallback_of_saturated_joint_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightSaturatedEnergySourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hjoint : Φ ∈ saturatedFerromagnetJointEigenspace (V := V) J N :=
    hright M hM_right hμM_lt hv_pos hΦ
  have hHmem :
      Φ ∈ Module.End.eigenspace (heisenbergHamiltonianS J N).mulVecLin
        (saturatedFerromagnetEigenvalueS (V := V) J N) :=
    (Submodule.mem_inf.mp hjoint).1
  have hH : (heisenbergHamiltonianS J N).mulVec Φ =
      saturatedFerromagnetEigenvalueS (V := V) J N • Φ := by
    rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hHmem
  have hsmul : (μM : ℂ) • Φ =
      saturatedFerromagnetEigenvalueS (V := V) J N • Φ :=
    hΦ.symm.trans hH
  by_contra hne
  have hΦ_ne : Φ ≠ 0 :=
    tasaki23_marshallPositive_magSectorEmbedding_ne_zero (V := V) A hv_pos
  apply hΦ_ne
  have hzero :
      ((μM : ℂ) - saturatedFerromagnetEigenvalueS (V := V) J N) • Φ = 0 := by
    rw [sub_smul, hsmul, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-Casimir source from joint
source**: the saturated joint source-vector input contains the
`(Ŝ_tot)^2` eigenspace component, which is exactly the left saturated-Casimir
source callback after expanding eigenspace membership. -/
theorem tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_saturated_joint_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hjoint : Φ ∈ saturatedFerromagnetJointEigenspace (V := V) J N :=
    hleft M hM_left hμM_lt hv_pos hΦ
  have hCas :
      Φ ∈ Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) :=
    (Submodule.mem_inf.mp hjoint).2
  rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hCas

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-Casimir source from joint
source**: the saturated joint source-vector input contains the
`(Ŝ_tot)^2` eigenspace component, which is exactly the right
saturated-Casimir source callback after expanding eigenspace membership. -/
theorem tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_saturated_joint_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hjoint : Φ ∈ saturatedFerromagnetJointEigenspace (V := V) J N :=
    hright M hM_right hμM_lt hv_pos hΦ
  have hCas :
      Φ ∈ Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
      (saturatedFerromagnetCasimirEigenvalueS V N) :=
    (Submodule.mem_inf.mp hjoint).2
  rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hCas

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-joint source from a
saturated-joint reference**: a Marshall-positive saturated joint reference in
the same left outside sector forces every Marshall-positive source
eigenvector to be the same sector ground state up to a positive scalar.
Consequently the source vector also lies in the saturated-ferromagnet joint
eigenspace.

This is the source-vector/eigenvalue bridge from the reference-vector API to
the left saturated-joint source callback. -/
theorem tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_joint_reference
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v _hμM_lt hv_pos hΦ
  obtain ⟨μsat, w, hμsat, hw_pos, hw_joint⟩ := hleft_ref M hM_left
  let Φv : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  let Φw : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)
  have hΦv_sec_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φv =
        (μM : ℂ) • Φv := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦ
    rwa [magSectorRestriction_magSectorEmbedding] at hrestrict
  have hΦv_sec_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μM • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦv_sec_complex
    simpa [Φv] using hre
  have hHw_mem :
      magSectorEmbedding Φw ∈
        Module.End.eigenspace (heisenbergHamiltonianS J N).mulVecLin
          (saturatedFerromagnetEigenvalueS (V := V) J N) :=
    (Submodule.mem_inf.mp hw_joint).1
  have hHw_full :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φw) =
        (μsat : ℂ) • magSectorEmbedding Φw := by
    have h :=
      (show (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φw) =
          saturatedFerromagnetEigenvalueS (V := V) J N • magSectorEmbedding Φw by
        rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hHw_mem)
    rwa [← hμsat] at h
  have hΦw_sec_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φw =
        (μsat : ℂ) • Φw := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hHw_full
    rwa [magSectorRestriction_magSectorEmbedding] at hrestrict
  have hΦw_sec_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * w τ) =
        μsat • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * w τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦw_sec_complex
    simpa [Φw] using hre
  have hΦv_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v τ) := fun τ => by
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos τ
  have hΦw_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * w τ) := fun τ => by
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hw_pos τ
  have hμ_eq : μsat = μM :=
    marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N hJ_real hJ_real' hΦw_sec_real hΦw_marshall_pos
      hΦv_sec_real hΦv_marshall_pos
  have hΦv_sec_real_sat :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μsat • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    rw [hμ_eq]
    exact hΦv_sec_real
  obtain ⟨r, _hr_pos, hrel⟩ :=
    marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hΦw_sec_real hΦw_marshall_pos
      hΦv_sec_real_sat hΦv_marshall_pos
  have hfull_eq : magSectorEmbedding Φv = (r : ℂ) • magSectorEmbedding Φw := by
    funext σ
    by_cases hσ : magSumS σ = M
    · let τ : magConfigS V N M := ⟨σ, hσ⟩
      have hτ := congrFun hrel τ
      change (marshallSignS A τ.1).re * v τ =
        r * ((marshallSignS A τ.1).re * w τ) at hτ
      rw [Pi.smul_apply, magSectorEmbedding_apply_of_mem Φv hσ,
        magSectorEmbedding_apply_of_mem Φw hσ]
      change (((marshallSignS A σ).re * v τ : ℝ) : ℂ) =
        (r : ℂ) * (((marshallSignS A σ).re * w τ : ℝ) : ℂ)
      exact_mod_cast hτ
    · rw [Pi.smul_apply, magSectorEmbedding_apply_of_not_mem Φv hσ,
        magSectorEmbedding_apply_of_not_mem Φw hσ, smul_zero]
  rw [hfull_eq]
  exact Submodule.smul_mem _ _ hw_joint

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-joint source from a
saturated-joint reference**: right-side analogue of
`tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_joint_reference`.
The proof uses sector eigenvalue uniqueness to identify the source energy
with the saturated reference energy, then sector eigenvector uniqueness to
show the source embedding is a positive scalar multiple of the saturated
joint reference. -/
theorem tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_joint_reference
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  obtain ⟨μsat, w, hμsat, hw_pos, hw_joint⟩ := hright_ref M hM_right
  let Φv : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  let Φw : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * w τ : ℝ) : ℂ)
  have hΦv_sec_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φv =
        (μM : ℂ) • Φv := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦ
    rwa [magSectorRestriction_magSectorEmbedding] at hrestrict
  have hΦv_sec_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μM • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦv_sec_complex
    simpa [Φv] using hre
  have hHw_mem :
      magSectorEmbedding Φw ∈
        Module.End.eigenspace (heisenbergHamiltonianS J N).mulVecLin
          (saturatedFerromagnetEigenvalueS (V := V) J N) :=
    (Submodule.mem_inf.mp hw_joint).1
  have hHw_full :
      (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φw) =
        (μsat : ℂ) • magSectorEmbedding Φw := by
    have h :=
      (show (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φw) =
          saturatedFerromagnetEigenvalueS (V := V) J N • magSectorEmbedding Φw by
        rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hHw_mem)
    rwa [← hμsat] at h
  have hΦw_sec_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φw =
        (μsat : ℂ) • Φw := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hHw_full
    rwa [magSectorRestriction_magSectorEmbedding] at hrestrict
  have hΦw_sec_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * w τ) =
        μsat • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * w τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦw_sec_complex
    simpa [Φw] using hre
  have hΦv_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v τ) := fun τ => by
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos τ
  have hΦw_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * w τ) := fun τ => by
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hw_pos τ
  have hμ_eq : μsat = μM :=
    marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N hJ_real hJ_real' hΦw_sec_real hΦw_marshall_pos
      hΦv_sec_real hΦv_marshall_pos
  have hΦv_sec_real_sat :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μsat • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    rw [hμ_eq]
    exact hΦv_sec_real
  obtain ⟨r, _hr_pos, hrel⟩ :=
    marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hΦw_sec_real hΦw_marshall_pos
      hΦv_sec_real_sat hΦv_marshall_pos
  have hfull_eq : magSectorEmbedding Φv = (r : ℂ) • magSectorEmbedding Φw := by
    funext σ
    by_cases hσ : magSumS σ = M
    · let τ : magConfigS V N M := ⟨σ, hσ⟩
      have hτ := congrFun hrel τ
      change (marshallSignS A τ.1).re * v τ =
        r * ((marshallSignS A τ.1).re * w τ) at hτ
      rw [Pi.smul_apply, magSectorEmbedding_apply_of_mem Φv hσ,
        magSectorEmbedding_apply_of_mem Φw hσ]
      change (((marshallSignS A σ).re * v τ : ℝ) : ℂ) =
        (r : ℂ) * (((marshallSignS A σ).re * w τ : ℝ) : ℂ)
      exact_mod_cast hτ
    · rw [Pi.smul_apply, magSectorEmbedding_apply_of_not_mem Φv hσ,
        magSectorEmbedding_apply_of_not_mem Φw hσ, smul_zero]
  rw [hfull_eq]
  exact Submodule.smul_mem _ _ hw_joint

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-joint source from saturated
eigen-source callbacks**: the saturated-Heisenberg source callback supplies
the `H_J` eigenspace half and the saturated-Casimir source callback supplies
the `(Ŝ_tot)^2` eigenspace half of
`saturatedFerromagnetJointEigenspace`. -/
theorem tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_eigen_sources
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleftH :
      tasaki23OutsideGroundLeftSaturatedHeisenbergSourceCallback (V := V) A J N c)
    (hleftCas :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hH : (heisenbergHamiltonianS J N).mulVec Φ =
      saturatedFerromagnetEigenvalueS (V := V) J N • Φ :=
    hleftH M hM_left hμM_lt hv_pos hΦ
  have hCas : (totalSpinSSquared V N).mulVec Φ =
      saturatedFerromagnetCasimirEigenvalueS V N • Φ :=
    hleftCas M hM_left hμM_lt hv_pos hΦ
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact hH
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact hCas

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-joint source from saturated
eigen-source callbacks**: the saturated-Heisenberg source callback supplies
the `H_J` eigenspace half and the saturated-Casimir source callback supplies
the `(Ŝ_tot)^2` eigenspace half of
`saturatedFerromagnetJointEigenspace`. -/
theorem tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_eigen_sources
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hrightH :
      tasaki23OutsideGroundRightSaturatedHeisenbergSourceCallback (V := V) A J N c)
    (hrightCas :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hH : (heisenbergHamiltonianS J N).mulVec Φ =
      saturatedFerromagnetEigenvalueS (V := V) J N • Φ :=
    hrightH M hM_right hμM_lt hv_pos hΦ
  have hCas : (totalSpinSSquared V N).mulVec Φ =
      saturatedFerromagnetCasimirEigenvalueS V N • Φ :=
    hrightCas M hM_right hμM_lt hv_pos hΦ
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact hH
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact hCas

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-ladder-span source from
saturated joint source**: the saturated-ferromagnet joint eigenspace equals
the span of `ladderIterateUp`, so a left outside-sector source in that joint
eigenspace has the concrete saturated-ladder-span source property. -/
theorem tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback_of_saturated_joint_source
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  have hjoint :
      magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        saturatedFerromagnetJointEigenspace (V := V) J N :=
    hleft M hM_left hμM_lt hv_pos hΦ
  rwa [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp
    (V := V) (N := N) J] at hjoint

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-ladder-span source from
saturated joint source**: the saturated-ferromagnet joint eigenspace equals
the span of `ladderIterateUp`, so a right outside-sector source in that joint
eigenspace has the concrete saturated-ladder-span source property. -/
theorem tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback_of_saturated_joint_source
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  have hjoint :
      magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        saturatedFerromagnetJointEigenspace (V := V) J N :=
    hright M hM_right hμM_lt hv_pos hΦ
  rwa [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp
    (V := V) (N := N) J] at hjoint

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left saturated-Casimir source from ladder
span**: the maximum-Casimir eigenspace equals the saturated ladder span,
so a left outside-sector source in that span has the saturated
total-Casimir eigenvalue. -/
theorem tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_ladder_span_source
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedLadderSpanSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  have hspan :
      magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range (ladderIterateUp V N)) :=
    hleft M hM_left hμM_lt hv_pos hΦ
  have heig :
      magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N) := by
    rwa [totalSpinSSquaredEigenspace_max_eq_span_ladderIterateUp (V := V) (N := N)]
  rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at heig

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right saturated-Casimir source from ladder
span**: the maximum-Casimir eigenspace equals the saturated ladder span,
so a right outside-sector source in that span has the saturated
total-Casimir eigenvalue. -/
theorem tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_ladder_span_source
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightSaturatedLadderSpanSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  have hspan :
      magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range (ladderIterateUp V N)) :=
    hright M hM_right hμM_lt hv_pos hΦ
  have heig :
      magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
          (saturatedFerromagnetCasimirEigenvalueS V N) := by
    rwa [totalSpinSSquaredEigenspace_max_eq_span_ladderIterateUp (V := V) (N := N)]
  rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at heig

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left Casimir full reach from saturated
Casimir**: the left saturated-Casimir source callback supplies the existing
iterated-ladder Casimir full-reach callback by choosing the left endpoint as
target and using the saturated endpoint-mismatch arithmetic for every
intermediate lowering step. -/
theorem tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback_of_saturated_casimir_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  let K :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
      N
  have hK_mem : K ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [K] using tasaki23GroundStateSectors_left_mem (V := V) A N
  have hK_le_card : K ≤ Fintype.card V * N :=
    tasaki23GroundStateSectors_le_card_mul (V := V) A N hK_mem
  have hM_le_K : M ≤ K := Nat.le_of_lt hM_left
  refine ⟨K, hK_mem, magConfigS_nonempty_of_le_card_mul (V := V) (N := N) hK_le_card,
    K - M, ?_, saturatedFerromagnetCasimirEigenvalueS V N, ?_, ?_⟩
  · omega
  · simpa [K] using hleft M hM_left hμM_lt hv_pos hΦ
  · intro j hj
    have hMj_lt_K : M + j < K := by omega
    convert
      saturatedFerromagnetCasimirEigenvalueS_ne_lowering_kernel_value_of_lt_card_mul
        (V := V) N (M + j) (Nat.lt_of_lt_of_le hMj_lt_K hK_le_card) using 1
    · norm_num [Nat.cast_add]
      ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right Casimir full reach from saturated
Casimir**: the right saturated-Casimir source callback supplies the existing
iterated-ladder Casimir full-reach callback by choosing the right endpoint as
target and using the saturated endpoint-mismatch arithmetic for every
intermediate raising step. -/
theorem tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback_of_saturated_casimir_source
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  let K :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
      N
  have hK_mem : K ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [K] using tasaki23GroundStateSectors_right_mem (V := V) A N
  have hK_le_card : K ≤ Fintype.card V * N :=
    tasaki23GroundStateSectors_le_card_mul (V := V) A N hK_mem
  obtain ⟨τ⟩ := (inferInstance : Nonempty (magConfigS V N M))
  have hM_le_card : M ≤ Fintype.card V * N := by
    simpa [τ.2] using magSumS_le (Λ := V) (N := N) τ.1
  refine ⟨K, hK_mem, magConfigS_nonempty_of_le_card_mul (V := V) (N := N) hK_le_card,
    M - K, ?_, saturatedFerromagnetCasimirEigenvalueS V N, ?_, ?_⟩
  · omega
  · simpa [K] using hright M hM_right hμM_lt hv_pos hΦ
  · intro j hj
    have hK_lt_M_sub_j : K < M - j := by omega
    have hM_sub_j_pos : 0 < M - j := by omega
    have hM_sub_j_le : M - j ≤ Fintype.card V * N := by omega
    exact fun hEq => by
      apply
        saturatedFerromagnetCasimirEigenvalueS_ne_raising_kernel_value_of_pos_of_le_card_mul
          (V := V) N (M - j) hM_sub_j_pos hM_sub_j_le
      convert hEq using 1
      · norm_num [Nat.cast_sub (show j ≤ M by omega)]
        ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left outside-sector admissible-reach
callback**: for an outside-sector Marshall-positive representative below
the left endpoint of `tasaki23GroundStateSectors A N`, the lowering ladder
direction reaches a nonzero eigenvector at the same eigenvalue in some
admissible sector. -/
def tasaki23OutsideGroundLeftAdmissibleReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Φ : magConfigS V N K → ℂ,
          Φ ≠ 0 ∧
          (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec Φ =
            (μM : ℂ) • Φ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right outside-sector admissible-reach
callback**: for an outside-sector Marshall-positive representative above
the right endpoint of `tasaki23GroundStateSectors A N`, the raising ladder
direction reaches a nonzero eigenvector at the same eigenvalue in some
admissible sector. -/
def tasaki23OutsideGroundRightAdmissibleReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Φ : magConfigS V N K → ℂ,
          Φ ≠ 0 ∧
          (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec Φ =
            (μM : ℂ) • Φ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector admissible reach from side
callbacks**: the full outside-sector reach callback follows by splitting an
outside magnetization sector into the left-of-interval and right-of-interval
cases, then applying the corresponding directional ladder-reach callback. -/
theorem tasaki23OutsideGroundAdmissibleReachCallback_of_side_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftAdmissibleReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightAdmissibleReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c := by
  intro M _ hM_out μM v hμM_lt hv_pos hΦ
  rcases
      (tasaki23GroundStateSectors_not_mem_iff_lt_left_or_right_lt
        (V := V) A N M).mp hM_out with hM_left | hM_right
  · exact hleft M hM_left hμM_lt hv_pos hΦ
  · exact hright M hM_right hμM_lt hv_pos hΦ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector reach from full reach**:
restricting the full-space ladder output in an admissible magnetization
subspace gives the sector-coordinate eigenvector required by
`tasaki23OutsideGroundAdmissibleReachCallback`.  Nonzeroness is preserved
because a vector in the target `magSubspaceS` is recovered by embedding its
sector restriction. -/
theorem tasaki23OutsideGroundAdmissibleReachCallback_of_full_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hfull :
      tasaki23OutsideGroundAdmissibleFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c := by
  intro M _ hM_out μM v hμM_lt hv_pos hΦ
  obtain ⟨K, hK_mem, hK_nonempty, Ψ, hΨ_ne, hΨ_mag, hΨ_eigen⟩ :=
    hfull M hM_out hμM_lt hv_pos hΦ
  refine ⟨K, hK_mem, hK_nonempty, magSectorRestriction (M := K) Ψ, ?_, ?_⟩
  · intro hrestrict_zero
    have hroundtrip :
        magSectorEmbedding (magSectorRestriction (M := K) Ψ) = Ψ :=
      magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS
        (V := V) (N := N) (M := K) hΨ_mag
    rw [hrestrict_zero] at hroundtrip
    have hzero_embed :
        magSectorEmbedding (0 : magConfigS V N K → ℂ) =
          (0 : (V → Fin (N + 1)) → ℂ) := by
      funext σ
      unfold magSectorEmbedding
      by_cases hσ : magSumS σ = K
      · rw [dif_pos hσ]
        rfl
      · rw [dif_neg hσ]
        rfl
    rw [hzero_embed] at hroundtrip
    exact hΨ_ne hroundtrip.symm
  · exact
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (V := V) (N := N) (M := K) J hΨ_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 full reach from iterated total-spin ladders**:
left and right iterated ladder non-zeroness callbacks supply the full-space
admissible-reach callback.  The proof uses the commutation of the Heisenberg
Hamiltonian with `(Ŝ^-_tot)^k` and `(Ŝ^+_tot)^k`, plus the corresponding
magnetization-subspace shift lemmas, to turn the nonzero ladder output into
the full-space reached eigenvector required by
`tasaki23OutsideGroundAdmissibleFullReachCallback`. -/
theorem tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderFullReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundAdmissibleFullReachCallback (V := V) A J N c := by
  intro M _ hM_out μM v hμM_lt hv_pos hΦ
  let ΨM : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hΨM_eigen :
      (heisenbergHamiltonianS J N).mulVec ΨM = (μM : ℂ) • ΨM := by
    simpa [ΨM] using hΦ
  have hΨM_mag :
      ΨM ∈ magSubspaceS V N
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    simpa [ΨM] using
      magSectorEmbedding_mem_magSubspaceS
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  rcases
      (tasaki23GroundStateSectors_not_mem_iff_lt_left_or_right_lt
        (V := V) A N M).mp hM_out with hM_left | hM_right
  · obtain ⟨K, hK_mem, hK_nonempty, k, hK_eq, hpow_ne⟩ :=
      hleft M hM_left hμM_lt hv_pos hΦ
    refine ⟨K, hK_mem, hK_nonempty,
      ((totalSpinSOpMinus V N) ^ k).mulVec ΨM, ?_, ?_, ?_⟩
    · simpa [ΨM] using hpow_ne
    · have hmag :=
        totalSpinSOpMinus_pow_mulVec_mem_magSubspaceS_of_mem
          (V := V) (N := N) k hΨM_mag
      convert hmag using 1
      rw [hK_eq]
      push_cast
      ring_nf
    · exact
        heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_of_eigenvec
          (V := V) J N k hΨM_eigen
  · obtain ⟨K, hK_mem, hK_nonempty, k, hM_eq, hpow_ne⟩ :=
      hright M hM_right hμM_lt hv_pos hΦ
    refine ⟨K, hK_mem, hK_nonempty,
      ((totalSpinSOpPlus V N) ^ k).mulVec ΨM, ?_, ?_, ?_⟩
    · simpa [ΨM] using hpow_ne
    · have hmag :=
        totalSpinSOpPlus_pow_mulVec_mem_magSubspaceS_of_mem
          (V := V) (N := N) k hΨM_mag
      convert hmag using 1
      rw [hM_eq]
      push_cast
      ring_nf
    · exact
        heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_pow_of_eigenvec
          (V := V) J N k hΨM_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left iterated full reach from Casimir
avoidance**: the left Casimir callback discharges the left iterated
ladder non-zeroness callback by applying the local iterated lowering
non-vanishing lemma to the Marshall-positive source vector. -/
theorem tasaki23OutsideGroundLeftIteratedLadderFullReachCallback_of_iterated_ladder_casimir_callback
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundLeftIteratedLadderFullReachCallback (V := V) A J N c := by
  intro M _ hM_left μM v hμM_lt hv_pos hΦ
  let ΨM : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  obtain ⟨K, hK_mem, hK_nonempty, k, hK_eq, γ, hΨM_cas, hγ_ne⟩ :=
    hleft M hM_left hμM_lt hv_pos hΦ
  refine ⟨K, hK_mem, hK_nonempty, k, hK_eq, ?_⟩
  have hΨM_mag :
      ΨM ∈ magSubspaceS V N
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    simpa [ΨM] using
      magSectorEmbedding_mem_magSubspaceS
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hΨM_ne : ΨM ≠ 0 := by
    simpa [ΨM] using
      tasaki23_marshallPositive_magSectorEmbedding_ne_zero (V := V) A hv_pos
  have hΨM_cas' :
      (totalSpinSSquared V N).mulVec ΨM = γ • ΨM := by
    simpa [ΨM] using hΨM_cas
  simpa [ΨM] using
    totalSpinSOpMinus_pow_mulVec_ne_zero_of_casimir_ne_kernel_values
      (V := V) (N := N) k hΨM_mag hΨM_cas' hΨM_ne hγ_ne

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right iterated full reach from Casimir
avoidance**: the right Casimir callback discharges the right iterated
ladder non-zeroness callback by applying the local iterated raising
non-vanishing lemma to the Marshall-positive source vector. -/
theorem tasaki23OutsideGroundRightIteratedLadderFullReachCallback_of_iterated_ladder_casimir_callback
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundRightIteratedLadderFullReachCallback (V := V) A J N c := by
  intro M _ hM_right μM v hμM_lt hv_pos hΦ
  let ΨM : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding
      (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  obtain ⟨K, hK_mem, hK_nonempty, k, hM_eq, γ, hΨM_cas, hγ_ne⟩ :=
    hright M hM_right hμM_lt hv_pos hΦ
  refine ⟨K, hK_mem, hK_nonempty, k, hM_eq, ?_⟩
  have hΨM_mag :
      ΨM ∈ magSubspaceS V N
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
    simpa [ΨM] using
      magSectorEmbedding_mem_magSubspaceS
        (fun τ : magConfigS V N M =>
          (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
  have hΨM_ne : ΨM ≠ 0 := by
    simpa [ΨM] using
      tasaki23_marshallPositive_magSectorEmbedding_ne_zero (V := V) A hv_pos
  have hΨM_cas' :
      (totalSpinSSquared V N).mulVec ΨM = γ • ΨM := by
    simpa [ΨM] using hΨM_cas
  simpa [ΨM] using
    totalSpinSOpPlus_pow_mulVec_ne_zero_of_casimir_ne_kernel_values
      (V := V) (N := N) k hΨM_mag hΨM_cas' hΨM_ne hγ_ne

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 full reach from iterated Casimir
avoidance**: left and right Casimir callbacks discharge the iterated
ladder full-reach callbacks and hence supply the full-space admissible
reach callback. -/
theorem tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_casimir_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundAdmissibleFullReachCallback (V := V) A J N c :=
  tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_callbacks
    (V := V) A (J := J) N c
    (tasaki23OutsideGroundLeftIteratedLadderFullReachCallback_of_iterated_ladder_casimir_callback
      (V := V) A (J := J) N c hleft)
    (tasaki23OutsideGroundRightIteratedLadderFullReachCallback_of_iterated_ladder_casimir_callback
      (V := V) A (J := J) N c hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector lower family from sector
minimality**: a sector-minimality callback immediately supplies the
outside-sector ground-energy lower family.  The Marshall-positive
outside-sector representative is restricted to its magnetization sector,
where sector minimality gives `μ ≤ μM`. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_min : tasaki23SectorMinimalityCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c := by
  intro μ hcommon M _ hM_out μM v _hμM_lt hv_pos hΦ
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μM : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦ
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hΦ_ne : Φ ≠ 0 := by
    intro hzero
    obtain ⟨τ⟩ := (inferInstance : Nonempty (magConfigS V N M))
    have hτ_complex : (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ) = 0 := by
      simpa [Φ] using congrFun hzero τ
    have hτ_real : (marshallSignS A τ.1).re * v τ = 0 := by
      exact_mod_cast hτ_complex
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv := hv_pos τ
    rcases mul_eq_zero.mp hτ_real with ha | hv_zero
    · nlinarith
    · nlinarith
  exact hsector_min hcommon M hΦ_ne hsector_complex

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real-sector lower bound on admissible
sectors**: once the common-energy chain has produced a Marshall-positive
sector representative at energy `μ` in an admissible sector, the
Perron-Frobenius shifted-matrix comparison makes `μ` a lower bound for
every real-form eigenvalue in that same sector.

This proves the real-sector spectral-minimality callback on the
`tasaki23GroundStateSectors` interval; sectors outside the interval remain
the separate global spectral input for the final Theorem 2.3 wrapper. -/
theorem tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ) :
    ∀ M : ℕ, M ∈ tasaki23GroundStateSectors (V := V) A N →
      [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
          φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
          μ ≤ μ' := by
  intro M hM _ μ' φ hφ_ne hφ_eigen
  obtain ⟨v, _hμ_lt, hv_pos, hfull⟩ := hcommon M hM
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μ : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hfull
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hsector_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μ • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hsector_complex
    simpa [Φ] using hre
  exact
    heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hsector_real
      (fun τ => by
        have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
          marshallSignS_re_sq A τ.1
        nlinarith [hv_pos τ])
      hφ_ne hφ_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from admissible
reach**: if every outside-sector Marshall-positive ground representative
can be transported to a nonzero eigenvector in an admissible sector at
the same eigenvalue, then the outside-sector ground-energy lower family
follows.

The proof applies the admissible-sector real spectral lower bound coming
from the common-energy chain.  The reached complex sector eigenvector has
either nonzero real part or nonzero imaginary part, and the real-coupling
complex-to-real eigenvector bridge supplies the real-form eigen equation
at the same `μM`. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach : tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c := by
  intro μ hcommon M _ hM_out μM v hμM_lt hv_pos hΦ
  obtain ⟨K, hK_mem, hK_nonempty, ΦK, hΦK_ne, hΦK_eigen⟩ :=
    hreach M hM_out hμM_lt hv_pos hΦ
  letI : Nonempty (magConfigS V N K) := hK_nonempty
  have hadm_real_min :
      ∀ {μ' : ℝ} {φ : magConfigS V N K → ℝ},
        φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N K).mulVec φ = μ' • φ →
        μ ≤ μ' :=
    tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hcommon K hK_mem
  classical
  by_cases hRe_ne : (fun τ : magConfigS V N K => (ΦK τ).re) ≠ 0
  · exact hadm_real_min (μ' := μM) (φ := fun τ => (ΦK τ).re) hRe_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦK_eigen)
  · have hRe_zero : (fun τ : magConfigS V N K => (ΦK τ).re) = 0 := by
      by_contra h
      exact hRe_ne h
    have hIm_ne : (fun τ : magConfigS V N K => (ΦK τ).im) ≠ 0 := by
      intro hIm_zero
      apply hΦK_ne
      funext τ
      apply Complex.ext
      · have h := congrFun hRe_zero τ
        simpa using h
      · have h := congrFun hIm_zero τ
        simpa using h
    exact hadm_real_min (μ' := μM) (φ := fun τ => (ΦK τ).im) hIm_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
        N hJ_real hΦK_eigen)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from full admissible
reach**: a full-space admissible-reach callback supplies the sector
admissible-reach callback by restriction, and hence gives the
outside-sector ground-energy lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_full_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hfull :
      tasaki23OutsideGroundAdmissibleFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleReachCallback_of_full_reach
      (V := V) A (J := J) N c hfull)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from iterated ladder
full reach**: iterated left and right total-spin ladder callbacks first
produce the full-space admissible-reach callback, then the existing
full-reach bridge supplies the outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_full_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderFullReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_full_admissible_reach
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_callbacks
      (V := V) A (J := J) N c hleft hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from iterated
Casimir full reach**: iterated left and right Casimir callbacks first
produce the iterated ladder full-reach callbacks, then the existing
full-reach bridge supplies the outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_casimir_full_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_full_admissible_reach
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleFullReachCallback_of_iterated_ladder_casimir_callbacks
      (V := V) A (J := J) N c hleft hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated
Casimir sources**: left and right saturated total-Casimir source callbacks
first supply the iterated-ladder Casimir full-reach callbacks, and the
existing full-reach bridge then supplies the outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_casimir_sources
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightSaturatedCasimirSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_iterated_ladder_casimir_full_reach
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftIteratedLadderCasimirFullReachCallback_of_saturated_casimir_source
      (V := V) A (J := J) N c hleft)
    (tasaki23OutsideGroundRightIteratedLadderCasimirFullReachCallback_of_saturated_casimir_source
      (V := V) A (J := J) N c hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated joint
sources**: left and right saturated joint source-vector callbacks already
contain the saturated total-Casimir source equations.  Projecting those
Casimir components and reusing the saturated-Casimir bridge supplies the
outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_sources
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftSaturatedJointSourceCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightSaturatedJointSourceCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_casimir_sources
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedCasimirSourceCallback_of_saturated_joint_source
      (V := V) A (J := J) N c hleft)
    (tasaki23OutsideGroundRightSaturatedCasimirSourceCallback_of_saturated_joint_source
      (V := V) A (J := J) N c hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated joint
references**: left and right saturated joint reference callbacks first supply
the saturated joint source-vector callbacks by the Marshall-positive
source-vector/eigenvalue uniqueness bridge.  The existing saturated
joint-source bridge then produces the outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_references
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedJointReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedJointReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_sources
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundLeftSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointSourceCallback_of_saturated_joint_reference
      (V := V) A (J := J) N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated ladder
references**: left and right saturated ladder reference callbacks are first
converted to saturated joint reference callbacks by the Tasaki §2.4
joint-eigenspace/span identification.  The saturated joint-reference route
then supplies the outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_references
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_joint_references
    (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate
    (tasaki23OutsideGroundLeftSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedJointReferenceCallback_of_saturated_ladder_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated
ladder-iterate references**: sectorwise singleton ladder-iterate reference
callbacks first supply the saturated ladder-reference callbacks, and the
existing ladder-reference route then supplies the outside-sector lower family.
-/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_references
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback (V := V) A J N) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_references
    (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedLadderReferenceCallback_of_saturated_ladder_iterate_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated
ladder-iterate Marshall-positive references**: concrete equality with the
sector ladder iterates first supplies the singleton-span iterate reference
callbacks, and the existing ladder-iterate reference route then supplies the
outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_marshall_positive_references
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback
        (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveReferenceCallback
        (V := V) A J N) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_references
    (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderIterateReferenceCallback_of_marshall_positive_reference
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedLadderIterateReferenceCallback_of_marshall_positive_reference
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from saturated
ladder-iterate Marshall-positive coefficients**: pointwise Marshall-positive
sector coefficients first supply full zero-extended Marshall-positive
reference callbacks, and the existing equality-reference route then supplies
the outside-sector lower family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_marshall_positive_coefficients
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hleft_ref :
      tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback
        (V := V) A J N)
    (hright_ref :
      tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback
        (V := V) A J N) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_marshall_positive_references
    (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveReferenceCallback_of_marshall_positive_coefficients
      (V := V) A (J := J) N hleft_ref)
    (tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveReferenceCallback_of_marshall_positive_coefficients
      (V := V) A (J := J) N hright_ref)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from explicit lowerable
coefficient dominance**: attached-sum dominance for the explicit lowerable
predecessor coefficients supplies the left and right saturated ladder-iterate
coefficient callbacks, and hence the outside-sector lower-energy family. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_lowerable_attach_sum_dominance
    [Nonempty V] (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hμsat :
      ∃ μsat : ℝ, (μsat : ℂ) = saturatedFerromagnetEigenvalueS (V := V) J N)
    (hdominates : ∀ (M : ℕ)
        (hM_succ : M + 1 < Fintype.card V * N + 1)
        (w : magConfigS V N M → ℝ),
      (∀ σ : magConfigS V N M,
        ladderIterateUp V N ⟨M, Nat.lt_of_succ_lt hM_succ⟩ σ.1 =
          (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) →
      ∀ τ : magConfigS V N (M + 1),
        (((Finset.univ.filter (fun x : V => A x = true)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                w τ x.1 ((Finset.mem_filter.mp x.2).2))) <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                  w τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_saturated_ladder_iterate_marshall_positive_coefficients
    (V := V) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate
    (tasaki23OutsideGroundLeftSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_lowerable_attach_sum_dominance
      (V := V) A (J := J) N hμsat hdominates)
    (tasaki23OutsideGroundRightSaturatedLadderIterateMarshallPositiveCoefficientCallback_of_lowerable_attach_sum_dominance
      (V := V) A (J := J) N hμsat hdominates)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from side admissible
reach**: left and right directional outside-sector reach callbacks supply
the outside-sector ground-energy lower family by first recombining into the
full admissible-reach callback and then applying
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach`. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_side_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftAdmissibleReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightAdmissibleReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleReachCallback_of_side_callbacks
      (V := V) A (J := J) N c hleft hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector real lower bound from
outside-sector ground energies**: for sectors outside the admissible
Theorem 2.3 interval, it is enough to prove the lower bound against the
Marshall-positive sector ground-state representative supplied by the
per-sector Theorem 2.2 wrapper.

The Perron-Frobenius comparison for the shifted dressed real sector matrix
then places that sector ground energy below every real-form sector
eigenvalue, giving the full outside-real-sector callback needed by the
final global-minimality step. -/
theorem tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ) :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      M ∉ tasaki23GroundStateSectors (V := V) A N →
      ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
        φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
        μ ≤ μ' := by
  intro M _ hM_out μ' φ hφ_ne hφ_eigen
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hΦM, _hsupportM, _huniqM⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μM : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦM
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hsector_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * vM τ) =
        μM • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * vM τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hsector_complex
    simpa [Φ] using hre
  have hμ_le_μM : μ ≤ μM :=
    houtside_ground_energy_lower M hM_out hμM_lt hvM_pos hΦM
  have hμM_le_μ' : μM ≤ μ' :=
    heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hsector_real
      (fun τ => by
        have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
          marshallSignS_re_sq A τ.1
        have hv := hvM_pos τ
        nlinarith [hv])
      hφ_ne hφ_eigen
  exact hμ_le_μM.trans hμM_le_μ'

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector minimality from common interval energy
and outside-sector ground energies**: combine the admissible-sector
minimality supplied by the common-energy chain with the outside-sector
ground-energy bridge, then pass from real-form sector eigenvectors to
complex sector eigenvectors.

This is the sectorwise spectral-minimality package needed to turn the
outside-sector ground-energy lower-bound callback into the final global
minimality callback for Theorem 2.3. -/
theorem
    tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ) :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
        Φ ≠ 0 →
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
          (μ' : ℂ) • Φ →
        μ ≤ μ' := by
  exact
    tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
      (fun M => by
        by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
        · exact
            tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
              A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
              hcommon M hM
        · exact
            tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
              A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
              hc_strict h_intermediate houtside_ground_energy_lower M hM)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from a common interval energy**:
if one real energy `μ` is already realised by Marshall-positive sector
eigenvectors in every admissible sector, then the per-sector Theorem 2.2
uniqueness wrapper upgrades those representatives to the final
existence-and-uniqueness format.

This helper isolates the final packaging step from the particular mechanism
used to construct the common sector energy. -/
theorem tasaki_2_5_theorem_2_3_of_common_energy_chain
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ)
    (hglobal_min :
      ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  refine ⟨μ, ?_, hglobal_min⟩
  intro M hM _hM_nonempty
  obtain ⟨v_chain, hμ_chain_lt, hv_chain_pos, hΦ_chain⟩ := hcommon M hM
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hΦM, _hsupportM, huniqM⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hsupport_chain :
      ∀ σ, magSumS σ ≠ M →
        magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v_chain τ : ℝ) : ℂ)) σ = 0 := by
    intro σ hσ
    exact magSectorEmbedding_apply_of_not_mem _ hσ
  have hpos_chain_full :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v_chain τ : ℝ) : ℂ)) τ.1).re := by
    intro τ
    rw [magSectorEmbedding_apply_subtype, Complex.ofReal_re]
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv := hv_chain_pos τ
    nlinarith
  obtain ⟨hμ_eq_μM, _hr⟩ := huniqM hΦ_chain hsupport_chain hpos_chain_full
  refine ⟨vM, ?_, hvM_pos, ?_, ?_⟩
  · exact hμ_chain_lt
  · rwa [hμ_eq_μM]
  · intro μ' Ψ' hΨ'_eigen hΨ'_support hΨ'_positive
    obtain ⟨hμ'_eq_μM, hr⟩ := huniqM hΨ'_eigen hΨ'_support hΨ'_positive
    exact ⟨by rw [hμ'_eq_μM, ← hμ_eq_μM], hr⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from common interval energy and
outside-sector ground energies**: once the adjacent-sector chain has
produced a common Marshall-positive energy on the admissible interval, it
is enough to prove lower bounds only for the Marshall-positive
ground-state representatives in outside sectors.

The sector-minimality bridge packages the admissible and outside sectors,
and the global-minimality bridge then supplies the final full-space
minimality callback required by the textbook statement. -/
theorem
    tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro _hJ_real _hJ_real' _hJ_sym _hJ_nn _hJ_bipartite _hJ_pos
    _hc_strict _h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N
        (tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate hcommon houtside_ground_energy_lower))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

end LatticeSystem.Quantum
