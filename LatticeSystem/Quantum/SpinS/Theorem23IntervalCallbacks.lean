import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence
import LatticeSystem.Quantum.SpinS.Theorem23DominancePredictedGS
import LatticeSystem.Quantum.SpinS.Theorem23PredictedLadder
import LatticeSystem.Quantum.SpinS.Theorem23PredictedSourceWeight
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceUnpacked
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceMarshall

/-!
# Tasaki §2.5 Theorem 2.3 interval callback API

This module contains the named callback propositions used by the interval-chain
and final-boundary wrappers for Tasaki §2.5 Theorem 2.3.  The callback names and
statements are kept stable while the proof-bearing interval-chain wrappers live
in `Theorem23Interval.lean` and its suffix modules.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left-endpoint predicted-GS callback**:
the Marshall-positive representative selected in the left endpoint sector
belongs to the predicted toy-Hamiltonian ground-state subspace.

This names the left-endpoint input used before the uniform source-sector
predicted-GS callback feeds that same endpoint into the interval chain. -/
def tasaki23LeftEndpointPredictedGSCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ {μ : ℝ}
    {v : magConfigS V N
      (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N) → ℝ},
      μ < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      magSectorEmbedding
          (fun τ : magConfigS V N
            (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
              (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
                N) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
        bipartiteToyGroundStateSubspacePredicted (Λ := V) A N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 source predicted-GS callback**:
every admissible source-sector Marshall-positive representative selected
below the spectral shift belongs to the predicted toy ground-state
subspace.

This names the uniform predicted-GS input left visible at the final
outside-ground boundary. -/
def tasaki23SourcePredictedGSCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor-difference callback**:
for each non-right-endpoint admissible sector, the local predecessor
raising-source difference is strictly positive after the interval-chain
representative is unpacked through the re-embedded real source-weight
identity and the lowered sublattice-Casimir/support data.

This names the remaining local adjacent-sector comparison used by the
outside-ground final boundary. -/
def tasaki23PredecessorDifferenceCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              ∀ hx : 0 < (τ.1 x).val,
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
                  ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                      2 *
                        ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                            ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                          (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                            ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
                    ((marshallSignS A pred).re *
                      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              0 <
                (((Finset.univ.filter (fun x : V => A x = false)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    let predVal : Fin (N + 1) :=
                      ⟨(τ.1 x.1).val - 1, by omega⟩
                    let pred : V → Fin (N + 1) :=
                      Function.update τ.1 x.1 predVal
                    (spinSOpPlus N predVal (τ.1 x.1)).re *
                      v ⟨pred,
                        magSumS_single_site_lowering_predecessor
                          τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
                  (((Finset.univ.filter (fun x : V => A x = true)).filter
                      (fun x : V => 0 < (τ.1 x).val)).attach.sum
                    (fun x =>
                      let predVal : Fin (N + 1) :=
                        ⟨(τ.1 x.1).val - 1, by omega⟩
                      let pred : V → Fin (N + 1) :=
                        Function.update τ.1 x.1 predVal
                      (spinSOpPlus N predVal (τ.1 x.1)).re *
                        v ⟨pred,
                          magSumS_single_site_lowering_predecessor
                            τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered-site-sum callback**:
for each non-right-endpoint admissible sector, the lowered total-spin
site-sum expression is strictly Marshall positive after applying it to
the selected Marshall-positive representative.

This names the direct interval-chain local positivity input used before
the later predecessor-difference route refines it. -/
def tasaki23LoweredSiteSumCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)

end LatticeSystem.Quantum
