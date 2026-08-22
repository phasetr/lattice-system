import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsivePerturbationSetup

/-!
# Superexchange reduced-inverse layer for Theorem 10.4 (Tasaki §10.2.2, PR-6)

Sixth installment of the Theorem 10.4 discharge arc (issue #5320); first of the three-PR
superexchange-identity sub-arc (PR-6 to PR-8). PR-5 built the perturbation family
`Ĥ(λ)|_K = Ĥ₀|_K + λ V̂|_K` on the half-filled fixed-`Ŝ³` sector `K` and its first-order vanishing
`P̂₀ V̂|_K P̂₀ = 0`; this file supplies the two remaining pieces of Tasaki's `λ → 0` deformation
(§10.2.2, p. 353) that are needed *before* the superexchange operator identity itself can be
computed (PR-7/PR-8):

* **`V̂` preserves the half-filled sector** (`liebPerturbationV_preserves_liebHalfFillingPred`):
  every hopping term of `V̂` moves one electron of a fixed spin between two sites, so the total
  electron number and the total spin-up number are both unchanged. This is the entrywise
  sector-preservation hypothesis that
  `LatticeSystem.Fermion.configSectorCompress_mul_of_preserves`
  (`HubbardImpossibilityLowUVariationalCore.lean`) needs to identify the compressed product
  `V̂|_K · V̂|_K` with the compression `(V̂ · V̂)|_K` of the whole-Fock-space product — the step
  PR-8 uses to reduce its target identity to a Fock-space computation.
* **The compressed reduced inverse of `Ĥ₀|_K`** (`liebPerturbationH0InvCompressed`,
  `liebPerturbationH0Compressed_isReducedInverse`): the compression of PR-5's explicit
  whole-Fock-space reduced inverse `Ĥ₀Inv`, discharging PR-5 debt item (a).
* **The crux: intermediate states have weight exactly `1`**
  (`liebPerturbationV_intermediate_weight_eq_one`): Tasaki's "the site `x` is doubly occupied in
  `ĉ†_{x,σ}ĉ_{y,σ}|Φ⟩`" (eq. (10.1.7), p. 344), read at this arc's `U = 1` normalisation as
  "the intermediate interaction weight is exactly `1`" rather than merely `1/U`. A later
  restoration of a general on-site coupling `U` must not silently reuse this statement verbatim.
* **`Ĥ₀⁻¹|_K` acts as the identity on `V̂|_K · P̂₀`**
  (`liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection`) and, consequently, the **PR-6
  capstone** (`secondOrderEffectiveHamiltonian_liebPerturbation_eq`): the second-order effective
  Hamiltonian collapses to `−(P̂₀ · V̂|_K · V̂|_K · P̂₀)`, the object PR-8 computes explicitly as
  the superexchange sum.

Two cheap debt items of PR-5 are cleared alongside this layer, since both are needed by the
Lemma 10.1 application (PR-11 to PR-13) and neither depends on the superexchange identity itself:

* `configSector_liebHalfFillingPred_nonempty` — PR-5 debt (c), an instance hypothesis of
  `tasaki_lemma_10_1_degenerate_perturbation`.
* `homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian` — PR-5 debt (b), the compressed
  bridge to `LatticeSystem.Math.perturbedHamiltonian`. This bridge is pure linearity of
  `configSectorCompress` and does **not** presuppose the sector preservation of `V̂` proved above;
  only its later *interpretation* at assembly does.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1 (Lemma 10.1, eq. (10.1.20)) and §10.2.2 (eq. (10.1.7), p. 344; p. 353).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped ComplexOrder

variable {N : ℕ}

/-! ## `V̂` preserves the half-filled fixed-`Ŝ³` sector -/

/-- **`V̂` preserves the half-filled fixed-`Ŝ³` sector**: every hopping term of `V̂` moves a single
electron of one spin between two sites, leaving both the total electron number and the total
spin-up number unchanged. Hence `V̂ c' c = 0` whenever `c` lies in the sector and `c'` does not —
the entrywise sector-preservation hypothesis needed by `configSectorCompress_mul_of_preserves`
(`HubbardImpossibilityLowUVariationalCore.lean`) to identify `V̂|_K · V̂|_K` with the compression of
the whole-Fock-space product `V̂ · V̂`. -/
theorem liebPerturbationV_preserves_liebHalfFillingPred (N nUp : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) {c c' : Fin (2 * N + 2) → Fin 2}
    (hc : liebHalfFillingPred N nUp c) (hc' : ¬ liebHalfFillingPred N nUp c') :
    liebPerturbationV N A T c' c = 0 := by
  sorry

/-! ## The compressed reduced inverse of `Ĥ₀|_K` -/

/-- **The compressed reduced inverse of `Ĥ₀|_K`**: the compression of the whole-Fock-space
explicit reduced inverse `Ĥ₀Inv` (`liebPerturbationH0Inv`, PR-5) to the half-filled fixed-`Ŝ³`
sector. -/
noncomputable def liebPerturbationH0InvCompressed (N nUp : ℕ) :
    Matrix (configSector N (liebHalfFillingPred N nUp))
      (configSector N (liebHalfFillingPred N nUp)) ℂ :=
  configSectorCompress N (liebHalfFillingPred N nUp) (liebPerturbationH0Inv N)

/-- The compressed reduced inverse stays diagonal, with the reciprocal interaction weight of the
sector configuration as its eigenvalue (mirroring `liebPerturbationH0Compressed_eq_diagonal`). -/
theorem liebPerturbationH0InvCompressed_eq_diagonal (N nUp : ℕ) :
    liebPerturbationH0InvCompressed N nUp
      = Matrix.diagonal (fun s : configSector N (liebHalfFillingPred N nUp) =>
          let w := hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val
          if w = 0 then 0 else w⁻¹) := by
  sorry

/-- **`Ĥ₀InvCompressed` is the reduced inverse of `Ĥ₀|_K`** — closes PR-5 debt item (a): the
compressed `IsReducedInverse` contract, mirroring the whole-Fock-space
`liebPerturbationH0_isReducedInverse`. -/
theorem liebPerturbationH0Compressed_isReducedInverse (N nUp : ℕ) :
    LatticeSystem.Math.IsReducedInverse (liebPerturbationH0Compressed N nUp)
      (liebPerturbationH0InvCompressed N nUp) := by
  sorry

/-! ## The crux: intermediate states have weight exactly `1` -/

/-- **Crux of PR-6: the intermediate weight is exactly `1`.** For `c` a hard-core configuration of
the half-filled sector, every `d` reached by a nonzero matrix element of `V̂` has interaction
weight exactly `1`: half filling plus hard-core forces one electron per site
(`liebHalfFilling_site_occupation`), so a nonzero hop entry has source `y` occupied and target `x`
empty, and `d` is `c` with `x` now doubly occupied and `y` now empty — Tasaki's "the site `x` is
doubly occupied in `ĉ†_{x,σ}ĉ_{y,σ}|Φ⟩`" (eq. (10.1.7), p. 344), at this arc's `U = 1`
normalisation read as "exactly `1`" rather than merely "exactly `U`"; a later restoration of a
general on-site coupling must not reuse this statement verbatim. -/
theorem liebPerturbationV_intermediate_weight_eq_one {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    {c d : Fin (2 * N + 2) → Fin 2}
    (hc : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0)
    (hd : liebPerturbationV N A T d c ≠ 0) :
    hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) d = 1 := by
  sorry

/-! ## `Ĥ₀⁻¹|_K` on the range of `V̂|_K · P̂₀`, and the PR-6 capstone -/

/-- **`Ĥ₀⁻¹|_K` acts as the identity on `V̂|_K · P̂₀`**: on a weight-`1` column the reciprocal
interaction weight of `Ĥ₀⁻¹|_K` is exactly `1` (Crux,
`liebPerturbationV_intermediate_weight_eq_one`), so it fixes every column reached from a hard-core
configuration by `V̂|_K`. -/
theorem liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) :
    liebPerturbationH0InvCompressed N nUp
        * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      = liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp) := by
  sorry

/-- **PR-6 capstone**: the second-order effective Hamiltonian for the compressed perturbation
family collapses to `−(P̂₀ · V̂|_K · V̂|_K · P̂₀)`, since `Ĥ₀⁻¹|_K` acts as the identity on the
range of `V̂|_K · P̂₀` (`liebPerturbationH0InvCompressed_mul_V_mul_kernelProjection`). This is the
object PR-8 computes explicitly as the superexchange sum. -/
theorem secondOrderEffectiveHamiltonian_liebPerturbation_eq (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) :
    LatticeSystem.Math.secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)
      = -(LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
          * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
          * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)) := by
  sorry

/-! ## Cheap debt clearance (PR-5 items (b) and (c)) -/

/-- **PR-5 debt (c) discharged**: the half-filled fixed-`Ŝ³` sector is nonempty whenever
`nUp ≤ N + 1` — an instance hypothesis of `tasaki_lemma_10_1_degenerate_perturbation`
(`Math/MatrixAnalysis/DegeneratePerturbationConvergence.lean`). -/
theorem configSector_liebHalfFillingPred_nonempty (N nUp : ℕ) (hnUp : nUp ≤ N + 1) :
    Nonempty (configSector N (liebHalfFillingPred N nUp)) := by
  sorry

/-- **PR-5 debt (b) discharged**: the compressed `s = 1` homotopy endpoint is the compressed
perturbed Hamiltonian `Ĥ₀|_K + λ V̂|_K` — pure linearity of `configSectorCompress` applied to
`homotopyHamiltonian_one_eq_perturbedHamiltonian` (PR-5). This bridge does **not** presuppose the
sector preservation of `V̂` (`liebPerturbationV_preserves_liebHalfFillingPred`); only its later
*interpretation* at assembly (PR-11 to PR-13) does. -/
theorem homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian (N nUp : ℕ)
    (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ) :
    configSectorCompress N (liebHalfFillingPred N nUp) (homotopyHamiltonian N A T U lam 1)
      = LatticeSystem.Math.perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
          (liebPerturbationVCompressed N nUp A T) lam := by
  sorry

end LatticeSystem.Fermion
