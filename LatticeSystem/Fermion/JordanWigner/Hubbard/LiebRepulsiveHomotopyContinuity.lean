import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCasimirSector

/-!
# Homotopy continuity for Theorem 10.4 (Tasaki §10.2.2, PR-4)

Fourth installment of the Theorem 10.4 discharge arc (issue #5320). Tasaki's proof pins the
ground-state total spin of the repulsive model by continuously deforming the couplings
(`U_x → U`, `t_{x,y} → ±λ`) from the original model to an explicit uniform `±λ` endpoint and
letting `λ → 0` (p. 353). This file sets up that homotopy `H_s` (`s ∈ [0, 1]`, `s = 0` the
original model, `s = 1` the explicit endpoint) and its two load-bearing analytic facts:

* **Continuity** of `s ↦ H_s` (`continuous_homotopyHamiltonian`), transported through PR-2's
  `Continuous.minEnergyOn_comp` to continuity of the sector-restricted minimum energy
  (`continuous_minEnergyOn_homotopyHamiltonian`);
* **Local-constancy-to-constancy**: if every `s ∈ (0, 1]` has a *unique* occupied Casimir sector
  attaining the ground energy (PR-3's `exists_unique_casimir_sector_strict_min`), then that
  occupied sector is the *same* for every `s ∈ (0, 1]`
  (`casimirSelector_eq_const_of_locally_unique_strict_min`).
  This is the topological core of the deformation argument: a selector into a discrete space
  (`ℂ`, indexing eigenvalues) that is locally constant on the preconnected set `(0, 1]` is constant
  there, by `IsLocallyConstant.apply_eq_of_isPreconnected`.

## Scope of this PR

The **algebraic** properties of the concrete homotopy — that `T_s` preserves the sign of the
original hopping and never vanishes on the extended support, that the bipartition/connectivity of
the support graph survive along `s ∈ (0, 1]`, and that `U_s > 0` — are recorded here as signatures
only (`sorry`), together with the concrete homotopy and endpoint definitions they refer to. The
strict-inequality selector `c` and its instantiation via `exists_unique_casimir_sector_strict_min`
along the whole homotopy, and the `λ → 0` limit that identifies the endpoint Casimir value with
Tasaki's `S₀ = ||A| − |B||/2`, are deferred to the next PRs of the arc (PR-5 onward): this PR
isolates the homotopy-independent topological machinery (continuity and local-constancy) so it can
be reused verbatim once the concrete algebraic facts are discharged.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-! ## The homotopy `T_s`, `U_s`, `H_s` -/

/-- The **explicit uniform `±λ` endpoint hopping matrix** `T₁` of Tasaki's deformation (p. 353):
on the original support it carries the sign of `T x y` scaled to `λ`; on an "added" `A`-`B` edge
(sites in different sublattices with vanishing original hopping) it is `λ`; on a same-sublattice
pair it is `0`. -/
noncomputable def liebEndpointHopping (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun x y =>
    if T x y ≠ 0 then (if 0 < T x y then lam else -lam)
    else if x ∈ A ↔ y ∉ A then lam else 0

/-- The **hopping homotopy** `T_s := (1 - s) T + s T₁`, the convex combination of the original
hopping matrix `T` and an endpoint matrix `T₁` (in practice `T₁ = liebEndpointHopping A T lam`). -/
def homotopyHopping (T T₁ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (s : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (1 - s) • T + s • T₁

/-- The **on-site coupling homotopy** `U_s := (1 - s) U + s · 1`, the convex combination of the
original repulsion strength `U` and the endpoint value `1`. -/
def homotopyOnSite (U : ℝ) (s : ℝ) : ℝ :=
  (1 - s) * U + s * 1

/-- The **Hamiltonian homotopy** `H_s`, built from the hopping and on-site homotopies via the
uniform repulsive Hubbard Hamiltonian (`repulsiveHubbardHamiltonian`, eq. (10.2.5)). -/
noncomputable def homotopyHamiltonian (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ) (s : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  repulsiveHubbardHamiltonian N (homotopyHopping T (liebEndpointHopping A T lam) s)
    (homotopyOnSite U s)

/-! ## Algebraic properties of the homotopy (deferred to later PRs of the arc) -/

/-- **Lemma 1** (sign preservation on the original support): on the original hopping support
(`T x y ≠ 0`), the homotopy carries the same sign as `T x y` and its magnitude interpolates
between `|T x y|` and `λ`; in particular (for `s ∈ [0, 1]` and `λ ≠ 0`, or `s < 1`) it never
vanishes. -/
theorem homotopyHopping_apply_of_ne_zero (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {x y : Fin (N + 1)} (hxy : T x y ≠ 0) :
    homotopyHopping T (liebEndpointHopping A T lam) s x y
      = (if 0 < T x y then 1 else -1) * ((1 - s) * |T x y| + s * lam) := by
  sorry

/-- **Lemma 2** (added `A`-`B` edges never vanish for `s > 0`): on a pair `x, y` in different
sublattices with vanishing original hopping (`T x y = 0`), the homotopy is `s * λ`. -/
theorem homotopyHopping_apply_of_added_edge (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) (s : ℝ)
    {x y : Fin (N + 1)} (hT0 : T x y = 0) (hAB : x ∈ A ↔ y ∉ A) :
    homotopyHopping T (liebEndpointHopping A T lam) s x y = s * lam := by
  sorry

/-- **Lemma 3** (same-sublattice entries stay zero): on a pair `x, y` in the *same* sublattice with
vanishing original hopping, the homotopy stays `0` for every `s`. -/
theorem homotopyHopping_apply_eq_zero_of_same_sublattice (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) (s : ℝ)
    {x y : Fin (N + 1)} (hT0 : T x y = 0) (hAA : ¬ (x ∈ A ↔ y ∉ A)) :
    homotopyHopping T (liebEndpointHopping A T lam) s x y = 0 := by
  sorry

/-- **Lemma 4** (symmetry preserved along the homotopy): if `T` is symmetric, so is `T_s` at every
`s`, since the endpoint `liebEndpointHopping A T lam` is symmetric whenever `T` is (the bipartition
membership test `x ∈ A ↔ y ∉ A` is symmetric in `x, y`). -/
theorem homotopyHopping_symm (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ x y, T x y = T y x) (lam : ℝ) (s : ℝ) :
    ∀ x y, homotopyHopping T (liebEndpointHopping A T lam) s x y
      = homotopyHopping T (liebEndpointHopping A T lam) s y x := by
  sorry

/-- **Lemma 5** (bipartition respected along the homotopy): if `T` respects the bipartition `A`,
so does every `T_s` with `s ∈ (0, 1]` and `λ ≠ 0`, since Lemmas 1–3 place every nonzero entry of
`T_s` on an `A`-`B` pair. -/
theorem homotopyHopping_bipartite (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hbip : HoppingRespectsBipartition A T)
    {lam : ℝ} (hlam : lam ≠ 0) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    HoppingRespectsBipartition A (homotopyHopping T (liebEndpointHopping A T lam) s) := by
  sorry

/-- **Lemma 6** (connectivity preserved along the homotopy): if the original support graph is
connected, so is the support graph of `T_s` for every `s ∈ (0, 1]` with `λ ≠ 0`, because the
homotopy only ever adds edges (Lemma 2) to the original support and never removes one before
`s = 1` (Lemma 1). -/
theorem homotopyHopping_connected (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hconn : (hoppingSupportGraph T).Preconnected)
    {lam : ℝ} (hlam : lam ≠ 0) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (hoppingSupportGraph (homotopyHopping T (liebEndpointHopping A T lam) s)).Preconnected := by
  sorry

/-- **Lemma 7** (on-site coupling stays positive): the on-site homotopy `U_s` is positive for every
`s ∈ [0, 1]` whenever `U > 0`, being a convex combination of the positive values `U` and `1`. -/
theorem homotopyOnSite_pos {U : ℝ} (hU : 0 < U) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < homotopyOnSite U s := by
  sorry

/-! ## Continuity of the homotopy (this PR's core analytic content) -/

/-- **Continuity of the Hamiltonian homotopy**: `s ↦ H_s` is continuous, since it is built from
the entrywise-affine hopping and on-site homotopies through the (multilinear, hence continuous)
construction of `repulsiveHubbardHamiltonian`. -/
theorem continuous_homotopyHamiltonian (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ) :
    Continuous (fun s : ℝ => homotopyHamiltonian N A T U lam s) := by
  sorry

/-- **Continuity of the sector-restricted minimum energy along the homotopy**: for any fixed
occupied Casimir sector `K_c`, `s ↦ minEnergyOn K_c H_s` is continuous. This is `PR-2`'s
`Continuous.minEnergyOn_comp` composed with `continuous_homotopyHamiltonian` above — the intended
discharge route for the continuity hypothesis of
`casimirSelector_eq_const_of_locally_unique_strict_min` below. -/
theorem continuous_minEnergyOn_homotopyHamiltonian (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ)
    {L m₀ c : ℂ} (hKc : numberSpinZCasimirSectorEuclidean N L m₀ c ≠ ⊥) :
    Continuous (fun s : ℝ => minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c)
      (homotopyHamiltonian N A T U lam s)) :=
  Continuous.minEnergyOn_comp hKc (continuous_homotopyHamiltonian A T U lam)

/-! ## Local constancy ⇒ constancy: the topological core of the deformation argument -/

/-- **Local-constancy-to-constancy along the homotopy** (item 7 of the PR-4 design; the
homotopy-independent topological core of Tasaki's deformation argument, p. 353): suppose every
`s ∈ (0, 1]` has a *unique occupied Casimir sector attaining the ground energy* of `H s`
(the conclusion of PR-3's `exists_unique_casimir_sector_strict_min`, packaged here as the selector
`c : ℝ → ℂ` together with its defining strict-minimality property `hStrict`), and the
sector-restricted minimum energy is continuous in `s` for every fixed comparison sector `c'`
(discharged in the concrete instance by `continuous_minEnergyOn_homotopyHamiltonian` above). Then
the occupied Casimir eigenvalue `c s` is the **same** for every `s ∈ (0, 1]`: the strict inequality
in `hStrict` is an open condition preserved under small perturbations of `s` (continuity), so `c`
is locally constant on the preconnected set `(0, 1]`, hence (by
`IsLocallyConstant.apply_eq_of_isPreconnected`) constant there. Discharging this for the concrete
endpoint at `s = 1` pins the ground-state total spin of the whole homotopy family, including the
original model at `s → 0⁺`, to the explicit endpoint value. -/
theorem casimirSelector_eq_const_of_locally_unique_strict_min
    {N : ℕ} {L m₀ : ℂ} {H : ℝ → ManyBodyOp (Fin (2 * N + 2))} {c : ℝ → ℂ} {E : ℝ → ℝ}
    (hStrict : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      numberSpinZCasimirSectorEuclidean N L m₀ (c s) ≠ ⊥ ∧
        minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ (c s)) (H s) = E s ∧
        ∀ c' : ℂ, c' ≠ c s → numberSpinZCasimirSectorEuclidean N L m₀ c' ≠ ⊥ →
          E s < minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c') (H s))
    (hCont : ∀ c' : ℂ,
      Continuous (fun s : ℝ => minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c') (H s)))
    (hEcont : ContinuousOn E (Set.Ioc (0 : ℝ) 1)) :
    ∀ s₁ ∈ Set.Ioc (0 : ℝ) 1, ∀ s₂ ∈ Set.Ioc (0 : ℝ) 1, c s₁ = c s₂ := by
  sorry

end LatticeSystem.Fermion
