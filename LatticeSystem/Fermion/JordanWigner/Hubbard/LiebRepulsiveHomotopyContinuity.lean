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
  there, by `IsLocallyConstant.apply_eq_of_preconnectedSpace` on the subtype `↥(0, 1]`.

## Scope of this PR

The **algebraic** properties of the concrete homotopy are proved here alongside the topological
core: `T_s` preserves the sign of the original hopping on its support and is `s λ` on an added
`A`-`B` edge, the symmetry, bipartition and connectivity of the hopping matrix survive the
deformation, and `U_s > 0`. The strict-inequality selector `c` and its instantiation via
`exists_unique_casimir_sector_strict_min` along the whole homotopy, and the `λ → 0` limit that
identifies the endpoint Casimir value with Tasaki's `S₀ = ||A| − |B||/2`, are deferred to the next
PRs of the arc (PR-5 onward): this PR isolates the homotopy-independent topological machinery
(continuity and local-constancy) so it can be reused verbatim by them.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators Topology

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

/-! ## Algebraic properties of the homotopy -/

/-- Entrywise form of the hopping homotopy: `T_s x y = (1 - s) T x y + s T₁ x y`. -/
private theorem homotopyHopping_apply (T T₁ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (s : ℝ)
    (x y : Fin (N + 1)) :
    homotopyHopping T T₁ s x y = (1 - s) * T x y + s * T₁ x y := by
  simp [homotopyHopping]

/-- **Lemma 1** (sign preservation on the original support): on the original hopping support
(`T x y ≠ 0`), the homotopy carries the same sign as `T x y` and its magnitude interpolates
between `|T x y|` and `λ`; in particular (for `s ∈ [0, 1]` and `λ > 0`) it never vanishes. -/
theorem homotopyHopping_apply_of_ne_zero (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) (s : ℝ)
    {x y : Fin (N + 1)} (hxy : T x y ≠ 0) :
    homotopyHopping T (liebEndpointHopping A T lam) s x y
      = (if 0 < T x y then 1 else -1) * ((1 - s) * |T x y| + s * lam) := by
  have hend : liebEndpointHopping A T lam x y = if 0 < T x y then lam else -lam := by
    simp [liebEndpointHopping, hxy]
  rw [homotopyHopping_apply, hend]
  by_cases hpos : 0 < T x y
  · rw [if_pos hpos, if_pos hpos, abs_of_pos hpos]
    ring
  · rw [if_neg hpos, if_neg hpos, abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hxy)]
    ring

/-- **Lemma 2** (added `A`-`B` edges never vanish for `s > 0`): on a pair `x, y` in different
sublattices with vanishing original hopping (`T x y = 0`), the homotopy is `s * λ`. -/
theorem homotopyHopping_apply_of_added_edge (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) (s : ℝ)
    {x y : Fin (N + 1)} (hT0 : T x y = 0) (hAB : x ∈ A ↔ y ∉ A) :
    homotopyHopping T (liebEndpointHopping A T lam) s x y = s * lam := by
  have hend : liebEndpointHopping A T lam x y = lam := by
    simp [liebEndpointHopping, hT0, hAB]
  rw [homotopyHopping_apply, hend, hT0]
  ring

/-- **Lemma 3** (same-sublattice entries stay zero): on a pair `x, y` in the *same* sublattice with
vanishing original hopping, the homotopy stays `0` for every `s`. -/
theorem homotopyHopping_apply_eq_zero_of_same_sublattice (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (lam : ℝ) (s : ℝ)
    {x y : Fin (N + 1)} (hT0 : T x y = 0) (hAA : ¬ (x ∈ A ↔ y ∉ A)) :
    homotopyHopping T (liebEndpointHopping A T lam) s x y = 0 := by
  have hend : liebEndpointHopping A T lam x y = 0 := by
    simp [liebEndpointHopping, hT0, hAA]
  rw [homotopyHopping_apply, hend, hT0]
  ring

/-- **Lemma 4** (symmetry preserved along the homotopy): if `T` is symmetric, so is `T_s` at every
`s`, since the endpoint `liebEndpointHopping A T lam` is symmetric whenever `T` is (the bipartition
membership test `x ∈ A ↔ y ∉ A` says that exactly one of `x, y` lies in `A`, which is symmetric in
`x, y`). -/
theorem homotopyHopping_symm (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ x y, T x y = T y x) (lam : ℝ) (s : ℝ) :
    ∀ x y, homotopyHopping T (liebEndpointHopping A T lam) s x y
      = homotopyHopping T (liebEndpointHopping A T lam) s y x := by
  have hend : ∀ x y : Fin (N + 1),
      liebEndpointHopping A T lam x y = liebEndpointHopping A T lam y x := by
    intro x y
    have hiff : (x ∈ A ↔ y ∉ A) ↔ (y ∈ A ↔ x ∉ A) := by tauto
    simp only [liebEndpointHopping, hT x y, hiff]
  intro x y
  rw [homotopyHopping_apply, homotopyHopping_apply, hT x y, hend x y]

/-- **Lemma 5** (bipartition respected along the homotopy): if `T` respects the bipartition `A`,
so does every `T_s`, since Lemma 3 forces a same-sublattice entry of `T_s` to vanish whenever the
original entry does, while a nonvanishing original entry already sits on an `A`-`B` pair. -/
theorem homotopyHopping_bipartite (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hbip : HoppingRespectsBipartition A T)
    (lam : ℝ) (s : ℝ) :
    HoppingRespectsBipartition A (homotopyHopping T (liebEndpointHopping A T lam) s) := by
  intro x y hne
  by_cases hT0 : T x y = 0
  · by_contra hAA
    exact hne (homotopyHopping_apply_eq_zero_of_same_sublattice A T lam s hT0 hAA)
  · exact hbip hT0

/-- **Lemma 6** (connectivity preserved along the homotopy): if the original support graph is
connected, so is the support graph of `T_s` for every `s ∈ (0, 1]` with `λ > 0`, because for such
`s` and `λ` the interpolated magnitude `(1 - s) |T x y| + s λ` of Lemma 1 stays strictly positive,
so no original edge is lost (extra `A`-`B` edges of Lemma 2 only add edges). Positivity of `λ` is
essential rather than cosmetic: with `λ < 0` the two terms cancel at an interior `s`, breaking the
original edge — e.g. `|T x y| = 1`, `λ = -1`, `s = 1/2` gives `T_s x y = 0`. -/
theorem homotopyHopping_connected (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hconn : (hoppingSupportGraph T).Preconnected)
    {lam : ℝ} (hlam : 0 < lam) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (hoppingSupportGraph (homotopyHopping T (liebEndpointHopping A T lam) s)).Preconnected := by
  have key : ∀ u v : Fin (N + 1), T u v ≠ 0 →
      homotopyHopping T (liebEndpointHopping A T lam) s u v ≠ 0 := by
    intro u v huv
    rw [homotopyHopping_apply_of_ne_zero A T lam s huv]
    have hmag : 0 < (1 - s) * |T u v| + s * lam := by
      have h1 : 0 ≤ (1 - s) * |T u v| := mul_nonneg (by linarith [hs.2]) (abs_nonneg _)
      have h2 : 0 < s * lam := mul_pos hs.1 hlam
      linarith
    exact mul_ne_zero (by split_ifs <;> norm_num) (ne_of_gt hmag)
  refine SimpleGraph.Preconnected.mono (fun u v huv => ?_) hconn
  simp only [hoppingSupportGraph, SimpleGraph.fromRel_adj] at huv ⊢
  exact ⟨huv.1, huv.2.imp (key u v) (key v u)⟩

/-- **Lemma 7** (on-site coupling stays positive): the on-site homotopy `U_s` is positive for every
`s ∈ [0, 1]` whenever `U > 0`, being a convex combination of the positive values `U` and `1`. -/
theorem homotopyOnSite_pos {U : ℝ} (hU : 0 < U) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < homotopyOnSite U s := by
  obtain ⟨h0, h1⟩ := hs
  rcases eq_or_lt_of_le h0 with rfl | hspos
  · simpa [homotopyOnSite] using hU
  · have hconv : 0 ≤ (1 - s) * U := mul_nonneg (by linarith) hU.le
    simp only [homotopyOnSite]
    linarith

/-! ## Continuity of the homotopy (this PR's core analytic content) -/

/-- **Continuity of the Hamiltonian homotopy**: `s ↦ H_s` is continuous, since it is built from
the entrywise-affine hopping and on-site homotopies through the (multilinear, hence continuous)
construction of `repulsiveHubbardHamiltonian`. -/
theorem continuous_homotopyHamiltonian (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ) :
    Continuous (fun s : ℝ => homotopyHamiltonian N A T U lam s) := by
  have hhop : ∀ x y : Fin (N + 1), Continuous fun s : ℝ =>
      ((homotopyHopping T (liebEndpointHopping A T lam) s x y : ℝ) : ℂ) := by
    intro x y
    simp only [homotopyHopping_apply]
    exact Complex.continuous_ofReal.comp (by fun_prop)
  have hons : Continuous fun s : ℝ => ((homotopyOnSite U s : ℝ) : ℂ) := by
    simp only [homotopyOnSite]
    exact Complex.continuous_ofReal.comp (by fun_prop)
  simp only [homotopyHamiltonian, repulsiveHubbardHamiltonian, hubbardKinetic,
    hubbardOnSiteInteractionSite]
  exact Continuous.add
    (continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => (hhop i j).smul continuous_const)
    (continuous_finset_sum _ fun _ _ => hons.smul continuous_const)

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
`IsLocallyConstant.apply_eq_of_preconnectedSpace` on the subtype `↥(0, 1]`) constant there.
Discharging this for the concrete endpoint at `s = 1` pins the ground-state total spin of the whole
homotopy family, including the original model at `s → 0⁺`, to the explicit endpoint value.

The local step needs a *uniform* energy gap between the occupied sector `c s₀` and its rivals, and
that uniformity is not an extra hypothesis: only finitely many `c'` index a nonzero sector, since
`K_{c'} ≠ ⊥` forces `c'` to be an eigenvalue of `Ŝ²` and an endomorphism of a finite-dimensional
space has finitely many eigenvalues (`Module.End.finite_hasEigenvalue`). -/
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
  have hfin : {d : ℂ | numberSpinZCasimirSectorEuclidean N L m₀ d ≠ ⊥}.Finite := by
    refine Set.Finite.subset
      (Module.End.finite_hasEigenvalue (Matrix.toEuclideanLin (fermionTotalSpinSquared N)))
      fun d hd => ?_
    change Module.End.eigenspace (Matrix.toEuclideanLin (fermionTotalSpinSquared N)) d ≠ ⊥
    intro hbot
    exact hd (by simp only [numberSpinZCasimirSectorEuclidean, hbot, inf_bot_eq])
  have hlocal : ∀ s₀ ∈ Set.Ioc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Set.Ioc (0 : ℝ) 1] s₀, c s = c s₀ := by
    intro s₀ hs₀
    obtain ⟨-, -, hgap₀⟩ := hStrict s₀ hs₀
    have hrivals :
        {d : ℂ | numberSpinZCasimirSectorEuclidean N L m₀ d ≠ ⊥ ∧ d ≠ c s₀}.Finite :=
      hfin.subset fun d hd => hd.1
    obtain ⟨gap, hgap_pos, hgap_le⟩ : ∃ gap : ℝ, 0 < gap ∧ ∀ d ∈ hrivals.toFinset,
        E s₀ + gap ≤ minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ d) (H s₀) := by
      rcases hrivals.toFinset.eq_empty_or_nonempty with hempty | hne
      · exact ⟨1, one_pos, by simp [hempty]⟩
      refine ⟨hrivals.toFinset.inf' hne fun d =>
        minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ d) (H s₀) - E s₀, ?_, fun d hd => ?_⟩
      · refine (Finset.lt_inf'_iff hne).mpr fun d hd => ?_
        have hd' := hrivals.mem_toFinset.mp hd
        have hlt := hgap₀ d hd'.2 hd'.1
        linarith
      · have hle : hrivals.toFinset.inf' hne (fun d =>
            minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ d) (H s₀) - E s₀)
            ≤ minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ d) (H s₀) - E s₀ :=
          Finset.inf'_le _ hd
        linarith
    have hEev : ∀ᶠ s in 𝓝[Set.Ioc (0 : ℝ) 1] s₀, E s < E s₀ + gap / 2 :=
      (hEcont s₀ hs₀).tendsto.eventually_lt_const (by linarith)
    have hrival : ∀ᶠ s in 𝓝[Set.Ioc (0 : ℝ) 1] s₀, ∀ d ∈ hrivals.toFinset,
        E s₀ + gap / 2 < minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ d) (H s) := by
      refine (Filter.eventually_all_finset _).mpr fun d hd => ?_
      refine Filter.Tendsto.eventually_const_lt ?_ (hCont d).continuousWithinAt.tendsto
      have hle := hgap_le d hd
      linarith
    filter_upwards [hEev, hrival, self_mem_nhdsWithin] with s hEs hrs hsmem
    by_contra hne
    obtain ⟨hKs, hEsmin, -⟩ := hStrict s hsmem
    have hlt := hrs (c s) (hrivals.mem_toFinset.mpr ⟨hKs, hne⟩)
    rw [hEsmin] at hlt
    linarith
  haveI : PreconnectedSpace (Set.Ioc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioc
  have hlc : IsLocallyConstant fun t : Set.Ioc (0 : ℝ) 1 => c (t : ℝ) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr ?_
    rintro ⟨s₀, hs₀⟩
    have h := hlocal s₀ hs₀
    rw [nhdsWithin_eq_map_subtype_coe hs₀, Filter.eventually_map] at h
    exact h
  intro s₁ hs₁ s₂ hs₂
  exact hlc.apply_eq_of_preconnectedSpace ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩

end LatticeSystem.Fermion
