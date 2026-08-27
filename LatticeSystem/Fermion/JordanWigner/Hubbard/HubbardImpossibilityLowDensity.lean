import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardFerromagnetismStructure
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRoth
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityFloor
import LatticeSystem.Math.MatrixAnalysis.PermInvariantUniformEigenvector
import LatticeSystem.Math.MonotoneEnumeration
import LatticeSystem.Math.Analysis.RpowSublinearThreshold
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Tasaki §11.1.1: impossibility of ferromagnetism at low densities (Theorem 11.4)

For a translation-invariant Hubbard model whose single-particle band satisfies the dimensional
density-of-states bound (11.1.8) in dimension `d > 2`, there is a density threshold `ρ₁ > 0` below
which the model is not ferromagnetic, for *any* `U ≥ 0` (Pieri–Daul–Baeriswyl–Dzierzawa–Fazekas).

The dimension enters only through the exponent `2/d` of the band condition (11.1.8) — no explicit
`d`-dimensional lattice geometry is needed — so the statement is rendered on the project's
`Fin (N+1)`-site Hubbard model with `d > 2` kept as an explicit hypothesis (the conclusion is false
in `d = 1`, so dropping `d > 2` would be unsound).

The proof squeezes the ground energy between Roth's projected trial state above and the
ferromagnetic occupation floor below: the first costs at most one extra level plus a hopping term
of order `K·ρ`, the second costs at least one extra level of size `c·ρ^{2/d}`, and sublinearity
`2/d < 1` makes `c·ρ^{2/d}` beat `K·ρ` below an explicit density threshold.

References: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.8)–(11.1.10), p. 376; Tasaki,
Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, Appendix F, eqs. (F.12)/(F.13), pp. 546–547.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math

variable {N : ℕ} (t : Fin (N + 1) → Fin (N + 1) → ℂ)

/-- **The dimensional band condition (Tasaki eq. (11.1.8))** on the ascending single-particle
energies `ε_1 ≤ ε_2 ≤ ⋯` (`ε 0 = ε_1`, `ε n = ε_{n+1}`): there are positive constants `c, ρ₀` and a
cutoff `n₀` such that for the `n`-th level (`n ≥ n₀`, `n/|Λ| ≤ ρ₀`)
`ε_n − ε_1 ≥ c·((n − n₀)/|Λ|)^{2/d}`.  The right-hand side is the `n`-dependence of the levels of a
single particle in `d` dimensions. -/
def hubbardBandCondition (ε : Fin (N + 1) → ℝ) (c ρ₀ : ℝ) (n₀ d : ℕ) : Prop :=
  ∀ n : Fin (N + 1), n₀ ≤ n.val + 1 → ((n.val + 1 : ℝ)) / (N + 1) ≤ ρ₀ →
    c * (((n.val + 1 - n₀ : ℝ)) / (N + 1)) ^ ((2 : ℝ) / (d : ℝ)) ≤ ε n - ε 0

/-- **Tasaki Theorem 11.4 (impossibility of ferromagnetism at low densities).**  Fix
`d > 2`, positive band constants `c, ρ₀`, a level cutoff `n₀` and a hopping scale `K`.  Then there
is a density threshold `ρ₁ > 0`, *uniform in the system size*, such that for any Hermitian,
translation-invariant hopping `t` whose row sums of `‖t x y‖` are at most `K` and whose ascending
single-particle spectrum `ε` satisfies the band condition (11.1.8), and any electron number `Ne`
with density `Ne/|Λ| ≤ ρ₁` and any `U ≥ 0`, the ground states at filling `Ne` are **not** all
maximal-spin: some ground state has `S_tot < S_max`.

As in Theorem 11.3 the conclusion negates the *pinned* ground-state max-spin property over the real
ground eigenspace `hubbardEigenspaceAt … E₀ Ne` (`E₀` nonempty `hne` and minimal `hmin`), so the
impossibility statement is sound.  Translation invariance is required genuinely (the symmetry `σ`
acts transitively, ruling out the trivial `σ = id`), and the filling is nontrivial (`2 ≤ Ne`, the
zero- and one-electron sectors are trivially maximal-spin).

Two hypotheses strengthen Tasaki's bare statement, in the idiom already used for the Hermiticity
hypotheses of Proposition 11.2.  `_hK` bounds the row sums of `t` uniformly by the outer parameter
`K`, which is what the variational estimate available here needs given the order of the
quantifiers: `ρ₁` is fixed before `t`, and that estimate weighs the kinetic cost of the trial state
against the band constant `c`, so the threshold it yields is governed by the ratio `c/K` and an
upper bound on the bandwidth has to be fixed in advance; every concrete `t` admits such a `K`, so
only the order of the quantifiers is restricted.  `_hNen₀` demands `2 * n₀ ≤ Ne`: the band
condition (11.1.8) constrains only the levels `n ≥ n₀` and measures its gap from the cutoff `n₀`.
The floor below is evaluated on a fully polarized state, whose `Ne` electrons occupy `Ne` distinct
levels, so the squeeze is applied at the `Ne`-th level; `n₀ ≤ Ne` is what puts that level inside
the constrained range, and the spare factor of two leaves the margin `ρ/2 ≤ (Ne − n₀)/|Λ|`, which
makes the band gap there at least `c·(ρ/2)^{2/d}` and hence comparable with the trial state's
kinetic cost `8·max(K,1)·ρ`.  Below the cutoff the band condition says nothing about the occupied
levels — the flat-band regime where ferromagnetism does occur — so this variational approach gives
no bound there.

The threshold produced is `ρ₁ = min ρ₀ (min (1/2) r)`, with `r` the crossing point supplied by
`exists_pos_forall_mul_lt_rpow` at `a = c/2^{2/d}` and `b = 8·max K 1`.  Taking `max K 1` rather
than `K` keeps `b` positive at `K = 0`, where the hypothesis `_hK` alone forces only `K ≥ 0`, and
costs nothing since `8Kρ ≤ 8·max(K,1)·ρ`.  The `1/2` supplies both `2|S_↑| ≤ |Λ|`, needed for the
Roth state to be normalizable, and `Ne ≤ |Λ|`, needed for the floor.

The upper bound is `rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le` evaluated on
the Roth state built from the `Ne − 1` lowest eigenmodes and the delocalized lowest mode furnished
by translation invariance; the lower bound is
`sum_lowestLevels_mul_le_rayleighOnVec_hubbardKinetic` evaluated on a top-weight ground state,
which exists precisely when the ground states are all maximal-spin. -/
theorem hubbard_theorem_11_4 (c ρ₀ K : ℝ) (hc : 0 < c) (hρ₀ : 0 < ρ₀) (n₀ d : ℕ) (hd : 2 < d) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧
      ∀ (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (ht : Matrix.IsHermitian t)
        (_hK : ∀ x : Fin (N + 1), ∑ y : Fin (N + 1), ‖t x y‖ ≤ K)
        (σ : Equiv.Perm (Fin (N + 1))) (_htrans : ∀ i j, t (σ i) (σ j) = t i j)
        (_htransitive : ∀ i j : Fin (N + 1), ∃ k : ℕ, (σ ^ k) i = j)
        (ε : Fin (N + 1) → ℝ) (_hmono : Monotone ε)
        (_hspec : Finset.univ.val.map ε = Finset.univ.val.map ht.eigenvalues)
        (_hband : hubbardBandCondition ε c ρ₀ n₀ d)
        (Ne : ℕ) (_hNe2 : 2 ≤ Ne) (_hNen₀ : 2 * n₀ ≤ Ne)
        (_hNe : (Ne : ℝ) / (N + 1) ≤ ρ₁)
        (U : ℝ) (_hU : 0 ≤ U) (E₀ : ℂ)
        (_hne : hubbardEigenspaceAt t (U : ℂ) E₀ Ne ≠ ⊥)
        (_hmin : ∀ E : ℂ, hubbardEigenspaceAt t (U : ℂ) E Ne ≠ ⊥ → E₀.re ≤ E.re),
        ¬ ∀ v ∈ hubbardEigenspaceAt t (U : ℂ) E₀ Ne,
          (fermionTotalSpinSquared N).mulVec v
            = (((Ne : ℂ) / 2) * ((Ne : ℂ) / 2 + 1)) • v := by
  classical
  have hdR : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set p : ℝ := (2 : ℝ) / (d : ℝ) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  have hp1 : p < 1 := by rw [hp, div_lt_one (by linarith)]; linarith
  have h2p : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have ha : 0 < c / 2 ^ p := div_pos hc h2p
  have hKp : (0 : ℝ) < 8 * max K 1 := by
    have h1 : (1 : ℝ) ≤ max K 1 := le_max_right K 1
    linarith
  obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_mul_lt_rpow ha hKp hp1
  refine ⟨min ρ₀ (min (1 / 2) r), lt_min hρ₀ (lt_min (by norm_num) hrpos), ?_⟩
  intro N t ht hK σ htrans htransitive ε hmono hspec hband Ne hNe2 hNen₀ hNe U hU E₀ hne hmin
    hferro
  have hNspos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNeR : (2 : ℝ) ≤ (Ne : ℝ) := by exact_mod_cast hNe2
  set ρ : ℝ := (Ne : ℝ) / ((N : ℝ) + 1) with hρdef
  have hρpos : 0 < ρ := div_pos (by linarith) hNspos
  have hρ₀le : ρ ≤ ρ₀ := le_trans hNe (min_le_left _ _)
  have hρhalf : ρ ≤ 1 / 2 := le_trans hNe (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρr : ρ ≤ r := le_trans hNe (le_trans (min_le_right _ _) (min_le_right _ _))
  have hNeNs : 2 * Ne ≤ N + 1 := by
    have h : 2 * (Ne : ℝ) ≤ (N : ℝ) + 1 := by
      rw [hρdef, div_le_div_iff₀ hNspos (by norm_num : (0 : ℝ) < 2)] at hρhalf
      linarith
    exact_mod_cast h
  obtain ⟨n, rfl⟩ : ∃ n, Ne = n + 2 := ⟨Ne - 2, by omega⟩
  have hk : n + 2 ≤ N + 1 := by omega
  have hk' : n + 1 ≤ N + 1 := Nat.le_of_succ_le hk
  have hht : ∀ i j, star (t i j) = t j i := fun i j => ht.apply j i
  have hhU : star ((U : ℝ) : ℂ) = ((U : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  obtain ⟨v, hv, hmodcard⟩ := exists_uniformModulus_eigenvector_of_transitive_perm_invariance
    htrans htransitive (eigenspace_mulVecLin_ne_bot_of_map_eq ht hspec 0)
  have hmod : ∀ x : Fin (N + 1), ‖v x‖ ^ 2 = 1 / ((N : ℝ) + 1) := by
    intro x
    rw [hmodcard x, Fintype.card_fin]
    push_cast
    ring
  obtain ⟨SUp, hSUpcard, hSUpsum⟩ :=
    exists_lowestLevels_finset_of_map_eq (k := n + 1) hk' hmono hspec
  have hocc : (occupiedEigenEnergy ht SUp ∅).re = ∑ i : Fin (n + 1), ε (Fin.castLE hk' i) := by
    rw [occupiedEigenEnergy, Finset.sum_empty, add_zero, ← Complex.ofReal_sum, Complex.ofReal_re,
      hSUpsum]
  have hhalf : 2 * (SUp.card : ℝ) ≤ (N : ℝ) + 1 := by
    rw [hSUpcard]
    have h : ((2 * (n + 1) : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    push_cast at h ⊢
    linarith
  set Ψ := hubbardLowDensityRothState (eigenbasisAsBasis ht) SUp v with hΨ
  have hnrmpos : 0 < (star Ψ ⬝ᵥ Ψ).re :=
    dotProduct_star_self_hubbardLowDensityRothState_pos ht SUp hmod hhalf
  have hsector : (fermionTotalNumber (2 * N + 1)).mulVec Ψ = ((n + 2 : ℕ) : ℂ) • Ψ := by
    rw [hΨ, fermionTotalNumber_mulVec_hubbardLowDensityRothState, hSUpcard]
  haveI hNEsec : Nonempty (hubbardSectorConfig N (n + 2)) := by
    obtain ⟨v0, hv0mem, hv0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨hHv0, hNum⟩ := (mem_hubbardEigenspaceAt t ((U : ℝ) : ℂ)).mp hv0mem
    obtain ⟨wcfg, hwcfg⟩ := Function.ne_iff.mp hv0ne
    simp only [Pi.zero_apply] at hwcfg
    refine ⟨⟨wcfg, ?_⟩⟩
    by_contra hcount
    exact hwcfg (mulVec_apply_eq_zero_of_number_ne N v0 ((n + 2 : ℕ) : ℂ) hNum wcfg
      (fun hcc => hcount (by exact_mod_cast hcc)))
  have hvar := hubbardSector_minEnergy_mul_le_rayleighOnVec (N := N) (n + 2) hht hhU hsector
  obtain ⟨E, hEval, hEne⟩ :=
    hubbardSector_minEnergy_eigenspace_ne_bot (N := N) (n + 2) hht hhU
  have hE₀le : E₀.re ≤ E.re := hmin E hEne
  have hEre : E.re = hermitianMinEigenvalue (configSectorCompress_isHermitian
      (hubbardNumberSectorPred N (n + 2)) (hubbardHamiltonian_isHermitian N hht hhU)) := by
    rw [hEval, Complex.ofReal_re]
  have hcap := rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le ht SUp hv hmod hK
    hhalf U
  rw [← hΨ] at hcap
  have hEupper : E₀.re ≤ (∑ i : Fin (n + 1), ε (Fin.castLE hk' i)) + ε 0
      + 8 * K * ((SUp.card : ℝ) / ((N : ℝ) + 1)) := by
    refine le_of_mul_le_mul_right ?_ hnrmpos
    rw [hocc] at hcap
    have h1 : E₀.re * (star Ψ ⬝ᵥ Ψ).re ≤ E.re * (star Ψ ⬝ᵥ Ψ).re :=
      mul_le_mul_of_nonneg_right hE₀le (le_of_lt hnrmpos)
    rw [hEre] at h1
    linarith [hvar, hcap, h1]
  obtain ⟨u, humem, hu0, huZ⟩ :=
    exists_topWeight_of_maxSpin t ((U : ℝ) : ℂ) (n + 2) hferro hne
  obtain ⟨hHu, hNu⟩ := (mem_hubbardEigenspaceAt t ((U : ℝ) : ℂ)).mp humem
  have hdown := fermionTotalDownNumber_mulVec_eq_zero_of_topWeight (Ne := n + 2) hNu huZ
  have hint : (hubbardOnSiteInteraction N ((U : ℝ) : ℂ)).mulVec u = 0 :=
    hubbardOnSiteInteraction_mulVec_eq_zero_of_downNumber_zero N ((U : ℝ) : ℂ) hdown
  have hPu : (star u ⬝ᵥ u) = (((star u ⬝ᵥ u).re : ℝ) : ℂ) := by
    rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_re]
  have hPupos : 0 < (star u ⬝ᵥ u).re := dotProduct_star_self_re_pos hu0
  have hray : rayleighOnVec (hubbardHamiltonian N t ((U : ℝ) : ℂ)) u
      = rayleighOnVec (hubbardKinetic N t) u := by
    unfold rayleighOnVec
    rw [hubbardHamiltonian, Matrix.add_mulVec, dotProduct_add, hint, dotProduct_zero, add_zero]
  have hswap : E₀ * (star u ⬝ᵥ u) = (((star u ⬝ᵥ u).re : ℝ) : ℂ) * E₀ := by
    rw [← hPu]; ring
  have hrayE : rayleighOnVec (hubbardHamiltonian N t ((U : ℝ) : ℂ)) u
      = E₀.re * (star u ⬝ᵥ u).re := by
    unfold rayleighOnVec
    rw [hHu, dotProduct_smul, smul_eq_mul, hswap, Complex.re_ofReal_mul]
    ring
  have hfloor := sum_lowestLevels_mul_le_rayleighOnVec_hubbardKinetic ht hk hmono hspec hu0
    hdown hNu
  have hEfloor : (∑ i : Fin (n + 2), ε (Fin.castLE hk i)) ≤ E₀.re := by
    refine le_of_mul_le_mul_right ?_ hPupos
    rw [← hrayE, hray]
    exact hfloor
  have hsplit : (∑ i : Fin (n + 2), ε (Fin.castLE hk i))
      = (∑ i : Fin (n + 1), ε (Fin.castLE hk' i)) + ε ⟨n + 1, hk⟩ :=
    sum_lowestLevels_succ (k := n + 1) hk
  rw [hsplit] at hEfloor
  have hKnn : (0 : ℝ) ≤ K := le_trans (Finset.sum_nonneg fun y _ => norm_nonneg (t 0 y)) (hK 0)
  have hρup : (SUp.card : ℝ) / ((N : ℝ) + 1) ≤ ρ := by
    rw [hρdef, hSUpcard]
    gcongr
    omega
  have hgap : ε ⟨n + 1, hk⟩ - ε 0 ≤ 8 * max K 1 * ρ := by
    have h1 : 8 * K * ((SUp.card : ℝ) / ((N : ℝ) + 1)) ≤ 8 * K * ρ :=
      mul_le_mul_of_nonneg_left hρup (by linarith)
    have h2 : 8 * K * ρ ≤ 8 * max K 1 * ρ :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left K 1]) (le_of_lt hρpos)
    linarith
  set jtop : Fin (N + 1) := ⟨n + 1, hk⟩ with hjtop
  have hjval : (jtop : ℕ) = n + 1 := rfl
  have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
  have hband1 : (((jtop : ℕ) : ℝ) + 1) / ((N : ℝ) + 1) ≤ ρ₀ := by
    rw [hjval, hcast, ← hρdef]
    exact hρ₀le
  have hbandapp := hband jtop (by rw [hjval]; omega) hband1
  rw [hjval] at hbandapp
  have hn₀ : (2 : ℝ) * (n₀ : ℝ) ≤ (n : ℝ) + 2 := by
    have h : ((2 * n₀ : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_le.mpr hNen₀
    push_cast at h
    linarith
  have hqhalf : ρ / 2 ≤ (((n + 1 : ℕ) : ℝ) + 1 - (n₀ : ℝ)) / ((N : ℝ) + 1) := by
    rw [hρdef, div_div, div_le_div_iff₀ (by linarith) hNspos]
    push_cast
    have hprod : (0 : ℝ) ≤ ((N : ℝ) + 1) * ((n : ℝ) + 2 - 2 * (n₀ : ℝ)) :=
      mul_nonneg (le_of_lt hNspos) (by linarith)
    nlinarith [hprod]
  have hchain : c * ((ρ / 2) ^ p) ≤ ε jtop - ε 0 :=
    le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hqhalf (le_of_lt hppos)) (le_of_lt hc)) hbandapp
  have hsplitp : c * ((ρ / 2) ^ p) = c / 2 ^ p * ρ ^ p := by
    rw [Real.div_rpow (le_of_lt hρpos) (by norm_num)]
    field_simp
  have hT1 := hr ρ hρpos hρr
  linarith [hgap, hchain, hT1, hsplitp]

end LatticeSystem.Fermion
