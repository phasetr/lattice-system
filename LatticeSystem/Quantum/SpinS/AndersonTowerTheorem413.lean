import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaCapstone
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaLowerBounds
import LatticeSystem.Quantum.SpinS.AndersonTowerField
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisProofCore

/-!
# Tasaki §4.2.1 Theorem 4.13 — SSB under an infinitesimal staggered field (axiom-free)

This module hosts **Theorem 4.13**, `tanakaSSB_field_lowerBound`, **proved** (no book axiom): for
the staggered-field Hamiltonian `Ĥ_h = Ĥ − h Ô_L^{(1)}` (eq. (4.2.27)) with a *given* field ground
state `Φ_{GS,h,L}`, the per-site staggered moment survives the iterated limit
`lim_{h↓0} liminf_{L↑∞}` and is bounded below by the SSB order parameter `m∗` (eq. (4.2.28)),
`lim_{h↓0} liminf_{L↑∞} ⟨Φ_{GS,h,L}| Ô_L^{(1)}/L^d |Φ_{GS,h,L}⟩ ≥ m∗`
(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer, 2020,
§4.2.1, Theorem 4.13, eqs. (4.2.27)–(4.2.28), pp. 102–103, footnote 26 "rigorously `liminf`").

The proof is the **Rayleigh–Ritz variational method** of §3.4, Theorem 3.2 (Kaplan–Horsch–von der
Linden), pp. 69–70 (p. 102: "Repeating the variational proof by using `|Ξ(1,0,0)⟩` as a trial
state"): the Tanaka symmetry-breaking state `Ξ_L = tanakaSSBState A N (M L) (Φ₀ L)` (eq. (4.2.10))
is the trial state, its energy bounded by the proved companion
`tanakaSSB_realizingFamily_energyBound` (Theorem 4.8, eq. (4.2.11)), and its per-site staggered
moment converges to `m∗` by the realizing family's own limit (eq. (4.2.12)).  Neither Conjecture
4.12 nor Theorem 4.11 is consumed, so `#print axioms tanakaSSB_field_lowerBound` lists only the
standard three (`propext`, `Classical.choice`, `Quot.sound`) — **completely axiom-free**.
Together with Theorem 4.11 (`√(3 q₀) ≤ m∗`) it yields the strictly positive SSB order parameter.
The realizing family is unsatisfiable in `d = 1` (no long-range order, Corollary 4.3), so the
statement is vacuous there.

This module also hosts the proved trial-energy input `tanakaSSB_realizingFamily_energyBound` and the
four generic finite-dimensional Hermitian linear-algebra lemmas powering the variational argument.

Reference: Hal Tasaki, §4.2.1, Theorem 4.13, eqs. (4.2.27)–(4.2.28), pp. 102–103; §3.4, Theorem 3.2,
pp. 69–70; §4.2.2, Theorem 4.8, eq. (4.2.11), p. 98.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **The staggered-field Hamiltonian is Hermitian.**  `Ĥ_h = Ĥ − h Ô_L^{(1)}` is the difference of
the Hermitian Heisenberg torus Hamiltonian (`heisenbergHamiltonianS_torus_isHermitian`) and the real
(`h`) scalar multiple of the Hermitian `1`-axis staggered order operator
(`staggeredOrderOp1S_isHermitian`), hence Hermitian. -/
theorem staggeredFieldHamiltonianS_isHermitian (d L N : ℕ) [NeZero L] (h : ℝ) :
    (staggeredFieldHamiltonianS d L N h).IsHermitian := by
  unfold staggeredFieldHamiltonianS
  refine (heisenbergHamiltonianS_torus_isHermitian d L N).sub
    ((staggeredOrderOp1S_isHermitian (torusParitySublattice d L) N).smul ?_)
  rw [isSelfAdjoint_iff]
  exact Complex.conj_ofReal h

/-- **Minimum-eigenvalue Rayleigh lower bound (generic).**  For a Hermitian `H` whose eigenvalue
`E₀` is the spectral minimum (`hmin`: every eigenvalue's real part dominates `E₀.re`), the real
Rayleigh quotient of *any* nonzero vector `v` is at least `E₀.re`.  Chains
`E₀.re ≤ hermitianMinEigenvalue H ≤ expectationRatioRe H v`: the minimality step feeds `hmin` at the
minimum-eigenvalue eigenvector, and the Rayleigh step is the shared core
`hermitianMinEigenvalue_le_expectationRatioRe`.  Spectral-minimizer companion of the ground-energy
form `groundEnergy_le_expectationRatioRe_general`, used for both `Ĥ` and `Ĥ_h`. -/
theorem minimizerEigenvalue_le_expectationRatioRe {ι : Type*} [Fintype ι] [Nonempty ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E₀ : ℂ)
    (hmin : ∀ E : ℂ, ∀ Ψ : ι → ℂ, Ψ ≠ 0 → H.mulVec Ψ = E • Ψ → E₀.re ≤ E.re)
    {v : ι → ℂ} (hv : v ≠ 0) :
    E₀.re ≤ expectationRatioRe H v := by
  classical
  obtain ⟨w, hw0, hweig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hH
  have h2 : E₀.re ≤ hermitianMinEigenvalue hH := by
    have := hmin ((hermitianMinEigenvalue hH : ℝ) : ℂ) w hw0 hweig
    rwa [Complex.ofReal_re] at this
  exact le_trans h2 (hermitianMinEigenvalue_le_expectationRatioRe hH hv)

/-- **Rayleigh-quotient operator linearity in a real staggered field.**  For real `c`,
`expectationRatioRe (O₁ − c • O₂) v = expectationRatioRe O₁ v − c · expectationRatioRe O₂ v` (common
denominator `⟨v, v⟩.re`; `c` real so its scalar factors through `.re`).  This is the algebraic step
that peels the field `−h Ô` off the Rayleigh quotient of `Ĥ_h`. -/
theorem expectationRatioRe_sub_smul_real {ι : Type*} [Fintype ι]
    (O₁ O₂ : Matrix ι ι ℂ) (c : ℝ) (v : ι → ℂ) :
    expectationRatioRe (O₁ - (c : ℂ) • O₂) v =
      expectationRatioRe O₁ v - c * expectationRatioRe O₂ v := by
  unfold expectationRatioRe
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul]
  ring

/-- **Rayleigh quotient of an eigenvector equals the eigenvalue's real part (generic).**  For a
nonzero eigenvector `v` of `H` at (complex) eigenvalue `E`, `expectationRatioRe H v = E.re`, since
`⟨v, v⟩` is real so `⟨v, E v⟩.re = E.re · ⟨v, v⟩.re`.  Generic companion of the real-eigenvalue
`expectationRatioRe_of_eigenvector_general`. -/
theorem expectationRatioRe_eigenvalue_re {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (v : ι → ℂ) (E : ℂ) (hne : v ≠ 0)
    (heig : H.mulVec v = E • v) :
    expectationRatioRe H v = E.re := by
  have hpos : 0 < (star v ⬝ᵥ v).re := dotProduct_star_self_re_pos hne
  have him : (star v ⬝ᵥ v).im = 0 := by
    classical
    have hsum : (star v ⬝ᵥ v) = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def]
      push_cast
      exact Finset.sum_congr rfl (fun i _ => (Complex.normSq_eq_conj_mul_self ..).symm)
    rw [hsum, Complex.ofReal_im]
  unfold expectationRatioRe
  rw [heig, dotProduct_smul, smul_eq_mul, Complex.mul_re, him, mul_zero, sub_zero,
    mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- **Tasaki Theorem 4.8 trial-energy input for a realizing family, PROVED (axiom-free).**  For a
realizing Tanaka ground-state family (`hFamily : IsRealizingTanakaGroundStateFamily
d N q₀ mStar C₁ Φ E₀ M`), there is a constant `C₂ > 0` and a threshold `L₀` beyond which every
even-side torus obeys the Tanaka symmetry-breaking trial-energy bound (eq. (4.2.11), p. 98)
`⟨Ξ, Ĥ Ξ⟩ / ⟨Ξ, Ξ⟩ ≤ (E₀ L).re + C₂ (M(L) + 1)² / L^d`, with `Ξ = tanakaSSBState A N (M L) (Φ L)`.

Proof (all axiom-free, given Theorem 4.8 proved).  Run Theorem 4.8
(`tanakaSSB_lowLying_energy_bound`) at `q₀' := q₀/2` to fix `C₁_E, C₂_E` with
`IsTanakaSSBConstants d N (q₀/2) C₁_E C₂_E`; set `C₂ := C₂_E`.  Instantiate the family's
`o(L^{d/2})` slow-divergence conjunct at `c := C₁_E` to get the Theorem 4.8 **gate**
`M(L) + 1 ≤ C₁_E L^{d/2}` eventually, and the long-range-order limit conjunct at `ε := q₀/2` to get
`q₀/2 ≤ ⟨Φ, ô² Φ⟩ / (⟨Φ,Φ⟩ V²)` eventually.  Beyond the max of the three thresholds, feed
`IsTanakaSSBConstants` its verbatim block hypotheses (eigenvector, minimizer, `Φ ≠ 0`, singlet
`Ŝ³Φ = Ŝ¹Φ = 0`, `0 < M L`, tower positivity) together with the gate and the LRO bound; it fires
the trial-energy inequality.

`#print axioms tanakaSSB_realizingFamily_energyBound` = `propext`, `Classical.choice`, `Quot.sound`
only.  This is the companion consumed by Theorem 4.13 (`tanakaSSB_field_lowerBound`); with Theorem
4.11 it yields `m∗ ≥ √(3 q₀) > 0`.  Unsatisfiable in `d = 1` (Corollary 4.3), so vacuous there.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Theorem 4.8, eq. (4.2.11), p. 98; Theorem 4.9, footnote 21, p. 98. -/
theorem tanakaSSB_realizingFamily_energyBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (_hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      (star (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) ⬝ᵥ
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
            (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L))).re /
        (star (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) ⬝ᵥ
          tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)).re ≤
      (E₀ L).re + C₂ * ((M L : ℝ) + 1) ^ 2 / (L : ℝ) ^ d := by
  -- Theorem 4.8 at `q₀/2` fixes the constants `C₁_E`, `C₂_E`.
  obtain ⟨C₁_E, C₂_E, _hAnd, hSSB⟩ :=
    tanakaSSB_lowLying_energy_bound d N hd (q₀ / 2) (by positivity)
  -- Family per-`L` block, `o(L^{d/2})` growth (at `c := C₁_E`), and LRO limit (at `ε := q₀/2`).
  obtain ⟨L₁_block, hblock⟩ := hFamily.2.1
  obtain ⟨L_gate, hgate⟩ := hFamily.2.2.2.2.2 C₁_E hSSB.1
  obtain ⟨L_lro, hlro⟩ := hFamily.2.2.1 (q₀ / 2) (by positivity)
  refine ⟨C₂_E, hSSB.2.1, max (max L₁_block L_gate) L_lro, fun L _ hL h2 hev => ?_⟩
  have hLb : L₁_block ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLg : L_gate ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLl : L_lro ≤ L := le_trans (le_max_right _ _) hL
  -- Verbatim block conjuncts (reversal `_hrev` and the `O`-form growth `_hMO` are unused here).
  obtain ⟨hev0, hmin, hne, hs3, hs1, _hrev, hMpos, _hMO, htw1, htw2, hst⟩ :=
    hblock L hLb h2 hev
  -- LRO limit ⟹ `q₀/2 ≤` ratio (the Theorem 4.8 per-`L` LRO premise at `q₀' = q₀/2`).
  have hlroL := hlro L hLl h2 hev
  rw [abs_lt] at hlroL
  have hq2 : q₀ / 2 ≤ (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
      staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
      ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) := by linarith [hlroL.1]
  -- Feed Theorem 4.8 (`IsTanakaSSBConstants`) its hypotheses; the gate is `hgate L …`.
  exact hSSB.2.2 L h2 hev (Φ L) (E₀ L) (M L) hev0 hmin hne hs3 hs1 hq2 hMpos
    (hgate L hLg h2 hev) htw1 htw2 hst

set_option maxHeartbeats 800000 in -- large explicit-constant variational Rayleigh inequality
/-- **Tasaki Theorem 4.13 (SSB under an infinitesimal staggered field), PROVED (axiom-free).**  For
the staggered-field Hamiltonian `Ĥ_h = Ĥ − h Ô_L^{(1)}` (eq. (4.2.27)), the per-site staggered
moment of any given field ground state `Φ_{GS,h,L}` survives the iterated limit
`lim_{h↓0} liminf_{L↑∞}` and is bounded below by the SSB order parameter `m∗` (eq. (4.2.28)): for
every `ε > 0` there is a field threshold `δ > 0` (`δ = 1` works) so that for each `0 < h < δ` there
is a size threshold `L₀` (depending on `h`) beyond which every even-side field ground state has
`m∗ − ε ≤ ⟨Φ_{GS,h,L}, Ô_L^{(1)} Φ_{GS,h,L}⟩.re / L^d`.

Proof — the Rayleigh–Ritz (Kaplan–Horsch–von der Linden) variational method of §3.4, Theorem 3.2,
with the Tanaka state `Ξ_L = tanakaSSBState A N (M L) (Φ₀ L)` (eq. (4.2.10)) as trial state.  Write
`R_A(v) = expectationRatioRe A v`.  Hermiticity of `Ĥ`/`Ĥ_h` gives (V1) `(EField h L).re ≤
R_{Ĥ_h}(Ξ)` and (V2) `(E₀ L).re ≤ R_{Ĥ}(Φ_{GS,h,L})`; the eigenvector identity gives
`R_{Ĥ_h}(Φ_{GS,h,L}) = (EField h L).re`; Rayleigh linearity peels the field,
`R_{Ĥ_h}(v) = R_{Ĥ}(v) − h R_{Ô}(v)`.  Chaining and dividing by `hV = hL^d > 0` gives (eq. (4.2.28))
`R_{Ô}(Φ_{GS,h,L})/V ≥ R_{Ô}(Ξ)/V + (E₀.re − R_{Ĥ}(Ξ))/(hV)`.  The error term vanishes as `L↑∞` by
the proved companion `tanakaSSB_realizingFamily_energyBound` (Theorem 4.8) with the growth bound
`(M L+1)² ≤ C₁² V`; the leading term `R_{Ô}(Ξ)/V = tanakaOrderMean1 …` converges to `m∗` by the
family's staggered-moment limit (eq. (4.2.12)).  The field threshold `δ = 1` is free (the bound
holds for every `h > 0`); `h` enters only through `L₀`.

Neither Conjecture 4.12 nor Theorem 4.11 is consumed, so
`#print axioms tanakaSSB_field_lowerBound` = `propext`, `Classical.choice`, `Quot.sound` only —
**completely axiom-free**.  Combined with Theorem 4.11 (`tanakaSSB_orderParameter_lowerBound`,
`√(3 q₀) ≤ m∗`) it yields the strictly positive SSB order parameter.  The realizing family is
unsatisfiable in `d = 1` (Corollary 4.3), so the statement is vacuous there.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1, Theorem 4.13, eqs. (4.2.27)–(4.2.28), pp. 102–103 (footnote 26: rigorously `liminf`);
§3.4, Theorem 3.2, pp. 69–70 (Kaplan–Horsch–von der Linden variational template). -/
theorem tanakaSSB_field_lowerBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ₀ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ₀ E₀ M)
    (PhiGS : ℝ → (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (EField : ℝ → ℕ → ℂ)
    (hField : ∀ h : ℝ, 0 < h → ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (staggeredFieldHamiltonianS d L N h).mulVec (PhiGS h L) = EField h L • PhiGS h L ∧
      (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (staggeredFieldHamiltonianS d L N h).mulVec Ψ = E • Ψ → (EField h L).re ≤ E.re) ∧
      PhiGS h L ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        mStar - ε ≤
          expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) N) (PhiGS h L) /
            (L : ℝ) ^ d := by
  intro ε hε
  refine ⟨1, one_pos, fun h hh0 _hhδ => ?_⟩
  -- Proved trial-energy companion (Theorem 4.8), the family block/limits, and the size threshold.
  obtain ⟨C₂, hC₂, L_E, henergy⟩ :=
    tanakaSSB_realizingFamily_energyBound d N hd q₀ mStar C₁ hq₀ hC₁ Φ₀ E₀ M hFamily
  obtain ⟨L_field, hfield⟩ := hField h hh0
  obtain ⟨L_blk, hblk⟩ := hFamily.2.1
  obtain ⟨L_mom, hmom⟩ := hFamily.2.2.2.1 (ε / 2) (by positivity)
  set K : ℝ := 2 * C₂ * C₁ ^ 2 / (h * ε) with hKdef
  refine ⟨max (max (max L_field L_blk) (max L_E L_mom)) (⌊K⌋₊ + 1), fun L _ hLmax hle2 hev => ?_⟩
  simp only [max_le_iff] at hLmax
  obtain ⟨⟨⟨hL_field, hL_blk⟩, hL_E, hL_mom⟩, hLsize⟩ := hLmax
  -- Positivity facts.
  have hLnat : 0 < L := by omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLnat
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLnat
  -- Raw field/family data and Hermiticity, obtained *before* abbreviating so that the subsequent
  -- `set` commands fold every occurrence uniformly (avoiding costly `let`-unfold defeq later).
  obtain ⟨heig_field, hmin_field, hPgs_ne⟩ := hfield L hL_field hle2 hev
  obtain ⟨_hev0, hmin_H, _hΦ0, _hs3, _hs1, _hrev, _hMpos, hMgrow, _hn1, _hn2, hΞnorm⟩ :=
    hblk L hL_blk hle2 hev
  have hHh_herm := staggeredFieldHamiltonianS_isHermitian d L N h
  have hH_herm := heisenbergHamiltonianS_torus_isHermitian d L N
  have hΞ_ne : tanakaSSBState (torusParitySublattice d L) N (M L) (Φ₀ L) ≠ 0 := by
    intro h0
    rw [h0] at hΞnorm
    simp only [vecNormSqRe, star_zero, zero_dotProduct, Complex.zero_re, lt_self_iff_false]
      at hΞnorm
  have hV1 := minimizerEigenvalue_le_expectationRatioRe hHh_herm (EField h L) hmin_field hΞ_ne
  have h3 := minimizerEigenvalue_le_expectationRatioRe hH_herm (E₀ L) hmin_H hPgs_ne
  have h4raw := henergy L hL_E hle2 hev
  have hmomL := hmom L hL_mom hle2 hev
  -- Operator/vector abbreviations (fold all occurrences in the hypotheses above).
  set HH := heisenbergHamiltonianS (torusNNCoupling d L) N with hHH
  set OO := staggeredOrderOp1S (torusParitySublattice d L) N with hOO
  set Xi := tanakaSSBState (torusParitySublattice d L) N (M L) (Φ₀ L) with hXi
  set Pgs := PhiGS h L with hPgs
  set V := (L : ℝ) ^ d with hVdef
  have hV0 : (0 : ℝ) < V := by rw [hVdef]; exact pow_pos hLpos d
  -- Field Hamiltonian as `Ĥ − h Ô`; Rayleigh linearity chained through it (V1) and the eigenvector.
  have hHhdef : staggeredFieldHamiltonianS d L N h = HH - (h : ℂ) • OO := by
    simp only [hHH, hOO, staggeredFieldHamiltonianS]
  have h1 : (EField h L).re ≤ expectationRatioRe HH Xi - h * expectationRatioRe OO Xi := by
    rw [← expectationRatioRe_sub_smul_real HH OO h Xi, ← hHhdef]; exact hV1
  have h2 : expectationRatioRe HH Pgs - h * expectationRatioRe OO Pgs = (EField h L).re := by
    rw [← expectationRatioRe_sub_smul_real HH OO h Pgs, ← hHhdef]
    exact expectationRatioRe_eigenvalue_re _ Pgs (EField h L) hPgs_ne heig_field
  -- trial energy bound (Theorem 4.8 companion), rewritten into Rayleigh form.
  have h4 : expectationRatioRe HH Xi ≤ (E₀ L).re + C₂ * ((M L : ℝ) + 1) ^ 2 / V := by
    unfold expectationRatioRe; exact h4raw
  -- growth `(M L+1)² ≤ C₁² V`.
  have hrpow_sq : ((L : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = V := by
    rw [hVdef, ← Real.rpow_natCast ((L : ℝ) ^ ((d : ℝ) / 2)) 2, ← Real.rpow_mul hLpos.le,
      ← Real.rpow_natCast (L : ℝ) d]
    congr 1
    push_cast; ring
  have h5 : ((M L : ℝ) + 1) ^ 2 ≤ C₁ ^ 2 * V := by
    have hnn : (0 : ℝ) ≤ (M L : ℝ) + 1 := by positivity
    have hrhs_nn : (0 : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) := by positivity
    calc ((M L : ℝ) + 1) ^ 2 ≤ (C₁ * (L : ℝ) ^ ((d : ℝ) / 2)) ^ 2 := by
          nlinarith [hMgrow, hnn, hrhs_nn]
      _ = C₁ ^ 2 * ((L : ℝ) ^ ((d : ℝ) / 2)) ^ 2 := by ring
      _ = C₁ ^ 2 * V := by rw [hrpow_sq]
  -- leading term `R_Ô(Ξ)/V > m∗ − ε/2`.
  have h6 : mStar - ε / 2 < expectationRatioRe OO Xi / V := by
    have heq : tanakaOrderMean1 d L N (M L) (Φ₀ L) = expectationRatioRe OO Xi / V := by
      simp only [tanakaOrderMean1, hOO, hXi, hVdef]
    rw [heq, abs_lt] at hmomL
    linarith [hmomL.1]
  -- cleared master inequalities.
  have hpEG : expectationRatioRe HH Xi - (E₀ L).re ≤ C₂ * C₁ ^ 2 := by
    have hdiv : C₂ * ((M L : ℝ) + 1) ^ 2 / V ≤ C₂ * C₁ ^ 2 := by
      rw [div_le_iff₀ hV0]; nlinarith [mul_le_mul_of_nonneg_left h5 hC₂.le]
    linarith [h4, hdiv]
  have hb1_cleared :
      h * expectationRatioRe OO Xi - C₂ * C₁ ^ 2 ≤ h * expectationRatioRe OO Pgs := by
    linarith [h1, h2, h3, hpEG]
  -- size threshold `V > 2 C₂ C₁² / (h ε)`.
  have hKlt : K < (L : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one K) (by exact_mod_cast hLsize)
  have hLleV : (L : ℝ) ≤ V := by
    rw [hVdef]
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have h7 : K < V := lt_of_lt_of_le hKlt hLleV
  have hCC : C₂ * C₁ ^ 2 < ε / 2 * (h * V) := by
    rw [hKdef, div_lt_iff₀ (by positivity : (0 : ℝ) < h * ε)] at h7
    nlinarith [h7, hh0, hV0]
  have hQ : (mStar - ε / 2) * V < expectationRatioRe OO Xi := (lt_div_iff₀ hV0).mp h6
  rw [le_div_iff₀ hV0]
  nlinarith [hb1_cleared, mul_lt_mul_of_pos_left hQ hh0, hCC, hh0, hV0, mul_pos hh0 hV0]

end LatticeSystem.Quantum
