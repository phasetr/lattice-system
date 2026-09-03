import LatticeSystem.Quantum.KaplanHorschVonderLindenTheorem32
import LatticeSystem.Quantum.SpinS.HorschVonderLindenAfmRing
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingGroundData

/-!
# Tasaki §4.1: absence of long-range order in one dimension (Corollary 4.3), conditional

Tasaki proves Corollary 4.3 by contraposition against Theorem 3.2 (p. 77): "The condition (3.4.4)
for Theorem 3.2 is satisfied because of the Marshall–Lieb–Mattis theorem.  Since the conclusion
(3.4.22) of Theorem 3.2 does not hold, the other condition (3.4.3) must be violated."  That is the
route taken here.  `no_long_range_order_1d_of_theorem_4_2` assumes Theorem 4.2's conclusion
verbatim and derives Corollary 4.3; `no_long_range_order_1d` is its application to
`shastry_no_symmetry_breaking_1d`.

**This discharges nothing.**  Corollary 4.3 now rests on the documented axiom `shastryEnergyGain`,
the scalar staggered-field energy-gain condition behind Theorem 4.2, instead of on a susceptibility
axiom of its own; `#print axioms no_long_range_order_1d` names `shastryEnergyGain`.  Both
Corollary 4.3 and Theorem 4.2 remain **open**: Tasaki does not prove Theorem 4.2 (footnote 3,
p. 76), and nothing here reconstructs the argument he cites.  What changes is which unproved
statement the corollary is charged to — its own, strictly stronger susceptibility assumption
before, Theorem 4.2's own missing input now, which is the input Tasaki's own proof uses.  Only the
degenerate spin-`0` case `N = 0` is unconditional.

The contraposition runs at a **single** volume.  Negating Corollary 4.3's conclusion produces one
even `L`, as large as required, carrying staggered long-range order; eq. (3.4.16) turns that into a
low-lying trial state at that `L`, and the single-volume inequality
`tasaki_eq_3_4_21_perVolume_energyBound` turns the trial state into a lower bound on the staggered
moment of the field ground state there, contradicting Theorem 4.2.  The Theorem 3.2 capstone
`tasaki_theorem_3_2_kaplanHorschVonderLinden` is *not* usable for this: its family form assumes
long-range order at every `L`, which the negation of an `∃ L₀, ∀ L ≥ L₀` statement does not supply.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Corollary 4.3, eq. (4.1.11), p. 77 (proof: contraposition against Theorem 3.2, p. 70,
and Theorem 4.2, p. 76, footnote 3, p. 76); §3.4, eqs. (3.4.3), (3.4.16), (3.4.21), pp. 65–70.
-/

namespace LatticeSystem.Quantum

open Matrix Module
open scoped ComplexOrder

/-- The staggered order operator is the zero operator at spin `S = 0` (`N = 0`): the single-site
spin-`3` matrix `spinSOp3 0` is the `1 × 1` diagonal with entry `(0/2 - 0) = 0`, so each summand
`ε_x • Ŝ_x^{(3)}` vanishes.  This makes the (squared) staggered order parameter trivially zero for
the degenerate spin-`0` chain, discharging the `N = 0` case of Corollary 4.3 unconditionally. -/
private theorem staggeredOrderOpS_spin_zero {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) :
    staggeredOrderOpS A 0 = 0 := by
  have h3 : spinSOp3 0 = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [spinSOp3]
  rw [staggeredOrderOpS]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [spinSSiteOp3_def, h3, onSiteS_zero, smul_zero]

/-- **Tasaki Corollary 4.3 from Theorem 4.2 (his own proof, by contraposition), CONDITIONAL
THEOREM.**  Assuming `h42` — the conclusion of Theorem 4.2 (eq. (4.1.10), p. 77) verbatim, that the
per-site staggered moment of every normalized ground state of the staggered-field ring `Ĥ_h`
vanishes in the iterated limit `lim_{h↓0} lim_{L↑∞}` — the squared staggered order parameter per
site of every normalized ground state of the **zero-field even** ring vanishes in the
thermodynamic limit (eq. (4.1.11), p. 77).

This is Tasaki's proof of Corollary 4.3, p. 77, read at spin `S = N/2`: "The condition (3.4.4) for
Theorem 3.2 is satisfied because of the Marshall–Lieb–Mattis theorem.  Since the conclusion
(3.4.22) of Theorem 3.2 does not hold, the other condition (3.4.3) must be violated."  It transfers
the missing mathematical content of Corollary 4.3 onto Theorem 4.2 and **discharges nothing**:
Theorem 4.2 is itself unproved (footnote 3, p. 76), so the corollary remains open.

Proof.  Suppose the conclusion fails at some `ε > 0`.  Then for every threshold there is an even
`L` beyond it carrying staggered long-range order at level `q₀ := ε` — condition (3.4.3), p. 65 —
for some normalized ground state `Φ` of the zero-field ring.  Run Theorem 4.2 at margin `√ε/2`,
fix a field `h` inside the window it returns, and take `L` beyond both the size threshold it
returns there and a threshold making the error term below negligible.

At that single `L`: `afm_ring_ground_state_data` supplies a ground energy `E₀` whose eigenspace is
one-dimensional (Marshall–Lieb–Mattis, the condition (3.4.4) input of Tasaki's sentence), and
`groundState_mulVec_eq_hermitianMinEigenvalue` identifies `Φ`'s own eigenvalue with it — the
eigenspace datum is about `E₀`, not about the particular vector, so it applies to `Φ`.  Eq.
(3.4.16) (`tasaki_eq_3_4_16_afmRing_ssb_fromGroundState`) then produces the low-lying trial state
`Ξ₊` of eq. (3.4.14), p. 68: normalized, within `C/L` of `E₀` in energy, and with per-site
staggered moment at least `√ε`.  Feeding `Ξ₊` and a normalized ground state `Ψ` of `Ĥ_h` to the
single-volume eq. (3.4.21) bound `tasaki_eq_3_4_21_perVolume_energyBound` gives
`√ε − C/(h·L²) ≤ ⟨Ψ|Ô_L|Ψ⟩/L`, whose left-hand side exceeds `√ε/2` at the chosen `L`, while
Theorem 4.2 bounds the right-hand side by `√ε/2`.  Contradiction.

The volume enters only through this one `L`, which is why the single-volume eq. (3.4.21) bound is
the entry point rather than the Theorem 3.2 capstone: the latter's hypothesis is long-range order
at *every* volume, and negating `∃ L₀, ∀ L ≥ L₀, …` supplies it at one volume at a time.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Corollary 4.3 and eq. (4.1.11), p. 77, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77;
§3.4, eqs. (3.4.3)–(3.4.4), p. 65, eqs. (3.4.14)–(3.4.16), p. 68, eq. (3.4.21), p. 70. -/
theorem no_long_range_order_1d_of_theorem_4_2 (N : ℕ) (hN : 1 ≤ N)
    (h42 : ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
          star Φ ⬝ᵥ Φ = 1 →
          (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L h N).mulVec Φ = E₀ • Φ ∧
            (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
              (staggeredFieldChainHamiltonianS L h N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
            Φ ≠ 0) →
          |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re / (L : ℝ)|
            < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
        star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)|
          < ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hbad⟩ := hcon
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  -- the trial state's energy budget, as one opaque constant
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 3 * (N : ℝ) ^ 4 / ε := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; positivity
  -- Theorem 4.2 at margin `√ε/2`, at one field inside the window it returns
  obtain ⟨h₀, hh₀, hfield⟩ := h42 (Real.sqrt ε / 2) (by positivity)
  set h : ℝ := h₀ / 2 with hhdef
  have hhpos : 0 < h := by rw [hhdef]; linarith
  obtain ⟨Lthm, hLthm⟩ := hfield h hhpos (by rw [hhdef]; linarith)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * C / (h * Real.sqrt ε))
  -- one volume beyond every threshold, carrying long-range order
  obtain ⟨L, hLge, hLeven, Φ, hΦnorm, hΦgs, hLROabs⟩ := hbad (max (max Lthm K) 2)
  have hLthm' : Lthm ≤ L := (le_max_left Lthm K).trans ((le_max_left _ 2).trans hLge)
  have hKL : K ≤ L := (le_max_right Lthm K).trans ((le_max_left _ 2).trans hLge)
  have hL2 : 2 ≤ L := (le_max_right _ 2).trans hLge
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos hL2
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_of_lt hL2
  -- the zero-field ring is the antiferromagnetic Heisenberg ring
  obtain ⟨E₀c, heig, hmin, hΦne⟩ := hΦgs
  rw [staggeredFieldChainHamiltonianS_zero_eq_afmHeisenberg] at heig hmin
  -- (3.4.4): the unique ground energy of the even ring, from Marshall–Lieb–Mattis
  obtain ⟨E₀, Φ_GS, hE, hΦ_GS_ne, hΦ_GS_eig, hfin, -⟩ :=
    afm_ring_ground_state_data L N hLeven hL2 hN
  have hHafm := afmHeisenbergChainHamiltonianS_isHermitian L N
  have hE₀eq : hermitianMinEigenvalue hHafm = E₀ := by
    refine le_antisymm ?_ ?_
    · simpa using hermitianMinEigenvalue_le_re_of_eigenpair hHafm hΦ_GS_ne hΦ_GS_eig
    · obtain ⟨w, hw, hweig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHafm
      exact hE.2 _ ⟨w, hw, hweig⟩
  have hΦE : (afmHeisenbergChainHamiltonianS L N).mulVec Φ = (E₀ : ℂ) • Φ := by
    rw [← hE₀eq]
    exact groundState_mulVec_eq_hermitianMinEigenvalue hHafm hΦnorm heig hmin
  -- (3.4.3): the negated conclusion is long-range order at level `q₀ = ε`
  have hsqnn : 0 ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
      staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re := by
    rw [hermitian_dotProduct_shift (staggeredOrderOpS_isHermitian _ N) Φ]
    exact (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  rw [abs_of_nonneg (div_nonneg hsqnn (by positivity))] at hLROabs
  have hLRO : ε ≤ rayleighOnVec ((staggeredOrderOpS (ringStaggeredSublattice L) N) ^ 2) Φ
      / ((L : ℝ) ^ (1 : ℕ)) ^ 2 := by
    rw [pow_one, pow_two (staggeredOrderOpS (ringStaggeredSublattice L) N)]
    exact hLROabs
  -- (3.4.16): the low-lying trial state at this volume
  obtain ⟨hΞnorm, -, hΞen, hΞord⟩ :=
    tasaki_eq_3_4_16_afmRing_ssb_fromGroundState L N hLeven hL2 hN hE hΦne hΦE hfin hΦnorm ε hε hLRO
  set Ξ := hvlPlusState (staggeredOrderOpS (ringStaggeredSublattice L) N) Φ with hΞdef
  rw [pow_one] at hΞen hΞord
  -- a normalized ground state of the staggered-field ring at the chosen field
  have hHfield := staggeredFieldChainHamiltonianS_isHermitian L h N
  obtain ⟨Ψ, hΨnorm, hΨeig⟩ := exists_unit_eigenvector_hermitianMinEigenvalue hHfield
  have hΨne : Ψ ≠ 0 := by
    intro h0
    rw [h0] at hΨnorm
    simp at hΨnorm
  have hΨmin : ∀ E : ℂ, ∀ X : (Fin L → Fin (N + 1)) → ℂ, X ≠ 0 →
      (staggeredFieldChainHamiltonianS L h N).mulVec X = E • X →
      (((hermitianMinEigenvalue hHfield : ℝ) : ℂ)).re ≤ E.re := by
    intro E X hX hXeig
    rw [Complex.ofReal_re]
    exact hermitianMinEigenvalue_le_re_of_eigenpair _ hX hXeig
  have habs := hLthm L hLthm' Ψ hΨnorm ⟨_, hΨeig, hΨmin, hΨne⟩
  -- (3.4.21) at this single volume
  have hHsub : afmHeisenbergChainHamiltonianS L N
      - (h : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N
      = staggeredFieldChainHamiltonianS L h N := by
    rw [staggeredFieldChainHamiltonianS, afmHeisenbergChainHamiltonianS]
  have hvar : rayleighOnVec (afmHeisenbergChainHamiltonianS L N
        - (h : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N) Ψ
      ≤ rayleighOnVec (afmHeisenbergChainHamiltonianS L N
        - (h : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N) Ξ := by
    rw [hHsub, rayleighOnVec_eq_re_of_eigenvector _ _ _ hΨeig hΨnorm, Complex.ofReal_re]
    exact hermitianMinEigenvalue_le_rayleighOnVec_of_unit hHfield hΞnorm
  have hE₀le : E₀ ≤ rayleighOnVec (afmHeisenbergChainHamiltonianS L N) Ψ := by
    rw [← hE₀eq]
    exact hermitianMinEigenvalue_le_rayleighOnVec_of_unit hHafm hΨnorm
  have hen : rayleighOnVec (afmHeisenbergChainHamiltonianS L N) Ξ - E₀ ≤ C / (L : ℝ) := by
    rw [afmHeisenbergChainHamiltonianS, heisenbergHamiltonianS_ringCoupling_eq_bondSum_general]
    refine hΞen.trans (le_of_eq ?_)
    rw [hCdef]
    push_cast
    ring
  have key := tasaki_eq_3_4_21_perVolume_energyBound (afmHeisenbergChainHamiltonianS L N)
    (staggeredOrderOpS (ringStaggeredSublattice L) N) hhpos hLpos Ψ Ξ hvar hE₀le hΞord hen
  -- the error term is negligible at this volume, so the two bounds collide
  have hthresh : 2 * C / (h * Real.sqrt ε) < (L : ℝ) :=
    hK.trans_le (by exact_mod_cast hKL)
  rw [div_lt_iff₀ (by positivity)] at hthresh
  have hsmall : C / (h * (L : ℝ) ^ 2) < Real.sqrt ε / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hthresh hLpos, le_mul_of_one_le_right hCpos.le hL1]
  have hupper : rayleighOnVec (staggeredOrderOpS (ringStaggeredSublattice L) N) Ψ / (L : ℝ)
      < Real.sqrt ε / 2 := lt_of_abs_lt habs
  linarith [key, hsmall, hupper]

/-- **Tasaki Corollary 4.3 (absence of long-range order in one dimension), CONDITIONAL
THEOREM.**  For the
zero-field one-dimensional spin-`S` antiferromagnetic Heisenberg ring
(`heisenbergHamiltonianS (ringCoupling L) N`, i.e. `staggeredFieldChainHamiltonianS L 0 N`), the
squared staggered order parameter per site vanishes in the thermodynamic limit (eq. (4.1.11)):
for every `ε > 0` there is a size threshold `L₀` beyond which every normalized ground state `Φ` of
the zero-field **even** ring `L` has `|⟨Φ, (Ô_L^{(3)})² Φ⟩.re / L²| < ε`.

Restricted to even rings (`Even L`), faithful to Tasaki: §3.1 defines the lattice `(Λ_L, B_L)`
for even `L`, and §4.1.1 states the model "with even L".  Only bipartite (even) rings carry the
balanced staggered sublattice underlying the staggered order parameter and the unique-singlet
ground state (MLM, Thm 2.2); odd rings are non-bipartite and lie outside §4.1's setting.

**Conditional, and a discharge of nothing.**  For `N ≥ 1` this is Tasaki's own contraposition
argument `no_long_range_order_1d_of_theorem_4_2` applied to Theorem 4.2
(`shastry_no_symmetry_breaking_1d`), which is itself conditional on the documented axiom
`shastryEnergyGain`.  So `#print axioms` here names `shastryEnergyGain`, and both Corollary 4.3 and
Theorem 4.2 remain open: Tasaki does not prove Theorem 4.2 (footnote 3, p. 76) and nothing here
reconstructs the argument he cites.  Only the degenerate spin-`0` case `N = 0` is unconditional,
the staggered order operator vanishing there (`staggeredOrderOpS_spin_zero`). -/
theorem no_long_range_order_1d (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
        star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)| < ε
    := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- spin-`0`: the staggered order operator vanishes, so the parameter is identically zero.
    intro ε hε
    refine ⟨0, fun L _ _ Φ _ _ => ?_⟩
    rw [staggeredOrderOpS_spin_zero]
    simpa using hε
  · -- `N ≥ 1`: Tasaki's contraposition, fed with Theorem 4.2.
    exact no_long_range_order_1d_of_theorem_4_2 N hN (shastry_no_symmetry_breaking_1d N)

end LatticeSystem.Quantum
