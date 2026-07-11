import LatticeSystem.Quantum.SpinS.NoLongRangeOrderConditional

/-!
# Tasaki §4.1: absence of long-range order in one dimension (Corollary 4.3), discharged

The conditional reduction `no_long_range_order_1d_of_susceptibility`
(`NoLongRangeOrderConditional.lean`) proves the exact `ε`–`δ` statement of Tasaki's Corollary 4.3
*modulo a single quantitative input*: the staggered static susceptibility of every ground state of
the zero-field one-dimensional antiferromagnetic Heisenberg ring is `O(L)`, i.e. there is a
potential `y` for `ÔΦ` with `Re⟨y, ÔΦ⟩ ≤ C·L`.  Tasaki does **not** prove that bound in the
book — he defers it to the external hard-analysis literature (Shastry [58]; Tanaka–Takeda–Idogaki
[63]; Kennedy–Lieb–Shastry [29]).  We record exactly that quantitative input as a documented axiom
`shastry_staggered_susceptibility_bound` (following the project's explicit instruction to axiomatise
this genuinely external hard-analysis estimate), and feed it into the conditional reduction to
discharge Corollary 4.3 (`no_long_range_order_1d`) from an axiom into a theorem.

Only the *zero-field* Corollary 4.3 is discharged here; the field version Theorem 4.2
(`shastry_no_symmetry_breaking_1d`, the iterated `lim_{h↓0} lim_{L↑∞}` double limit) is a strictly
stronger statement not reachable by this static-susceptibility route and remains a documented axiom
in `ShastryNoSSB.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Corollary 4.3, eq. (4.1.11), p. 77 (with footnotes 3, p. 76 and 9, p. 83).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Shastry staggered susceptibility bound (`χ(k*) ≤ C·L`), DOCUMENTED AXIOM.**  For the
zero-field one-dimensional spin-`S` antiferromagnetic Heisenberg ring on an **even** number `L ≥ 2`
of sites there is a
size-uniform
constant `C ≥ 0` such that every *normalized* ground state `Φ` (energy `hermitianMinEigenvalue`)
admits a potential `y` for `ÔΦ` — `(Ĥ − E₀) y = ÔΦ` — whose static staggered susceptibility is
`O(L)`: `Re⟨y, ÔΦ⟩ ≤ C·L`.  Physically `Re⟨y, ÔΦ⟩ = χ(k*) = L · f_L^{(-1)}(k*)`, the zero-frequency
staggered susceptibility at the antiferromagnetic wavevector `k* = π`.

Tasaki does **not** prove this bound in the book.  His footnote 3 (§4.1, p. 76) attributes the
one-dimensional result to Shastry and refers to [63] for a rigorous mathematical formulation, and
his footnote 9 (§4.1, p. 83) singles out the bound on `f_L^{(-1)}(k*)` as the only "nontrivial part
that requires some hard analysis", deferring it to the external literature.  The quantitative
estimate rests on a massive-Green-function / inverse-Fourier analysis with an `O(L)` control of the
`k* = π` singularity that lies outside the book's scope; per the project's explicit instruction it
is recorded here as a documented axiom (a genuinely external, hard-analysis estimate, not an
in-book argument):

* B. S. Shastry, *Bounds for correlation functions of the Heisenberg antiferromagnet*,
  J. Phys. A: Math. Gen. **25**, L249 (1992) — the original bound.
* K. Tanaka, K. Takeda, T. Idogaki, *Rigorous results for the antiferromagnetic Heisenberg model*,
  J. Magn. Magn. Mater. **272–276**, 908 (2004) — the rigorous mathematical formulation cited by
  Tasaki [63].

Restricted to **even** rings `L ≥ 2` (`Even L`): only bipartite (even) rings carry a balanced
staggered sublattice `Σ_x ε_x = 0`, so the ground state is an SU(2)-invariant singlet with
`⟨Φ, ÔΦ⟩ = 0`, hence `ÔΦ ⊥ ker(Ĥ − E₀)` and the resolvent potential `y` with `(Ĥ − E₀) y = ÔΦ`
genuinely exists.  Odd rings are non-bipartite: the staggered sublattice is unbalanced
(`Σ_x ε_x ≠ 0`, e.g. `L = 3`), `ÔΦ` need not be orthogonal to the ground state, no such `y` exists,
and they lie outside Tasaki's §4.1 setting (whose lattice `(Λ_L, B_L)` is defined for even `L`
only; §3.1, §4.1.1).  The statement is the `hsusc` hypothesis of
`no_long_range_order_1d_of_susceptibility`, bundled with its size-uniform constant
`∃ C, 0 ≤ C ∧ …`, so that feeding it into the conditional reduction discharges the even-ring
Corollary 4.3. -/
axiom shastry_staggered_susceptibility_bound (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 2 ≤ L → Even L → ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
      star Φ ⬝ᵥ Φ = 1 →
      (heisenbergHamiltonianS (ringCoupling L) N).mulVec Φ
          = (hermitianMinEigenvalue
              (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ) • Φ →
      ∃ y : (Fin L → Fin (N + 1)) → ℂ,
        (heisenbergHamiltonianS (ringCoupling L) N
            - (hermitianMinEigenvalue
                (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N) : ℂ)
              • (1 : ManyBodyOpS (Fin L) N)).mulVec y
          = (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ
        ∧ (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re ≤ C * (L : ℝ)

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

/-- **Tasaki Corollary 4.3 (absence of long-range order in one dimension), THEOREM.**  For the
zero-field one-dimensional spin-`S` antiferromagnetic Heisenberg ring
(`heisenbergHamiltonianS (ringCoupling L) N`, i.e. `staggeredFieldChainHamiltonianS L 0 N`), the
squared staggered order parameter per site vanishes in the thermodynamic limit (eq. (4.1.11)):
for every `ε > 0` there is a size threshold `L₀` beyond which every normalized ground state `Φ` of
the zero-field **even** ring `L` has `|⟨Φ, (Ô_L^{(3)})² Φ⟩.re / L²| < ε`.

Restricted to even rings (`Even L`), faithful to Tasaki: §3.1 defines the lattice `(Λ_L, B_L)`
for even `L`, and §4.1.1 states the model "with even L".  Only bipartite (even) rings carry the
balanced staggered sublattice underlying the staggered order parameter and the unique-singlet
ground state (MLM, Thm 2.2); odd rings are non-bipartite and lie outside §4.1's setting.

Discharged from the conditional reduction `no_long_range_order_1d_of_susceptibility` fed with the
documented Shastry susceptibility axiom `shastry_staggered_susceptibility_bound` (for `N ≥ 1`); the
degenerate spin-`0` case `N = 0` is unconditional since the staggered order operator vanishes there
(`staggeredOrderOpS_spin_zero`). -/
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
  · -- `N ≥ 1`: feed the Shastry susceptibility axiom into the conditional reduction.
    obtain ⟨C, hC, hbound⟩ := shastry_staggered_susceptibility_bound N hN
    exact no_long_range_order_1d_of_susceptibility N hN C hC hbound

end LatticeSystem.Quantum
