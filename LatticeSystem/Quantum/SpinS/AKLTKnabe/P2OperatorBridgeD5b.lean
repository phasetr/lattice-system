import LatticeSystem.Quantum.SpinS.AKLTKnabe.Sector2BaseNarrow
import LatticeSystem.Quantum.SpinS.AKLTBondProjection

/-!
# Gate D5b Stage 2: the rational model of the bond spin-two projection, validated

This module (Issue #5094; Tasaki §7.1.4, Knabe) performs the **first independent verification
inside Lean** of the frozen Gate C entry model: the rational table `sector2P2Entry` is proved to be
the genuine matrix element of the *production* bond projection

  `bondSpin2ProjectionS (0 : Fin 2) 1 = ½ (Ŝ₀ · Ŝ₁) + ⅙ (Ŝ₀ · Ŝ₁)² + ⅓`
  (`LatticeSystem/Quantum/SpinS/AKLTBondProjection.lean`),

which is Tasaki's `P̂₂[Ŝ_x + Ŝ_{x+1}]` of eq. (7.1.6). Until now that agreement had only been
checked by exact-rational arithmetic *outside* Lean; here it becomes a theorem.

## Where the `√2` goes

The production ladder operators carry `√2`:
`spinSOpPlus 2 i j = √2` iff `i + 1 = j` and `spinSOpMinus 2 i j = √2` iff `j + 1 = i`
(`SpinOneTwoSiteEntries.lean`). But `Ŝ₀ · Ŝ₁` uses them only in the **matched** combination
`½ (Ŝ⁺ ⊗ Ŝ⁻ + Ŝ⁻ ⊗ Ŝ⁺) + Ŝ⁽³⁾ ⊗ Ŝ⁽³⁾` (`spinSDot_fin2_apply'`), so every surviving off-diagonal
term contains `½ · √2 · √2 = 1` and `Ŝ₀ · Ŝ₁` is already an **integer** matrix. Accordingly the
only irrational fact used anywhere in this module is
`((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2`, discharged once inside
`spinDot_two_site_entry_eq_dotRatEntry`. No Clebsch–Gordan amplitude is ever represented; the
bridge goes through the projector, never through amplitudes.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.2–§7.1.4, eqs. (7.1.5)–(7.1.6) p. 182 and (7.1.30) p. 189.
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open Matrix

/-! ## The rational model of `Ŝ₀ · Ŝ₁` -/

/-- The rational matrix element `⟨a b| Ŝ₀ · Ŝ₁ |c d⟩` of the two-site spin-one Heisenberg
operator, in the production label convention `m = 1 − k` for `k : Fin 3`. The first two summands
are the ladder contributions `½ Ŝ⁺ ⊗ Ŝ⁻` and `½ Ŝ⁻ ⊗ Ŝ⁺`, whose `½ · √2 · √2` has already been
evaluated to `1`; the last summand is the diagonal `Ŝ⁽³⁾ ⊗ Ŝ⁽³⁾`. Written as products of single
`if`s (rather than `if`s on conjunctions) so that it matches the shape of the operator entry term
by term. -/
def dotRatEntry (a b c d : Fin 3) : ℚ :=
  (if a.val + 1 = c.val then 1 else 0) * (if d.val + 1 = b.val then 1 else 0)
    + (if c.val + 1 = a.val then 1 else 0) * (if b.val + 1 = d.val then 1 else 0)
    + (if a = c then 1 - (a.val : ℚ) else 0) * (if b = d then 1 - (b.val : ℚ) else 0)

/-- **The single place where an irrational number appears.** The two-site spin-one dot product,
written in its imaginary-free ladder form, has the rational entries `dotRatEntry`. The proof
splits the six `if` conditions and uses `(√2)² = 2` once. -/
private theorem spinDot_two_site_entry_eq_dotRatEntry (a b c d : Fin 3) :
    (1 / 2 : ℂ) * (spinSOpPlus 2 a c * spinSOpMinus 2 b d
        + spinSOpMinus 2 a c * spinSOpPlus 2 b d)
      + spinSOp3 2 a c * spinSOp3 2 b d = ((dotRatEntry a b c d : ℚ) : ℂ) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [spinSOpPlus_two_apply, spinSOpMinus_two_apply, spinSOp3_two_apply, dotRatEntry]
  split_ifs <;> push_cast [h2] <;> ring

/-- The two-site dot product `Ŝ₀ · Ŝ₁` on `Λ = Fin 2` has the rational entries `dotRatEntry`,
read off the two sites of the row and column configurations. -/
theorem spinSDot_fin2_apply_eq_dotRatEntry (σ' σ : Fin 2 → Fin 3) :
    spinSDot (0 : Fin 2) 1 2 σ' σ = ((dotRatEntry (σ' 0) (σ' 1) (σ 0) (σ 1) : ℚ) : ℂ) := by
  rw [spinSDot_fin2_apply']
  exact spinDot_two_site_entry_eq_dotRatEntry _ _ _ _

/-! ## The rational model of the bond spin-two projection -/

/-- The rational matrix element `⟨a b| P̂₂ |c d⟩` obtained by evaluating the *defining* polynomial
`½ D + ⅙ D² + ⅓` of `bondSpin2ProjectionS` on the rational model `D = dotRatEntry` of the two-site
dot product. The middle term is the `9`-term fibre sum computing the entry of `D²`. -/
def p2Rat (a b c d : Fin 3) : ℚ :=
  (1 / 2 : ℚ) * dotRatEntry a b c d
    + (1 / 6 : ℚ) * (∑ e : Fin 3, ∑ f : Fin 3, dotRatEntry a b e f * dotRatEntry e f c d)
    + (1 / 3 : ℚ) * (if a = c ∧ b = d then 1 else 0)

/-- The inner fibre sum of `p2Rat`, expanded into its nine terms. Expanding the `Finset.sum`
*before* the entry-by-entry evaluation is what keeps each of the `81` goals shallow enough for
`norm_num` to finish inside the default recursion depth. -/
private theorem p2Rat_expand (a b c d : Fin 3) :
    p2Rat a b c d = (1 / 2 : ℚ) * dotRatEntry a b c d
      + (1 / 6 : ℚ) * (dotRatEntry a b 0 0 * dotRatEntry 0 0 c d
        + dotRatEntry a b 0 1 * dotRatEntry 0 1 c d
        + dotRatEntry a b 0 2 * dotRatEntry 0 2 c d
        + dotRatEntry a b 1 0 * dotRatEntry 1 0 c d
        + dotRatEntry a b 1 1 * dotRatEntry 1 1 c d
        + dotRatEntry a b 1 2 * dotRatEntry 1 2 c d
        + dotRatEntry a b 2 0 * dotRatEntry 2 0 c d
        + dotRatEntry a b 2 1 * dotRatEntry 2 1 c d
        + dotRatEntry a b 2 2 * dotRatEntry 2 2 c d)
      + (1 / 3 : ℚ) * (if a = c ∧ b = d then 1 else 0) := by
  rw [p2Rat]
  simp only [Fin.sum_univ_three]
  ring

/-- The `27` entries of `p2Rat = sector2P2Entry` with first label `0`. -/
private theorem p2Rat_eq_sector2P2Entry_zero (b c d : Fin 3) :
    p2Rat 0 b c d = sector2P2Entry 0 b c d := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [p2Rat_expand, dotRatEntry, sector2P2Entry, Fin.mk.injEq, Fin.ext_iff]

/-- The `27` entries of `p2Rat = sector2P2Entry` with first label `1`. -/
private theorem p2Rat_eq_sector2P2Entry_one (b c d : Fin 3) :
    p2Rat 1 b c d = sector2P2Entry 1 b c d := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [p2Rat_expand, dotRatEntry, sector2P2Entry, Fin.mk.injEq, Fin.ext_iff]

/-- The `27` entries of `p2Rat = sector2P2Entry` with first label `2`. -/
private theorem p2Rat_eq_sector2P2Entry_two (b c d : Fin 3) :
    p2Rat 2 b c d = sector2P2Entry 2 b c d := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [p2Rat_expand, dotRatEntry, sector2P2Entry, Fin.mk.injEq, Fin.ext_iff]

/-- **The validation of the frozen Gate C entry model, in `ℚ`.** The projector polynomial
`½ D + ⅙ D² + ⅓` evaluated on the rational two-site dot product agrees with the frozen table
`sector2P2Entry` on all `81` entries. `sector2P2Entry` was written from the Clebsch–Gordan
decomposition and `p2Rat` from the operator definition, so this is a genuine cross-check. -/
theorem p2Rat_eq_sector2P2Entry (a b c d : Fin 3) :
    p2Rat a b c d = sector2P2Entry a b c d := by
  fin_cases a
  · exact p2Rat_eq_sector2P2Entry_zero b c d
  · exact p2Rat_eq_sector2P2Entry_one b c d
  · exact p2Rat_eq_sector2P2Entry_two b c d

/-! ## The operator bridge -/

/-- The complex form of `p2Rat`: the cast distributes over the projector polynomial. -/
private theorem p2Rat_cast (a b c d : Fin 3) :
    ((p2Rat a b c d : ℚ) : ℂ) = (1 / 2 : ℂ) * ((dotRatEntry a b c d : ℚ) : ℂ)
      + (1 / 6 : ℂ) * (∑ e : Fin 3, ∑ f : Fin 3,
          ((dotRatEntry a b e f : ℚ) : ℂ) * ((dotRatEntry e f c d : ℚ) : ℂ))
      + (1 / 3 : ℂ) * (if a = c ∧ b = d then (1 : ℂ) else 0) := by
  rw [p2Rat]
  split_ifs <;> push_cast <;> ring

/-- On `Λ = Fin 2` the identity operator is the product of the two site-wise Kronecker deltas. -/
private theorem one_fin2_apply (σ' σ : Fin 2 → Fin 3) :
    (1 : ManyBodyOpS (Fin 2) 2) σ' σ = if σ' 0 = σ 0 ∧ σ' 1 = σ 1 then (1 : ℂ) else 0 := by
  rw [Matrix.one_apply]
  by_cases h : σ' 0 = σ 0 ∧ σ' 1 = σ 1
  · have hσ : σ' = σ := funext (Fin.forall_fin_two.mpr h)
    rw [if_pos hσ, if_pos h]
  · rw [if_neg h, if_neg]
    intro hσ
    exact h ⟨congrFun hσ 0, congrFun hσ 1⟩

/-- **The Stage-2 capstone: the production bond projection has the frozen rational entries.**
Every matrix element of `bondSpin2ProjectionS (0 : Fin 2) 1`, i.e. of Tasaki's spin-two bond
projection `P̂₂[Ŝ₀ + Ŝ₁]` of eq. (7.1.6) built from the production spin-one operators, is the cast
of the corresponding entry of the frozen rational table `sector2P2Entry`. No hypothesis, no
Clebsch–Gordan amplitude, and only the single irrational fact `(√2)² = 2`. -/
theorem bondSpin2ProjectionS_fin2_apply_eq_sector2P2Entry (σ' σ : Fin 2 → Fin 3) :
    bondSpin2ProjectionS (0 : Fin 2) 1 σ' σ
      = ((sector2P2Entry (σ' 0) (σ' 1) (σ 0) (σ 1) : ℚ) : ℂ) := by
  rw [← p2Rat_eq_sector2P2Entry, p2Rat_cast]
  simp only [bondSpin2ProjectionS, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply]
  rw [sum_fin2_fin3]
  simp only [spinSDot_fin2_apply_eq_dotRatEntry, one_fin2_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.sum_univ_three]
  ring

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
