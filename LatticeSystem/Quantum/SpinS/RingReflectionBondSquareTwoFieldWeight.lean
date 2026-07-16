/-
The bond-square DLS decomposition and its field-dependent two-field Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: bond-square route PR-BS6).

Toward the field-dependent two-field reflection Cauchy–Schwarz bound driving Dyson–Lieb–Simon
Gaussian domination for the bond-square (real-operator) model (Tasaki §4.1, (4.1.65)–(4.1.69),
book p. 90), this file supplies the three PR-BS6 objects, all in the gauge spin basis
(bare `onSiteS x (spinSOp_ N)` with the `(−1)ˣ`/`i` staggering carried by the reflection `θ`):

* `ringBondSquareLeftFieldHamiltonian` — the left half `Ĥᴸ_a` of (4.1.67) in the repo DLS
  plain-sum (physical Heisenberg) frame: the intra-left bond terms
  `+Ŝ¹Ŝ¹ + Ŝ²Ŝ² + ½(Ŝ³ₓ + Ŝ³_y − a_x − a_y)²`,
  the single-ion `−(Ŝ³)²`, and the boundary half-square `½(Ŝ³ₓ − a_x)²`.  (Sign-frame corrected from
  the earlier T̂-ferromagnetic verbatim transcription: on an intra-left bond the `(−1)ˣ` of
  `T̂³ = (−1)ˣŜ³` flips the α = 1 sign to `+Ŝ¹Ŝ¹` and turns the longitudinal difference `Ŝ³ₓ − Ŝ³_y`
  into the sum `Ŝ³ₓ + Ŝ³_y`; the α = 2 slot and the single-site squares are unchanged.)  Only its
  left-supportedness is proved here (square-non-expanded, coefficient/sign-agnostic); the exact
  physical coefficients are the deferred PR-BS8 content.
* `ringBondSquareCrossingGen` / `ringBondSquareFieldCrossing` — the field-dependent crossing
  generators `C^{(α)}_b(a)` (kinetic α = 1, 2 field-free; longitudinal α = 3 a bare central scalar
  shift `+ (−a_x)•1`) and the two-field crossing `∑_c θ(C_c(b))·C_c(a)`, exhibited as a
  `RPTwoFieldConeRepS` — the object the PR-BS5 exp-of-cone Cauchy–Schwarz fires on.
* `ringBondSquareTwoFieldWeight` — the two-field weight `exp(−β·(H_L(a) + θ(H_L(b)) − crossing))`,
  its diagonal `b = a` collapse (`_self`), and its Trotter-limit representation (`_isLimit`, via
  `lieProductFormula`).

The reflection Cauchy–Schwarz capstone `(Re Tr W(a,b))² ≤ Re Tr W(a,a)·Re Tr W(b,b)` and the
physical-field identification are deferred to PR-BS7/BS8.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldWeight
import LatticeSystem.Quantum.SpinS.RingReflectionRingInstance
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsCone
import LatticeSystem.Quantum.SpinS.RingReflectionLeftHamiltonian

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- **Bond-square left-half Hamiltonian** `Ĥᴸ_a` in the gauge spin basis (Tasaki (4.1.67), book
p. 90), in the repo DLS plain-sum (physical Heisenberg) frame: the intra-left bond terms
`+Ŝ¹ₓŜ¹_y + Ŝ²ₓŜ²_y + ½(Ŝ³ₓ + Ŝ³_y − a_x − a_y)²` (summed over ordered left pairs gated by the ring
coupling), the single-ion `−(Ŝ³ₓ)²` over the left half, and the boundary half-square `½(Ŝ³ₓ − a_x)²`
over the two crossing-left sites `0`, `n − 1`.  The intra-left signs are the corrected gauge frame:
the `(−1)ˣ` of `T̂³ = (−1)ˣŜ³` (absorbed in `θ`, not written explicitly) flips the α = 1 sign to
`+Ŝ¹Ŝ¹` and turns the longitudinal difference into the sum-form `½(Ŝ³ₓ + Ŝ³_y − a_x − a_y)²` (both
fields subtracted) on an adjacent intra-left bond — matching the merged linear left frame; the α = 2
term and the single-site squares are sign-neutral.  It is left-supported; the exact bulk/single-ion/
field coefficients are the deferred PR-BS8 physical identification and do not gate any PR-BS6
obligation. -/
noncomputable def ringBondSquareLeftFieldHamiltonian (n N : ℕ) [NeZero n]
    (a : Fin (2 * n) → ℝ) : ManyBodyOpS (Fin (2 * n)) N :=
  (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
      ∑ y ∈ Finset.univ.filter (fun y : Fin (2 * n) => (y : ℕ) < n),
        ringLeftCoupling n x y • (onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N)
          + onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)
          + (1 / 2 : ℂ) • ((onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
                + (-(a x : ℂ)) • 1 + (-(a y : ℂ)) • 1)
              * (onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
                + (-(a x : ℂ)) • 1 + (-(a y : ℂ)) • 1))))
    + ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
        (-1 : ℂ) • (onSiteS x (spinSOp3 N) * onSiteS x (spinSOp3 N))
    + ∑ p : Fin 2, (1 / 2 : ℂ) • ((onSiteS (ringCrossingSite n p) (spinSOp3 N)
          + (-(a (ringCrossingSite n p) : ℂ)) • 1)
        * (onSiteS (ringCrossingSite n p) (spinSOp3 N)
          + (-(a (ringCrossingSite n p) : ℂ)) • 1))

/-- The bond-square left-half Hamiltonian is left-supported.  Every summand is a product / square /
`•` / finite `∑` of single-left-site operators `onSiteS x (spinSOp_ N)` (`x < n`) and central
scalars, so left-support closes by `.mul`/`.add`/`.smul`/`.sum`/`.one` (no square is expanded). -/
theorem ringBondSquareLeftFieldHamiltonian_supportedOnLeft (n N : ℕ) [NeZero n]
    (a : Fin (2 * n) → ℝ) :
    SupportedOnLeftS n N (ringBondSquareLeftFieldHamiltonian n N a) := by
  unfold ringBondSquareLeftFieldHamiltonian
  refine ((SupportedOnLeftS.sum _ _ (fun x hx => SupportedOnLeftS.sum _ _ (fun y hy => ?_))).add
    (SupportedOnLeftS.sum _ _ (fun x hx => ?_))).add (SupportedOnLeftS.sum _ _ (fun p _ => ?_))
  · have hxn : (x : ℕ) < n := (Finset.mem_filter.mp hx).2
    have hyn : (y : ℕ) < n := (Finset.mem_filter.mp hy).2
    refine SupportedOnLeftS.smul _ ?_
    have hd : SupportedOnLeftS n N (onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
        + (-(a x : ℂ)) • 1 + (-(a y : ℂ)) • 1) :=
      (((onSiteS_supportedOnLeft hxn _).add (onSiteS_supportedOnLeft hyn _)).add
        (SupportedOnLeftS.one.smul _)).add (SupportedOnLeftS.one.smul _)
    refine (((onSiteS_supportedOnLeft hxn _).mul (onSiteS_supportedOnLeft hyn _)).add
      ((onSiteS_supportedOnLeft hxn _).mul (onSiteS_supportedOnLeft hyn _))).add ?_
    exact (hd.mul hd).smul _
  · have hxn : (x : ℕ) < n := (Finset.mem_filter.mp hx).2
    exact ((onSiteS_supportedOnLeft hxn _).mul (onSiteS_supportedOnLeft hxn _)).smul _
  · have hsite : (ringCrossingSite n p : ℕ) < n := by
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      fin_cases p
      · exact hn
      · exact Nat.sub_lt hn Nat.one_pos
    have hb : SupportedOnLeftS n N (onSiteS (ringCrossingSite n p) (spinSOp3 N)
        + (-(a (ringCrossingSite n p) : ℂ)) • 1) :=
      (onSiteS_supportedOnLeft hsite _).add (SupportedOnLeftS.one.smul _)
    exact (hb.mul hb).smul _

/-- **Bond-square crossing generator** `C^{(α)}_b(z)` in the gauge spin basis.  For each crossing
bond index `p = (i, α)` it is the field-free single-site crossing operator
`onSiteS (ringCrossingSite n i) (spinSOpFin3 N α)` plus, on the longitudinal slot `α = 2` (`Ŝ³`)
only, the bare central scalar field shift `+ (−z_x)•1` (Tasaki longitudinal factor `T̂³ₓ − h_x`,
(4.1.69), book p. 90; the gauge `(−1)ˣ` rides on the operator, not on the field).  The kinetic slots
`α = 0, 1` are field-free and identical to the merged field-free crossing generators. -/
noncomputable def ringBondSquareCrossingGen (n N : ℕ) [NeZero n] (p : Fin 2 × Fin 3)
    (z : Fin (2 * n) → ℝ) : ManyBodyOpS (Fin (2 * n)) N :=
  onSiteS (ringCrossingSite n p.1) (spinSOpFin3 N p.2)
    + (-(if p.2 = 2 then (z (ringCrossingSite n p.1) : ℂ) else 0)) • 1

/-- The bond-square crossing generator is left-supported for **every** field `z`: the single-site
operator sits at a crossing-left site (`0` or `n − 1`, both `< n`) and the field enters as a central
scalar shift by the identity, preserved by `.one`/`.smul`/`.add`. -/
theorem ringBondSquareCrossingGen_supportedOnLeft (n N : ℕ) [NeZero n] (p : Fin 2 × Fin 3)
    (z : Fin (2 * n) → ℝ) : SupportedOnLeftS n N (ringBondSquareCrossingGen n N p z) := by
  unfold ringBondSquareCrossingGen
  refine (onSiteS_supportedOnLeft ?_ _).add (SupportedOnLeftS.one.smul _)
  obtain ⟨i, j⟩ := p
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  fin_cases i
  · exact hn
  · exact Nat.sub_lt hn Nat.one_pos

/-- **Field-dependent two-field bond-square crossing** `∑_c θ(C_c(b))·C_c(a)` in the canonical
`RPTwoFieldConeRepS` order (Tasaki crossing interaction of (4.1.69), book p. 90), with the reflected
pile carrying the right field `b` and the non-reflected pile the left field `a`. -/
noncomputable def ringBondSquareFieldCrossing (n N : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) : ManyBodyOpS (Fin (2 * n)) N :=
  ∑ p : Fin 2 × Fin 3,
    ringReflectionThetaS n N (ringBondSquareCrossingGen n N p b)
      * ringBondSquareCrossingGen n N p a

/-- **The two-field bond-square crossing is a field-crossing cone.**  With the field-independent
index family `Fin 2 × Fin 3`, unit weights, and the left-supported (for every field) generators
`ringBondSquareCrossingGen`, the crossing has the `RPTwoFieldConeRepS` shape on which the PR-BS5
field-dependent exp-of-cone Cauchy–Schwarz fires. -/
theorem ringBondSquareFieldCrossing_twoFieldConeRep (n N : ℕ) [NeZero n] :
    RPTwoFieldConeRepS n N (fun a b => ringBondSquareFieldCrossing n N a b) :=
  ⟨Fin 2 × Fin 3, inferInstance, ringBondSquareCrossingGen n N, fun _ => 1,
    ringBondSquareCrossingGen_supportedOnLeft n N, fun _ => zero_le_one, fun u v => by
      simp only [ringBondSquareFieldCrossing, Complex.ofReal_one, one_smul]⟩

/-- **Bond-square two-field ("doubled") Gibbs weight.**  The weight `exp(−β · Ĥ^{BS}(a,b))` of the
doubled bond-square Hamiltonian `Ĥ^{BS}(a,b) = H_L(a) + θ(H_L(b)) − ∑_c C_c(a)·θ(C_c(b))`, carrying
an independent left field `a` on the left half and an independent field `b` transported to the right
half by `θ`, with the genuinely field-dependent crossing.  For `a = b` it is the single-field
bond-square DLS Gibbs operator (`_self`). -/
noncomputable def ringBondSquareTwoFieldWeight (n N : ℕ) [NeZero n] (β : ℝ)
    (a b : Fin (2 * n) → ℝ) : ManyBodyOpS (Fin (2 * n)) N :=
  NormedSpace.exp (-(β : ℂ) • (ringBondSquareLeftFieldHamiltonian n N a
    + ringReflectionThetaS n N (ringBondSquareLeftFieldHamiltonian n N b)
    - ringBondSquareFieldCrossing n N a b))

/-- **Diagonal specialisation.**  With the same field `a` on both halves the doubled bond-square
weight collapses to `exp(−β·Ĥ^{BS}(a))` with the single-field DLS Hamiltonian
`H_L(a) + θ(H_L(a)) − ∑_c C_c(a)·θ(C_c(a))` — the PR-BS8 physical-identification landing point. -/
theorem ringBondSquareTwoFieldWeight_self (n N : ℕ) [NeZero n] (β : ℝ) (a : Fin (2 * n) → ℝ) :
    ringBondSquareTwoFieldWeight n N β a a
      = NormedSpace.exp (-(β : ℂ) • (ringBondSquareLeftFieldHamiltonian n N a
        + ringReflectionThetaS n N (ringBondSquareLeftFieldHamiltonian n N a)
        - ringBondSquareFieldCrossing n N a a)) := rfl

/-- **Trotter-limit representation of the doubled bond-square weight.**  The weight `W(a,b)` is the
Lie-product limit of the Dyson–Lieb–Simon approximant with the field-dependent left kinetic factor
`exp(−(β/m)·H_L(a))`, its `θ`-reflected right partner, and the field-crossing factor
`exp((β/m)·crossing(a,b))`.  The left and right kinetic factors commute (disjoint supports), so the
two-factor Lie product formula `lieProductFormula` applies, with the crossing's genuine two-field
dependence carried through the cone representation. -/
theorem ringBondSquareTwoFieldWeight_isLimit (n N : ℕ) [NeZero n] (β : ℝ)
    (a b : Fin (2 * n) → ℝ) :
    Tendsto (fun m : ℕ =>
        (NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringBondSquareLeftFieldHamiltonian n N a))
          * ringReflectionThetaS n N
              (NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringBondSquareLeftFieldHamiltonian n N b)))
          * NormedSpace.exp ((m : ℂ)⁻¹
              • ((β : ℂ) • ringBondSquareFieldCrossing n N a b))) ^ m)
      atTop (𝓝 (ringBondSquareTwoFieldWeight n N β a b)) := by
  set A : ManyBodyOpS (Fin (2 * n)) N := -(β : ℂ) • (ringBondSquareLeftFieldHamiltonian n N a
    + ringReflectionThetaS n N (ringBondSquareLeftFieldHamiltonian n N b)) with hA
  set B : ManyBodyOpS (Fin (2 * n)) N := (β : ℂ) • ringBondSquareFieldCrossing n N a b with hB
  -- the commuting left/right kinetic factors merge into `exp((1/m)·A)`
  have hkin : ∀ m : ℕ,
      NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringBondSquareLeftFieldHamiltonian n N a))
        * ringReflectionThetaS n N
            (NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringBondSquareLeftFieldHamiltonian n N b)))
        = NormedSpace.exp ((m : ℂ)⁻¹ • A) := by
    intro m
    rw [ringReflectionThetaS_exp_mul_theta_exp
        (((ringBondSquareLeftFieldHamiltonian_supportedOnLeft n N a).smul _).smul _)
        (((ringBondSquareLeftFieldHamiltonian_supportedOnLeft n N b).smul _).smul _)]
    congr 1
    rw [ringReflectionThetaS_smul, ringReflectionThetaS_smul, hA, smul_add, smul_add]
    simp only [map_neg, Complex.conj_ofReal, map_inv₀, Complex.conj_natCast]
  -- the doubled weight is `exp(A + B)`
  have hexp : ringBondSquareTwoFieldWeight n N β a b = NormedSpace.exp (A + B) := by
    rw [ringBondSquareTwoFieldWeight, hA, hB]
    congr 1
    module
  rw [hexp]
  refine (LatticeSystem.Math.lieProductFormula A B).congr (fun m => ?_)
  rw [hkin m]

end LatticeSystem.Quantum
