import LatticeSystem.Quantum.IsingLowEnergyProblem33aSpectrum

/-!
# Existence of the two parity roots and the (S.40) energy ordering (Tasaki Problem 3.3.a)

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a (statement p. 59,
solution pp. 498-501) fixes the decay rate `κ` of the ansatz of
`LatticeSystem/Quantum/IsingLowEnergyProblem33aEigenvectors.lean` by

* (S.33), p. 500: `ε (1 ± e^-κL) = -λ (e^-κ ± e^-κ(L-1))`, the recursion (S.30) at the label
  `j = 0` (equivalently, at `j = L`), both signs being the same one;
* (S.34), p. 500: `e^κ - e^-κ = λ⁻¹ (1 ± e^-κL) / (1 ∓ e^-κL)`, whose numerator carries `±` and
  whose denominator carries the opposite sign `∓`, the upper signs belonging to the symmetric and
  the lower ones to the antisymmetric solution.

This module solves (S.34) in `κ`. `rootEquation_iff_cleared` multiplies out its denominator, which
turns the root equation into `λ (e^κ - e^-κ) (1 - s e^-κL) = 1 + s e^-κL`; the left factor
`λ (e^κ - e^-κ) = 2 λ sinh κ` is strictly increasing and takes the value `1` at the `L ↑ ∞` rate
`kappaInf λ` of eq. (S.35), so the cleared equation compares that factor with the finite-`L`
right-hand side. `exists_root_symmetric` and `eventually_exists_root_antisymmetric` produce a root
in each parity sector by the intermediate value theorem, and `tightBindingEnergy_lt_of_roots`
compares the two sectors' eigenvalues.

The comparison is the exact content of

* (S.40), p. 501: `ε_± ≃ ε∞ ∓ [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L`, followed by "We see that
  the symmetric solution has a lower energy, as it should be".

`tightBindingEnergy_lt_of_roots` asserts only that ordering, `ε_+ < ε_-`, as a strict inequality
between the values of `tightBindingEnergy` at any positive root of either sector; the displayed
asymptotic form of (S.40), which the source writes with `≃` and derives from the non-rigorous
Taylor steps (S.36)-(S.38), is not asserted here.

Limitations measured in this layer. Uniqueness of the root in either sector is neither proved nor
used: every statement quantifies over all positive roots. The symmetric root exists at every ring
size, whereas the antisymmetric one is produced only for large `L` — the defect of the cleared
equation at `κ ↓ 0` is negative only once `L` exceeds a multiple of `λ` — so its existence is
stated with `∀ᶠ N in atTop`.

`tightBindingEnergy λ κ` is an eigenvalue of the compression `lowEnergyMatrix N λ` of `Ĥ` to a span
that `Ĥ` does not preserve; it is not identified with a ground-state or first-excited energy of
`Ĥ`. Tasaki notes on p. 59 that the perturbative analysis of this problem is not mathematically
rigorous. The ring carrying the labels `j` is a ring of basis labels of type `ZMod (2 * (N + 1))`,
not of lattice sites: the chain itself stays open.
-/

namespace LatticeSystem.Quantum

/-! ### The monotone factor of the cleared root equation -/

/-- The left-hand side of Tasaki eq. (S.34), p. 500, multiplied by `λ`, i.e.
`hop λ κ = λ (e^κ - e^-κ) = 2 λ sinh κ`. Clearing the denominator of (S.34) rewrites the root
equation as `hop λ κ (1 - s e^-κL) = 1 + s e^-κL`, so `hop λ ·` is the quantity whose comparison
with `1` locates a root. -/
private noncomputable def hop (lam kappa : ℝ) : ℝ :=
  lam * (Real.exp kappa - Real.exp (-kappa))

/-- For a positive transverse field `hop λ ·` is strictly increasing, because `e^κ` increases and
`e^-κ` decreases. -/
private theorem hop_strictMono {lam : ℝ} (hlam : 0 < lam) : StrictMono (hop lam) := by
  intro x y hxy
  have h1 : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr hxy
  have h2 : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  simp only [hop]
  nlinarith

/-- Tasaki eq. (S.35), p. 500, in cleared form: `hop λ κ∞ = λ (e^κ∞ - e^-κ∞) = λ λ⁻¹ = 1`. The
value `1` is the `L ↑ ∞` right-hand side of the cleared root equation. -/
private theorem hop_kappaInf_eq_one {lam : ℝ} (hlam : 0 < lam) : hop lam (kappaInf lam) = 1 := by
  rw [hop, exp_kappaInf_sub_exp_neg hlam]
  field_simp

/-- `hop λ ·` is continuous, the hypothesis under which the intermediate value theorem applies to
the defect of the cleared root equation. -/
private theorem hop_continuous (lam : ℝ) : Continuous (hop lam) := by
  change Continuous fun k : ℝ => lam * (Real.exp k - Real.exp (-k))
  fun_prop

/-! ### The cleared form of (S.34) -/

/-- Tasaki eq. (S.34), p. 500, with its denominator cleared: for `0 < κ` and `s = ±1`,
`e^κ - e^-κ = λ⁻¹ (1 + s e^-κL) / (1 - s e^-κL)` holds exactly when
`λ (e^κ - e^-κ) (1 - s e^-κL) = 1 + s e^-κL`.

Clearing is legitimate for either sign because `0 < κ` forces `0 < e^-κL < 1`, so the denominator
`1 - s e^-κL` is positive. No hypothesis on `λ` is needed: for `λ ≠ 0` the two sides differ by
multiplication with the nonzero factor `λ (1 - s e^-κL)`, and at `λ = 0` both are false, since
`e^κ - e^-κ` is positive while `1 + s e^-κL` is nonzero. -/
theorem rootEquation_iff_cleared (N : ℕ) (lam kappa s : ℝ) (hk : 0 < kappa)
    (hs : s = 1 ∨ s = -1) :
    rootEquation N lam kappa s ↔
      lam * (Real.exp kappa - Real.exp (-kappa))
          * (1 - s * Real.exp (-kappa * (N + 1 : ℕ)))
        = 1 + s * Real.exp (-kappa * (N + 1 : ℕ)) := by
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hwpos : (0 : ℝ) < Real.exp (-kappa * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hwlt : Real.exp (-kappa * ((N + 1 : ℕ) : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  have hA : 0 < Real.exp kappa - Real.exp (-kappa) := by
    have := Real.exp_lt_exp.mpr (show -kappa < kappa by linarith)
    linarith
  rw [rootEquation]
  revert hA hwpos hwlt
  generalize Real.exp kappa - Real.exp (-kappa) = A
  generalize Real.exp (-kappa * ((N + 1 : ℕ) : ℝ)) = w
  intro hwpos hwlt hA
  have hden : (1 : ℝ) - s * w ≠ 0 := by rcases hs with rfl | rfl <;> intro hcon <;> linarith
  have hnum : (0 : ℝ) < 1 + s * w := by rcases hs with rfl | rfl <;> linarith
  rcases eq_or_ne lam 0 with rfl | hlam
  · refine iff_of_false ?_ ?_
    · simp only [inv_zero, zero_mul]
      linarith
    · simp only [zero_mul]
      linarith
  · constructor
    · intro h
      rw [h]
      field_simp
    · intro h
      field_simp
      linear_combination h

/-! ### Existence of a root in each parity sector -/

/-- A sign change of the defect `κ ↦ hop λ κ (1 - s e^-κL) - (1 + s e^-κL)` of the cleared root
equation on an interval `[a, b]` with `0 < a` yields a positive root of Tasaki eq. (S.34): the
intermediate value theorem produces a zero of the defect, and `rootEquation_iff_cleared` turns
that zero back into a root of (S.34). -/
private theorem exists_root_of_defect_sign (N : ℕ) (lam s a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hs : s = 1 ∨ s = -1)
    (hfa : hop lam a * (1 - s * Real.exp (-a * (N + 1 : ℕ)))
        ≤ 1 + s * Real.exp (-a * (N + 1 : ℕ)))
    (hfb : 1 + s * Real.exp (-b * (N + 1 : ℕ))
        ≤ hop lam b * (1 - s * Real.exp (-b * (N + 1 : ℕ)))) :
    ∃ kappa : ℝ, 0 < kappa ∧ rootEquation N lam kappa s := by
  have hexp : Continuous fun k : ℝ => Real.exp (-k * ((N + 1 : ℕ) : ℝ)) := by fun_prop
  have hcont : ContinuousOn (fun k : ℝ =>
      hop lam k * (1 - s * Real.exp (-k * ((N + 1 : ℕ) : ℝ)))
        - (1 + s * Real.exp (-k * ((N + 1 : ℕ) : ℝ)))) (Set.Icc a b) :=
    (((hop_continuous lam).mul (continuous_const.sub (continuous_const.mul hexp))).sub
      (continuous_const.add (continuous_const.mul hexp))).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc
      (hop lam a * (1 - s * Real.exp (-a * ((N + 1 : ℕ) : ℝ)))
        - (1 + s * Real.exp (-a * ((N + 1 : ℕ) : ℝ))))
      (hop lam b * (1 - s * Real.exp (-b * ((N + 1 : ℕ) : ℝ)))
        - (1 + s * Real.exp (-b * ((N + 1 : ℕ) : ℝ)))) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hcont hmem
  have hcpos : 0 < c := lt_of_lt_of_le ha hc.1
  refine ⟨c, hcpos, ?_⟩
  rw [rootEquation_iff_cleared N lam c s hcpos hs]
  simpa only [hop, sub_eq_zero] using hfc

/-- Tasaki eq. (S.34), p. 500, with the upper signs: for every ring size and every `λ > 0` the
symmetric sector has a positive root `κ`, namely one with `κ∞ ≤ κ ≤ κ∞ + 2`.

The defect of the cleared equation is `-2 e^-κL < 0` at `κ∞`, where `hop λ ·` equals `1`, and it
is positive at `κ∞ + 2`, where `hop λ ·` is at least `e²` while `e^-κL` is below `1/2`. -/
theorem exists_root_symmetric (N : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    ∃ kappa : ℝ, 0 < kappa ∧ rootEquation N lam kappa 1 := by
  have hkinf : 0 < kappaInf lam := kappaInf_pos hlam
  have hone : hop lam (kappaInf lam) = 1 := hop_kappaInf_eq_one hlam
  have hLone : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    exact_mod_cast this
  -- the defect at the lower endpoint `κ∞`
  have hwa : (0 : ℝ) < Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hfa : hop lam (kappaInf lam)
      * (1 - 1 * Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ)))
      ≤ 1 + 1 * Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ)) := by
    rw [hone]; linarith
  -- the defect at the upper endpoint `κ∞ + 2`
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hhop : (3 : ℝ) ≤ hop lam (kappaInf lam + 2) := by
    have hsplit : hop lam (kappaInf lam + 2)
        = lam * (Real.exp (kappaInf lam) * Real.exp 2
            - Real.exp (-kappaInf lam) * Real.exp (-2)) := by
      simp only [hop, Real.exp_add, neg_add_rev]
      ring
    have hgap : Real.exp (-2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have hnegpos : (0 : ℝ) < Real.exp (-kappaInf lam) := Real.exp_pos _
    have hbase : lam * (Real.exp (kappaInf lam) - Real.exp (-kappaInf lam)) = 1 := by
      simpa only [hop] using hone
    have hmul : 0 ≤ lam * Real.exp (-kappaInf lam) * (Real.exp 2 - Real.exp (-2)) :=
      mul_nonneg (mul_nonneg hlam.le hnegpos.le) (by linarith)
    have hkey : lam * (Real.exp (kappaInf lam) * Real.exp 2
        - Real.exp (-kappaInf lam) * Real.exp (-2))
        = Real.exp 2 * (lam * (Real.exp (kappaInf lam) - Real.exp (-kappaInf lam)))
          + lam * Real.exp (-kappaInf lam) * (Real.exp 2 - Real.exp (-2)) := by ring
    rw [hsplit, hkey, hbase]
    linarith
  have hwb : Real.exp (-(kappaInf lam + 2) * ((N + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
    have hstep : Real.exp (-(kappaInf lam + 2) * ((N + 1 : ℕ) : ℝ))
        ≤ Real.exp (-(kappaInf lam + 2)) := Real.exp_le_exp.mpr (by nlinarith)
    have hlt : Real.exp (-(kappaInf lam + 2)) ≤ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hinv : Real.exp (-2) = (Real.exp 2)⁻¹ := by rw [← Real.exp_neg]
    have h2pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos _
    have : Real.exp (-2) ≤ 1 / 3 := by
      rw [hinv, inv_le_comm₀ h2pos (by norm_num)]
      linarith
    linarith
  have hwbpos : (0 : ℝ) < Real.exp (-(kappaInf lam + 2) * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hfb : 1 + 1 * Real.exp (-(kappaInf lam + 2) * ((N + 1 : ℕ) : ℝ))
      ≤ hop lam (kappaInf lam + 2)
        * (1 - 1 * Real.exp (-(kappaInf lam + 2) * ((N + 1 : ℕ) : ℝ))) := by
    have hpos : (0 : ℝ) ≤ 1 - 1 * Real.exp (-(kappaInf lam + 2) * ((N + 1 : ℕ) : ℝ)) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hhop hpos]
  exact exists_root_of_defect_sign N lam 1 (kappaInf lam) (kappaInf lam + 2) hkinf
    (by linarith) (Or.inl rfl) hfa hfb

/-- Tasaki eq. (S.34), p. 500, with the lower signs: for every `λ > 0` and every sufficiently
large ring size the antisymmetric sector has a positive root `κ`, namely one with
`1/L ≤ κ ≤ κ∞`.

The defect of the cleared equation is `2 e^-κL > 0` at `κ∞`, where `hop λ ·` equals `1`. At
`κ = 1/L` the factor `hop λ κ ≤ 2 λ κ e^κ` is of order `λ/L` while `1 - e^-κL` is bounded below,
so the defect is negative once `L` exceeds `24 λ`; the statement is therefore restricted to large
`L`, which is also what makes `1/L ≤ κ∞`. -/
theorem eventually_exists_root_antisymmetric (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ kappa : ℝ, 0 < kappa ∧ rootEquation N lam kappa (-1) := by
  have hkinf : 0 < kappaInf lam := kappaInf_pos hlam
  obtain ⟨M, hM⟩ := exists_nat_gt (max (24 * lam) (1 / kappaInf lam))
  filter_upwards [Filter.eventually_ge_atTop M, Filter.eventually_ge_atTop 1] with N hN hN1
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hL2 : (2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hN1
  have hbig : max (24 * lam) (1 / kappaInf lam) < ((N + 1 : ℕ) : ℝ) := by
    have hMle : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
  have h24 : 24 * lam < ((N + 1 : ℕ) : ℝ) := lt_of_le_of_lt (le_max_left _ _) hbig
  have hinvk : 1 / kappaInf lam < ((N + 1 : ℕ) : ℝ) := lt_of_le_of_lt (le_max_right _ _) hbig
  have hk0pos : (0 : ℝ) < 1 / ((N + 1 : ℕ) : ℝ) := by positivity
  have hk0le : 1 / ((N + 1 : ℕ) : ℝ) ≤ kappaInf lam := by
    rw [div_lt_iff₀ hkinf] at hinvk
    rw [div_le_iff₀ hLpos]
    nlinarith
  -- at the lower endpoint `κ = 1/L` the exponent `-κ L` is exactly `-1`
  have hexp1 : Real.exp (-(1 / ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ)) = Real.exp (-1) := by
    congr 1
    field_simp
  have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have he1pos : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
  -- `hop λ κ ≤ 2 λ κ e^κ ≤ 4 λ κ` for `0 < κ ≤ 1/2`
  have hk0half : 1 / ((N + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hLpos (by norm_num)]
    linarith
  have hhople : hop lam (1 / ((N + 1 : ℕ) : ℝ)) ≤ 4 * lam * (1 / ((N + 1 : ℕ) : ℝ)) := by
    set k : ℝ := 1 / ((N + 1 : ℕ) : ℝ) with hkdef
    have hkpos : (0 : ℝ) < Real.exp k := Real.exp_pos _
    have hnegpos : (0 : ℝ) < Real.exp (-k) := Real.exp_pos _
    have hprod : Real.exp k * Real.exp (-k) = 1 := by rw [← Real.exp_add]; simp
    have hlow : 1 - k ≤ Real.exp (-k) := by
      have := Real.add_one_le_exp (-k)
      linarith
    have hexpk : Real.exp k ≤ 2 := by nlinarith
    have hsq : Real.exp (-k) = Real.exp k * Real.exp (-2 * k) := by
      rw [← Real.exp_add]; ring_nf
    have hlin : 1 - Real.exp (-2 * k) ≤ 2 * k := by
      have := Real.add_one_le_exp (-2 * k)
      linarith
    have hstep1 : Real.exp k - Real.exp (-k) ≤ 2 * k * Real.exp k := by
      rw [hsq]; nlinarith
    have hstep2 : 2 * k * Real.exp k ≤ 4 * k := by nlinarith
    calc hop lam k = lam * (Real.exp k - Real.exp (-k)) := rfl
      _ ≤ lam * (4 * k) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hlam.le
      _ = 4 * lam * k := by ring
  have hhopnn : 0 ≤ hop lam (1 / ((N + 1 : ℕ) : ℝ)) := by
    simp only [hop]
    have : Real.exp (-(1 / ((N + 1 : ℕ) : ℝ))) ≤ Real.exp (1 / ((N + 1 : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    nlinarith
  have hquart : 4 * lam * (1 / ((N + 1 : ℕ) : ℝ)) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_iff₀ hLpos]
    linarith
  have hfa : hop lam (1 / ((N + 1 : ℕ) : ℝ))
      * (1 - (-1) * Real.exp (-(1 / ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ)))
      ≤ 1 + (-1) * Real.exp (-(1 / ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ)) := by
    rw [hexp1]
    nlinarith
  have hwb : (0 : ℝ) < Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hfb : 1 + (-1) * Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ))
      ≤ hop lam (kappaInf lam)
        * (1 - (-1) * Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ))) := by
    rw [hop_kappaInf_eq_one hlam]
    linarith
  exact exists_root_of_defect_sign N lam (-1) (1 / ((N + 1 : ℕ) : ℝ)) (kappaInf lam) hk0pos
    hk0le (Or.inr rfl) hfa hfb

/-! ### The (S.40) ordering of the two sectors -/

/-- Tasaki's conclusion after eq. (S.40), p. 501, "We see that the symmetric solution has a lower
energy, as it should be", as an exact strict inequality: if `kp` is a positive root of the
symmetric (`s = 1`) root equation (S.34) and `km` a positive root of the antisymmetric (`s = -1`)
one, then `tightBindingEnergy λ kp < tightBindingEnergy λ km`.

Both roots are compared through the cleared equation, which gives
`λ (e^kp - e^-kp) = (1 + w)/(1 - w) > 1` and `λ (e^km - e^-km) = (1 - w)/(1 + w) < 1`; that factor
is strictly increasing in the exponent, so `km < kp`, and `tightBindingEnergy λ ·` is strictly
decreasing on the positive reals because `cosh` is strictly increasing there. Positivity of `λ`
is not assumed: it follows from either root hypothesis, since a positive `κ` makes the left-hand
side of (S.34) positive.

The statement carries no asymptotics; the displayed `≃` form of (S.40) is not asserted, and
`tightBindingEnergy` is an eigenvalue of the compressed matrix rather than an energy of `Ĥ`. -/
theorem tightBindingEnergy_lt_of_roots (N : ℕ) (lam kp km : ℝ) (hkp : 0 < kp) (hkm : 0 < km)
    (hroot_p : rootEquation N lam kp 1) (hroot_m : rootEquation N lam km (-1)) :
    tightBindingEnergy lam kp < tightBindingEnergy lam km := by
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hwp : (0 : ℝ) < Real.exp (-kp * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hwplt : Real.exp (-kp * ((N + 1 : ℕ) : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hwm : (0 : ℝ) < Real.exp (-km * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hwmlt : Real.exp (-km * ((N + 1 : ℕ) : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hAp : 0 < Real.exp kp - Real.exp (-kp) := by
    have := Real.exp_lt_exp.mpr (show -kp < kp by linarith)
    linarith
  -- positivity of `λ` is forced by the symmetric root equation
  have hlam : 0 < lam := by
    rw [rootEquation] at hroot_p
    have hq : (0 : ℝ) < (1 + 1 * Real.exp (-kp * ((N + 1 : ℕ) : ℝ)))
        / (1 - 1 * Real.exp (-kp * ((N + 1 : ℕ) : ℝ))) :=
      div_pos (by linarith) (by linarith)
    have hprod : 0 < lam⁻¹ * ((1 + 1 * Real.exp (-kp * ((N + 1 : ℕ) : ℝ)))
        / (1 - 1 * Real.exp (-kp * ((N + 1 : ℕ) : ℝ)))) := hroot_p ▸ hAp
    refine inv_pos.mp ?_
    by_contra hcon
    push Not at hcon
    nlinarith
  -- the two cleared equations place the roots on opposite sides of `κ∞`
  have hcp := (rootEquation_iff_cleared N lam kp 1 hkp (Or.inl rfl)).mp hroot_p
  have hcm := (rootEquation_iff_cleared N lam km (-1) hkm (Or.inr rfl)).mp hroot_m
  have hopp : 1 < hop lam kp := by
    simp only [hop]
    nlinarith
  have hopm : hop lam km < 1 := by
    simp only [hop]
    nlinarith
  have hlt : km < kp := (hop_strictMono hlam).lt_iff_lt.mp (by linarith)
  -- `tightBindingEnergy λ ·` is strictly decreasing on the positive reals
  have hcosh : Real.cosh km < Real.cosh kp := by
    rw [Real.cosh_lt_cosh, abs_of_pos hkm, abs_of_pos hkp]
    exact hlt
  have hsum : Real.exp km + Real.exp (-km) < Real.exp kp + Real.exp (-kp) := by
    rw [Real.cosh_eq, Real.cosh_eq] at hcosh
    linarith
  simp only [tightBindingEnergy]
  nlinarith

end LatticeSystem.Quantum
