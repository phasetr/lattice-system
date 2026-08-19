import LatticeSystem.Math.ProjectiveRepresentation

/-!
# Tests: §8.3.5 projective-representation definition layer (PR-1 of #5306)

Behavioural (TDD Red) tests for `LatticeSystem.Math.ProjectiveRepresentation`, targeting the
accepted design (`.self-local/reports/design-5306-pr1-definitions-coboundary.md` §6, T1-T4):

* **T1** non-vacuity: the trivial representation satisfies `IsProjectiveRep`,
  `IsTrivialProjectiveRep`, and `IsPhaseCoboundary` simultaneously.
* **T2** negative control: an asymmetric phase on an abelian `s = 1` group is *not* a
  coboundary (coboundaries with `s = 1` are symmetric in `g, h`).
* **T3** the sign twist is not a no-op: `signConj`/`signConjMatrix` at `ε = -1` genuinely
  conjugate, and a concrete `(u, s, φ)` with `s ≠ 1` satisfies `IsProjectiveRep` only because
  of the twist.
* **T4** round trip: both directions of the capstone
  `isTrivialProjectiveRep_iff_isPhaseCoboundary` fire on a nonconstant-phase example.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §8.3.5,
eqs. (8.3.40)-(8.3.43), pp. 277-278.  Refs #5306, #4718.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Math

/-! ## Shared fixtures -/

/-- The nonidentity element of the two-element group `Multiplicative (ZMod 2)`. -/
private def g0 : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)

private lemma g0_ne_one : g0 ≠ 1 := by decide

private lemma g0_mul_self : g0 * g0 = 1 := by decide

/-- `Multiplicative (ZMod 2)` has exactly two elements, `1` and `g0`. -/
private lemma multiplicativeZMod2_eq_one_or_eq_g0 :
    ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = g0 := by decide

/-- A `Circle`-scaled identity matrix is unitary: shared fixture for T1/T3/T4. -/
private lemma circleSmul_one_mem_unitaryGroup {D : Type*} [Fintype D] [DecidableEq D]
    (z : Circle) : z • (1 : Matrix D D ℂ) ∈ Matrix.unitaryGroup D ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simp [Circle.smul_def, star_smul, smul_smul, ← Circle.coe_inv_eq_conj]

/-- Applying a ring hom `f` entrywise to a `Circle`-scaled identity matrix scales by `f z`. -/
private lemma map_circleSmul_one {D : Type*} [DecidableEq D] (f : ℂ →+* ℂ) (z : ℂ) :
    (z • (1 : Matrix D D ℂ)).map f = f z • (1 : Matrix D D ℂ) := by
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.smul_apply, Matrix.map_apply]

/-- `signConjMatrix` on a `Circle`-scaled identity matrix reduces to `signConj` on the scalar
(bundles `Circle.smul_def` with `map_circleSmul_one`). -/
private lemma signConjMatrix_circleSmul_one {D : Type*} [Fintype D] [DecidableEq D] (ε : ℤˣ)
    (z : Circle) : signConjMatrix ε (z • (1 : Matrix D D ℂ)) =
      signConj ε (z : ℂ) • (1 : Matrix D D ℂ) := by
  rw [signConjMatrix, RingHom.mapMatrix_apply, Circle.smul_def, map_circleSmul_one]

/-- Same as `signConjMatrix_circleSmul_one`, stated for an already-coerced `ℂ`-scalar (used once
`Circle.smul_def` has already fired elsewhere in a `simp` normal form). -/
private lemma signConjMatrix_smul_one {D : Type*} [Fintype D] [DecidableEq D] (ε : ℤˣ) (w : ℂ) :
    signConjMatrix ε (w • (1 : Matrix D D ℂ)) = signConj ε w • (1 : Matrix D D ℂ) := by
  rw [signConjMatrix, RingHom.mapMatrix_apply, map_circleSmul_one]

/-! ## T1: non-vacuity -/

/-- T1: the one-dimensional trivial representation is a genuine (hence trivial) projective
representation with the identically-`1` phase, and its phase is a coboundary. -/
private lemma t1_isProjectiveRep :
    IsProjectiveRep (D := Fin 1) (G := Multiplicative (ZMod 2))
      (fun _ => 1) (1 : Multiplicative (ZMod 2) →* ℤˣ)
      (1 : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Circle) := by
  refine ⟨fun _ => Submonoid.one_mem _, rfl, fun g h => ?_⟩
  simp [signConjMatrix, signConj]

/-- T1: the trivial representation of T1 is trivial in the technical sense (witnessed by
itself and the constant-`1` gauge). -/
private lemma t1_isTrivialProjectiveRep :
    IsTrivialProjectiveRep (D := Fin 1) (G := Multiplicative (ZMod 2))
      (fun _ => 1) (1 : Multiplicative (ZMod 2) →* ℤˣ) :=
  ⟨fun _ => 1, 1, t1_isProjectiveRep, fun _ => by simp⟩

/-- T1: the identically-`1` phase is a coboundary (witnessed by the identically-`1` gauge). -/
private lemma t1_isPhaseCoboundary :
    IsPhaseCoboundary (G := Multiplicative (ZMod 2)) (1 : Multiplicative (ZMod 2) →* ℤˣ)
      (1 : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Circle) :=
  ⟨1, fun _ _ => by simp⟩

/-! ## T2: negative control (asymmetric phase is not a coboundary) -/

/-- The `Z₂×Z₂` pair of generators used to exhibit an asymmetric, non-coboundary phase. -/
private def a2 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := (g0, 1)

private def b2 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := (1, g0)

private lemma a2_ne_b2 : a2 ≠ b2 := by decide

/-- An asymmetric phase: `-1` at `(a2, b2)`, `1` everywhere else (in particular at `(b2, a2)`). -/
private noncomputable def phi2 (g h : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    Circle :=
  if g = a2 ∧ h = b2 then Circle.exp Real.pi else 1

private lemma phi2_a2_b2 : phi2 a2 b2 = Circle.exp Real.pi := if_pos ⟨rfl, rfl⟩

private lemma phi2_b2_a2 : phi2 b2 a2 = 1 :=
  if_neg fun h => a2_ne_b2 h.1.symm

/-- T2: on an abelian group with the trivial sign `s = 1`, a coboundary phase is symmetric
(`φ g h = φ h g`); `phi2` is not symmetric (`phi2 a2 b2 ≠ phi2 b2 a2`), hence it is not a
coboundary.  Guards `IsPhaseCoboundary` against being vacuously true. -/
private lemma t2_not_isPhaseCoboundary :
    ¬ IsPhaseCoboundary
        (1 : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* ℤˣ) phi2 := by
  rintro ⟨ψ, hψ⟩
  have hab := hψ a2 b2
  have hba := hψ b2 a2
  rw [phi2_a2_b2] at hab
  rw [phi2_b2_a2] at hba
  simp only [MonoidHom.one_apply, Units.val_one, zpow_one] at hab hba
  have hRHSeq : ψ a2 * ψ b2 * (ψ (a2 * b2))⁻¹ = ψ b2 * ψ a2 * (ψ (b2 * a2))⁻¹ := by
    rw [mul_comm a2 b2, mul_comm (ψ a2) (ψ b2)]
  exact Circle.exp_pi_ne_one (hab.trans (hRHSeq.trans hba.symm))

/-! ## T3: the sign twist is not a no-op -/

/-- A concrete nonconstant phase in `Circle`, used as the "twist" scalar throughout T3/T4. -/
private noncomputable def iCircle : Circle := Circle.exp (Real.pi / 2)

private lemma iCircle_mul_self_ne_one : iCircle * iCircle ≠ 1 := by
  have hsq : iCircle * iCircle = Circle.exp Real.pi := by
    rw [iCircle, ← Circle.exp_add]
    norm_num
  rw [hsq]
  exact Circle.exp_pi_ne_one

private lemma iCircle_mul_conj : (iCircle : ℂ) * starRingEnd ℂ (iCircle : ℂ) = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]

private lemma iCircle_conj_mul : starRingEnd ℂ (iCircle : ℂ) * (iCircle : ℂ) = 1 := by
  rw [mul_comm]; exact iCircle_mul_conj

/-- T3a: `signConj` at `ε = -1` is entrywise complex conjugation (eq. (8.3.40)). -/
private lemma t3_signConj_neg_one (z : ℂ) : signConj (-1 : ℤˣ) z = starRingEnd ℂ z := by
  simp [signConj]

/-- T3b: `signConjMatrix` at `ε = -1` is entrywise complex conjugation, and this is *not* the
identity on a genuinely complex matrix (the twist is not a no-op). -/
private lemma t3_signConjMatrix_neg_one_ne_self :
    signConjMatrix (-1 : ℤˣ) (iCircle • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ≠
      iCircle • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [signConjMatrix_circleSmul_one, t3_signConj_neg_one]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [Circle.smul_def, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    at h00
  rw [← Circle.coe_inv_eq_conj] at h00
  have hinv : iCircle⁻¹ = iCircle := Circle.coe_injective h00
  exact iCircle_mul_self_ne_one (by nth_rewrite 2 [← hinv]; exact mul_inv_cancel iCircle)

/-- The one-dimensional representation `u g0 = iCircle`, `u 1 = 1`, whose defining identity for
`s ≠ 1` genuinely uses the sign twist (dropping it would force `iCircle² = 1`, which is false by
`iCircle_mul_self_ne_one`). -/
private noncomputable def uT3 (g : Multiplicative (ZMod 2)) : Matrix (Fin 1) (Fin 1) ℂ :=
  if g = 1 then 1 else iCircle • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The nontrivial sign homomorphism `ZMod 2 → {±1}` used to trigger the twist in T3/T4. -/
private noncomputable def sT3 : Multiplicative (ZMod 2) →* ℤˣ where
  toFun g := if g = 1 then 1 else -1
  map_one' := by simp
  map_mul' := by decide

private lemma sT3_one : sT3 (1 : Multiplicative (ZMod 2)) = 1 := by simp [sT3]

private lemma sT3_g0 : sT3 g0 = -1 := by simp [sT3, g0_ne_one]

/-- T3c: `(uT3, sT3, 1)` satisfies `IsProjectiveRep`; the `g = h = g0` case genuinely needs the
sign twist (`sT3 g0 = -1`), since `uT3 g0 * uT3 g0` (no twist) would compute to `-1 ≠ 1`
whereas `uT3 g0 * signConjMatrix (sT3 g0) (uT3 g0) = 1` (with the twist) matches `uT3 (g0 * g0)`
(eq. (8.3.41)-(8.3.42) with the nontrivial sign). -/
private lemma t3_isProjectiveRep :
    IsProjectiveRep uT3 sT3
      (1 : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Circle) := by
  refine ⟨fun g => ?_, by simp [uT3], fun g h => ?_⟩
  · rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;> subst hg
    · simp only [uT3]
      exact Submonoid.one_mem (Matrix.unitaryGroup (Fin 1) ℂ)
    · simp only [uT3, if_neg g0_ne_one]
      exact circleSmul_one_mem_unitaryGroup (D := Fin 1) iCircle
  · rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;>
      rcases multiplicativeZMod2_eq_one_or_eq_g0 h with hh | hh <;> subst hg <;> subst hh
    · simp [uT3, signConjMatrix, signConj, sT3_one]
    · simp [uT3, signConjMatrix, signConj, sT3_one]
    · simp [uT3, signConjMatrix, signConj, sT3_g0]
    · simp [g0_mul_self, g0_ne_one, sT3_g0, uT3, signConjMatrix_smul_one,
        t3_signConj_neg_one, Circle.smul_def, smul_smul, iCircle_conj_mul]

/-! ## T4: round trip (both directions of the capstone fire) -/

/-- A nonconstant `Circle`-valued gauge `ψ : G → Circle` with `ψ 1 = 1`, `ψ g0 = iCircle`. -/
private noncomputable def psiT4 (g : Multiplicative (ZMod 2)) : Circle :=
  if g = 1 then 1 else iCircle

private lemma psiT4_one : psiT4 (1 : Multiplicative (ZMod 2)) = 1 := if_pos rfl

private lemma psiT4_g0 : psiT4 g0 = iCircle := if_neg g0_ne_one

/-- The genuine (untwisted, `s = 1`) representation gauge-transformed by `psiT4`. -/
private noncomputable def uT4 (g : Multiplicative (ZMod 2)) : Matrix (Fin 1) (Fin 1) ℂ :=
  psiT4 g • (1 : Matrix (Fin 1) (Fin 1) ℂ)

/-- The genuine representation underlying `uT4` (trivial, `s = 1`). -/
private lemma uT4_isProjectiveRep :
    IsProjectiveRep (D := Fin 1) (G := Multiplicative (ZMod 2)) (fun _ => 1)
      (1 : Multiplicative (ZMod 2) →* ℤˣ)
      (1 : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Circle) :=
  t1_isProjectiveRep

/-- `uT4` is a genuine `IsProjectiveRep` on its own (it is the trivial rep gauge-twisted by the
group's own multiplication, `s = 1`), with phase `φT4 g h = psiT4 g * psiT4 h * (psiT4 (g*h))⁻¹`
matching the coboundary formula on the nose. -/
private noncomputable def phiT4 (g h : Multiplicative (ZMod 2)) : Circle :=
  psiT4 g * psiT4 h * (psiT4 (g * h))⁻¹

private lemma uT4_isProjectiveRep' :
    IsProjectiveRep uT4 (1 : Multiplicative (ZMod 2) →* ℤˣ) phiT4 := by
  refine ⟨fun g => ?_, by simp [uT4, psiT4_one], fun g h => ?_⟩
  · rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;> subst hg
    · simp only [uT4, psiT4_one]
      exact circleSmul_one_mem_unitaryGroup (D := Fin 1) 1
    · simp only [uT4, psiT4_g0]
      exact circleSmul_one_mem_unitaryGroup (D := Fin 1) iCircle
  · change uT4 g * signConjMatrix ((1 : Multiplicative (ZMod 2) →* ℤˣ) g) (uT4 h) =
      (phiT4 g h : ℂ) • uT4 (g * h)
    have hgroup : phiT4 g h * psiT4 (g * h) = psiT4 g * psiT4 h := by
      rw [phiT4]; group
    have hcoe : (phiT4 g h : ℂ) * (psiT4 (g * h) : ℂ) = (psiT4 g : ℂ) * (psiT4 h : ℂ) := by
      rw [← Circle.coe_mul, ← Circle.coe_mul, hgroup]
    simp [uT4, MonoidHom.one_apply, Circle.smul_def, signConjMatrix_smul_one, signConj,
      smul_smul, hcoe, mul_comm]

/-- T4 (⟹, `.mp`): the trivial representation `uT4` is trivial by construction, so its phase
`phiT4` must be a coboundary. -/
private lemma t4_mp :
    IsPhaseCoboundary (1 : Multiplicative (ZMod 2) →* ℤˣ) phiT4 :=
  (isTrivialProjectiveRep_iff_isPhaseCoboundary uT4_isProjectiveRep').mp
    ⟨fun _ => 1, psiT4, t1_isProjectiveRep, fun g => by simp [uT4, Circle.smul_def]⟩

/-- T4 (⟸, `.mpr`): since `phiT4` is a coboundary (by direct computation with `psiT4`), the
capstone gives back triviality of `uT4` — exercising the converse direction on the same data. -/
private lemma t4_mpr :
    IsTrivialProjectiveRep uT4 (1 : Multiplicative (ZMod 2) →* ℤˣ) :=
  (isTrivialProjectiveRep_iff_isPhaseCoboundary uT4_isProjectiveRep').mpr
    ⟨psiT4, fun _ _ => by simp [phiT4]⟩

end LatticeSystem.Tests
