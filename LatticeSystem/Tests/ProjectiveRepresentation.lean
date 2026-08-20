import LatticeSystem.Math.ProjectiveRepresentation
import LatticeSystem.Quantum.Pauli

/-!
# Tests: §8.3.5 projective-representation definition layer (PR-1 of #5306)

Behavioural tests for `LatticeSystem.Math.ProjectiveRepresentation`:

* **T1** non-vacuity: the trivial representation satisfies `IsProjectiveRep`,
  `IsTrivialProjectiveRep`, and `IsPhaseCoboundary` simultaneously.
* **T2** negative control: an asymmetric phase on an abelian `s = 1` group is *not* a
  coboundary (coboundaries with `s = 1` are symmetric in `g, h`).
* **T3** the sign twist is not a no-op: `signConj`/`signConjMatrix` at `ε = -1` genuinely
  conjugate, and a concrete `(u, s, φ)` with `s ≠ 1` satisfies `IsProjectiveRep` only because
  of the twist.
* **T4** both directions of the capstone `isTrivialProjectiveRep_iff_isPhaseCoboundary` on a
  two-dimensional bond space (`D = Fin 2`), applied to the *same* family `û(e) = 1̂`,
  `û(a) = û₂ = -iσ^y` with the *same* phase `φ(a,a) = -1` (the spin-1/2 time-reversal example of
  p. 278, `Θ̂² = -1̂`).  For the trivial sign character `.mpr` yields triviality, for the
  antiunitary one `.mp` yields *non*triviality: with `s(a) = -1` formula (8.3.43) degenerates to
  `ψ(a) ψ(a)⁻¹ ψ(e)⁻¹` at `(a,a)` and can no longer produce `-1`.  The two conclusions differ in
  nothing but the sign character `s` and contradict each other as soon as `s` is ignored, so the
  twist is load-bearing.
* **T5** a second capstone negative control, untwisted and on a larger group: the `Z₂ × Z₂` Pauli
  representation on `ℂ²` (`σ^x`, `σ^z`, which realise the anticommutation half of Tasaki
  eq. (2.1.31) in the gauge where the generators square to `+1̂` rather than `-1̂`) has an
  asymmetric phase, so `.mp` shows it is *not* trivial.  Together with T4 this pins the capstone
  down on a space where both sides can fail — on a one-dimensional space every projective
  representation is trivial.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §8.3.5,
eqs. (8.3.40)-(8.3.43), pp. 277-278; §2.1, eq. (2.1.31), p. 20.  Refs #5306, #4718.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Math
open LatticeSystem.Quantum (pauliX pauliZ pauliX_isHermitian pauliZ_isHermitian pauliX_mul_self
  pauliZ_mul_self)

/-! ## Shared fixtures -/

/-- The nonidentity element of the two-element group `Multiplicative (ZMod 2)`. -/
private def g0 : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)

/-- `g0` is not the identity, so the two-element group really has two elements. -/
private lemma g0_ne_one : g0 ≠ 1 := by decide

/-- `g0` is an involution. -/
private lemma g0_mul_self : g0 * g0 = 1 := by decide

/-- `Multiplicative (ZMod 2)` has exactly two elements, `1` and `g0`. -/
private lemma multiplicativeZMod2_eq_one_or_eq_g0 :
    ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = g0 := by decide

/-- The phase `-1 = e^{iπ}` on the circle: the sign produced by the Pauli anticommutation
relation and the value separating the asymmetric phases of T2/T5 from `1`. -/
private noncomputable def negCircle : Circle := Circle.exp Real.pi

/-- `negCircle` is the complex number `-1`. -/
private lemma coe_negCircle : (negCircle : ℂ) = -1 := by
  rw [negCircle, Circle.coe_exp, Complex.exp_pi_mul_I]

/-- `negCircle ≠ 1`: the asymmetric phase functions below really take two values. -/
private lemma negCircle_ne_one : negCircle ≠ 1 := Circle.exp_pi_ne_one

/-- With the trivial sign character on an abelian group, the coboundary formula (8.3.43) is
symmetric in `g` and `h`; hence an asymmetric phase function is not a coboundary. -/
private lemma not_isPhaseCoboundary_of_ne {G : Type*} [CommGroup G] {φ : G → G → Circle}
    {a b : G} (hab : φ a b ≠ φ b a) : ¬ IsPhaseCoboundary (1 : G →* ℤˣ) φ := by
  rintro ⟨ψ, hψ⟩
  refine hab ?_
  have h₁ := hψ a b
  have h₂ := hψ b a
  simp only [MonoidHom.one_apply, Units.val_one, zpow_one] at h₁ h₂
  rw [h₁, h₂, mul_comm a b, mul_comm (ψ a) (ψ b)]

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

/-- The first `Z₂ × Z₂` generator, also used as the `σ^x` generator in T5. -/
private def a2 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := (g0, 1)

/-- The second `Z₂ × Z₂` generator, also used as the `σ^z` generator in T5. -/
private def b2 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) := (1, g0)

/-- The two `Z₂ × Z₂` generators are distinct. -/
private lemma a2_ne_b2 : a2 ≠ b2 := by decide

/-- An asymmetric phase: `-1` at `(a2, b2)`, `1` everywhere else (in particular at `(b2, a2)`). -/
private noncomputable def phi2 (g h : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    Circle :=
  if g = a2 ∧ h = b2 then negCircle else 1

/-- `phi2` takes the value `-1` at `(a2, b2)`. -/
private lemma phi2_a2_b2 : phi2 a2 b2 = negCircle := if_pos ⟨rfl, rfl⟩

/-- `phi2` takes the value `1` at the transposed pair `(b2, a2)`. -/
private lemma phi2_b2_a2 : phi2 b2 a2 = 1 :=
  if_neg fun h => a2_ne_b2 h.1.symm

/-- T2: `phi2` is not symmetric (`phi2 a2 b2 ≠ phi2 b2 a2`), hence — on an abelian group with the
trivial sign `s = 1` — it is not a coboundary.  Guards `IsPhaseCoboundary` against being
vacuously true. -/
private lemma t2_not_isPhaseCoboundary :
    ¬ IsPhaseCoboundary
        (1 : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* ℤˣ) phi2 :=
  not_isPhaseCoboundary_of_ne (by rw [phi2_a2_b2, phi2_b2_a2]; exact negCircle_ne_one)

/-! ## T3: the sign twist is not a no-op -/

/-- A concrete nonconstant phase in `Circle`, used as the "twist" scalar throughout T3/T4. -/
private noncomputable def iCircle : Circle := Circle.exp (Real.pi / 2)

/-- `iCircle` squares to `-1`. -/
private lemma iCircle_mul_self : iCircle * iCircle = negCircle := by
  rw [iCircle, negCircle, ← Circle.exp_add]
  norm_num

/-- `iCircle` is not a square root of `1`. -/
private lemma iCircle_mul_self_ne_one : iCircle * iCircle ≠ 1 := by
  rw [iCircle_mul_self]
  exact negCircle_ne_one

/-- `iCircle` has unit modulus (stated as `z * conj z = 1`). -/
private lemma iCircle_mul_conj : (iCircle : ℂ) * starRingEnd ℂ (iCircle : ℂ) = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]

/-- `iCircle` has unit modulus (stated as `conj z * z = 1`). -/
private lemma iCircle_conj_mul : starRingEnd ℂ (iCircle : ℂ) * (iCircle : ℂ) = 1 := by
  rw [mul_comm]; exact iCircle_mul_conj

/-- T3b: `signConjMatrix` at `ε = -1` is entrywise complex conjugation, and this is *not* the
identity on a genuinely complex matrix (the twist is not a no-op). -/
private lemma t3_signConjMatrix_neg_one_ne_self :
    signConjMatrix (-1 : ℤˣ) (iCircle • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ≠
      iCircle • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [Circle.smul_def, signConjMatrix_smul, map_one, signConj_neg_one_apply]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
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

/-- The sign character is `+1` at the identity (the unitary case). -/
private lemma sT3_one : sT3 (1 : Multiplicative (ZMod 2)) = 1 := by simp [sT3]

/-- The sign character is `-1` at `g0` (the antiunitary case). -/
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
      exact circle_smul_mem_unitaryGroup iCircle (Submonoid.one_mem _)
  · rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;>
      rcases multiplicativeZMod2_eq_one_or_eq_g0 h with hh | hh <;> subst hg <;> subst hh
    · simp [uT3, signConjMatrix, signConj, sT3_one]
    · simp [uT3, signConjMatrix, signConj, sT3_one]
    · simp [uT3, signConjMatrix, signConj, sT3_g0]
    · simp [g0_mul_self, g0_ne_one, sT3_g0, uT3, signConjMatrix_smul, signConj_neg_one_apply,
        Circle.smul_def, smul_smul, iCircle_conj_mul]

/-! ## T4: capstone on a two-dimensional space, with and without the sign twist -/

/-- `σ^x` is unitary. -/
private lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, pauliX_isHermitian.eq,
    pauliX_mul_self]

/-- `σ^z` is unitary. -/
private lemma pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, pauliZ_isHermitian.eq,
    pauliZ_mul_self]

/-- The unitary part of spin-1/2 time reversal, `Θ̂ = û₂ K̂` with `û₂ = -i σ^y = ((0, -1), (1, 0))`
(p. 278).  Its entries are real, so the antiunitary twist `C_{-1}` fixes it; its square is `-1̂`,
which is the relation `Θ̂² = -1̂` for half-odd-integer spin. -/
private def thetaMat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

/-- `û₂ û₂ = -1̂`. -/
private lemma thetaMat_mul_self : thetaMat * thetaMat = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `û₂` is unitary. -/
private lemma thetaMat_mem_unitaryGroup : thetaMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thetaMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

/-- `û₂` has real entries, so it is fixed by the twist `C_ε` for *both* signs. -/
private lemma signConjMatrix_thetaMat (ε : ℤˣ) : signConjMatrix ε thetaMat = thetaMat := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · exact signConjMatrix_one_apply thetaMat
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signConjMatrix, signConj, thetaMat, RingHom.mapMatrix_apply]

/-- The two-dimensional family `û(e) = 1̂`, `û(a) = û₂` of the time-reversal example of p. 278. -/
private def uT4 (g : Multiplicative (ZMod 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  if g = 1 then 1 else thetaMat

/-- The phase function of `uT4`: `-1` exactly at `(g0, g0)`, read off from
`û₂ û₂ = -1̂ = e^{iπ} û(e)` (eq. (8.3.42)). -/
private noncomputable def phiT4 (g h : Multiplicative (ZMod 2)) : Circle :=
  if g = g0 ∧ h = g0 then negCircle else 1

/-- `phiT4` is trivial at the identity pair, as `IsProjectiveRep` forces. -/
private lemma phiT4_one_one : phiT4 1 1 = 1 := if_neg fun h => g0_ne_one h.1.symm

/-- `phiT4` is `-1` at `(g0, g0)`: the obstruction that the twisted coboundary formula cannot
absorb. -/
private lemma phiT4_g0_g0 : phiT4 g0 g0 = negCircle := if_pos ⟨rfl, rfl⟩

/-- T4a: `(uT4, s, phiT4)` is a projective representation for *every* sign character `s`, because
`û₂` is real and hence fixed by `C_{s(g)}`.  The two capstone tests below instantiate this at
`s = 1` and at the nontrivial `s = sT3`, so they differ in nothing but the sign character. -/
private lemma uT4_isProjectiveRep (s : Multiplicative (ZMod 2) →* ℤˣ) :
    IsProjectiveRep uT4 s phiT4 := by
  refine ⟨fun g => ?_, by simp [uT4], fun g h => ?_⟩
  · rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;> subst hg
    · simp [uT4]
    · simpa [uT4, if_neg g0_ne_one] using thetaMat_mem_unitaryGroup
  · rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;>
      rcases multiplicativeZMod2_eq_one_or_eq_g0 h with hh | hh <;> subst hg <;> subst hh
    · simp [uT4, phiT4, g0_ne_one.symm]
    · simp [uT4, phiT4, g0_ne_one, g0_ne_one.symm, signConjMatrix_thetaMat]
    · simp [uT4, phiT4, g0_ne_one, g0_ne_one.symm]
    · simp [uT4, phiT4_g0_g0, g0_ne_one, g0_mul_self, signConjMatrix_thetaMat, thetaMat_mul_self,
        coe_negCircle]

/-- A nonconstant `Circle`-valued gauge `ψ : G → Circle` with `ψ 1 = 1`, `ψ g0 = iCircle`. -/
private noncomputable def psiT4 (g : Multiplicative (ZMod 2)) : Circle :=
  if g = 1 then 1 else iCircle

/-- The gauge is trivial at the identity. -/
private lemma psiT4_one : psiT4 (1 : Multiplicative (ZMod 2)) = 1 := if_pos rfl

/-- The gauge is `iCircle` at `g0`, so it is not constant. -/
private lemma psiT4_g0 : psiT4 g0 = iCircle := if_neg g0_ne_one

/-- T4b: for the *untwisted* sign character `s = 1` the phase `phiT4` is a coboundary, witnessed by
the gauge `psiT4`: the untwisted formula (8.3.43) contributes `ψ(g0) ψ(g0) = i² = -1` at `(g0, g0)`,
matching `û₂ û₂ = -1̂`. -/
private lemma t4_isPhaseCoboundary_one :
    IsPhaseCoboundary (1 : Multiplicative (ZMod 2) →* ℤˣ) phiT4 := by
  refine ⟨psiT4, fun g h => ?_⟩
  rcases multiplicativeZMod2_eq_one_or_eq_g0 g with hg | hg <;>
    rcases multiplicativeZMod2_eq_one_or_eq_g0 h with hh | hh <;> subst hg <;> subst hh
  · simp [phiT4, psiT4_one, g0_ne_one.symm]
  · simp [phiT4, psiT4_one, psiT4_g0, g0_ne_one.symm]
  · simp [phiT4, psiT4_one, psiT4_g0, g0_ne_one.symm]
  · simp [phiT4_g0_g0, psiT4_one, psiT4_g0, g0_mul_self, iCircle_mul_self]

/-- T4c (`.mpr`, untwisted): the capstone turns the coboundary of T4b into triviality of `uT4` for
`s = 1`.  The genuine representation behind it is `i⁻¹ û₂ = -σ^y` (which squares to `1̂`); it is
produced by the capstone, not handed to it. -/
private lemma t4_isTrivialProjectiveRep_one :
    IsTrivialProjectiveRep uT4 (1 : Multiplicative (ZMod 2) →* ℤˣ) :=
  (isTrivialProjectiveRep_iff_isPhaseCoboundary (uT4_isProjectiveRep 1)).mpr
    t4_isPhaseCoboundary_one

/-- T4d: for the *twisted* sign character `sT3` the very same phase is **not** a coboundary.  The
twist is what kills it: at `(g0, g0)` the exponent `s(g0) = -1` turns eq. (8.3.43) into
`ψ(g0) ψ(g0)⁻¹ ψ(1)⁻¹ = 1`, which can never equal `-1`, whereas the untwisted formula of T4b gives
`ψ(g0)²` and is free to be `-1`. -/
private lemma t4_not_isPhaseCoboundary_sT3 : ¬ IsPhaseCoboundary sT3 phiT4 := by
  rintro ⟨ψ, hψ⟩
  have h11 := hψ 1 1
  simp only [phiT4_one_one, map_one, Units.val_one, zpow_one, mul_one,
    mul_inv_cancel_right] at h11
  have hgg := hψ g0 g0
  simp only [phiT4_g0_g0, sT3_g0, Units.val_neg, Units.val_one, zpow_neg, zpow_one, g0_mul_self,
    mul_inv_cancel, one_mul, ← h11, inv_one] at hgg
  exact negCircle_ne_one hgg

/-- T4e (`.mp`, twisted): the capstone converts the failure of T4d into nontriviality of `uT4` for
the antiunitary sign character `sT3` — the formal counterpart of `Θ̂² = -1̂` obstructing a
time-reversal-symmetric injective MPS (p. 278).  Together with T4c this pins the twist down: the
statements of T4c and T4e differ only in `s`, and are contradictory the moment `s` is ignored. -/
private lemma t4_not_isTrivialProjectiveRep_sT3 : ¬ IsTrivialProjectiveRep uT4 sT3 := fun h =>
  t4_not_isPhaseCoboundary_sT3
    ((isTrivialProjectiveRep_iff_isPhaseCoboundary (uT4_isProjectiveRep sT3)).mp h)

/-! ## T5: capstone negative control (the Pauli representation of `Z₂ × Z₂` is nontrivial) -/

/-- The Pauli projective representation of `Z₂ × Z₂` on `ℂ²`: the two generators act by `σ^x`
and `σ^z` (Tasaki §2.1, eq. (2.1.31)).  Since `σ^x` and `σ^z` anticommute, the composition law
closes only up to a sign. -/
private noncomputable def uPauli (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if g.1 = g0 then pauliX else 1) * (if g.2 = g0 then pauliZ else 1)

/-- The phase function of `uPauli`: `-1` exactly when the left factor carries `σ^z` and the right
factor carries `σ^x`, which is the anticommutation `σ^z σ^x = -σ^x σ^z`. -/
private noncomputable def phiPauli (g h : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    Circle :=
  if g.2 = g0 ∧ h.1 = g0 then negCircle else 1

/-- Each `uPauli g` is unitary, being a product of unitaries. -/
private lemma uPauli_mem_unitaryGroup (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    uPauli g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  refine Submonoid.mul_mem _ ?_ ?_
  · by_cases h : g.1 = g0
    · simpa [uPauli, h] using pauliX_mem_unitaryGroup
    · simp [h]
  · by_cases h : g.2 = g0
    · simpa [uPauli, h] using pauliZ_mem_unitaryGroup
    · simp [h]

/-- T5a: `(uPauli, 1, phiPauli)` is a projective representation — the sixteen instances of
eq. (8.3.42), of which four carry the sign `-1`. -/
private lemma uPauli_isProjectiveRep :
    IsProjectiveRep uPauli
      (1 : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* ℤˣ) phiPauli := by
  refine ⟨uPauli_mem_unitaryGroup, by simp [uPauli, g0_ne_one.symm], fun g h => ?_⟩
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := h
  rcases multiplicativeZMod2_eq_one_or_eq_g0 g1 with rfl | rfl <;>
    rcases multiplicativeZMod2_eq_one_or_eq_g0 g2 with rfl | rfl <;>
    rcases multiplicativeZMod2_eq_one_or_eq_g0 h1 with rfl | rfl <;>
    rcases multiplicativeZMod2_eq_one_or_eq_g0 h2 with rfl | rfl <;>
    simp only [uPauli, phiPauli, MonoidHom.one_apply, signConjMatrix_one_apply, Prod.mk_mul_mk,
      g0_mul_self, mul_one, one_mul, if_pos, g0_ne_one.symm, and_self, and_true, and_false,
      if_false, coe_negCircle] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- T5b: the Pauli phase is asymmetric (`φ(a2, b2) = 1` but `φ(b2, a2) = -1`), hence not a
coboundary. -/
private lemma t5_not_isPhaseCoboundary :
    ¬ IsPhaseCoboundary
        (1 : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* ℤˣ) phiPauli :=
  not_isPhaseCoboundary_of_ne (a := a2) (b := b2) (by
    have hab : phiPauli a2 b2 = 1 := if_neg fun h => g0_ne_one h.1.symm
    have hba : phiPauli b2 a2 = negCircle := if_pos ⟨rfl, rfl⟩
    rw [hab, hba]
    exact fun h => negCircle_ne_one h.symm)

/-- T5c: the capstone's `.mp` direction turns the non-coboundary phase into nontriviality, so the
Pauli representation of `Z₂ × Z₂` is a genuinely nontrivial projective representation.  This is
the negative control for the capstone: on the two-dimensional bond space `IsTrivialProjectiveRep`
really can fail, whereas on a one-dimensional space it never does. -/
private lemma t5_not_isTrivialProjectiveRep :
    ¬ IsTrivialProjectiveRep uPauli
      (1 : (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →* ℤˣ) := fun h =>
  t5_not_isPhaseCoboundary
    ((isTrivialProjectiveRep_iff_isPhaseCoboundary uPauli_isProjectiveRep).mp h)

/-! ## T6: entrywise-conjugation API (M1-M9 of #5306 PR-2, design §5a)

Behavioural tests for the extension of `LatticeSystem.Math.ProjectiveRepresentation` with
involutivity, adjoint, unitary-preservation, spectrum, and rank/kernel-finrank lemmas for
`signConj`/`signConjMatrix` (Tasaki §8.3.5 eq. (8.3.40)'s `C_g`). Each test both locks the exact
public name/signature `dev-implement` must produce and exercises the mathematical content, so it
cannot pass by an accidentally vacuous statement. Refs #5306, #4718. -/

/-- M1 (unitary case): `signConj` at `ε = 1` is the identity. -/
private lemma t6_signConj_one_id (z : ℂ) : signConj (1 : ℤˣ) z = z :=
  signConj_one_apply z

/-- M1 (antiunitary case): `signConj` at `ε = -1` is complex conjugation. -/
private lemma t6_signConj_neg_one_conj (z : ℂ) :
    signConj (-1 : ℤˣ) z = starRingEnd ℂ z :=
  signConj_neg_one_apply z

/-- M2 (unitary case): `signConjMatrix` at `ε = 1` is the identity. -/
private lemma t6_signConjMatrix_one_id (M : Matrix (Fin 2) (Fin 2) ℂ) :
    signConjMatrix (1 : ℤˣ) M = M :=
  signConjMatrix_one_apply M

/-- M2 (antiunitary case): `signConjMatrix` at `ε = -1` is entrywise complex conjugation. -/
private lemma t6_signConjMatrix_neg_one_map (M : Matrix (Fin 2) (Fin 2) ℂ) :
    signConjMatrix (-1 : ℤˣ) M = M.map (starRingEnd ℂ) :=
  signConjMatrix_neg_one_apply M

/-- M3: `signConj` is an involution. -/
private lemma t6_signConj_involutive (ε : ℤˣ) (z : ℂ) :
    signConj ε (signConj ε z) = z :=
  signConj_signConj ε z

/-- M3: `signConjMatrix` is an involution. -/
private lemma t6_signConjMatrix_involutive (ε : ℤˣ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    signConjMatrix ε (signConjMatrix ε M) = M :=
  signConjMatrix_signConjMatrix ε M

/-- M4: `signConj` preserves the complex norm. -/
private lemma t6_norm_signConj (ε : ℤˣ) (z : ℂ) : ‖signConj ε z‖ = ‖z‖ :=
  norm_signConj ε z

/-- M5: `signConjMatrix` commutes with the conjugate-transpose. -/
private lemma t6_signConjMatrix_conjTranspose (ε : ℤˣ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (signConjMatrix ε M).conjTranspose = signConjMatrix ε M.conjTranspose :=
  signConjMatrix_conjTranspose ε M

/-- M6: `signConjMatrix` preserves membership in the unitary group; witnessed on the concrete
unitary `σ^x`. -/
private lemma t6_signConjMatrix_pauliX_mem_unitaryGroup (ε : ℤˣ) :
    signConjMatrix ε pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  signConjMatrix_mem_unitaryGroup ε pauliX_mem_unitaryGroup

/-- M7: `signConjMatrix`'s effect on the spectrum is `signConj` applied to eigenvalues. -/
private lemma t6_mem_spectrum_signConjMatrix_iff (ε : ℤˣ) (M : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ (signConjMatrix ε M) ↔ signConj ε μ ∈ spectrum ℂ M :=
  mem_spectrum_signConjMatrix_iff ε M μ

/-- M9: `signConjMatrix` preserves the kernel finrank of `Matrix.mulVecLin`. -/
private lemma t6_finrank_ker_mulVecLin_signConjMatrix (ε : ℤˣ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Module.finrank ℂ (LinearMap.ker (signConjMatrix ε M).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker M.mulVecLin) :=
  finrank_ker_mulVecLin_signConjMatrix ε M

end LatticeSystem.Tests
