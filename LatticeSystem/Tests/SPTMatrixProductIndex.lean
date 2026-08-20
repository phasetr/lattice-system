import LatticeSystem.Quantum.SpinS.SPTMatrixProductIndex
import LatticeSystem.Quantum.SpinS.SpinOneHalfTurn
import LatticeSystem.Quantum.SpinS.SPTSymmetryTransportedMPS
import LatticeSystem.Quantum.SpinS.MPSInvarianceGauge
import LatticeSystem.Quantum.SpinS.MPSTheorem75Defs
import LatticeSystem.Math.ProjectiveRepresentation
import LatticeSystem.Quantum.Pauli

/-!
# Tests: §8.3.5 Theorem 8.7 cocycle chase and Corollary 8.5

Behavioural tests for the layer that proves Tasaki Theorem 8.7 and Corollary 8.5: the signatures
of the transport algebra and of the chase are pinned here, and each capstone is exercised on a
concrete instance so that no statement can be satisfied vacuously.

* **T1** `LatticeSystem.Math.signConjMatrix_signConjMatrix_mul`: the two-sign generalisation of
  `signConjMatrix_signConjMatrix`, checked concretely on a genuinely complex `1×1` matrix (a
  double antiunitary twist cancels).
* **T2** `mpsMix_smul`: mixing by a rescaled matrix rescales the mixed family, checked concretely
  on the Pauli matrix `σ^x`.
* **T3** `symmetryTransportMPS_symmetryTransportMPS` with two independent signs `ε`, `δ`, plus the
  degenerate single-sign instance.
* **T4** `symmetryTransportMPS_conj`: transport of a phased conjugate family, checked concretely
  at the trivial sign/mixing (`ε = 1`, `u = 1`).
* **T5** `pos_of_isInjectiveMPS`: an injective MPS family forces a positive bond dimension,
  instantiated on a genuine bond-`1` witness (`unitA` below).
* **T6** `eq_one_of_unitary_conj_smul`: footnote 52's `c = 1`, the crux of the shorter route via
  Theorem 7.5(ii).
* **T7** `symmetryTransportMPS_mul_of_isProjectiveRep`: the composition law replacing
  (8.3.51)–(8.3.52).
* **T8** `isPhaseCoboundary_of_invariantInjectiveMPS`: the cocycle chase itself.
* **T9** Theorem 8.7: `SymmetricInjectiveMPSExists` is non-vacuously satisfiable, and
  `tasaki_theorem_8_7` discharges it to `Math.IsTrivialProjectiveRep`, on the trivial
  one-dimensional witness (`N = 0`, `D = 1`, `u ≡ 1`, `s ≡ 1`, `φ ≡ 1`).
* **T10** Corollary 8.5, `Z₂ × Z₂` half: at `S = 1/2` the closed forms of `û₁`, `û₃` are the
  textbook `iσ^x`, `iσ^z`, they anticommute, and `tasaki_corollary_8_5_z2z2` applies.
* **T11** the closed forms at `S = 1`: `û₁`, `û₃` and the product `û₁û₃` are the spin-one half
  turns `spinOneHalfTurnS 0`, `spinOneHalfTurnS 2`, `spinOneHalfTurnS 1` of
  `Quantum/SpinS/SpinOneHalfTurn.lean`, the identifications claimed by the module docstring of
  `Quantum/SpinS/SpinSPiRotation.lean`.
* **T12** Corollary 8.5, time-reversal half: at `S = 1/2` the antiunitary square `Θ̂²` is genuinely
  `-1̂`, and `tasaki_corollary_8_5_time_reversal` applies.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1, eqs. (2.1.29)-(2.1.31), pp. 18-19; §8.3.5, Theorem 8.7 and Corollary 8.5,
eqs. (8.3.40)-(8.3.54), footnote 52, pp. 276-280.
Refs #5306, #4718.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Quantum
open LatticeSystem.Math (signConjMatrix signConjMatrix_one_apply)

/-! ## T1: `signConjMatrix_signConjMatrix_mul` -/

/-- T1a: locks the exact public name/signature of the two-sign involution generalisation. -/
private lemma t1_signConjMatrix_signConjMatrix_mul {D : Type*} [Fintype D] [DecidableEq D]
    (ε δ : ℤˣ) (X : Matrix D D ℂ) :
    signConjMatrix ε (signConjMatrix δ X) = signConjMatrix (ε * δ) X :=
  LatticeSystem.Math.signConjMatrix_signConjMatrix_mul ε δ X

/-- T1b: concretely, two antiunitary twists compose to the identity twist (`(-1) * (-1) = 1`) on a
genuinely complex `1 × 1` matrix — the fact that reproves the existing involution
`signConjMatrix_signConjMatrix` from the new lemma, per the design report §2.1. -/
private lemma t1_neg_one_neg_one_cancels :
    signConjMatrix (-1 : ℤˣ) (signConjMatrix (-1 : ℤˣ)
      (Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ))) =
      Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  have hone : (-1 : ℤˣ) * (-1 : ℤˣ) = 1 := by decide
  rw [LatticeSystem.Math.signConjMatrix_signConjMatrix_mul, hone, signConjMatrix_one_apply]

/-! ## T2: `mpsMix_smul` -/

/-- T2a: locks the exact public name/signature of the scalar-homogeneity lemma for `mpsMix`. -/
private lemma t2_mpsMix_smul {D N : ℕ} (z : ℂ) (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (A : MPSMatrices D N) :
    mpsMix (z • u) A = fun σ => z • mpsMix u A σ :=
  mpsMix_smul z u A

/-- A minimal `D = 1, N = 1` MPS family (`A⁰ = 1̂`, `A¹ = 0`), used only to exhibit
`t2_mpsMix_smul` concretely; not reused from `Tests.SPTSymmetryTransportedMPS` since `fixtureA`
there is file-private. -/
private def sampleA : MPSMatrices 1 1 := ![1, 0]

/-- T2b: concretely, mixing `sampleA` by `Complex.I • σ^x` is `Complex.I` times mixing by `σ^x`
plain — the rescaling is not silently absorbed or dropped. -/
private lemma t2_mpsMix_smul_pauliX :
    mpsMix (Complex.I • pauliX) sampleA = fun σ => Complex.I • mpsMix pauliX sampleA σ :=
  mpsMix_smul Complex.I pauliX sampleA

/-! ## T3: the generalised two-sign `symmetryTransportMPS_symmetryTransportMPS` -/

/-- T3: locks the *two-sign* generalisation (§2.2 of the design report): the current production
lemma takes a single shared sign `ε` for both transports, so this call — with independent signs
`ε`, `δ` and the corresponding output `symmetryTransportMPS (ε * δ) (u * signConjMatrix ε v) A`
(not a bare `mpsMix`) — is a genuine arity/shape change, not merely a missing declaration. -/
private lemma t3_symmetryTransportMPS_symmetryTransportMPS_two_signs {D N : ℕ}
    (ε δ : ℤˣ) (u v : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (A : MPSMatrices D N) :
    symmetryTransportMPS ε u (symmetryTransportMPS δ v A) =
      symmetryTransportMPS (ε * δ) (u * signConjMatrix ε v) A :=
  symmetryTransportMPS_symmetryTransportMPS ε δ u v A

/-- T3 (sanity, trivial instance): at `ε = δ = 1`, `u = v = 1`, the generalised identity
degenerates to the original single-sign statement (`1 * signConjMatrix 1 1 = 1`), so this is a
regression guard that the generalisation still recovers the trivial case. -/
private lemma t3_trivial_instance {D N : ℕ} (A : MPSMatrices D N) :
    symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        (symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) A) =
      symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) A := by
  rw [symmetryTransportMPS_symmetryTransportMPS, signConjMatrix_one_apply, mul_one, mul_one]

/-! ## T4: `symmetryTransportMPS_conj` -/

/-- T4a: locks the exact public name/signature of the gauge-transport lemma (§0 step 2 / §2.2 of
the design report), the one-screen computation that `R_g` moves through a phased conjugate
family. -/
private lemma t4_symmetryTransportMPS_conj {D N : ℕ} (ε : ℤˣ)
    (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (z : Circle) (V : Matrix (Fin D) (Fin D) ℂ)
    (A : MPSMatrices D N) :
    symmetryTransportMPS ε u (fun σ => (z : ℂ) • (V.conjTranspose * A σ * V)) =
      fun σ => ((z ^ (ε : ℤ) : Circle) : ℂ) •
        ((signConjMatrix ε V).conjTranspose * symmetryTransportMPS ε u A σ *
          signConjMatrix ε V) :=
  symmetryTransportMPS_conj ε u z V A

/-- Shared helper: transporting by the trivial sign and the identity mixing matrix is the
identity on MPS families. Reproved here (not imported from `Tests.SPTSymmetryTransportedMPS`,
whose analogous `t1_symmetryTransportMPS_one_one` is file-private) because both T4b and T9 need
it. -/
private lemma symmetryTransportMPS_one_one {D N : ℕ} (A : MPSMatrices D N) :
    symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) A = A := by
  unfold symmetryTransportMPS mpsConjugate
  have hconj : (fun σ => signConjMatrix (1 : ℤˣ) (A σ)) = A :=
    funext fun σ => signConjMatrix_one_apply (A σ)
  rw [hconj, mpsMix_one]

/-- T4b: concretely, at the trivial sign and mixing (`ε = 1`, `u = 1`), the transport of a phased
conjugate family is just the phased conjugate family itself (`z ^ (1 : ℤ) = z`,
`signConjMatrix 1 V = V`, `symmetryTransportMPS 1 1 A = A`). -/
private lemma t4_symmetryTransportMPS_conj_trivial {D N : ℕ} (z : Circle)
    (V : Matrix (Fin D) (Fin D) ℂ) (A : MPSMatrices D N) :
    symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
        (fun σ => (z : ℂ) • (V.conjTranspose * A σ * V)) =
      fun σ => (z : ℂ) • (V.conjTranspose * A σ * V) := by
  have h := symmetryTransportMPS_conj (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) z V A
  funext σ
  rw [congrFun h σ, symmetryTransportMPS_one_one, signConjMatrix_one_apply, Units.val_one,
    zpow_one]

/-! ## T5: `pos_of_isInjectiveMPS` -/

/-- T5a: locks the exact public name/signature of the `D = 0` exclusion (§1 of the design report:
`IsInjectiveMPS` already forces `D ≠ 0`, so `SymmetricInjectiveMPSExists` needs no separate
`0 < D` conjunct). -/
private lemma t5_pos_of_isInjectiveMPS {D N : ℕ} {A : MPSMatrices D N} {lam : ℝ}
    (hA : IsInjectiveMPS A lam) : 0 < D :=
  pos_of_isInjectiveMPS hA

/-- The simplest nonzero MPS family: `D = 1`, `N = 0` (a single spin state), `A⁰ = 1̂`. Distinct
from `Tests.SPTSymmetryTransportedMPS`'s (file-private) `fixtureA`, which has `N = 1`. -/
private def unitA : MPSMatrices 1 0 := fun _ => 1

/-- Every length-`ℓ` ordered product of `unitA` is `1`: `Fin (0 + 1) = Fin 1` is a subsingleton,
so every word is the all-`0` word, and `unitA 0 = 1`. -/
private lemma unitA_orderedProd_replicate_zero (ℓ : ℕ) :
    orderedProd unitA (List.replicate ℓ 0) = 1 := by
  induction ℓ with
  | zero => rfl
  | succ n ih =>
      change unitA 0 * orderedProd unitA (List.replicate n 0) = 1
      rw [show unitA 0 = (1 : Matrix (Fin 1) (Fin 1) ℂ) from rfl, ih, one_mul]

/-- `unitA` is normalized with `λ = 1`. -/
private lemma unitA_isMPSNormalized : IsMPSNormalized unitA (1 : ℝ) := by
  refine ⟨zero_lt_one, ?_⟩
  rw [Fin.sum_univ_one]
  simp [unitA]

/-- `unitA`'s ordered products span the (one-dimensional) `1 × 1` matrix space at every length. -/
private lemma unitA_mpsProductsSpanAt (ℓ : ℕ) : mpsProductsSpanAt unitA ℓ := by
  unfold mpsProductsSpanAt
  have hone : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈
      Submodule.span ℂ {M : Matrix (Fin 1) (Fin 1) ℂ |
        ∃ σs : List (Fin 1), σs.length = ℓ ∧ M = orderedProd unitA σs} :=
    Submodule.subset_span ⟨List.replicate ℓ 0, List.length_replicate,
      (unitA_orderedProd_replicate_zero ℓ).symm⟩
  refine Submodule.eq_top_iff'.mpr fun M => ?_
  have hM : M = (M 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [hM]
  exact Submodule.smul_mem _ _ hone

/-- `unitA`'s transfer matrix is the `1 × 1` identity. -/
private lemma unitA_mpsTransferMatrix_eq_one :
    mpsTransferMatrix unitA = (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  ext p q
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  fin_cases p1; fin_cases p2; fin_cases q1; fin_cases q2
  simp [mpsTransferMatrix, unitA]

/-- `unitA` satisfies Theorem 7.5(iii): `λ = 1` is the unique, simple transfer eigenvalue. -/
private lemma unitA_hasPrimitiveTransferSpectrum :
    HasPrimitiveTransferSpectrum unitA (1 : ℝ) := by
  unfold HasPrimitiveTransferSpectrum
  rw [unitA_mpsTransferMatrix_eq_one]
  haveI : Nontrivial (Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :=
    ⟨0, 1, by
      intro h
      have h00 := congrFun (congrFun h (0, 0)) (0, 0)
      simp at h00⟩
  have hspec : spectrum ℂ (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) = {1} :=
    spectrum.one_eq
  refine ⟨by rw [hspec]; rfl, ?_, fun μ hμ hne => absurd (by
    rwa [hspec, Set.mem_singleton_iff] at hμ) hne⟩
  have hzero : (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ).mulVecLin -
      ((1 : ℝ) : ℂ) • LinearMap.id = 0 := by
    ext v i
    simp [Matrix.mulVecLin_one]
  rw [hzero, LinearMap.ker_zero, finrank_top]
  simp

/-- `unitA` is genuinely injective (Tasaki Theorem 7.5), the non-vacuity witness for `t5b` and for
the capstone T9 below. -/
private lemma unitA_isInjectiveMPS : IsInjectiveMPS unitA (1 : ℝ) :=
  ⟨unitA_isMPSNormalized, ⟨0, unitA_mpsProductsSpanAt 0⟩,
    ⟨0, fun ℓ _ => unitA_mpsProductsSpanAt ℓ⟩, unitA_hasPrimitiveTransferSpectrum⟩

/-- T5b: non-vacuity — `pos_of_isInjectiveMPS` applied to a genuine witness returns `0 < 1`, not
just a vacuously-true universally-quantified statement. -/
private lemma t5b_pos_of_isInjectiveMPS_unitA : (0 : ℕ) < 1 :=
  pos_of_isInjectiveMPS unitA_isInjectiveMPS

/-! ## T6: `eq_one_of_unitary_conj_smul` (footnote 52's `c = 1`) -/

/-- T6: locks the exact public name/signature of the design report's shortened footnote-52 route
(word induction + `Theorem 7.5(ii)` + `LinearMap.ext_on`, §0 "`c = 1`" and §2.4). -/
private lemma t6_eq_one_of_unitary_conj_smul {D N : ℕ} {A : MPSMatrices D N} {lam : ℝ}
    (hA : IsInjectiveMPS A lam) {T : Matrix (Fin D) (Fin D) ℂ}
    (hT : T ∈ Matrix.unitaryGroup (Fin D) ℂ) {c : Circle}
    (h : ∀ σ, T.conjTranspose * A σ * T = (c : ℂ) • A σ) : c = 1 :=
  eq_one_of_unitary_conj_smul hA hT h

/-! ## T7: `symmetryTransportMPS_mul_of_isProjectiveRep` (the composition law, §0 step 1) -/

/-- T7: locks the exact public name/signature of the composition law that replaces the book's
(8.3.51)+(8.3.52): the transport of a projective representation composes up to the phase `φ g h`,
directly from `mpsMix ∘ mpsMix`, `s` being a group hom, and eq. (8.3.42). -/
private lemma t7_symmetryTransportMPS_mul_of_isProjectiveRep {G : Type*} [Group G] {N : ℕ}
    {u : G → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {s : G →* ℤˣ} {φ : G → G → Circle}
    (hrep : LatticeSystem.Math.IsProjectiveRep u s φ) (g h : G) {D : ℕ} (A : MPSMatrices D N) :
    symmetryTransportMPS (s g) (u g) (symmetryTransportMPS (s h) (u h) A) =
      fun σ => (φ g h : ℂ) • symmetryTransportMPS (s (g * h)) (u (g * h)) A σ :=
  symmetryTransportMPS_mul_of_isProjectiveRep hrep g h A

/-! ## T8: `isPhaseCoboundary_of_invariantInjectiveMPS` (the cocycle chase itself) -/

/-- T8: locks the exact public name/signature of the forward cocycle chase (§0 steps 1-4 of the
design report): a projective representation whose transported family agrees with the original
one up to a phase, on an injective MPS, has a phase function that is a coboundary — this is the
substance behind Theorem 8.7. -/
private lemma t8_isPhaseCoboundary_of_invariantInjectiveMPS {G : Type*} [Group G] {N : ℕ}
    {u : G → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {s : G →* ℤˣ} {φ : G → G → Circle}
    {D : ℕ} {A : MPSMatrices D N} {lam : ℝ}
    (hrep : LatticeSystem.Math.IsProjectiveRep u s φ) (hA : IsInjectiveMPS A lam)
    (hinv : ∀ g, ∃ η : ℕ → Circle,
      GeneratesPhasedMPS A (symmetryTransportMPS (s g) (u g) A) η) :
    LatticeSystem.Math.IsPhaseCoboundary s φ :=
  isPhaseCoboundary_of_invariantInjectiveMPS hrep hA hinv

/-! ## T9: the capstone — `SymmetricInjectiveMPSExists` non-vacuity and `tasaki_theorem_8_7` -/

/-- The trivial one-dimensional on-site symmetry action: `G = Multiplicative (ZMod 2)`, `N = 0`
(single-spin space `Fin 1`), `u ≡ 1̂`. -/
private def uTrivial (_ : Multiplicative (ZMod 2)) : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- `(uTrivial, 1, 1)` is a projective representation: every clause of eq. (8.3.41)-(8.3.42)
collapses to `1 * 1 = 1 • 1` at the trivial sign character. -/
private lemma uTrivial_isProjectiveRep :
    LatticeSystem.Math.IsProjectiveRep uTrivial
      (1 : Multiplicative (ZMod 2) →* ℤˣ)
      (1 : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Circle) :=
  ⟨fun _ => Submonoid.one_mem _, rfl,
    fun _ _ => by simp [uTrivial, signConjMatrix, LatticeSystem.Math.signConj]⟩

/-- `symmetryTransportMPS (1 g) (uTrivial g) unitA = unitA` for every `g`, since the trivial sign
character has `1 g = 1`, `uTrivial g = 1`, and the trivial sign/mixing transport is the identity
(`symmetryTransportMPS_one_one`, defined for T4 above). -/
private lemma symmetryTransportMPS_uTrivial_unitA (g : Multiplicative (ZMod 2)) :
    symmetryTransportMPS ((1 : Multiplicative (ZMod 2) →* ℤˣ) g) (uTrivial g) unitA = unitA := by
  change symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin 1) (Fin 1) ℂ) unitA = unitA
  exact symmetryTransportMPS_one_one unitA

/-- T9a: `SymmetricInjectiveMPSExists uTrivial 1` is genuinely satisfiable — the design report's
non-vacuity requirement (§5, item 3) — witnessed by `unitA` and the identically-`1` phase
family. -/
private lemma t9a_symmetricInjectiveMPSExists_nonvacuous :
    SymmetricInjectiveMPSExists uTrivial (1 : Multiplicative (ZMod 2) →* ℤˣ) :=
  ⟨1, unitA, 1, unitA_isInjectiveMPS, fun g =>
    ⟨fun _ => 1, fun L ss => by rw [symmetryTransportMPS_uTrivial_unitA]; simp⟩⟩

/-- T9b: the capstone — `tasaki_theorem_8_7`, now a *proved theorem* rather than an axiom, turns
the non-vacuous `SymmetricInjectiveMPSExists` witness of T9a into `Math.IsTrivialProjectiveRep`. -/
private lemma t9b_tasaki_theorem_8_7_nonvacuous :
    LatticeSystem.Math.IsTrivialProjectiveRep uTrivial
      (1 : Multiplicative (ZMod 2) →* ℤˣ) :=
  tasaki_theorem_8_7 uTrivial_isProjectiveRep t9a_symmetricInjectiveMPSExists_nonvacuous

/-! ## T10: the closed-form `π` rotations and Corollary 8.5, `Z₂ × Z₂` half -/

/-- T10a: at `S = 1/2` (`N = 1`) the closed form of `û₁ = exp(iπŜ^{(1)}) = exp(iπσ^x/2)` is
`iσ^x`, the textbook value — a concrete check that the `i^{2S}` normalisation of
`spinSPiRotation1` is the right one. -/
private lemma t10a_spinSPiRotation1_spin_half :
    spinSPiRotation1 1 = Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation1, spinSFlip, pauliX, Fin.rev]

/-- T10b: at `S = 1/2` the closed form of `û₃ = exp(iπŜ^{(3)}) = exp(iπσ^z/2)` is `iσ^z`. -/
private lemma t10b_spinSPiRotation3_spin_half :
    spinSPiRotation3 1 = Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, pauliZ, Matrix.diagonal]

/-- T10c: the `π` rotations genuinely anticommute at `S = 1/2`, so the `Z₂ × Z₂` hypothesis of
Corollary 8.5 is not vacuous. -/
private lemma t10c_spin_half_anticommute :
    spinSPiRotation3 1 * spinSPiRotation1 1 = -(spinSPiRotation1 1 * spinSPiRotation3 1) :=
  spinSPiRotation3_mul_spinSPiRotation1_of_odd odd_one

/-- T10d: the capstone `tasaki_corollary_8_5_z2z2`, now an unconditional theorem, applies at
`S = 1/2`: no `Z₂ × Z₂`-invariant injective matrix product state of spin-`1/2` chains exists. -/
private lemma t10d_tasaki_corollary_8_5_z2z2_spin_half :
    ¬ SymmetricInjectiveMPSExists (z2z2SpinRep 1)
      (1 : Multiplicative (ZMod 2 × ZMod 2) →* ℤˣ) :=
  tasaki_corollary_8_5_z2z2 1 odd_one

/-! ## T11: the `S = 1` closed forms agree with the spin-one half turns -/

/-- T11a: at `S = 1` (`N = 2`) the closed form of `û₁` is the spin-one half turn
`spinOneHalfTurnS 0 = 1̂ - 2(Ŝ^{(1)})²`, the identification claimed by the module docstring of
`Quantum/SpinS/SpinSPiRotation.lean` (`i^{2S} = -1` times the basis reversal). -/
private lemma t11a_spinSPiRotation1_spin_one :
    spinSPiRotation1 2 = spinOneHalfTurnS 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation1, spinSFlip, spinOneHalfTurnS, spinOnePiRot1, Fin.rev, Complex.I_sq]

/-- T11b: at `S = 1` the closed form of `û₃` is `spinOneHalfTurnS 2 = diag(-1, 1, -1)`. -/
private lemma t11b_spinSPiRotation3_spin_one :
    spinSPiRotation3 2 = spinOneHalfTurnS 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, spinOneHalfTurnS, spinOnePiRot3, Matrix.diagonal,
      Complex.I_sq]

/-- T11c: at `S = 1` the product `û₁û₃` — the matrix part of the time reversal used by
`timeReversalSpinRep` — is the remaining half turn `spinOneHalfTurnS 1`, i.e. the book's `û₂`. -/
private lemma t11c_spinSPiRotation_product_spin_one :
    spinSPiRotation1 2 * spinSPiRotation3 2 = spinOneHalfTurnS 1 := by
  rw [t11a_spinSPiRotation1_spin_one, t11b_spinSPiRotation3_spin_one, spinOneHalfTurnS_one_eq]

/-! ## T12: Corollary 8.5, time-reversal half -/

/-- T12a: the antiunitary square of the time reversal is genuinely `-1̂` at `S = 1/2`, so the
hypothesis feeding `tasaki_corollary_8_5_time_reversal` is not vacuous. -/
private lemma t12a_time_reversal_square_spin_half :
    (spinSPiRotation1 1 * spinSPiRotation3 1) * (spinSPiRotation1 1 * spinSPiRotation3 1) =
      -1 :=
  spinSPiRotation1_mul_spinSPiRotation3_mul_self_of_odd odd_one

/-- T12b: the capstone `tasaki_corollary_8_5_time_reversal` applies at `S = 1/2`: no
time-reversally invariant injective matrix product state of spin-`1/2` chains exists. -/
private lemma t12b_tasaki_corollary_8_5_time_reversal_spin_half :
    ¬ SymmetricInjectiveMPSExists (timeReversalSpinRep 1) (MonoidHom.id ℤˣ) :=
  tasaki_corollary_8_5_time_reversal 1 odd_one

end LatticeSystem.Tests
