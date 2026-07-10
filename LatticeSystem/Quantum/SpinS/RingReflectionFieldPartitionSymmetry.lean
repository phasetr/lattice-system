/-
Symmetries of the physical field partition function `Z_β(h)`
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: symmetrisation stage PR7d-i;
(4.1.49)–(4.1.52), pp. 85–86; chessboard estimate Lemma 4.5, pp. 87–88; FILS, Comm. Math. Phys.
62 (1978) 1–34).

Viewing the physical field partition function `Z_β(h) = ringFieldPartitionRe n N β h =
Re Tr exp(−β·Ĥ_field(h))` as a function of the per-site field `h : Fin (2n) → ℝ`, this file records
the three structural properties consumed by the `−log Z` symmetrisation step that turns PR7c's one
reflection step into the uniform-field bound `Z_β(h) ≤ Z_β(0)` (Tasaki (4.1.49)/(4.1.52)) via the
classical cyclic averaging inequality `reflectionPositivity_averaging` (Lemma 4.5):

* **A. Translation invariance** `Z_β(h) = Z_β(h ∘ finRotate)`: the physical ring Heisenberg
  Hamiltonian is translation invariant (`chainTranslation_conj_heisenbergHamiltonianS`) and the ring
  translation reindexes the Zeeman field term (`chainTranslation_conj_onSiteS`), so conjugation by
  the (unitary) ring translation carries `Ĥ_field(h ∘ finRotate)` to `Ĥ_field(h)` and the trace is
  invariant.  Assembly of existing assets; no new unitary.
* **B. Spin-flip invariance** `Z_β(−h) = Z_β(h)`: a global axis-2 `π`-rotation `fullGauge`
  (`AxisTwoPiRotS.U` on *all* sites) preserves the Heisenberg dot product
  (`(−Ŝ¹)(−Ŝ¹)+(Ŝ²)(Ŝ²)+(−Ŝ³)(−Ŝ³)`) hence the field-free Hamiltonian, while flipping the field
  term `Σ_z h_z Ŝ³_z ↦ Σ_z (−h_z) Ŝ³_z`; the trace is invariant.
* **C. Strict positivity** `0 < Z_β(h)`: the field Hamiltonian is Hermitian, so `exp(−β·Ĥ_field(h))`
  is positive definite (`Matrix.posDef_exp_of_isHermitian`) and its trace is strictly positive
  (`Matrix.PosDef.trace_pos`).  This is the genuine domain condition of the `−log Z` step.

Both A and B are needed for the cyclicity hypothesis of Lemma 4.5, because the staggered relabel
`P h z = (−1)^z h z` (PR7d-ii) has period 2, so a single one-step shift produces a global sign.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionFieldPartition
import LatticeSystem.Quantum.SpinS.RingTranslationGibbs
import LatticeSystem.Quantum.SpinS.StaggeredOrderSusceptibility
import LatticeSystem.Math.MatrixAnalysis.HermitianSum
import LatticeSystem.Math.PosSemidef.ExpPosDef

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {n N : ℕ}

/-! ## A. Translation invariance of `Z_β` -/

/-- **Ring-translation conjugation of the physical field Hamiltonian.**  Conjugating the field
Hamiltonian of the reindexed field `h ∘ finRotate` by the ring translation `T` returns the field
Hamiltonian of `h`: the field-free part is fixed (`chainTranslation_conj_heisenbergHamiltonianS`)
and the Zeeman field term is reindexed one site forward (`chainTranslation_conj_onSiteS`), which the
`finRotate` bijection undoes (`Equiv.sum_comp`).  This is the operator identity behind the
translation invariance of `Z_β` (Tasaki §4.1, cyclicity source (4.1.60), p. 88). -/
theorem chainTranslation_conj_ringFieldHamiltonian (n N : ℕ) (h : Fin (2 * n) → ℝ) :
    (chainTranslationOp (2 * n) N).conjTranspose
        * ringFieldHamiltonian n N (h ∘ finRotate (2 * n)) * chainTranslationOp (2 * n) N
      = ringFieldHamiltonian n N h := by
  have hfield : (chainTranslationOp (2 * n) N).conjTranspose
        * (∑ z, ((h ∘ finRotate (2 * n)) z : ℂ) • onSiteS z (spinSOp3 N))
        * chainTranslationOp (2 * n) N
      = ∑ z, (h z : ℂ) • onSiteS z (spinSOp3 N) := by
    rw [Matrix.mul_sum, Finset.sum_mul]
    refine (Finset.sum_congr rfl (fun z _ => ?_)).trans
      (Equiv.sum_comp (finRotate (2 * n)) (fun w => (h w : ℂ) • onSiteS w (spinSOp3 N)))
    rw [mul_smul_comm, smul_mul_assoc, chainTranslation_conj_onSiteS, Function.comp_apply]
  rw [ringFieldHamiltonian, ringFieldHamiltonian, Matrix.mul_add, Matrix.add_mul,
    chainTranslation_conj_heisenbergHamiltonianS, hfield]

/-- **Translation invariance of the field partition function** `Z_β(h) = Z_β(h ∘ finRotate)`
(Tasaki §4.1, cyclicity source (4.1.60), p. 88).  The ring translation is unitary
(`chainTranslationUnit`), so `exp(−β·Ĥ_field(h))` conjugates to `exp(−β·Ĥ_field(h ∘ finRotate))`
(`Matrix.exp_units_conj` + `chainTranslation_conj_ringFieldHamiltonian`) and the trace is invariant
(`trace_chainTranslation_conj`).  This supplies the translation part of the cyclicity hypothesis of
the chessboard estimate (Lemma 4.5). -/
theorem ringFieldPartitionRe_translate (n N : ℕ) (β : ℝ) (h : Fin (2 * n) → ℝ) :
    ringFieldPartitionRe n N β h = ringFieldPartitionRe n N β (h ∘ finRotate (2 * n)) := by
  rw [ringFieldPartitionRe, ringFieldPartitionRe, thermalPartitionFnS, thermalPartitionFnS,
    thermalGibbsOpS, thermalGibbsOpS]
  have hconj := Matrix.exp_units_conj (chainTranslationUnit (2 * n) N)
    ((-(β : ℂ)) • ringFieldHamiltonian n N (h ∘ finRotate (2 * n)))
  rw [chainTranslationUnit_val, chainTranslationUnit_inv, mul_smul_comm, smul_mul_assoc,
    chainTranslation_conj_ringFieldHamiltonian] at hconj
  rw [hconj, trace_chainTranslation_conj]

/-! ## B. Spin-flip invariance of `Z_β` -/

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- **The global axis-2 gauge unitary** `⊗_i U` on every site of the ring (the `univ` analogue of
the right-half `rightGauge`), used to realise the global spin flip. -/
noncomputable def fullGauge : ManyBodyOpS (Fin (2 * n)) N :=
  manyBodyTensorS (fun _ : Fin (2 * n) => G.U)

/-- **The inverse global axis-2 gauge unitary** `⊗_i U⁻¹`. -/
noncomputable def fullGaugeInv : ManyBodyOpS (Fin (2 * n)) N :=
  manyBodyTensorS (fun _ : Fin (2 * n) => G.Uinv)

/-- The global gauge is a right inverse of its inverse: `fullGauge · fullGaugeInv = 1`. -/
theorem fullGauge_mul_fullGaugeInv : G.fullGauge n * G.fullGaugeInv n = 1 := by
  rw [fullGauge, fullGaugeInv, manyBodyTensorS_mul]
  simp only [G.U_mul_Uinv]
  exact manyBodyTensorS_one

/-- The global gauge is a left inverse of its inverse: `fullGaugeInv · fullGauge = 1`. -/
theorem fullGaugeInv_mul_fullGauge : G.fullGaugeInv n * G.fullGauge n = 1 := by
  rw [fullGauge, fullGaugeInv, manyBodyTensorS_mul]
  simp only [G.Uinv_mul_U]
  exact manyBodyTensorS_one

/-- **Conjugation of a single-site operator by the global gauge**: `fullGauge · onSiteS z A ·
fullGaugeInv = onSiteS z (U·A·U⁻¹)`. -/
theorem fullGauge_conj_onSiteS (z : Fin (2 * n)) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    G.fullGauge n * onSiteS z A * G.fullGaugeInv n = onSiteS z (G.U * A * G.Uinv) := by
  rw [fullGauge, fullGaugeInv, manyBodyTensorS_conj_onSiteS G.U_mul_Uinv]

/-- Conjugation by the global gauge distributes over products (`fullGauge` is a unit). -/
theorem fullGauge_conj_mul (P Q : ManyBodyOpS (Fin (2 * n)) N) :
    G.fullGauge n * (P * Q) * G.fullGaugeInv n
      = (G.fullGauge n * P * G.fullGaugeInv n) * (G.fullGauge n * Q * G.fullGaugeInv n) := by
  rw [show (G.fullGauge n * P * G.fullGaugeInv n) * (G.fullGauge n * Q * G.fullGaugeInv n)
      = G.fullGauge n * P * (G.fullGaugeInv n * G.fullGauge n) * (Q * G.fullGaugeInv n) by
    simp only [mul_assoc], G.fullGaugeInv_mul_fullGauge n]
  simp only [mul_one, mul_assoc]

/-- **The global axis-2 gauge preserves the Heisenberg dot product** `Ŝ_x · Ŝ_y`.  The conjugation
signs `U Ŝ^a U⁻¹ = (−Ŝ¹, Ŝ², −Ŝ³)` cancel in each squared component:
`(−Ŝ¹)(−Ŝ¹)+(Ŝ²)(Ŝ²)+(−Ŝ³)(−Ŝ³) = Ŝ_x · Ŝ_y` (Tasaki §4.1, spin-rotation invariance of the
exchange coupling; cf. `AxisSwapGaugeEquiv.tensor_conj_spinSDotXXZ`). -/
theorem fullGauge_conj_spinSDot (x y : Fin (2 * n)) :
    G.fullGauge n * spinSDot x y N * G.fullGaugeInv n = spinSDot x y N := by
  rw [spinSDot_def]
  simp only [Matrix.mul_add, Matrix.add_mul, G.fullGauge_conj_mul, G.fullGauge_conj_onSiteS,
    G.conj_spinSOp1, G.conj_spinSOp2, G.conj_spinSOp3, onSiteS_neg, neg_mul_neg]

/-- **The global axis-2 gauge preserves any Heisenberg Hamiltonian** `Σ_{x,y} J_{xy} Ŝ_x · Ŝ_y`,
because it preserves every bond dot product (`fullGauge_conj_spinSDot`). -/
theorem fullGauge_conj_heisenbergHamiltonianS (J : Fin (2 * n) → Fin (2 * n) → ℂ) :
    G.fullGauge n * heisenbergHamiltonianS J N * G.fullGaugeInv n = heisenbergHamiltonianS J N := by
  rw [heisenbergHamiltonianS, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, G.fullGauge_conj_spinSDot]

/-- **The global axis-2 gauge flips the single-site `Ŝ^{(3)}`**: `fullGauge · onSiteS z Ŝ³ ·
fullGaugeInv = −onSiteS z Ŝ³` (the DLS/Marshall sign `U Ŝ³ U⁻¹ = −Ŝ³`). -/
theorem fullGauge_conj_onSiteS_spinSOp3 (z : Fin (2 * n)) :
    G.fullGauge n * onSiteS z (spinSOp3 N) * G.fullGaugeInv n = - onSiteS z (spinSOp3 N) := by
  rw [G.fullGauge_conj_onSiteS, G.conj_spinSOp3, onSiteS_neg]

/-- **Global gauge conjugation flips the field of the physical field Hamiltonian**:
`fullGauge · Ĥ_field(h) · fullGaugeInv = Ĥ_field(−h)`.  The field-free part is preserved
(`fullGauge_conj_heisenbergHamiltonianS`) and every Zeeman term flips sign
(`fullGauge_conj_onSiteS_spinSOp3`), realising `Σ_z h_z Ŝ³_z ↦ Σ_z (−h_z) Ŝ³_z`
(Tasaki §4.1, spin-flip symmetry of the field bound, p. 86). -/
theorem fullGauge_conj_ringFieldHamiltonian (h : Fin (2 * n) → ℝ) :
    G.fullGauge n * ringFieldHamiltonian n N h * G.fullGaugeInv n
      = ringFieldHamiltonian n N (fun z => - h z) := by
  rw [ringFieldHamiltonian, ringFieldHamiltonian, Matrix.mul_add, Matrix.add_mul,
    G.fullGauge_conj_heisenbergHamiltonianS]
  congr 1
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, G.fullGauge_conj_onSiteS_spinSOp3]
  simp only [smul_neg, Complex.ofReal_neg, neg_smul]

/-- The global gauge unitary packaged as a unit of the operator ring. -/
noncomputable def fullGaugeUnit : (ManyBodyOpS (Fin (2 * n)) N)ˣ where
  val := G.fullGauge n
  inv := G.fullGaugeInv n
  val_inv := G.fullGauge_mul_fullGaugeInv n
  inv_val := G.fullGaugeInv_mul_fullGauge n

/-- The underlying operator of `fullGaugeUnit` is `fullGauge`. -/
@[simp] theorem fullGaugeUnit_val :
    (G.fullGaugeUnit n : ManyBodyOpS (Fin (2 * n)) N) = G.fullGauge n := rfl

/-- The underlying operator of `(fullGaugeUnit)⁻¹` is `fullGaugeInv`. -/
@[simp] theorem fullGaugeUnit_inv :
    (((G.fullGaugeUnit n)⁻¹ : (ManyBodyOpS (Fin (2 * n)) N)ˣ) : ManyBodyOpS (Fin (2 * n)) N)
      = G.fullGaugeInv n := rfl

/-- The trace is invariant under conjugation by the global gauge (a similarity transform). -/
theorem trace_fullGauge_conj (X : ManyBodyOpS (Fin (2 * n)) N) :
    (G.fullGauge n * X * G.fullGaugeInv n).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, G.fullGaugeInv_mul_fullGauge n, Matrix.one_mul]

end AxisTwoPiRotS

/-- **Spin-flip invariance of the physical field partition function** `Z_β(−h) = Z_β(h)`
(Tasaki §4.1, spin-flip symmetry of the field bound, p. 86).  The global axis-2 gauge is unitary,
so `exp(−β·Ĥ_field(−h))` conjugates to `exp(−β·Ĥ_field(h))`
(`Matrix.exp_units_conj` + `fullGauge_conj_ringFieldHamiltonian`) and the trace is invariant
(`trace_fullGauge_conj`).  Together with translation invariance this supplies the cyclicity
hypothesis of the chessboard estimate (Lemma 4.5) for the period-2 staggered relabel. -/
theorem ringFieldPartitionRe_neg (G : AxisTwoPiRotS N) (n : ℕ) (β : ℝ) (h : Fin (2 * n) → ℝ) :
    ringFieldPartitionRe n N β (fun z => - h z) = ringFieldPartitionRe n N β h := by
  rw [ringFieldPartitionRe, ringFieldPartitionRe, thermalPartitionFnS, thermalPartitionFnS,
    thermalGibbsOpS, thermalGibbsOpS]
  have hconj := Matrix.exp_units_conj (G.fullGaugeUnit n)
    ((-(β : ℂ)) • ringFieldHamiltonian n N h)
  rw [AxisTwoPiRotS.fullGaugeUnit_val, AxisTwoPiRotS.fullGaugeUnit_inv, mul_smul_comm,
    smul_mul_assoc, G.fullGauge_conj_ringFieldHamiltonian] at hconj
  rw [hconj, G.trace_fullGauge_conj]

/-! ## C. Strict positivity of `Z_β` -/

/-- **The physical field Hamiltonian is Hermitian.**  The field-free part is Hermitian for the real
ring coupling (`heisenbergHamiltonianS_isHermitian_of_real`, `ringCoupling_self_star`) and each
Zeeman term `(h z)·Ŝ³_z` is Hermitian (real coefficient times the Hermitian `onSiteS z Ŝ³`), so the
sum is Hermitian.  This is the hypothesis of the strict positivity `0 < Z_β(h)`. -/
theorem ringFieldHamiltonian_isHermitian (n N : ℕ) (h : Fin (2 * n) → ℝ) :
    (ringFieldHamiltonian n N h).IsHermitian := by
  rw [ringFieldHamiltonian]
  refine (heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star (2 * n)) N).add ?_
  refine Matrix.isHermitian_sum _ (fun z _ => ?_)
  refine (onSiteS_isHermitian z (spinSOp3_isHermitian N)).smul ?_
  rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

/-- **Strict positivity of the physical field partition function** `0 < Z_β(h)`
(Tasaki §4.1, positivity of the canonical partition function underlying the `−log Z` step).  The
field Hamiltonian is Hermitian (`ringFieldHamiltonian_isHermitian`), so `exp(−β·Ĥ_field(h))` is
positive definite (`Matrix.posDef_exp_of_isHermitian` applied to the self-adjoint `−β·Ĥ_field`) and
its trace is strictly positive (`Matrix.PosDef.trace_pos`); the real part is therefore positive.
This is the genuine domain condition of the `−log Z` symmetrisation (Lemma 4.5). -/
theorem ringFieldPartitionRe_pos (n N : ℕ) (β : ℝ) (h : Fin (2 * n) → ℝ) :
    0 < ringFieldPartitionRe n N β h := by
  have hHerm : ((-(β : ℂ)) • ringFieldHamiltonian n N h).IsHermitian :=
    (ringFieldHamiltonian_isHermitian n N h).smul
      (by rw [isSelfAdjoint_iff, star_neg, Complex.star_def, Complex.conj_ofReal])
  have hpos : (0 : ℂ) < (thermalPartitionFnS β (ringFieldHamiltonian n N h)) := by
    rw [thermalPartitionFnS, thermalGibbsOpS]
    exact (Matrix.posDef_exp_of_isHermitian hHerm).trace_pos
  have := (RCLike.pos_iff (K := ℂ)).mp hpos |>.1
  simpa [ringFieldPartitionRe] using this

end LatticeSystem.Quantum
