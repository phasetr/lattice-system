---
layout: page
title: "Legacy catalogue: Basis states and raising/lowering for S = 1 (Tasaki §2.1)"
permalink: /formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1/
---

# Legacy catalogue: Basis states and raising/lowering for S = 1 (Tasaki §2.1)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:425:466 -->
### Basis states and raising/lowering for S = 1 (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.2), (2.1.3), (2.1.6), p. 14 for the `S = 1`
case (`σ ∈ {-1, 0, +1}`).

| Lean name | Statement | File |
|---|---|---|
| `spinOnePlus/Zero/Minus` | column vectors `|ψ^{+1}⟩, |ψ^{0}⟩, |ψ^{-1}⟩` | `Quantum/SpinOneBasis.lean` |
| `spinOneOp3_mulVec_spinOnePlus/Zero/Minus` | `Ŝ^(3)` eigenvalue equations (Tasaki (2.1.2), S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus`, `spinOneOpMinus` | 3×3 raising/lowering `Ŝ^±` for S = 1 | `Quantum/SpinOneBasis.lean` |
| `spinOneOp{Plus,Minus}_mulVec_spinOne{Plus,Zero,Minus}` | raising/lowering actions `Ŝ^± |ψ^σ⟩ = √(2 - σ(σ±1)) |ψ^{σ±1}⟩` (Tasaki (2.1.3), S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOpPlus/Minus_conjTranspose` | `(Ŝ^±)† = Ŝ^∓` for S = 1 | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}` | S = 1 π-rotation matrices `û_α` (Tasaki eq. (2.1.33)) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot3_eq` | `û_3 = 1 - 2·(Ŝ^(3))²` (Tasaki eq. (2.1.32), α = 3 case) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}_sq` | `(û_α)² = 1` for integer S (Tasaki eq. (2.1.31) integer case) | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2,3}_comm_*` | distinct-axis commutation `û_α · û_β = û_β · û_α` for integer S | `Quantum/SpinOneBasis.lean` |
| `spinOneRot{1,2,3}` | `Û^(α)_θ = 1 - i sin θ · Ŝ^(α) - (1 - cos θ) · (Ŝ^(α))²` (Tasaki Problem 2.1.c, all 3 axes). Internal implementation record (private, not public API): `spinOneRot1`, `spinOneRot2`, `spinOneRot3` are `spinOneRotOf S θ` at `S = spinOneOp1, spinOneOp2, spinOneOp3` for the private def `spinOneRotOf : Matrix (Fin 3) (Fin 3) ℂ → ℝ → Matrix (Fin 3) (Fin 3) ℂ`. | `Quantum/SpinOneBasis.lean` |
| `spinOneRot{1,2,3}_zero` / `spinOneRot{1,2,3}_pi` | boundary checks `Û^(α)_0 = 1` and `Û^(α)_π = û_α`. Internal implementation record (private, not public API): both rows are proved from the private theorems `spinOneRotOf_zero` and `spinOneRotOf_pi` in the same file, combined with `spinOnePiRot{1,2,3}_eq`. | `Quantum/SpinOneBasis.lean` |
| `spinOnePiRot{1,2}_eq` | `û_α = 1 - 2·(Ŝ^(α))²` for axes 1, 2 (Tasaki eq. (2.1.30) for S = 1) | `Quantum/SpinOneBasis.lean` |
| `spinOneOp{1,2}_mul_self` | `(Ŝ^(α))²` explicit form (helper for the `_pi` boundary checks) | `Quantum/SpinOne.lean` |
| `spinOneOpPlus_eq_add`, `spinOneOpMinus_eq_sub` | `Ŝ^± = Ŝ^(1) ± i·Ŝ^(2)` for `S = 1` (Tasaki eq. (2.1.5), spin-1 case). Together with `spinOneUnit*_eq_polynomial` and `spinOneProj{Plus,Zero,Minus}_eq_polynomial`, fully reduces every off-diagonal matrix unit to a polynomial in `Ŝ^(1), Ŝ^(2), Ŝ^(3)` | `Quantum/SpinOneBasis.lean` |
| `spinHalfRot{1,2,3}_det_eq_one` | `det Û^(α)_θ = cos²(θ/2) + sin²(θ/2) = 1` (Pythagorean identity, complex form) | `Quantum/SpinHalfRotation.lean` |
| `SU2` | the special unitary submonoid `{ U | unitary U ∧ det U = 1 }` of `Matrix (Fin 2) (Fin 2) ℂ` | `Quantum/SU2.lean` |
| `spinHalfRot{1,2,3}_mem_unitary` | each axis rotation `Û^(α)_θ` lies in the unitary submonoid | `Quantum/SU2.lean` |
| `spinHalfRot{1,2,3}_mem_SU2` | each axis rotation `Û^(α)_θ` lies in `SU(2)` | `Quantum/SU2.lean` |
| `spinHalfEulerProduct φ θ ψ` | `Û^(3)_φ · Û^(2)_θ · Û^(3)_ψ` — the forward Euler-angle parametrization | `Quantum/SU2.lean` |
| `spinHalfEulerProduct_mem_SU2` | the Euler-angle product lies in `SU(2)` | `Quantum/SU2.lean` |
| `integral_cos_zero_two_pi` | `∫ φ in 0..2π, cos φ = 0` (trig integral for Problem 2.2.c) | `Quantum/SU2Integral.lean` |
| `integral_sin_zero_two_pi` | `∫ φ in 0..2π, sin φ = 0` | `Quantum/SU2Integral.lean` |
| `integral_sin_zero_pi` | `∫ θ in 0..π, sin θ = 2` | `Quantum/SU2Integral.lean` |
| `integral_sin_two_pi_pi` | `∫ φ in 0..2π, ∫ θ in 0..π, sin θ = 4π` (SU(2) volume in Euler coordinates) | `Quantum/SU2Integral.lean` |
| `integral_sin_mul_cos_zero_pi` | `∫ θ in 0..π, sin θ · cos θ = 0` (antiderivative `sin²/2` via FTC) | `Quantum/SU2Integral.lean` |
| `integral_sin_mul_cos_sq_half_zero_pi` | `∫ θ in 0..π, sin θ · cos²(θ/2) = 1` (half-angle identity → `integral_sin` + `integral_sin_mul_cos`) | `Quantum/SU2Integral.lean` |
| `integral_sin_mul_sin_sq_half_zero_pi` | `∫ θ in 0..π, sin θ · sin²(θ/2) = 1` (same technique) | `Quantum/SU2Integral.lean` |
| `integral_cexp_I_mul_zero_two_pi` | `∫ φ in 0..2π, e^{iφ} dφ = 0` (complex trig integral for Problem 2.2.c) | `Quantum/SU2Integral.lean` |
| `integral_cexp_neg_I_mul_zero_two_pi` | `∫ φ in 0..2π, e^{-iφ} dφ = 0` (conjugate of the above) | `Quantum/SU2Integral.lean` |
| `totalRot32_two_site` | for `Λ = Fin 2`, the Euler-angle rotation `Û^(3)_φ Û^(2)_θ` of the two-site system factors as `onSite 0 (Û^(3)_φ Û^(2)_θ) * onSite 1 (Û^(3)_φ Û^(2)_θ)` (Problem 2.2.c auxiliary) | `Quantum/SU2Integral.lean` |
| `onSite_zero_mul_one_mulVec_basisVec` | explicit tensor-product action `(onSite 0 A * onSite 1 B) |σ⟩ = (A (σ 0)) ⊗ (B (σ 1))` on a two-site basis vector (Problem 2.2.c auxiliary) | `Quantum/SU2Integral.lean` |
| `problem_2_2_c` | **Main theorem** (Tasaki §2.2 eq. (2.2.15)): `(1/4π) ∫₀^{2π} dφ ∫₀^π dθ sin θ · Û^(3)_φ Û^(2)_θ ρ (Û^(3)_φ Û^(2)_θ)† = (1/2) P_singlet` where `ρ = \|↑₁↓₂⟩⟨↑₁↓₂\|`. The SU(2)-averaged two-site state equals one-half times the singlet projector. | `Quantum/SU2Integral.lean` |
| `spinOnePiRot{1,2,3}_mulVec_spinOne{Plus,Zero,Minus}` | π-rotation matrix elements on the basis `|ψ^{+1,0,-1}⟩` (Tasaki eq. (2.1.34) / Problem 2.1.g for S = 1) | `Quantum/SpinOneBasis.lean` |

<!-- legacy-source:end:425:466 -->

---

[← Basis states and raising/lowering (Tasaki §2.1)](/lattice-system/formalization/legacy/11-basis-states-and-raising-lowering-tasaki-2-1/) · [Catalogue](/lattice-system/formalization/legacy/) · [Time-reversal map for `S = 1/2` (Tasaki §2.3) →](/lattice-system/formalization/legacy/13-time-reversal-map-for-tasaki-2-3/)
