module

public import BlockBand.Critical.RelativeVectors.FrameArray
public import BlockBand.Internal.Contracts.Transmission

/-!
# Angular vector fields and the true and reference generators

Definitions used by the relative mixed-vector theorem.

* `rotX`, `rotY`: the real vector fields `X_ij`, `Y_ij` rotating the pair `(z_i, z_j)`;
  `fieldSq W h = D²h(Wz,Wz) + Dh(W²z)`.
* `complexAngularGenerator N r λ`: `¼ Σ_{i<j} c_ij (X_ij² + Y_ij²)`, `c_ij = 1/(N(λ_i-λ_j)²)`.
* `refDamping`, `arrayMul`, `referenceArrayGenerator`: the damping `β̂_i = max(β_i, b₀N/ℓ)`, the
  label action `(Mz)_i = Σ_j M_ij z_j`, and the generator of the reference flow (short rotations
  `|i-j| < ℓ` and the circular Ornstein–Uhlenbeck part).
* `labelPhaseMatrix α M = P_α^{-1} M P_α`, `P_α = diag(e^{iα_i})` (phase conjugation of a label
  propagator).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N r : ℕ}

/-- `X_ij z_i = z_j`, `X_ij z_j = -z_i` (other labels `0`). -/
def rotX (i j : Fin N) (z : Fin N → Fin r → ℂ) : Fin N → Fin r → ℂ :=
  fun k => if k = i then z j else if k = j then -z i else 0

/-- `Y_ij z_i = i z_j`, `Y_ij z_j = i z_i` (other labels `0`). -/
def rotY (i j : Fin N) (z : Fin N → Fin r → ℂ) : Fin N → Fin r → ℂ :=
  fun k => if k = i then Complex.I • z j else if k = j then Complex.I • z i else 0

/-- `(W²h)(z) = D²h(z)(Wz, Wz) + Dh(z)(W(Wz))` for a linear vector field `W`. -/
def fieldSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (W : E → E) (h : E → ℝ)
    (z : E) : ℝ :=
  fderiv ℝ (fderiv ℝ h) z (W z) (W z) + fderiv ℝ h z (W (W z))

/-- Complex angular generator `¼ Σ_{i<j} c_ij (X_ij² + Y_ij²)`, `c_ij = 1/(N(λ_i-λ_j)²)`. -/
def complexAngularGenerator (N r : ℕ) (lam : Fin N → ℝ) (h : (Fin N → Fin r → ℂ) → ℝ)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
    dysonCoupling N lam i j * (fieldSq (rotX i j) h z + fieldSq (rotY i j) h z)

/-- Damping `β̂_i = max(β_i, b₀N/ℓ)` of the reference flow. -/
def refDamping (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ)
    (i : Fin N) : ℝ :=
  max (longCoupling F a ω ℓ σ i) (b₀ * N / ℓ)

/-- `(M z)_i = Σ_j M_ij z_j` on arrays `z ∈ (ℂ^r)^N` (the propagator acts on labels). -/
def arrayMul (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → Fin r → ℂ) : Fin N → Fin r → ℂ :=
  fun i q => ∑ j, M i j * z j q

/-- Generator of the reference flow on functions of `z ∈ (ℂ^r)^N`: the short
rotations `¼ Σ_{i<j, |i-j|<ℓ} c_ij (X_ij² + Y_ij²)` and, at every label, the circular
Ornstein–Uhlenbeck part of `dẑ_i = -½β̂_i ẑ_i ds + √β̂_i dC_i`, `E dC_i dC_i^* = I_r ds`:
`β̂_i (-½ Dh(z)[z_i e_i] + ¼ Σ_q (∂²_{Re z_iq} + ∂²_{Im z_iq}) h)`. -/
def referenceArrayGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ) : ℝ :=
  (1 / 4 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ labelDist i j < ℓ),
      flowRate F a ω σ i j * (fieldSq (rotX i j) h z + fieldSq (rotY i j) h z)) +
    ∑ i, refDamping F a b₀ ω ℓ σ i *
      (-(1 / 2 : ℝ) * fderiv ℝ h z (Pi.single i (z i)) +
        (1 / 4 : ℝ) * ∑ q : Fin r,
          (fderiv ℝ (fderiv ℝ h) z (Pi.single i (Pi.single q 1)) (Pi.single i (Pi.single q 1)) +
            fderiv ℝ (fderiv ℝ h) z (Pi.single i (Pi.single q Complex.I))
              (Pi.single i (Pi.single q Complex.I))))

/-- Phase conjugation `P_α^{-1} M P_α` of a label matrix, `P_α = diag(e^{iα_i})`:
`(P_α^{-1} M P_α)_{ij} = e^{-iα_i} M_ij e^{iα_j}`. -/
def labelPhaseMatrix (α : Fin N → ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => Complex.exp (-((α i : ℂ) * Complex.I)) * M i j *
    Complex.exp ((α j : ℂ) * Complex.I)

end BlockBand.Critical.RelativeVectors
