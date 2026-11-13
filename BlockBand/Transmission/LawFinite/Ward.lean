module

public import BlockBand.Transmission.LawFinite.Interface
public import BlockBand.Transmission.SourceMixing.MassUpdate
public import BlockBand.Transmission.PathScalar.Dissipative

/-!
# The absorbed update `Q₊ = L*QL + εC`

For a deterministic passive `X` (`Y = -Im X ⪰ 0`) and `ε ≥ 0`, the absorbed input
`X' = X - iε` is passive with `Y' = Y + ε` (`PathScalar.passiveY_absorb_eq`). The unabsorbed
update `SourceMixing.ae_passiveQ_freshSchur` at `X'` gives `Q₊ = L'*Q(X')L'`, `L' = K'𝒢₁₂`,
`K' = z - X'`. Since `R'K' = 1` and `RK = 1` (`PassiveCovariance.nearPencil_inverse`),
`L'*Q(X')L' = 𝒢₁₂*Y'𝒢₁₂ = 𝒢₁₂*Y𝒢₁₂ + ε𝒢₁₂*𝒢₁₂ = L*QL + εC` with the *old* `K = z - X`.

* `ward_alg`: the deterministic identity;
* **`absorbedWardIdentity_holds : AbsorbedWardIdentity`**;
* `ae_passiveMass_absorbed`: `q₊ = Re Tr(QLL*) + ε Re Tr C` almost surely.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder

variable {W : ℕ}

/-- `(KG)*(R*MR)(KG) = G*(RK)*M(RK)G`. -/
theorem ward_regroup (K R M G : Matrix (Fin W) (Fin W) ℂ) :
    (K * G)ᴴ * (Rᴴ * M * R) * (K * G) = Gᴴ * (R * K)ᴴ * M * (R * K) * G := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- **Deterministic absorbed Ward identity.** With `RK = 1`, `R'K' = 1`:
`(K'G)*(R'*(Y + ε)R')(K'G) = (KG)*(R*YR)(KG) + εG*G`. -/
theorem ward_alg {K K' R R' Y G : Matrix (Fin W) (Fin W) ℂ} (ε : ℝ) (hR : R * K = 1)
    (hR' : R' * K' = 1) :
    (K' * G)ᴴ * (R'ᴴ * (Y + (ε : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) * R') * (K' * G) =
      (K * G)ᴴ * (Rᴴ * Y * R) * (K * G) + (ε : ℂ) • (Gᴴ * G) := by
  rw [ward_regroup, ward_regroup, hR, hR', conjTranspose_one]
  simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The absorbed input is passive. -/
theorem passiveY_absorbedInput {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) : (passiveY (absorbedInput X ε)).PosSemidef :=
  PathScalar.passiveY_absorb hY hε

/-- `freshL` at the absorbed input is `K'𝒢₁₂`. -/
theorem freshL_absorbedInput (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshL b E (absorbedInput X ε) ω =
      (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - absorbedInput X ε) *
        freshG12 b E (absorbedInput X ε) ω := rfl

/-- **`AbsorbedWardIdentity`**: `Q₊ = L*QL + εC` almost surely. -/
theorem absorbedWardIdentity_holds : AbsorbedWardIdentity := by
  intro b hb0 hb E h1 h2 W hW X hY ε hε
  set X' := absorbedInput X ε
  have hY' := passiveY_absorbedInput hY hε
  filter_upwards [SourceMixing.ae_passiveQ_freshSchur hb0 hb hW h1 h2 hY'] with ω hω
  rw [hω, freshL_absorbedInput]
  have hR := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2 hY).2
  have hR' := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2 hY').2
  have hYe : passiveY X' = passiveY X + (ε : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) :=
    PathScalar.passiveY_absorb_eq X ε
  rw [passiveQ, hYe, ward_alg ε hR hR']
  rfl

/-- `q₊ = Re Tr(QLL*) + ε Re Tr C` almost surely (absorbed layer, old `K`). -/
theorem ae_passiveMass_absorbed {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (h1 : -2 < E)
    (h2 : E < 2) (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂freshLaw W b, passiveMass b E (freshSchur E (absorbedInput X ε) ω) =
      (passiveQ b E X * (absorbedL b E X ε ω * (absorbedL b E X ε ω)ᴴ)).trace.re +
        ε * (injection b E X ε ω).trace.re := by
  filter_upwards [absorbedWardIdentity_holds b hb0 hb E h1 h2 W hW X hY ε hε] with ω hω
  rw [passiveMass, hω, trace_add, Complex.add_re, trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]

end BlockBand.Transmission.LawFinite
