module

public import BlockBand.Critical.MatrixClosing.Statement
public import BlockBand.Critical.EntireLaw.RingPath

/-!
# The entire law: finite-width ring probes and the intermediate steps

Finite-width objects: `ringProbeVector` (probes of covariance `Q/W²` on all ring blocks),
`omitCollar`, `ringSourceMatrix` (`ζ^* R ζ`, `R = (H-E)⁻¹`), `omittedRingSourceMatrix`
(`ζ_o^* R ζ_o`), `fullRingProbeLaw` (physical law ⊗ i.i.d. circular Gaussians).

The five steps of the proof of the entire law, stated as `Prop`s:
* `FiniteGaussianMomentIdentity`: the finite-width Gaussian integral
  `E Π D_W(iy)^{∓1} = E exp{-iΣσ_j ζ_j^*Rζ_j}`;
* `CollarSourceRemoval`: the collar contribution tends to `0` in probability;
* `ClosedSourceLimitStep`: the phase expectations converge to `E exp{-iΣσ_j𝒯_jj}`;
* `EntireTightness`: tightness of the laws of `D_W`;
* `InverseMomentDetermination`: bounded mixed inverse moments determine cone-bounded laws.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate

variable {p : Parameters}

/-!
## 1. Finite-width probes of the closed physical ring
-/

/-- The global probe `ζ = W⁻¹ Q^{1/2} g` on **all** ring blocks, `Q = Σ_j q(j/n) P_j`
(covariance `Q/W²` for `g ~ CN(0, I)`). -/
def ringProbeVector (p : Parameters) (Q : C(Torus, ℝ)) (g : p.Site → ℂ) : p.Site → ℂ :=
  fun x => (((p.W : ℝ)⁻¹ * Real.sqrt (Q (p.ringProfilePoint x.1)) : ℝ) : ℂ) * g x

/-- The collar `{n-1, 0, 1}` of the ring (block `0` and its two neighbours). -/
def IsCollarBlock (p : Parameters) (j : ZMod p.n) : Prop := j = 0 ∨ j = 1 ∨ j = -1

instance (j : ZMod p.n) : Decidable (IsCollarBlock p j) := by
  unfold IsCollarBlock; infer_instance

/-- The probe with its collar coordinates removed, `ζ_o` (so `ζ = ζ_o + ζ_c`). -/
def omitCollar (p : Parameters) (v : p.Site → ℂ) : p.Site → ℂ :=
  fun x => if IsCollarBlock p x.1 then 0 else v x

/-- **The closed physical source matrix** `(ζ_a^* R ζ_c)_{a,c}`, `R = (H - E)⁻¹`, with probes on
all ring blocks (the matrix whose Gaussian integral is `D_W(iy)⁻¹`). -/
def ringSourceMatrix (p : Parameters) (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (H : p.SiteMatrix) (g : Fin J → p.Site → ℂ) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c => star (ringProbeVector p (Q a) (g a)) ⬝ᵥ
    ((H - (E : ℂ) • 1)⁻¹ *ᵥ ringProbeVector p (Q c) (g c))

/-- The same closed source matrix with the collar coordinates of every probe removed
(`ζ_o^* R ζ_o`, the probes omitting the three collar blocks). -/
def omittedRingSourceMatrix (p : Parameters) (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (H : p.SiteMatrix) (g : Fin J → p.Site → ℂ) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c => star (omitCollar p (ringProbeVector p (Q a) (g a))) ⬝ᵥ
    ((H - (E : ℂ) • 1)⁻¹ *ᵥ omitCollar p (ringProbeVector p (Q c) (g c)))

/-- Law of the physical ring and `J` independent standard circular Gaussian vectors on the sites. -/
def fullRingProbeLaw (model : p.GaussianRingModel) (J : ℕ) :
    Measure (p.SiteMatrix × (Fin J → p.Site → ℂ)) :=
  (model.law : Measure p.SiteMatrix).prod (Measure.pi fun _ : Fin J => circularVectorLaw p.Site)

/-!
## 2. The intermediate steps of the entire law
-/

/-- **Finite-width Gaussian moment identity**: at finite width the Gaussian integral gives the
mixed inverse moments exactly in terms of the physical probe matrix.
For every admissible `p` (both parities), every finite realization, every real `E`, every
nonnegative family `q`, every `y ∈ [0,∞)^{J×(k+1)}` and signs `σ`:
`E Π_{σ_j=1} D_W(iy^{(j)})⁻¹ Π_{σ_j=-1} conj(D_W(iy^{(j)})⁻¹) = E exp{-i Σ_j σ_j (ζ_j^* R ζ_j)}`,
one independent probe `ζ_j` of covariance `W⁻² Σ_a y_a^{(j)} Q_a` per factor. Exact; no limit. -/
def FiniteGaussianMomentIdentity : Prop :=
  ∀ (p : Parameters) (R : FiniteRealization p) (E : ℝ) (k : ℕ) (q : Fin k → C(Torus, ℝ)),
    IsProfileFamily q →
    ∀ (J : ℕ) (y : Fin J → Fin (k + 1) → ℝ) (σ : Fin J → ℤˣ), (∀ j a, 0 ≤ y j a) →
      mixedInverseMoment (finiteEntireLaw R E (fullProfile q)) y σ =
        ∫ x, closedSourcePhase σ (ringSourceMatrix p E (probeProfile q y) x.1 x.2)
          ∂fullRingProbeLaw R.model J

/-- **Restoring the collar sources.** Along every critical sequence and every choice of realizations, every
entry of `ζ^* R ζ - ζ_o^* R ζ_o` (full probes versus probes with the three collar blocks removed,
same Gaussians) tends to `0` in probability under the physical law. Domain: `0 < b < 1/2`,
`|E| < 2`, `τ > 0`, finitely many nonnegative profiles. -/
def CollarSourceRemoval : Prop :=
  ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (J : ℕ) (Q : Fin J → C(Torus, ℝ)), (∀ a x, 0 ≤ Q a x) →
    ∀ (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
    ∀ (a c : Fin J) (ε : ℝ), 0 < ε →
      Tendsto (fun j => fullRingProbeLaw (R j).model J
          {x | ε < ‖ringSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2 a c -
            omittedRingSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2 a c‖})
        atTop (𝓝 0)

/-- **The closed-source limit.** Given `MatrixClosingStatement` and the critical limit `κ` of
the physical ring's path-probe pairs `(𝒦_W, B_W)` (`IsRingProbeCriticalLimit`), for every
realization `C` of `𝖢_J(0)`, along every critical sequence and every choice of realizations:
`E exp{-i Σ_j σ_j (ζ_{o,j}^* R ζ_{o,j})} → E exp{-i Σ_j σ_j 𝒯_jj}`,
`𝒯 = Re 𝒦 + η B^{1/2} 𝖢_J(0) B^{1/2}`, `𝒦 ~ κ` independent of `𝖢_J(0)`. -/
def ClosedSourceLimitStep : Prop :=
  BlockBand.Critical.MatrixClosing.MatrixClosingStatement →
  ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (J : ℕ) (Q : Fin J → C(Torus, ℝ)), (∀ a x, 0 ≤ Q a x) →
    ∀ κ : Measure (Matrix (Fin J) (Fin J) ℂ), IsProbabilityMeasure κ →
      IsRingProbeCriticalLimit b E hb hb' τ.1 Q κ →
    ∀ (σ : Fin J → ℤˣ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))) (C : Ω → Matrix (Fin J) (Fin J) ℂ),
      IsCanonicalCauchyAtZero J P Ξ C →
    ∀ (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      Tendsto (fun j => ∫ x, closedSourcePhase σ
          (omittedRingSourceMatrix (s.parameters b hb hb' j) E Q x.1 x.2)
          ∂fullRingProbeLaw (R j).model J)
        atTop (𝓝 (∫ K, ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C ω)) ∂P ∂κ))

/-- **Tightness of the entire functions** (by the converse probe-tightness bound,
Sylvester's identity, `|det(I+B₀)| ≤ exp{Re Tr B₀ + ½‖B₀‖²_HS}` and Montel). Along every
critical sequence and every choice of realizations, the laws of `D_W` on `EntireFunction (k+1)`
(compact-open topology) form a tight family. -/
def EntireTightness : Prop :=
  ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
    ∀ (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      IsTightMeasureSet (Set.range fun j =>
        (finiteEntireLaw (R j) E (fullProfile q) : Measure (EntireFunction (k + 1))))

/-- **Bounded moment determination.** Two laws of random entire functions whose inverse values on
the positive imaginary cone lie in the closed unit disk (`HasInverseConeBound`) and which have the
same mixed inverse moments are equal. -/
def InverseMomentDetermination : Prop :=
  ∀ (m : ℕ) (μ μ' : RandomEntire m),
    HasInverseConeBound μ → HasInverseConeBound μ' →
    (∀ (J : ℕ) (y : Fin J → Fin m → ℝ) (σ : Fin J → ℤˣ), (∀ j a, 0 ≤ y j a) →
      mixedInverseMoment μ y σ = mixedInverseMoment μ' y σ) → μ = μ'

end BlockBand.Critical.EntireLaw
