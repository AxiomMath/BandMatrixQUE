module

public import BlockBand.Critical.GlobalSource.Closing

/-!
# Global Gaussian source: statement of the source replacement estimate

* `profileProbeMatrix`: Gaussian probes of covariance `r_a/W²` on a path of `L` blocks;
  `globalProbeMatrix` is the case `L = n - 3`, `r = pathProfileValue` (`rfl`).
* `optTag`, `blockSampledMatrix`: grouped tag matrix `(1/M) Σ_{i,i'} ξ_{a,i}^* G ξ_{c,i'}` as a
  function of the block indices (index `L` = no tag), the path and the tag Gaussians.
* `profileMass`, `discreteBlockLaw`, `discreteSampledLaw`, `discreteSampledMatrix`.
* `SourceReplacementStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open scoped Matrix

/-- Weight `W⁻¹ √r` of a Gaussian probe of covariance `r/W²` (block-constant profile values). -/
def profileWeight (W L : ℕ) (r : Fin L → ℝ) (y : Fin L × Fin W) : ℂ :=
  (((W : ℝ)⁻¹ * Real.sqrt (r y.1) : ℝ) : ℂ)

/-- **Gaussian probe matrix with profile values `r`** on the path of `L` blocks with its two matched
leads: `(ζ_a^* G ζ_c)_{a,c}`, `ζ_a = W⁻¹ r_a^{1/2} g_a` (covariance `r_a/W²`). -/
def profileProbeMatrix (b E : ℝ) (W L : ℕ) {J : ℕ} (r : Fin J → Fin L → ℝ)
    (x : GrowthPath W × (Fin J → Fin L × Fin W → ℂ)) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c => star (fun y => profileWeight W L (r a) y * x.2 a y) ⬝ᵥ
    ((fullInverse b E W L x.1).toBlocks₁₁ *ᵥ fun y => profileWeight W L (r c) y * x.2 c y)

/-- Law of the path and `J` independent standard circular probe vectors. -/
def profileProbeLaw (W L J : ℕ) (b : ℝ) :
    Measure (GrowthPath W × (Fin J → Fin L × Fin W → ℂ)) :=
  (growthPathLaw W b).prod (Measure.pi fun _ : Fin J => circularVectorLaw (Fin L × Fin W))

/-- `globalProbeMatrix` is `profileProbeMatrix` on the remaining path with `r = pathProfileValue`. -/
theorem globalProbeMatrix_eq_profileProbeMatrix (b E : ℝ) (W n : ℕ) {J : ℕ}
    (Q : Fin J → C(Torus, ℝ)) :
    globalProbeMatrix b E W n Q =
      profileProbeMatrix b E W (probePathLength n) (fun a => pathProfileValue n (Q a)) := rfl

/-- `globalProbeLaw` is `profileProbeLaw` on the remaining path. -/
theorem globalProbeLaw_eq_profileProbeLaw (W n J : ℕ) (b : ℝ) :
    globalProbeLaw W n J b = profileProbeLaw W (probePathLength n) J b := rfl

/-- A tag at an optional block `o : Fin (L + 1)`: for `o = k < L` it is `tagVector`, `√(m/W) ι_k g`;
`o = L` means no tag (the zero vector). -/
def optTag (W L : ℕ) (o : Fin (L + 1)) (m : ℝ) (g : Fin W → ℂ) : Fin L × Fin W → ℂ :=
  if h : o.val < L then tagVector W L ⟨o.val, h⟩ m g else 0

/-- **Grouped tag matrix** `(1/M) Σ_{i,i'} ξ_{(a,i)}^* G ξ_{(c,i')}`, `ξ_j = optTag (κ j) m_a g_j`,
on the path of `L` blocks, for block indices `κ`, masses `mass`, the path and the tag Gaussians of
the `ProbedPath`. -/
def blockSampledMatrix (b E : ℝ) (W L : ℕ) {J M : ℕ} (mass : Fin J → ℝ)
    (κ : Fin (J * M) → Fin (L + 1)) (x : ProbedPath W (J * M)) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c => (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ i' : Fin M,
    star (optTag W L (κ (finProdFinEquiv (a, i))) (mass a) (x.2 (finProdFinEquiv (a, i)))) ⬝ᵥ
      ((fullInverse b E W L x.1).toBlocks₁₁ *ᵥ
        optTag W L (κ (finProdFinEquiv (c, i'))) (mass c) (x.2 (finProdFinEquiv (c, i'))))

/-- Discrete mass `m = W⁻¹ Σ_k r_k` of a profile on the path. -/
def profileMass (W L : ℕ) (r : Fin L → ℝ) : ℝ := (W : ℝ)⁻¹ * ∑ k, r k

/-- **Discrete block law**: `P(K = k) = r_k/(W m)`, `m = profileMass`; a
zero-mass profile has no tag (the index `L`). -/
def discreteBlockLaw (W L : ℕ) (r : Fin L → ℝ) : Measure (Fin (L + 1)) :=
  if 0 < profileMass W L r then
    ∑ k : Fin L, ENNReal.ofReal (r k / ((W : ℝ) * profileMass W L r)) • Measure.dirac k.castSucc
  else Measure.dirac (Fin.last L)

/-- Law of the discretely sampled model: `M` i.i.d. blocks per group (`discreteBlockLaw`),
independent of the probed path (path and tag Gaussians). -/
def discreteSampledLaw (W L J M : ℕ) (b : ℝ) (r : Fin J → Fin L → ℝ) :
    Measure ((Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M)) :=
  (Measure.pi fun i : Fin (J * M) => discreteBlockLaw W L (r (tagGroup i))).prod
    (probedPathLaw W (J * M) b)

/-- The discretely sampled grouped matrix: tags of mass `profileMass W L (r a)` (so that
`E(ξξ^*) = r_a/W²` exactly). -/
def discreteSampledMatrix (b E : ℝ) (W L : ℕ) {J M : ℕ} (r : Fin J → Fin L → ℝ)
    (y : (Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M)) : Matrix (Fin J) (Fin J) ℂ :=
  blockSampledMatrix b E W L (fun a => profileMass W L (r a)) y.1 y.2

/-- **The source replacement estimate** for characteristic tests: for `0 < b < 1/2`, `κ > 0`,
`T`, `qmax` and `J` there are `C` and `W₀` such that for `W ≥ W₀`, `E ∈ bulkInterval κ`,
`L ≤ T W`, profiles `0 ≤ r_a ≤ qmax` and `M ≥ 1`, the characteristic functions of the Gaussian
probe matrix and of the discretely sampled matrix differ by at most `C (1 + ‖u‖)³ / √M`. Proved
from `ComplexSourceLawContract` in `sourceReplacement_holds`. -/
def SourceReplacementStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ T qmax : ℝ, ∀ J : ℕ,
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ L : ℕ, (L : ℝ) ≤ T * W →
      ∀ r : Fin J → Fin L → ℝ, (∀ a k, 0 ≤ r a k ∧ r a k ≤ qmax) → ∀ M : ℕ, 1 ≤ M →
        ∀ u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2),
          ‖charFun ((profileProbeLaw W L J b).map
              (fun x => matrixCoord J (profileProbeMatrix b E W L r x))) u -
            charFun ((discreteSampledLaw W L J M b r).map
              (fun y => matrixCoord J (discreteSampledMatrix b E W L r y))) u‖ ≤
            C * (1 + ‖u‖) ^ 3 / Real.sqrt M

end BlockBand.Critical.GlobalSource
