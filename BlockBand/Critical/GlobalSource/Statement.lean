module

public import BlockBand.Internal.Contracts.CriticalEntire

/-!
# Global Gaussian source: finite-width objects and the statement

The limit object is `IsGlobalProbeLaw b E τ Q κ`. This file defines the finite-width matrices
`(𝒦_W, B_W)` and the statement `GlobalGaussianSourceStatement` (a `Prop`). The path and its
inverse block `G = leadInverse b E W n` are obtained by removing a distinguished physical block `0`
and its two neighbours from the ring; the remaining `r = n-3` blocks form an independent Gaussian
path.

## Conventions

* The collar is the ring block `0` and its two neighbours `1, n-1`. The remaining physical path
  has `probePathLength n = n - 3` blocks, read from the near-end-grown path
  (`TransmissionPath.growthPathLaw`). Its inverse with the two matched leads is
  `TransmissionPath.fullInverse b E W (n-3)`; `G` is its interior block (`leadInverse`).
* Orientation: the grown path places birth index `k` at position `(n-3)-1-k`. Birth index `k` is
  identified with the ring block `k+2`, so path position `i` is ring block `n-2-i`
  (`pathRingBlock`), and it carries the profile value `q((n-2-i)/n)` exactly as
  `Parameters.profileSourceMatrix` (`Q_a = Σ_j q_a(j/n) P_j`). With this choice a block of birth
  time `t = k/W` carries `q((k+2)/n) → q(t/τ)`, the orientation of `birthDensity`.
* `ζ_a = W⁻¹ Q_a^{1/2} g_a`, `g_a ~ circularVectorLaw` (`E g gᴴ = I`), independent over `a` and
  of the path; so `E ζ_a ζ_aᴴ = Q_a/W²` and the pseudo-covariance vanishes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ComplexConjugate Matrix

/-- Number of blocks of the physical path left after removing the three collar blocks. -/
def probePathLength (n : ℕ) : ℕ := n - 3

/-- Sites `(position, coordinate)` of the remaining physical path. -/
abbrev PathSite (W n : ℕ) := Fin (probePathLength n) × Fin W

/-- Ring block of path position `i`: position `i` has birth index `(n-3)-1-i`, identified with ring
block `(n-3)-1-i+2 = n-2-i`. For `n ≥ 4` this ranges over `2, …, n-2`, the ring minus the collar
`{n-1, 0, 1}`. -/
def pathRingBlock (n : ℕ) (i : Fin (probePathLength n)) : ℕ := n - 2 - i.val

/-- The profile value `q(j/n)` of the ring block `j = pathRingBlock n i`, as in
`Parameters.ringProfilePoint` / `profileSourceMatrix`. -/
def pathProfileValue (n : ℕ) (Q : C(Torus, ℝ)) (i : Fin (probePathLength n)) : ℝ :=
  Q (QuotientAddGroup.mk ((pathRingBlock n i : ℝ) / n))

/-- The global Gaussian probe `ζ = W⁻¹ Q^{1/2} g` on the remaining path, with
`Q = Σ_j q(j/n) P_j` restricted to the path. For `g ~ CN(0, I)` its covariance is
`Q/W²` exactly and its pseudo-covariance is zero. -/
def globalProbeVector (W n : ℕ) (Q : C(Torus, ℝ)) (g : PathSite W n → ℂ) : PathSite W n → ℂ :=
  fun x => (((W : ℝ)⁻¹ * Real.sqrt (pathProfileValue n Q x.1) : ℝ) : ℂ) * g x

/-- Joint sample: the near-end-grown path and `J` standard circular Gaussian vectors on the
remaining path sites. -/
abbrev GlobalProbeSample (W n J : ℕ) := GrowthPath W × (Fin J → PathSite W n → ℂ)

/-- Law of `GlobalProbeSample`: the path law `growthPathLaw W b` and, independently of the path,
i.i.d. `g_a ~ circularVectorLaw`. -/
def globalProbeLaw (W n J : ℕ) (b : ℝ) : Measure (GlobalProbeSample W n J) :=
  (growthPathLaw W b).prod (Measure.pi fun _ : Fin J => circularVectorLaw (PathSite W n))

/-- `G`: the interior block of the inverse of the remaining path with its two matched leads
(`fullInverse` with `n-3` blocks). -/
def leadInverse (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Matrix (PathSite W n) (PathSite W n) ℂ :=
  (fullInverse b E W (probePathLength n) ω).toBlocks₁₁

/-- **`𝒦_W = (ζ_a^* G ζ_c)_{a,c}`**, for `J` probes with profiles `Q`. -/
def globalProbeMatrix (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (x : GlobalProbeSample W n J) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c => star (globalProbeVector W n (Q a) (x.2 a)) ⬝ᵥ
    (leadInverse b E W n x.1 *ᵥ globalProbeVector W n (Q c) (x.2 c))

/-- **`B_W = -η⁻¹ Im 𝒦_W`**, with `probeGram` (`η = etaZ b E`, `Im K = (K - Kᴴ)/(2i)`). -/
def globalProbeGram (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (x : GlobalProbeSample W n J) : Matrix (Fin J) (Fin J) ℂ :=
  probeGram b E (globalProbeMatrix b E W n Q x)

/-- `κ` is the critical limit of the joint law of `(𝒦_W, B_W)`: along every critical sequence
(`W → ∞`, `n/W → τ`, no parity or rate condition), for every bounded continuous test `Φ` of the pair
of complex matrices (so the full complex matrix law, not only determinant transforms), the
finite-width expectations converge to the expectation of `Φ(𝒦, B)` with `𝒦 ~ κ` and
`B = probeGram 𝒦 = -η⁻¹ Im 𝒦`. The laws of the finite matrices are written as integrals against
`globalProbeLaw`, as in `IsComplexSourceLimit`. -/
def IsGlobalProbeCriticalLimit (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (κ : Measure (Matrix (Fin J) (Fin J) ℂ)) : Prop :=
  ∀ s : CriticalSequence τ,
    ∀ Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) ℝ,
      Tendsto (fun j => ∫ x, Φ (globalProbeMatrix b E (s.W j) (s.n j) Q x,
          globalProbeGram b E (s.W j) (s.n j) Q x) ∂globalProbeLaw (s.W j) (s.n j) J b)
        atTop (𝓝 (∫ K, Φ (K, probeGram b E K) ∂κ))

/-- **The global Gaussian source statement.** For `0 < b < 1/2`, `-2 < E < 2`, `τ > 0` and
nonnegative continuous profiles `Q`, there is a unique law `κ` that is the global probe law
(`IsGlobalProbeLaw`) and the critical limit of `(𝒦_W, B_W)` (`IsGlobalProbeCriticalLimit`). -/
def GlobalGaussianSourceStatement : Prop :=
  ∀ (b E : ℝ), 0 < b → b < 1 / 2 → -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (J : ℕ) (Q : Fin J → C(Torus, ℝ)), (∀ a x, 0 ≤ Q a x) →
      ∃! κ : Measure (Matrix (Fin J) (Fin J) ℂ),
        IsGlobalProbeLaw b E τ.1 Q κ ∧ IsGlobalProbeCriticalLimit b E τ.1 Q κ

end BlockBand.Critical.GlobalSource
