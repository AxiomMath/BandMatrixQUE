module

public import BlockBand.Endpoints.Response.LifetimeBridgeParts

/-!
# The split of the H-transform law into three inputs

This file states the three inputs into which `LbkHTransformLaw` is split:
1. `LbkCornerHeatIdentity` (analytic, about the explicit kernel);
2. `LbkDoobKilledLaw`: the killed path law of the `H` transform on `{t_k < σ₀}`;
3. `LbkLifetimeMarkov`: the Markov property at `t_k` for lifetime functionals.

`1 ∧ 2 ∧ 3 → LbkHTransformLaw` is proved (`lbkHTransformLaw_of_split`), and `1 ∧ 2` alone already
gives the lifetime law (`lbk_lifetime_law_of_split`). No proper sub-collection gives
`LbkHTransformLaw` with the proved lemmas: input 1 says nothing about the process; input 3 does not
mention the kernel; inputs 1, 2 only fix the law of `σ₀` and the killed path law on `{t_k < σ₀}`,
not the joint law of the path and `σ₀`; inputs 2, 3 give the lifetime law only in the implicit form
`1 - (x+y)P_tH(z)`. Conversely `LbkHTransformLaw` implies none of 1–3 by itself: it only sees
`{σ₀ < ∞}`, while inputs 2, 3 also weigh `{σ₀ = ∞}`, and input 1 is a statement about the kernel
alone.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- The harmonic function `H(x, y) = (x + y)⁻¹` of the `H` transform. -/
def lbkHarm (w : ℝ × ℝ) : ℝ := (w.1 + w.2)⁻¹

/-- The corner heat identity for the explicit kernel `p = lbkKernel D₀`:
`∫ p_t(z,z') H(z') dz' + (D₀/2) ∫_{(0,t]} p_s(z,(0,0)) ds = H(z)` for `z ∈ baseStrip`,
`z ≠ (0,0)`, `t > 0` (the additive `ℝ≥0∞` form of `H - P_tH = (D₀/2)∫_0^t p_s(z,0) ds`; both
summands are then finite). Proof idea: `𝒟₀` is in divergence form, annihilates `H` off the corner,
and the flux of `(x(1+x)H_x, y(1-y)H_y)` through `x + y = ε` is `-1`, so
`-𝒟₀H = (D₀/2)δ_{(0,0)}`; convolve with the conservative heat kernel. This is a statement about
`lbkKernel` only (no process). -/
def LbkCornerHeatIdentity (D0 : ℝ) : Prop :=
  ∀ w ∈ baseStrip, w ≠ (0, 0) → ∀ t : ℝ, 0 < t →
    (∫⁻ w', ENNReal.ofReal (lbkKernel D0 t w w') * ENNReal.ofReal (lbkHarm w')) +
        ENNReal.ofReal (D0 / 2) * ∫⁻ s in Ioc 0 t, ENNReal.ofReal (lbkKernel D0 s w (0, 0)) =
      ENNReal.ofReal (lbkHarm w)

open scoped Classical in

/-- **Input 2 (Doob identification): the killed finite-dimensional law** of every one-pair
boundary dual (`IsBoundaryDualProcess`) from `z = (x, y)`: for `0 < t₁ < ⋯ < t_k` (`t₀ = 0`)
and measurable `F ≥ 0`,
`E[F(Z_{t₁}, …, Z_{t_k}); t_k < σ₀] = ∫ F(zs) p_{t₁}(z,z₁)⋯p_{t_k-t_{k-1}}(z_{k-1},z_k)
  (x+y) H(z_k) dzs`,
i.e. the killed transition densities of the `H` transform are `p_t(z,z')H(z')/H(z)`.
The event `{t_k < σ₀}` includes `σ₀ = ∞`. At `k = 0` it says `P(0 < σ₀) = 1`;
at `k = 1`, `F = 1` it is the survival probability `P_tH(z)/H(z)`.
Why it holds: the dual is a solution of the martingale problem of `H⁻¹𝒟₀(H ·)` in the open
chamber, the Doob transform of the base diffusion (whose transition density is
`p`, `LbkBaseTransitionLaw`; the corner is polar for it) by the `𝒟₀`-excessive `H` solves it, and
the killed martingale problem is well posed from boundary starts.
-/
def LbkDoobKilledLaw (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
        ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
          ∫⁻ ω, (if ENNReal.ofReal (lbkLastTime ts) < dualExtinction N ω
              then F (fun i => dualPoint X Y (ts i) ω) else 0) ∂P =
            ∫⁻ zs, F zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
              ENNReal.ofReal ((x + y) * lbkHarm (lbkLastPoint (x, y) zs))

open scoped Classical in

/-- **Input 3 (Markov property at `t_k` for the lifetime)** of every one-pair boundary dual from
`z = (x, y)`: let `h ≥ 0` be measurable and let `Λ` be the lifetime functional, i.e.
`E'[h(σ₀'); σ₀' < ∞] = Λ(a, b)` for every realization from every dual start `(a, b)`.
Then for
`0 < t₁ < ⋯ < t_k` (`t₀ = 0`, `Z_{t₀} = z`) and measurable `G ≥ 0`,
`E[G(Z_{t₁..t_k}) h(σ₀ - t_k); t_k < σ₀ < ∞] = E[G(Z_{t₁..t_k}) Λ(Z_{t_k}); t_k < σ₀]`:
given `𝓕_{t_k}` on `{t_k < σ₀}`, the remaining lifetime `σ₀ - t_k` has the lifetime law from
`Z_{t_k}`.
Why it holds: simple Markov property of the (well-posed) killed martingale
problem at the fixed time `t_k`, with `Z_{t_k}` in the open chamber on `{t_k < σ₀}`
(`IsBoundaryDeletionPath.chamber`), plus existence of the dual from every dual start (so that the
hypothesis determines `Λ` at every point `Z_{t_k}` can take).
It does not mention the kernel.
-/
def LbkLifetimeMarkov (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
        ∀ h : ℝ → ℝ≥0∞, Measurable h → ∀ Λ : ℝ × ℝ → ℝ≥0∞,
          (∀ a b : ℝ, IsDualStart ![a] ![b] →
            ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (P' : Measure Ω')
              (N' : ℝ≥0 → Ω' → ℕ) (X' Y' : ℝ≥0 → Ω' → ℕ → ℝ),
              IsBoundaryDualProcess P' 𝓖' D0 ![a] ![b] N' X' Y' →
              ∫⁻ ω', (if dualExtinction N' ω' < ⊤ then h (dualExtinction N' ω').toReal else 0) ∂P' =
                Λ (a, b)) →
          ∀ G : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable G →
            ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ENNReal.ofReal (lbkLastTime ts) < dualExtinction N ω
                then G (fun i => dualPoint X Y (ts i) ω) *
                  h ((dualExtinction N ω).toReal - lbkLastTime ts)
                else 0) ∂P =
              ∫⁻ ω, (if ENNReal.ofReal (lbkLastTime ts) < dualExtinction N ω
                then G (fun i => dualPoint X Y (ts i) ω) *
                  Λ (lbkLastPoint (x, y) (fun i => dualPoint X Y (ts i) ω))
                else 0) ∂P

/-- The split parts of the lifetime-bridge lemma at diffusivity `D₀`: `LbkParts` with
`LbkHTransformLaw` replaced by the three inputs above. -/
structure LbkSplitParts (D0 : ℝ) : Prop where
  spherePos : LbkSphereKernelPos D0
  existence : LbkBaseExistence D0
  transition : LbkBaseTransitionLaw D0
  cornerHeat : LbkCornerHeatIdentity D0
  doob : LbkDoobKilledLaw D0
  markov : LbkLifetimeMarkov D0
  bridge : LbkBridgeExistence D0

end BlockBand.Endpoints
