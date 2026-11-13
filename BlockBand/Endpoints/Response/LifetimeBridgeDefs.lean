module

public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The base Legendre–Jacobi diffusion, base bridges, and the lifetime-bridge statement

This file defines the base diffusion, its transition density and base bridges, and states the
lifetime-bridge lemma `LifetimeBridgeStatement`.

Let `𝒟₀` be the independent Legendre–Jacobi base generator, with transition density
`p_t⁰(z, z')` relative to `dx' dy'`, and `H(x, y) = (x + y)⁻¹`. For `z = (x, y) ≠ (0, 0)` the
lifetime of its absorbing `H` transform has density
`P_z(σ₀ ∈ dt) = (D₀/2)(x + y) p_t⁰(z, (0,0)) dt`, strictly positive for every `t > 0`. Conditional
on `σ₀ = t` the transformed path up to `t` is the base bridge from `z` to `(0,0)` of length `t`;
in particular its two coordinates are independent base bridges.

* `baseStrip = [0,∞) × [0,1]` (the closed strip), `baseGenerator D₀ f z =
  (D₀/2)[x(1+x)f_xx + (1+2x)f_x + y(1-y)f_yy + (1-2y)f_y]`, the expanded form of the divergence
  form `(D₀/2){∂_x[x(1+x)∂_x] + ∂_y[y(1-y)∂_y]}`.
* `IsBaseDiffusion`: a continuous adapted process in the closed strip started at `z`, solving the
  martingale problem of `𝒟₀` for every smooth compactly supported test on `ℝ²` (the square-root
  degenerate coefficients are Hölder-`1/2`, so this problem is well posed on the closed strip; no
  boundary condition is imposed, the boundaries being entrance/polar for this generator).
* `IsBaseDensity D₀ p`: the base diffusion exists from every point of the strip, and for `t > 0`
  every realization has `P(Z_t ∈ B) = ∫_B p_t(z, z') dz'`; `p_t(z, ·)` is nonnegative and
  continuous on the closed strip (this determines the corner value `p_t(z, (0,0))`, the continuous
  density value at the poles).
* `IsBaseCoordDensities D₀ pX pY`: the one-dimensional densities of the two coordinates
  (hyperbolic radial `X`, spherical radial `Y`), continuous on `[0,∞)`, `[0,1]`.
* `bridgeFddDensity p z e t ts zs`: the finite-dimensional bridge density
  `p_{t₁}(z,z₁)p_{t₂-t₁}(z₁,z₂)⋯p_{t-t_k}(z_k,e)/p_t(z,e)`, generic in the state space (so the
  same object gives the one-dimensional coordinate bridges).
* `IsBaseBridge P p z t Z`: a process with paths continuous on `[0,t]`, `Z₀ = z`, `Z_t = (0,0)`,
  and finite-dimensional laws `bridgeFddDensity` (the continuous version of the base bridge).

## Lean form of the lemma (`LifetimeBridgeStatement`)

For every `D₀ > 0` there is a jointly measurable `p` with `IsBaseDensity D₀ p`, a product
decomposition `p = pX ⊗ pY` on the strip with `IsBaseCoordDensities D₀ pX pY` (coordinate
independence), and for every start `IsDualStart ![x] ![y]` (that is `z = (x,y) ∈ baseStrip`,
`z ≠ (0,0)`):
1. `p_t(z, (0,0)) > 0` for every `t > 0`;
2. for every `t > 0` the base bridge from `z` to `(0,0)` of length `t` exists (`IsBaseBridge`);
3. for every realization of the `H` transform: the lifetime law on `{σ₀ < ∞}` is
   `(D₀/2)(x+y)p_t(z,(0,0)) dt` on `(0,∞)` (tested against all measurable `g ≥ 0`); and for all
   times `0 < t₁ < ⋯ < t_k`, all measurable `g, F ≥ 0`,
   `E[g(σ₀) F(Z_{t₁},…,Z_{t_k}); t_k < σ₀ < ∞] =
     ∫_{(0,∞)} g(t) (D₀/2)(x+y)p_t(z,(0,0)) 1{t_k < t} E^{br}_{z,t}[F] dt`,
   which says that conditional on `σ₀ = t`, the transformed path up to `t` has the base-bridge
   law (finite-dimensional form; paths are continuous on both sides).

Joint measurability of `p` is an additional (true) property of the smooth heat kernel; it is a
conclusion, so it strengthens the statement. The statement does not assert `σ₀ < ∞` a.s.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### The base generator and the base diffusion
-/

/-- The closed strip `[0, ∞) × [0, 1]` (state space of the base diffusion). -/
def baseStrip : Set (ℝ × ℝ) := Ici 0 ×ˢ Icc 0 1

/-- The independent Legendre–Jacobi base generator:
`𝒟₀ f = (D₀/2)[x(1+x)f_xx + (1+2x)f_x + y(1-y)f_yy + (1-2y)f_y]`
`= (D₀/2){∂_x[x(1+x)∂_x f] + ∂_y[y(1-y)∂_y f]}`. -/
def baseGenerator (D0 : ℝ) (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  D0 / 2 *
    ((z.1 * (1 + z.1) * fderiv ℝ (fun w => fderiv ℝ f w (1, 0)) z (1, 0) +
        (1 + 2 * z.1) * fderiv ℝ f z (1, 0)) +
      (z.2 * (1 - z.2) * fderiv ℝ (fun w => fderiv ℝ f w (0, 1)) z (0, 1) +
        (1 - 2 * z.2) * fderiv ℝ f z (0, 1)))

/-- The base diffusion started at `z`: an adapted process with continuous paths in the closed
strip, `Z₀ = z`, solving the martingale problem of `𝒟₀` for every smooth compactly supported test
`f` on `ℝ²`: `f(Z_t) - ∫_0^t 𝒟₀ f(Z_u) du` is a `𝓖`-martingale. -/
structure IsBaseDiffusion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) (z : ℝ × ℝ)
    (Z : ℝ≥0 → Ω → ℝ × ℝ) : Prop where
  prob : IsProbabilityMeasure P
  adapted : ∀ t, Measurable[𝓖 t] (Z t)
  start : ∀ᵐ ω ∂P, Z 0 ω = z
  paths : ∀ᵐ ω ∂P, Continuous (fun t => Z t ω) ∧ ∀ t, Z t ω ∈ baseStrip
  martingale : ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    Martingale (fun t ω => f (Z t ω) - ∫ u in Ioc (0 : ℝ) t, baseGenerator D0 f (Z u.toNNReal ω))
      𝓖 P

/-- The base diffusion from `z` exists (on some filtered probability space). -/
def HasBaseDiffusion (D0 : ℝ) (z : ℝ × ℝ) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ × ℝ), IsBaseDiffusion P 𝓖 D0 z Z

/-- The transition density `p_t⁰(z, z')` of the base diffusion relative to `dx' dy'`, in its
continuous version on the closed strip: the base diffusion exists from every point of the strip,
and for `t > 0`, `z` in the strip, every realization from `z` has `P(Z_t ∈ B) = ∫_B p_t(z,·)`;
`p_t(z, ·)` is nonnegative and continuous on the closed strip (which determines it there). -/
structure IsBaseDensity (D0 : ℝ) (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) : Prop where
  exists_ : ∀ z ∈ baseStrip, HasBaseDiffusion D0 z
  nonneg : ∀ t : ℝ, 0 < t → ∀ z ∈ baseStrip, ∀ z' ∈ baseStrip, 0 ≤ p t z z'
  cont : ∀ t : ℝ, 0 < t → ∀ z ∈ baseStrip, ContinuousOn (p t z) baseStrip
  law : ∀ t : ℝ≥0, 0 < t → ∀ z ∈ baseStrip,
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (Z : ℝ≥0 → Ω → ℝ × ℝ), IsBaseDiffusion P 𝓖 D0 z Z →
      ∀ B : Set (ℝ × ℝ), MeasurableSet B →
        P (Z t ⁻¹' B) = ∫⁻ z' in B, ENNReal.ofReal (p t z z')

/-- The coordinate densities of the base diffusion: `pX_t(x, ·)` is the density of the first
(hyperbolic radial) coordinate `X_t` on `[0, ∞)`, `pY_t(y, ·)` that of the second (spherical
radial) coordinate `Y_t` on `[0, 1]`, both nonnegative and continuous on these closed intervals. -/
structure IsBaseCoordDensities (D0 : ℝ) (pX pY : ℝ → ℝ → ℝ → ℝ) : Prop where
  nonnegX : ∀ t : ℝ, 0 < t → ∀ x, 0 ≤ x → ∀ x', 0 ≤ x' → 0 ≤ pX t x x'
  nonnegY : ∀ t : ℝ, 0 < t → ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1, 0 ≤ pY t y y'
  contX : ∀ t : ℝ, 0 < t → ∀ x, 0 ≤ x → ContinuousOn (pX t x) (Ici 0)
  contY : ∀ t : ℝ, 0 < t → ∀ y ∈ Icc (0 : ℝ) 1, ContinuousOn (pY t y) (Icc 0 1)
  lawX : ∀ t : ℝ≥0, 0 < t → ∀ z ∈ baseStrip,
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (Z : ℝ≥0 → Ω → ℝ × ℝ), IsBaseDiffusion P 𝓖 D0 z Z →
      ∀ A : Set ℝ, MeasurableSet A →
        P ((fun ω => (Z t ω).1) ⁻¹' A) = ∫⁻ x' in A, ENNReal.ofReal (pX t z.1 x')
  lawY : ∀ t : ℝ≥0, 0 < t → ∀ z ∈ baseStrip,
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (Z : ℝ≥0 → Ω → ℝ × ℝ), IsBaseDiffusion P 𝓖 D0 z Z →
      ∀ A : Set ℝ, MeasurableSet A →
        P ((fun ω => (Z t ω).2) ⁻¹' A) = ∫⁻ y' in A, ENNReal.ofReal (pY t z.2 y')

/-!
### Bridges
-/

/-- The finite-dimensional bridge density of a kernel `p` from `z` to `e` of length `t`, at times
`ts` with points `zs` (`t₀ = 0`, `z₀ = z`):
`p_{t₁}(z,z₁) p_{t₂-t₁}(z₁,z₂) ⋯ p_{t-t_k}(z_k,e) / p_t(z,e)`, in `[0, ∞]`. -/
def bridgeFddDensity {α : Type*} (p : ℝ → α → α → ℝ) (z e : α) (t : ℝ) {k : ℕ}
    (ts : Fin k → ℝ) (zs : Fin k → α) : ℝ≥0∞ :=
  (∏ i : Fin k, ENNReal.ofReal
      (p (ts i - (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc)
        ((Fin.cons z zs : Fin (k + 1) → α) i.castSucc) (zs i))) *
    ENNReal.ofReal (p (t - (Fin.cons 0 ts : Fin (k + 1) → ℝ) (Fin.last k))
      ((Fin.cons z zs : Fin (k + 1) → α) (Fin.last k)) e) /
    ENNReal.ofReal (p t z e)

/-- The base bridge from `z` to the corner `(0,0)` of length `t`: a process with paths continuous
on `[0, t]`, `Z₀ = z`, `Z_t = (0,0)`, whose finite-dimensional laws at times
`0 < t₁ < ⋯ < t_k < t` have density `bridgeFddDensity p z 0 t` relative to Lebesgue measure. -/
structure IsBaseBridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (t : ℝ) (Z : ℝ → Ω → ℝ × ℝ) : Prop where
  prob : IsProbabilityMeasure P
  meas : ∀ s, Measurable (Z s)
  paths : ∀ᵐ ω ∂P, ContinuousOn (fun s => Z s ω) (Icc 0 t) ∧ Z 0 ω = z ∧ Z t ω = (0, 0)
  fdd : ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i ∧ ts i < t) →
    ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ ω, F (fun i => Z (ts i) ω) ∂P = ∫⁻ zs, F zs * bridgeFddDensity p z (0, 0) t ts zs

/-!
### The absorbing `H` transform
-/

/-- The point `(X_s, Y_s)` of a one-pair dual realization at real time `s`. -/
def dualPoint {Ω : Type*} (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ) (ω : Ω) : ℝ × ℝ :=
  (X s.toNNReal ω 0, Y s.toNNReal ω 0)

/-- The corner-lifetime density `(D₀/2)(x + y) p_t⁰(z, (0,0))`. -/
def cornerLifetimeDensity (D0 : ℝ) (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (t : ℝ) : ℝ :=
  D0 / 2 * (z.1 + z.2) * p t z (0, 0)

open scoped Classical in
/-- The lifetime-bridge lemma; see the module docstring.
`IsDualStart ![x] ![y]` is `(x, y) ∈ baseStrip`, `(x, y) ≠ (0, 0)`. -/
def LifetimeBridgeStatement : Prop :=
  ∀ D0 : ℝ, 0 < D0 → ∃ p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ,
    IsBaseDensity D0 p ∧
    Measurable (fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) ∧
    (∃ pX pY : ℝ → ℝ → ℝ → ℝ, IsBaseCoordDensities D0 pX pY ∧
      ∀ t : ℝ, 0 < t → ∀ z ∈ baseStrip, ∀ z' ∈ baseStrip, p t z z' = pX t z.1 z'.1 * pY t z.2 z'.2) ∧
    ∀ x y : ℝ, IsDualStart ![x] ![y] →
      (∀ t : ℝ, 0 < t → 0 < p t (x, y) (0, 0)) ∧
      (∀ t : ℝ, 0 < t → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (Z : ℝ → Ω → ℝ × ℝ), IsBaseBridge P p (x, y) t Z) ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
        (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
        (∀ g : ℝ → ℝ≥0∞, Measurable g →
          ∫⁻ ω, (if dualExtinction N ω < ⊤ then g (dualExtinction N ω).toReal else 0) ∂P =
            ∫⁻ t in Ioi 0, g t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, y) t)) ∧
        ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
          ∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
            ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < dualExtinction N ω
                then g (dualExtinction N ω).toReal * F (fun i => dualPoint X Y (ts i) ω)
                else 0) ∂P =
              ∫⁻ t in Ioi 0, g t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, y) t) *
                (if ∀ i, ts i < t then ∫⁻ zs, F zs * bridgeFddDensity p (x, y) (0, 0) t ts zs
                  else 0)

end BlockBand.Endpoints
